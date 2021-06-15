// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Implementation of macOS specific tests and/or helper functions.

use std::{convert::TryInto, mem::MaybeUninit};
use mach::{
    kern_return::KERN_SUCCESS,
    traps::mach_task_self,
    vm::mach_vm_region,
    vm_page_size::vm_page_shift,
    vm_region::{vm_region_extended_info, vm_region_info_t, VM_REGION_EXTENDED_INFO},
    vm_types::{mach_vm_address_t, mach_vm_size_t},
};
use sc_executor_common::wasm_runtime::WasmInstance;

/// Returns how much bytes of the instance's memory is currently resident (backed by phys mem)
pub fn instance_resident_bytes(instance: &dyn WasmInstance) -> usize {
    let requested_addr = instance.linear_memory_base_ptr().unwrap() as usize;
	let mut addr: mach_vm_address_t = requested_addr.try_into().unwrap();
    let mut size = MaybeUninit::<mach_vm_size_t>::uninit();
    let mut info = MaybeUninit::<vm_region_extended_info>::uninit();
    let result = unsafe {
        mach_vm_region(
            mach_task_self(),
            &mut addr,
            size.as_mut_ptr(),
            VM_REGION_EXTENDED_INFO,
            (info.as_mut_ptr()) as vm_region_info_t,
            &mut vm_region_extended_info::count(),
            &mut 0,
        )
    };
    assert_eq!(result, KERN_SUCCESS, "mach_vm_region returned an error");
    let info = unsafe { info.assume_init() };
    let resident_size = unsafe { info.pages_resident << vm_page_shift };
    resident_size.try_into().unwrap()
}
