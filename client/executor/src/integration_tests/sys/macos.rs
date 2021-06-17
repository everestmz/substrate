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

use std::{convert::TryInto, mem::MaybeUninit, ops::Range};
use mach::{
    kern_return::KERN_SUCCESS,
    traps::mach_task_self,
    vm::mach_vm_region,
    vm_page_size::vm_page_shift,
    vm_region::{vm_region_extended_info, vm_region_info_t, VM_REGION_EXTENDED_INFO},
};
use sc_executor_common::wasm_runtime::WasmInstance;

/// Returns how much bytes of the instance's memory is currently resident (backed by phys mem)
pub fn instance_resident_bytes(instance: &dyn WasmInstance) -> usize {
    let range = instance.linear_memory_range().unwrap();
    let regions = get_regions((range.start as u64)..(range.end as u64));
    assert_ne!(regions.len(), 0);
    let resident_pages: u64 = regions.iter().map(|r| u64::from(r.1.pages_resident)).sum();
    let resident_size = unsafe { resident_pages << vm_page_shift };
    resident_size.try_into().unwrap()
}

/// Get all consecutive memory mappings that lie inside the specified range.
///
/// Panics is some parts of the range are unmapped.
pub fn get_regions(range: Range<u64>) -> Vec<(u64, vm_region_extended_info)> {
    let mut regions = Vec::new();
    let mut addr = range.start;

    loop {
        let mut size = MaybeUninit::<u64>::uninit();
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
        let size = unsafe { size.assume_init() };
        let info = unsafe { info.assume_init() };

        regions.push((addr, info));

        // Only continue if the next requested address lies inside the specified range.
        addr += size;
        if addr >= range.end {
            break;
        }
    }

    regions
}
