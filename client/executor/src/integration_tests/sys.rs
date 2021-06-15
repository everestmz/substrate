// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Low level operating system dependend tests.

// Constrain this only to wasmtime for the time being. Without this rustc will complain on unused
// imports and items. The alternative is to plop `cfg(feature = wasmtime)` everywhere which seems
// borthersome.
#![cfg(feature = "wasmtime")]

#[cfg(target_os = "linux")]
mod linux;

#[cfg(target_os = "linux")]
use linux::*;

#[cfg(target_os = "macos")]
mod macos;

#[cfg(target_os = "macos")]
use macos::*;

use crate::{
	WasmExecutionMethod,
	integration_tests::mk_test_runtime,
};
use codec::Encode as _;
#[cfg(target_os = "linux")]
use linux::*;

#[test]
fn memory_consumption_compiled() {
	// This aims to see if linear memory stays backed by the physical memory after a runtime call.
	//
	// For that we make a series of runtime calls, probing the RSS for the VMA matching the linear
	// memory. After the call we expect RSS to be equal to 0.

	let runtime = mk_test_runtime(WasmExecutionMethod::Compiled, 1024);

	let instance = runtime.new_instance().unwrap();
	let heap_base = instance
		.get_global_const("__heap_base")
		.expect("`__heap_base` is valid")
		.expect("`__heap_base` exists")
		.as_i32()
		.expect("`__heap_base` is an `i32`");

	instance
		.call_export(
			"test_dirty_plenty_memory",
			&(heap_base as u32, 1u32).encode(),
		)
		.unwrap();
	let probe_1 = instance_resident_bytes(&*instance);
	instance
		.call_export(
			"test_dirty_plenty_memory",
			&(heap_base as u32, 1024u32).encode(),
		)
		.unwrap();
	let probe_2 = instance_resident_bytes(&*instance);

	assert_eq!(probe_1, 0);
	assert_eq!(probe_2, 0);
}
