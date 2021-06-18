// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Defines a custom memory allocator for allocating host memory on the mach kernel.
//! This is needed in order to support purgable memory on macOS.

use std::sync::atomic::{AtomicU32, Ordering};
use bitflags::bitflags;
use libc::c_int;
use mach::{
    kern_return::KERN_SUCCESS,
    traps::mach_task_self,
	port::mach_port_t,
    vm::{mach_vm_allocate, mach_vm_deallocate, mach_vm_protect},
    vm_prot::{vm_prot_t, VM_PROT_NONE, VM_PROT_DEFAULT},
	vm_page_size::vm_page_size,
};
use wasmtime::{MemoryCreator, LinearMemory, MemoryType};

/// The size of wasm page. 2^WASM_PAGE_SHIFT = bytes per wasm page
const WASM_PAGE_SHIFT: u8 = 16;

bitflags! {
	/// Some of the flags that are allowed for `mach_vm_allocate`.
	///
	/// https://github.com/apple/darwin-xnu/blob/main/osfmk/mach/vm_statistics.h
	struct VmFlags: c_int {
		const FIXED = 0x0000;
		const ANYWHERE = 0x0001;
		const PURGABLE = 0x0002;
		const RANDOM_ADDR = 0x0008;
	}
}

/// Allocator that can allocate memory for wasmtime module instances.
pub struct Allocator {
	/// The task that spawned the allocator.
	task: mach_port_t,
}

/// One memory area allocated by [`Allocator`].
#[derive(Debug)]
pub struct Memory {
	/// The task that allocated this memory.
	task: mach_port_t,
	/// The virtual address of the mapping.
	address: u64,
	/// The size of the mapping created in bytes.
	///
	/// If this memory is grown beyond the virtual size we would need to allocate a new
	/// a new mapping and copy over. However, this would only happen on 32bit systems
	/// where not enough virtual space is available. Those systems are not supported
	/// anyways for macos.
	///
	/// # Note
	///
	/// This includes the guard bytes which are mapped but never accessible.
	mapped_bytes: u64,
	/// Size of the guard pages in bytes.
	guard_bytes: u64,
	/// The currently accesible number of wasm pages.
	///
	/// Starting with wasmtime 0.28 we can remove the atomic as `LinearMemory::grow` has
	/// an exclusive reference to this struct.
	wasm_pages: AtomicU32,
	/// The maximum number was wasm pages this memory is allowed to be growed to.
	wasm_pages_max: Option<u32>,
}

impl Allocator {
	/// Allocate some memory and return the address to it in the `address` field.
	fn allocate(&self, address: &mut u64, size: u64, flags: VmFlags) -> Result<(), String> {
		// # Safety
		//
		// We do not allow passing of `VM_FLAGS_OVERWRITE` which would allow overwriting
		// existing virtual regions. Other from that allocating memory is safe.
		let result = unsafe {
			// The `mach_vm` interface always returns page aligned addresses.
			mach_vm_allocate(self.task, address, size, flags.bits())
		};
		if result == KERN_SUCCESS {
			Ok(())
		} else {
			Err(format!(
				"mach_vm_allocate returned: {}. address: 0x{:08x} size: 0x{:08x} flags: {:?}",
				result, address, size, flags,
			))
		}
	}
}

impl Default for Allocator {
	fn default() -> Self {
		// # Safety
		//
		// There are no preconditions. It is unsafe only because it is a C-API.
		let task = unsafe { mach_task_self() };
		Self {
			task,
		}
	}
}

unsafe impl MemoryCreator for Allocator {
    fn new_memory(
        &self,
        ty: MemoryType,
        reserved_bytes: Option<u64>,
        guard_bytes: u64
    ) -> Result<Box<dyn LinearMemory>, String> {
		let mapped_bytes = mapped_bytes(&ty, reserved_bytes, guard_bytes)?;
		let anon_max_size = anon_max_size();

		let mut address = 0;
		self.allocate(
			&mut address,
			mapped_bytes.min(anon_max_size),
			VmFlags::ANYWHERE | VmFlags::RANDOM_ADDR | VmFlags::PURGABLE,
		)?;

		// Purgable mappings in macOS are at most `ANON_MAX_SIZE` large. We opt for a simple
		// allocator where only the first mapping is purgable and all the rest is allocated
		// unpurgable. When purging the memory only the first mapping is purged. This means
		// as soon as any wasm instance uses more than `ANON_MAX_SIZE` memory anything above
		// this threshold won't be purged. This is OK because we are not allowed to rely on
		// purging semantics. It is merely to reduce the memory footprint.
		//
		// # Note
		//
		// `ANON_MAX_SIZE` is 4GB - 1 page. This means that at most one page won't be purged
		// as memory sizes above 4GB don't make much sense.
		if mapped_bytes > anon_max_size {
			let mut address = address + anon_max_size;
			self.allocate(&mut address, mapped_bytes - anon_max_size, VmFlags::FIXED)?;
		}

		let memory = Box::new(Memory {
			task: self.task,
			address,
			mapped_bytes,
			guard_bytes,
			wasm_pages: AtomicU32::new(ty.limits().min()),
			wasm_pages_max: ty.limits().max(),
		});

		// We map all the reserved memory but only allow access to current the size of
		// the memory from point of view of the wasm instance.
		memory.protect()?;

		Ok(memory)
	}
}

impl Memory {
	/// Change the memory permissions of the specified range.
	///
	/// # Safety
	///
	/// Caller must make sure that the supplied range and state won't interfere with
	/// the correctness of the running program.
	unsafe fn change_prot(&self, addr: u64, size: u64, prot: vm_prot_t) -> Result<(), String> {
		let result = mach_vm_protect(self.task, addr, size, 0, prot);
		if result == KERN_SUCCESS {
			Ok(())
		} else {
			Err(format!("mach_vm_protect returned: {}", result))
		}
	}

	/// Free the specified memory.
	///
	/// # Safety
	///
	/// The caller must make sure that the memory is no longer in use.
	unsafe fn free(&self, address: u64, size: u64) -> Result<(), String> {
		let result =  mach_vm_deallocate(self.task, address, size);
		if result == KERN_SUCCESS {
			Ok(())
		} else {
			Err(format!(
				"mach_vm_deallocate returned: {}. address: 0x{:08x} size: 0x{:08x}",
				result, address, size
			))
		}
	}

	/// Returns number of currently accessible bytes.
	fn accessible_bytes(&self) -> u64 {
		(self.size() as u64) << WASM_PAGE_SHIFT
	}

	/// Remove permissions to access currently unaccessible bytes.
	fn protect(&self) -> Result<(), String> {
		let accessible_bytes = self.accessible_bytes();

		// # Safety
		//
		// We made sure when creating a memory that the calculated addresses are fully
		// located within the instances memory.
		unsafe {
			self.change_prot(
				self.address + accessible_bytes,
				self.mapped_bytes - accessible_bytes,
				VM_PROT_NONE,
			)
		}
	}

	/// Add permissions to access currently accessible bytes.
	fn increase_accessible_bytes(&self) -> Option<u64> {
		let accessible_bytes = self.accessible_bytes();

		// We do not support 32bit applications on macOS.
		assert!(accessible_bytes.checked_add(self.guard_bytes).unwrap() > self.mapped_bytes,
			"No memory relocation supported on macos. This will only happen on 32bit systems.");

		// # Safety
		//
		// We made sure when creating a memory that the calculated addresses are fully
		// located within the instances memory.
		unsafe {
			self.change_prot(self.address, accessible_bytes, VM_PROT_DEFAULT).ok()?;
		}

		Some(accessible_bytes)
	}
}

unsafe impl LinearMemory for Memory {
    fn size(&self) -> u32 {
		self.wasm_pages.load(Ordering::Acquire)
	}

    fn maximum(&self) -> Option<u32> {
		self.wasm_pages_max
	}

    fn grow(&self, delta: u32) -> Option<u32> {
		self.wasm_pages.fetch_update(Ordering::SeqCst, Ordering:: SeqCst, |pages| {
			let pages = pages.checked_add(delta)?;
			if let Some(max) = self.wasm_pages_max {
				if pages > max {
					return None;
				}
			}
			Some(pages)
		}).ok()?;

		// All the memory is already mapped. We just need to allow access.
		self.increase_accessible_bytes().map(|bytes| (bytes >> WASM_PAGE_SHIFT) as _)
	}

    fn as_ptr(&self) -> *mut u8 {
		self.address as _
	}
}

impl Drop for Memory {
	fn drop(&mut self) {
		let anon_max_size = anon_max_size();

		// # Safety
		//
		// The memory got dropped which means no reference to the memory exist. Therefore
		// it is no longer in use and can be freed safely.
		let result = unsafe {
			self.free(self.address, self.mapped_bytes.min(anon_max_size)).and_then(|_| {
				if self.mapped_bytes > anon_max_size {
					self.free(self.address + anon_max_size, self.mapped_bytes - anon_max_size)
				} else {
					Ok(())
				}
			})
		};

		if let Err(err) = result {
			log::error!("deallocating instance memory failed with: {}.\n{:#?}", err, self);
		}
	}
}

/// Max size of a purgable mapping in bytes.
///
/// https://github.com/apple/darwin-xnu/blob/main/osfmk/mach/vm_param.h
fn anon_max_size() -> u64 {
	// # Safety
	//
	// There are no preconditions. It is unsafe only because it is a C-API.
	(1u64 << 32) - unsafe { vm_page_size } as u64
}

fn mapped_bytes(ty: &MemoryType, reserved: Option<u64>, guard: u64) -> Result<u64, String> {
	let accessible_bytes = (u64::from(ty.limits().min())) << WASM_PAGE_SHIFT;
	let mapped_bytes = if let Some(reserved) = reserved {
		reserved.max(accessible_bytes)
	} else {
		accessible_bytes
	}
	.checked_add(guard)
	.ok_or_else(|| "Guard size overflowed u64".to_string())?;
	Ok(mapped_bytes)
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_executor_common::test_utils::{get_regions, Region};
	use wasmtime::Limits;

	const DEFAULT_RESERVED: u64 = 4 * 1024 * 1024 * 1024;
	const DEFAULT_GUARD: u64 = 2 * 1024 * 1024 * 1024;

	fn create_memory(
		ty: MemoryType,
		reserved: Option<u64>,
		guard: u64
	) -> (Box<dyn LinearMemory>, Vec<(u64, Region)>)
	{
		let allocator = Allocator::default();
		let mem = allocator.new_memory(ty.clone(), reserved, guard).unwrap();
		let start = mem.as_ptr() as u64;
		let mapped_bytes = mapped_bytes(&ty, reserved, guard).unwrap();
		let regions = get_regions(start..(start + mapped_bytes));
		(mem, regions)
	}

	#[test]
	fn alloc_works() {
		let ty = MemoryType::new(Limits::at_least(1));
		let (_, regions) = create_memory(ty, Some(DEFAULT_RESERVED), DEFAULT_GUARD);
		assert_eq!(regions.len(), 3);
	}
}
