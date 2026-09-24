// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

$ifdef OPENVM

// A single entry of the read-only program image: the instruction word held
// at `pc`.
struct frozen_program_entry = {
  pc : xlenbits,
  raw_inst : instbits,
}

// The read-only program image: an immutable partial map from address to
// instruction word.  An address with no entry holds no instruction.
register frozen_program : list(frozen_program_entry) = [||]

// The instruction word held at `pc` in `entries`, or None() if no entry
// has that pc.
function lookup_frozen_word(
  pc : xlenbits,
  entries : list(frozen_program_entry)
) -> option(instbits) =
  match entries {
    [||]         => None(),
    entry :: rest =>
      if entry.pc == pc then Some(entry.raw_inst)
      else lookup_frozen_word(pc, rest),
  }

// The instruction word to execute at `pc`, taken from the read-only program
// image.  Only four-byte-aligned addresses can hold an instruction.
function lookup_frozen_instruction(pc : xlenbits) -> option(instbits) =
  // This model disables Ext_Zca, so there is no compressed-instruction path.
  if pc[0] != bitzero | pc[1] != bitzero then None()
  else lookup_frozen_word(pc, frozen_program)

// Instruction fetch resolves against the read-only program image alone,
// discarding the standard fetch result.  An address holding no instruction
// faults.
function ext_fetch_hook(_f : FetchResult) -> FetchResult =
  match lookup_frozen_instruction(PC) {
    Some(word) => F_Base(word),
    None()     => F_Error(E_Fetch_Access_Fault(), PC),
  }

$else

function ext_fetch_hook(f : FetchResult) -> FetchResult = f

$endif

function ext_pre_step_hook()  -> unit = ()
function ext_post_step_hook() -> unit = ()

function ext_reset() -> unit = ()
