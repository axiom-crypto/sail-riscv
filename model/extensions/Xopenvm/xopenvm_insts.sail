// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject to the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// OpenVM instruction extension: I/O and execution control.

enum clause extension = Ext_Xopenvm
mapping clause extensionName = Ext_Xopenvm <-> "xopenvm"
function clause hartSupports(Ext_Xopenvm) = config extensions.Xopenvm.supported

type openvm_public_values_size : Int = 536870912
let openvm_public_values_size = sizeof(openvm_public_values_size)

let openvm_hint_word_limit : int = 1024

// Hint instructions consume a prefix of this byte oracle.
register hint_oracle : list(bits(8)) = [||]

// Public values are 2^29 address-indexed bytes.
register reveal : vector(openvm_public_values_size, bits(8)) = vector_init(0x00)

function clause currentlyEnabled(Ext_Xopenvm) = hartSupports(Ext_Xopenvm)

// Pop one hint byte, returning zero when the oracle is empty.
function next_hint_byte() -> bits(8) =
  match hint_oracle {
    [||]      => 0x00,
    b :: rest => { hint_oracle = rest; b },
  }

// Interpret a guest public-values address as its unsigned byte index.
function reveal_index(addr : xlenbits) -> int = unsigned(addr)

type reveal_index_constraint('n) = 0 <= 'n & 'n + 4 <= openvm_public_values_size
type reveal_index = { 'n, reveal_index_constraint('n). int('n) }

// Replace four consecutive public-value bytes in little-endian order.
function record_reveal(index : reveal_index, value : xlenbits) -> unit = {
  reveal[index] = value[7 .. 0];
  reveal[index + 1] = value[15 .. 8];
  reveal[index + 2] = value[23 .. 16];
  reveal[index + 3] = value[31 .. 24];
}

// Store `n` little-endian oracle words at consecutive data-memory addresses.
function store_hint_words(addr : xlenbits, n : int) -> ExecutionResult = {
  if n <= 0 then RETIRE_SUCCESS
  else {
    let b0 = next_hint_byte();
    let b1 = next_hint_byte();
    let b2 = next_hint_byte();
    let b3 = next_hint_byte();
    let w : word = b3 @ b2 @ b1 @ b0;
    match mem_write_value(
      Physaddr(zero_extend(addr)),
      4,
      w,
      Store(Data),
      PBMT_PMA,
      false,
      false,
      false
    ) {
      Ok(true)  => store_hint_words(addr + 4, n - 1),
      Ok(false) => internal_error(__FILE__, __LINE__, "OpenVM hint store got false from mem_write_value"),
      Err(exc_addr, e) => memory_exception(Virtaddr(truncate(bits_of(exc_addr), xlen)), e),
    }
  }
}
termination_measure store_hint_words(_, n) = n

// Validate and store a bounded hint block in the OpenVM user-memory domain.
function execute_hint_words(addr : xlenbits, n : int) -> ExecutionResult = {
  let base = unsigned(addr);
  let end_addr = base + 4 * n;
  if n < 0 | openvm_hint_word_limit <= n then Illegal_Instruction()
  else if base % 4 != 0 then memory_exception(Virtaddr(addr), E_SAMO_Addr_Align())
  else if openvm_public_values_size <= base then memory_exception(Virtaddr(addr), E_SAMO_Access_Fault())
  else if openvm_public_values_size < end_addr then memory_exception(Virtaddr(addr), E_SAMO_Access_Fault())
  else store_hint_words(addr, n)
}

// TERMINATE sets the completion flag and exit code while preserving the PC.
union clause instruction = OPENVM_TERMINATE : (regidx, regidx, bits(12))

mapping clause encdec = OPENVM_TERMINATE(rd, rs1, code)
  <-> code @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0001011
  when currentlyEnabled(Ext_Xopenvm)

function clause execute OPENVM_TERMINATE(_rd, _rs1, code) = {
  htif_done = true;
  htif_exit_code = zero_extend(code);
  nextPC = PC;
  RETIRE_SUCCESS
}

// HINT_STOREW consumes one oracle word into data memory at `X(rd)`.
union clause instruction = OPENVM_HINT_STOREW : (regidx, regidx)

mapping clause encdec = OPENVM_HINT_STOREW(rd, rs1)
  <-> 0b000000000000 @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0001011
  when currentlyEnabled(Ext_Xopenvm)

function clause execute OPENVM_HINT_STOREW(rd, _rs1) = {
  execute_hint_words(X(rd), 1)
}

// HINT_BUFFER consumes `X(rs1)` oracle words into data memory at `X(rd)`.
union clause instruction = OPENVM_HINT_BUFFER : (regidx, regidx)

mapping clause encdec = OPENVM_HINT_BUFFER(rd, rs1)
  <-> 0b000000000001 @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0001011
  when currentlyEnabled(Ext_Xopenvm)

function clause execute OPENVM_HINT_BUFFER(rd, rs1) = {
  let count = unsigned(X(rs1));
  execute_hint_words(X(rd), count)
}

// REVEAL writes `X(rs1)` at the bounded public-values index `X(rd) + sign_extend(imm)`.
union clause instruction = OPENVM_REVEAL : (regidx, regidx, bits(12))

mapping clause encdec = OPENVM_REVEAL(rd, rs1, imm)
  <-> imm @ encdec_reg(rs1) @ 0b010 @ encdec_reg(rd) @ 0b0001011
  when currentlyEnabled(Ext_Xopenvm)

function clause execute OPENVM_REVEAL(rd, rs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let addr : xlenbits = X(rd) + offset;
  let index = reveal_index(addr);
  if unsigned(addr) % 4 != 0 then Illegal_Instruction()
  else if 0 <= index & index + 4 <= openvm_public_values_size then {
    record_reveal(index, X(rs1));
    RETIRE_SUCCESS
  } else Illegal_Instruction()
}

// PHANTOM has no guest-state effect.
union clause instruction = OPENVM_PHANTOM : (regidx, regidx, bits(12))

mapping clause encdec = OPENVM_PHANTOM(rd, rs1, imm)
  <-> imm @ encdec_reg(rs1) @ 0b011 @ encdec_reg(rd) @ 0b0001011
  when currentlyEnabled(Ext_Xopenvm)

function clause execute OPENVM_PHANTOM(_rd, _rs1, _imm) = RETIRE_SUCCESS
