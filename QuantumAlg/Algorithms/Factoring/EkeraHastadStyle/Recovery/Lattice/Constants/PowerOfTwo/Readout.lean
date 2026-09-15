/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Constants.PowerOfTwo

/-!
# Actual stored values of lattice power-of-two loading

The original increment and left shifts compute the fixed-width residue of
`2 ^ count * (old + 1)` for every input word. In particular, the zero word
provided by fresh basis allocation becomes `2 ^ count` modulo the actual
word capacity. Every structural read outside that one destination survives.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.PowerOfTwo

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem increment_read (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((store.applyOp (incrementOp output)).read (.storage output.toCStorageRef)).toNat =
      ((store.read (.storage output.toCStorageRef)).toNat + 1) % 2 ^ width :=
  congrArg CShape.Value.toNat (Store.read_applyOp_output store (incrementOp output))

private theorem shift_read (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((store.applyOp (shiftOp output)).read (.storage output.toCStorageRef)).toNat =
      (2 * (store.read (.storage output.toCStorageRef)).toNat) % 2 ^ width :=
  congrArg CShape.Value.toNat (Store.read_applyOp_output store (shiftOp output))

private theorem shifts_read (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((shiftsStore count output store).read (.storage output.toCStorageRef)).toNat =
      (2 ^ count * (store.read (.storage output.toCStorageRef)).toNat) % 2 ^ width := by
  induction count generalizing store with
  | zero =>
      change (store.read (.storage output.toCStorageRef)).toNat =
        (2 ^ 0 * (store.read (.storage output.toCStorageRef)).toNat) % 2 ^ width
      simpa only [Nat.pow_zero, Nat.one_mul] using
        (Nat.mod_eq_of_lt (store.read (.storage output.toCStorageRef)).toNat_lt).symm
  | succ count ih =>
      change ((shiftsStore count output (store.applyOp (shiftOp output))).read
        (.storage output.toCStorageRef)).toNat = _
      refine (ih _).trans ?_
      rw [shift_read, Nat.mul_mod_mod, Nat.pow_succ, Nat.mul_assoc]

/-- The actual loading sequence computes the original residue for every incoming word. -/
theorem nativeLattice_powerOfTwo_read (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((storeStep count output store).read (.storage output.toCStorageRef)).toNat =
      (2 ^ count * ((store.read (.storage output.toCStorageRef)).toNat + 1)) % 2 ^ width := by
  refine (shifts_read count output (store.applyOp (incrementOp output))).trans ?_
  rw [increment_read, Nat.mul_mod_mod]

/-- An internally established zero word becomes the required power-of-two residue. -/
theorem nativeLattice_powerOfTwo_read_zero (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (zero : (store.read (.storage output.toCStorageRef)).toNat = 0) :
    ((storeStep count output store).read (.storage output.toCStorageRef)).toNat =
      2 ^ count % 2 ^ width := by
  rw [nativeLattice_powerOfTwo_read, zero, Nat.zero_add, Nat.mul_one]

private theorem shifts_read_other (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (different : output.key ∉ other.storageKeys) (store : Store ctx) :
    (shiftsStore count output store).read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (shiftsStore count output (store.applyOp (shiftOp output))).read other = _
      exact (ih _).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (shiftOp output) other different)

/-- The actual loading leaves all original structural reads outside its destination unchanged. -/
theorem nativeLattice_powerOfTwo_read_other (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (different : output.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep count output store).read other = store.read other :=
  (shifts_read_other count output other different (store.applyOp (incrementOp output))).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (incrementOp output) other different)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.PowerOfTwo
