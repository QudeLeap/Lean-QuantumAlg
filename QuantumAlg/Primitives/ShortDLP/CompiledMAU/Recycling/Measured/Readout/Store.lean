/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Chronological
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Source

/-!
# Exact real output values of both original exponent streams

The actual second stream preserves every first-stream result. The complete
output is its existing fixed vector of real binary cells; these equations
describe no integer packing instruction and impose no old-Store condition.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (Bits tupleCoordinates)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ReadoutStoreCtx := context base noQuantum m ell width

/-- A real exponent changes only its own original selected result cells. -/
lemma exponentOutputStore_preserves_result {bits : Nat}
    (selection : Fin bits → Fin (resultBits m ell)) (result : Fin (resultBits m ell))
    (separate : ∀ index, selection index ≠ result) (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (store : Store (ReadoutStoreCtx base noQuantum m ell width)) (outcome : Bits remaining) :
    (exponentOutputStore base noQuantum m ell width selection remaining position bounded store
      outcome).read (.storage (resultCell base noQuantum m ell width result).toCStorageRef) =
        store.read (.storage (resultCell base noQuantum m ell width result).toCStorageRef) := by
  induction remaining generalizing position store with
  | zero => rfl
  | succ remaining induction =>
      rcases outcome with ⟨bit, tail⟩
      change (exponentOutputStore base noQuantum m ell width selection remaining (position + 1)
        (by omega) (store.write
          (resultCell base noQuantum m ell width (selection ⟨position, by omega⟩)) (.finite bit))
        tail).read _ = _
      rw [induction]
      apply Store.read_write_other
      intro same
      exact separate ⟨position, by omega⟩
        (resultCell_key_injective base noQuantum m ell width same)

/-- The complete second exponent leaves every first exponent's true result unchanged. -/
lemma memberReadoutStore_first (store : Store (ReadoutStoreCtx base noQuantum m ell width))
    (outcome : MemberReadouts m ell) (position : Fin (ell + m)) :
    (memberReadoutStore base noQuantum m ell width store outcome).read
        (.storage
          (resultCell base noQuantum m ell width (Fin.castAdd ell position)).toCStorageRef) =
      .finite (tupleCoordinates (ell + m) outcome.1 position) := by
  have separate : ∀ index : Fin ell,
      Fin.natAdd (ell + m) index ≠ Fin.castAdd ell position := by
    intro index same
    have values : ell + m + index.val = position.val := congrArg Fin.val same
    have bound := position.isLt
    omega
  have preserved := exponentOutputStore_preserves_result base noQuantum m ell width
    (fun index : Fin ell => Fin.natAdd (ell + m) index) (Fin.castAdd ell position) separate ell 0
    (by omega)
    (exponentOutputStore base noQuantum m ell width
      (fun index : Fin (ell + m) => Fin.castAdd ell index) (ell + m) 0 (by omega) store outcome.1)
    outcome.2
  exact preserved.trans (exponentOutputStore_read base noQuantum m ell width
    (fun index : Fin (ell + m) => Fin.castAdd ell index) (Fin.castAdd_injective _ _) store outcome.1
    position)

/-- Every second exponent result is its own original measured output, for arbitrary old Stores. -/
lemma memberReadoutStore_second (store : Store (ReadoutStoreCtx base noQuantum m ell width))
    (outcome : MemberReadouts m ell) (position : Fin ell) :
    (memberReadoutStore base noQuantum m ell width store outcome).read
        (.storage (resultCell base noQuantum m ell width
          (Fin.natAdd (ell + m) position)).toCStorageRef) =
      .finite (tupleCoordinates ell outcome.2 position) := by
  apply exponentOutputStore_read base noQuantum m ell width
    (fun index : Fin ell => Fin.natAdd (ell + m) index) _ _ outcome.2 position
  intro first second same
  apply Fin.ext
  have values : ell + m + first.val = ell + m + second.val := congrArg Fin.val same
  omega

/-- The existing actual fixed-vector output contains exactly both original chronological tuples. -/
def memberReadoutValue (outcome : MemberReadouts m ell) :
    CShape.Value (.fixedVector (resultBits m ell) (.finite 2)) :=
  .fixedVector fun index => .finite (Fin.addCases
    (tupleCoordinates (ell + m) outcome.1) (tupleCoordinates ell outcome.2) index)

/-- Real complete output observation is independent of every overwritten or unrelated old value. -/
lemma memberReadoutStore_resultRead (store : Store (ReadoutStoreCtx base noQuantum m ell width))
    (outcome : MemberReadouts m ell) :
    (resultRead base noQuantum m ell width).eval
        (memberReadoutStore base noQuantum m ell width store outcome) =
      memberReadoutValue m ell outcome := by
  apply congrArg CShape.Value.fixedVector
  funext index
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index
  · have coordinate : Fin.addCases (motive := fun _ => Fin 2)
        (tupleCoordinates (ell + m) outcome.1) (tupleCoordinates ell outcome.2)
        (Fin.castAdd ell first) = tupleCoordinates (ell + m) outcome.1 first :=
      Fin.addCases_left first
    exact (memberReadoutStore_first base noQuantum m ell width store outcome first).trans
      (congrArg (fun bit : Fin 2 => (CShape.Value.finite bit : CShape.Value (.finite 2)))
        coordinate.symm)
  · have coordinate : Fin.addCases (motive := fun _ => Fin 2)
        (tupleCoordinates (ell + m) outcome.1) (tupleCoordinates ell outcome.2)
        (Fin.natAdd (ell + m) second) = tupleCoordinates ell outcome.2 second :=
      Fin.addCases_right second
    exact (memberReadoutStore_second base noQuantum m ell width store outcome second).trans
      (congrArg (fun bit : Fin 2 => (CShape.Value.finite bit : CShape.Value (.finite 2)))
        coordinate.symm)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
