/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement.Resources
import Mathlib.Tactic.Ring

/-!
# Place the HRS controlled increment inside the existing low word

The low word contains `extra + high` bits. Its least-significant `high`
bits supply the incrementer's borrowed word; its `extra` leading bits are
untouched. The target is the high word and the final wire is the dirty
control [HRS16, paper.tex:219-226,232-260]. Only an identity tensor extension
and a parenthesis change of the same big-endian basis label are used.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

/-- Reassociate widths without permuting any physical or basis bit. -/
def incrementPlacementIndex (extra high : Nat) :
    Fin (2 ^ (extra + (high + high + 1))) ≃ Fin (2 ^ ((extra + high) + high + 1)) :=
  finCongr (congrArg (fun width : Nat => 2 ^ width) (by omega))

/-- The exact basis-label equation for the unchanged physical bit order. -/
theorem hrsIncrementPlacementIndex_encode (extra high : Nat)
    (unused : Fin (2 ^ extra)) (borrowed target : Fin (2 ^ high)) (dirty : Bool) :
    incrementPlacementIndex extra high
        (prodEquiv (unused, (TTK.overflowEncoding high).encode ((borrowed, target), dirty))) =
      (bridgeEncoding (extra + high) high).encode
        ((prodEquiv (unused, borrowed), target), dirty) := by
  apply Fin.ext
  change (BinaryLabelEncoding.bool.encode dirty).val +
      2 ^ 1 * (target.val + 2 ^ high * borrowed.val) +
      2 ^ (high + high + 1) * unused.val =
    (BinaryLabelEncoding.bool.encode dirty).val +
      2 ^ 1 * (target.val + 2 ^ high * (borrowed.val + 2 ^ high * unused.val))
  simp only [pow_add, pow_one]
  ring

/-- Run the actual internally borrowed incrementer after the untouched leading bits. -/
def placedIncrementProgram (extra high : Nat) :
    UnitaryCircuit (Qubits (bridgeEncoding (extra + high) high).width) :=
  UnitaryCircuit.reindex (incrementPlacementIndex extra high)
    (UnitaryCircuit.prodRight (m := extra) (controlledBorrowedIncrementProgram high))

/-- The placed actual program increments only the high word when the dirty bit is set. -/
theorem hrsPlacedIncrement_realizes (extra high : Nat) :
    UnitaryCircuit.Realizes (bridgeEncoding (extra + high) high)
      (placedIncrementProgram extra high) bridgeIncrementStep where
  apply_encoded_ket := by
    rintro ⟨⟨low, target⟩, dirty⟩
    obtain ⟨⟨unused, borrowed⟩, rfl⟩ :=
      (prodEquiv (m := extra) (n := high)).surjective low
    have hrun := ((hrsControlledBorrowedIncrement_realizes high).prodRight
      (left := BinaryLabelEncoding.finIdentity extra)).apply_encoded_ket
        (unused, ((borrowed, target), dirty))
    have hplaced := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (extra + (high + high + 1)))
      (S := Qubits ((extra + high) + high + 1))
      (incrementPlacementIndex extra high)
      (UnitaryCircuit.prodRight (m := extra) (controlledBorrowedIncrementProgram high))
      _ _ hrun
    change (placedIncrementProgram extra high).applyNormalized
        (NormalizedVector.ket (incrementPlacementIndex extra high
          (prodEquiv (unused,
            (TTK.overflowEncoding high).encode ((borrowed, target), dirty))))) =
      NormalizedVector.ket (incrementPlacementIndex extra high
        (prodEquiv (unused, (TTK.overflowEncoding high).encode
          (controlledBorrowedIncrementOutput ((borrowed, target), dirty))))) at hplaced
    cases dirty <;>
      simpa only [controlledBorrowedIncrementOutput, Bool.false_eq_true, if_false, if_true,
        borrowedIncrementOutput, hrsIncrementPlacementIndex_encode,
        bridgeIncrementStep, incrementWord] using hplaced

/-- The actual footprint stays inside the low word, high word, and one dirty bit. -/
theorem hrsPlacedIncrement_physical_range (extra high : Nat) :
    (placedIncrementProgram extra high).physical_idx ⊆ List.range ((extra + high) + high + 1) := by
  have hsource := EncodedBit.GateSpec.programList_physical_idx_subset_range
    (controlledBorrowedIncrementGates high)
  have hplaced := UnitaryCircuit.prodRight_physical_idx_subset_range
    (m := extra) (controlledBorrowedIncrementProgram high) hsource
  intro index hindex
  have hlt := List.mem_range.mp (hplaced hindex)
  apply List.mem_range.mpr
  change index < extra + (high + high + 1) at hlt
  omega

/-- Placement retains the original actual native-event ledger and evaluated depth. -/
theorem hrsPlacedIncrement_resources (extra high : Nat)
    (assign : Resource.Event .quantum → Nat) :
    (placedIncrementProgram extra high).eventCost =
        (controlledBorrowedIncrementProgram high).eventCost ∧
      (placedIncrementProgram extra high).evaluatedEventDepth assign =
        (controlledBorrowedIncrementProgram high).evaluatedEventDepth assign := by
  constructor
  · change (UnitaryCircuit.prodRight (m := extra)
      (controlledBorrowedIncrementProgram high)).eventCost = _
    exact UnitaryCircuit.prodRight_eventCost _
  · change (UnitaryCircuit.prodRight (m := extra)
      (controlledBorrowedIncrementProgram high)).evaluatedEventDepth assign = _
    exact UnitaryCircuit.prodRight_evaluatedEventDepth assign _

end

end QuantumAlg.MAU.Addition.HRS
