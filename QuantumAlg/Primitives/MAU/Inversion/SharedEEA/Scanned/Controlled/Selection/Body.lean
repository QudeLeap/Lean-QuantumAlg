/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Specification
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Sandwich

/-!
# Actual complete address preparation, selected scan and inverse cleanup

The complete body is unchanged. Its full source action follows from the
already certified original phase-enable/body/phase-enable program by
injectivity of the actual original enable unitary. The proof never
expands a concrete-width selector or physical gate word.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelectionBody

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The full actual original address preparation, pruned traversal and same-source adjoint. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  (AddressPreparation.program width).seq ((SelectionScan.program width).seq
    ((AddressPreparation.program width).dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

def step (width : Nat) (state : Scanned.Data width) : Scanned.Data width :=
  (SelectionSpecification.selectedSource width state.1, state.2)

/-- Complete all-label body semantics retain arbitrary conjunction and the whole clean scan pool. -/
lemma program_apply_encoded_ket (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Scanned.Data width)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (prefixZero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (program width).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (step width state))) := by
  let input := SelectionEnable.step width state
  have first := (SelectionEnable.program_realizes width environment).apply_encoded_ket input
  rw [SelectionEnable.step_step] at first
  have last := (SelectionEnable.program_realizes width environment).apply_encoded_ket
    (step width state)
  have original := PreparedSelection.program_apply_sourceStep width environment input
    addressZero prefixZero
  have sourceEq : SelectionSpecification.sourceStep width
        (SelectionEnable.sourceStep width state.1) =
      SelectionEnable.sourceStep width (SelectionSpecification.selectedSource width state.1) := by
    have actual := SelectionSpecification.enable_selected_enable width
      (SelectionEnable.sourceStep width state.1)
    rw [SelectionSpecification.enable_twice] at actual
    exact actual.symm
  change (PreparedSelection.program width).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((Scanned.encoding width).encode input))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((Scanned.encoding width).encode
        (SelectionSpecification.sourceStep width (SelectionEnable.sourceStep width state.1),
          state.2))) at original
  rw [sourceEq] at original
  change (PreparedSelection.program width).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((Scanned.encoding width).encode input))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((Scanned.encoding width).encode (SelectionEnable.step width (step width state)))) at original
  apply SelectedSandwich.applyNormalized_injective (SelectionEnable.program width) environment
  rw [last]
  have originalFirst : ((SelectionEnable.program width).seq
      ((program width).seq (SelectionEnable.program width))).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode input))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((Scanned.encoding width).encode
        (SelectionEnable.step width (step width state)))) := by
    simpa only [PreparedSelection.program, program, UnitaryCircuit.applyNormalized_seq]
      using original
  simpa only [UnitaryCircuit.applyNormalized_seq, first] using originalFirst

lemma step_disabled (width : Nat) (state : Scanned.Data width)
    (disabled : state.1.control = false) : step width state = state := by
  simp only [step, SelectionSpecification.selectedSource, disabled, Bool.false_eq_true, if_false]

lemma step_pool (width : Nat) (state : Scanned.Data width) : (step width state).2 = state.2 := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelectionBody
