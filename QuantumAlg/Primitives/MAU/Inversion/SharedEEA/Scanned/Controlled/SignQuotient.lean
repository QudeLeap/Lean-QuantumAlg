/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Selection
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Original
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.SignQuotient

/-!
# Actual externally selected Sign scan followed by the original quotient word

The complete fused scan returns its actual pool before the separately
selected native quotient update executes. Original old metadata chooses
the Sign exchange first. The full original dirty work and original Iter
are retained, and inactive external selection accepts input zero.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSignQuotient

noncomputable section

open EncodedBit NumberTheory.SharedEEA

def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  (ControlledSelection.program width).seq
    (ControlledSourceWord.program width (PhaseQuotient.gates width))

def step (width : Nat) (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  ((if state.2.1 then SharedEEA.SignQuotient.sourceStep width state.1.1 else state.1.1,
    state.1.2), state.2)

private lemma complete_steps (width : Nat) (state : ControlledFrame.Data width)
    (control : state.1.1.control = false) :
    ((if (ControlledSelection.step width state).2.1 then
        PhaseQuotient.step (ControlledSelection.step width state).1.1
      else (ControlledSelection.step width state).1.1,
        (ControlledSelection.step width state).1.2),
      (ControlledSelection.step width state).2) = step width state := by
  cases selected : state.2.1 with
  | false =>
      simp only [ControlledSelection.step, selected, Bool.false_eq_true, if_false, step]
  | true =>
      simp only [ControlledSelection.step, selected, ↓reduceIte, step]
      rw [SelectionSpecification.sourceStep_eq_original width state.1.1 control,
        PhaseQuotient.step_eq_sourceStep _
          ((SharedEEA.SignQuotient.source_control width state.1.1).trans control)]
      rfl

/-- Actual source order and full pool/external restoration hold at every original width. -/
lemma program_apply_encoded_ket (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : ControlledFrame.Data width)
    (addressZero : state.1.2.1 = 0#(ScanMetadata.addressWidth width))
    (prefixZero : state.1.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (control : state.1.1.control = false) :
    (program width).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (step width state))) := by
  have first := ControlledSelection.program_apply_encoded_ket width environment state
    addressZero prefixZero control
  have second := (ControlledSourceWord.program_realizes width (PhaseQuotient.gates width)
    environment).apply_encoded_ket (ControlledSelection.step width state)
  rw [PhaseQuotient.phaseQuotient_gates_step] at second
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq first second
  change (program width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode
        ((if (ControlledSelection.step width state).2.1 then
            PhaseQuotient.step (ControlledSelection.step width state).1.1
          else (ControlledSelection.step width state).1.1,
            (ControlledSelection.step width state).1.2),
          (ControlledSelection.step width state).2))) at actual
  rw [complete_steps width state control] at actual
  exact actual

lemma step_disabled (width : Nat) (state : ControlledFrame.Data width)
    (disabled : state.2.1 = false) : step width state = state := by
  rw [step, disabled]
  rfl

lemma step_pool (width : Nat) (state : ControlledFrame.Data width) :
    (step width state).1.2 = state.1.2 := rfl

lemma step_external (width : Nat) (state : ControlledFrame.Data width) :
    (step width state).2 = state.2 := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSignQuotient
