/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Selection.Enable
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Selection.Body

/-!
# Actual externally fused Sign selection at arbitrary original width

Two actual selected phase-enable XORs surround the original complete
address/scan/adjoint body. Each enable uses two Toffolis; the expensive
scan is unchanged. Original internal Ctrl starts false, while the
existing conjunction and every original finite metadata value may be
arbitrary. Inactive execution is full identity, including input zero.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelection

noncomputable section

open EncodedBit NumberTheory.SharedEEA

def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  (ControlledSelectionEnable.program width).seq
    ((ControlledFrame.liftProgram width (ControlledSelectionBody.program width)).seq
      (ControlledSelectionEnable.program width))

def step (width : Nat) (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  (if state.2.1 then (SelectionSpecification.sourceStep width state.1.1, state.1.2)
    else state.1, state.2)

private lemma complete_steps (width : Nat) (state : ControlledFrame.Data width)
    (disabled : state.1.1.control = false) :
    ControlledSelectionEnable.step width
        (ControlledSelectionBody.step width (ControlledSelectionEnable.step width state).1,
          (ControlledSelectionEnable.step width state).2) = step width state := by
  cases selected : state.2.1 with
  | false =>
      simp only [ControlledSelectionEnable.step, selected, Bool.false_eq_true, if_false, step]
      rw [ControlledSelectionBody.step_disabled width state.1 disabled]
  | true =>
      simp only [ControlledSelectionEnable.step, selected, ↓reduceIte,
        ControlledSelectionBody.step, SelectionEnable.step, step]
      rw [SelectionSpecification.enable_selected_enable]

/-- Complete coherent source/pool/external semantics without any original source-range premise. -/
lemma program_apply_encoded_ket (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : ControlledFrame.Data width)
    (addressZero : state.1.2.1 = 0#(ScanMetadata.addressWidth width))
    (prefixZero : state.1.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (disabled : state.1.1.control = false) :
    (program width).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (step width state))) := by
  let first := ControlledSelectionEnable.step width state
  let second := (ControlledSelectionBody.step width first.1, first.2)
  have firstPool : first.1.2 = state.1.2 := ControlledSelectionEnable.step_pool width state
  have firstAddress : first.1.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (congrArg Prod.fst firstPool).trans addressZero
  have firstPrefix : first.1.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (congrArg (fun pool : Pool width => pool.2.1) firstPool).trans prefixZero
  have enableActual := ControlledSelectionEnable.program_realizes width environment
  have firstActual := enableActual.apply_encoded_ket state
  have bodyActual := ControlledSelectionBody.program_apply_encoded_ket width environment
    first.1 firstAddress firstPrefix
  have middle := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (Scanned.encoding width) ExternalWord.flags (ControlledSelectionBody.program width)
    first.1 (ControlledSelectionBody.step width first.1) first.2 bodyActual
  have last := enableActual.apply_encoded_ket second
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq firstActual
    (UnitaryCircuit.applyNormalized_seq_of_eq middle last)
  change (program width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode
        (ControlledSelectionEnable.step width
          (ControlledSelectionBody.step width (ControlledSelectionEnable.step width state).1,
            (ControlledSelectionEnable.step width state).2)))) at actual
  rw [complete_steps width state disabled] at actual
  exact actual

lemma step_disabled (width : Nat) (state : ControlledFrame.Data width)
    (disabled : state.2.1 = false) : step width state = state := by
  rw [step, disabled]
  rfl

lemma step_pool (width : Nat) (state : ControlledFrame.Data width) :
    (step width state).1.2 = state.1.2 := by
  unfold step
  split <;> rfl

lemma step_external (width : Nat) (state : ControlledFrame.Data width) :
    (step width state).2 = state.2 := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelection
