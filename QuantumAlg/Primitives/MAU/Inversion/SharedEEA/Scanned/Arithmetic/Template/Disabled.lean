/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Forward

/-!
# Disabled streaming arithmetic on every finite address

A rejected metadata key may leave any address. With the original root
control disabled and the conjunction zero, no payload or boundary toggle
acts. The actual selector restores its prefixes without requiring that
address to name a physical work-word position.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma callbacks_disabled (width : Nat) (stage : Stage)
    (labels : List (Fin (2 ^ ScanMetadata.addressWidth width)))
    (state : Data width) (zero : state.2.2.2 = false) :
    labels.foldl (fun value label => (payload width stage label.val).callbackStep false value)
      state = state := by
  have action (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
      (payload width stage label.val).callbackStep false state = state := by
    change (if state.2.2.2 then GateSpec.stepList (source width stage label.val) state
      else state) = state
    rw [zero]
    rfl
  induction labels with
  | nil => rfl
  | cons first rest ih =>
      rw [List.foldl_cons, action]
      exact ih

/-- The actual traversal is identity for every finite address when the root is disabled. -/
lemma program_apply_disabled (width : Nat) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (program width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  have actual := (family width stage).program_apply_encoded_ket_flags
    (QubitLayout.canonical _) .empty environment (tree width) state
    (SelectionFrame.clean_of_prefix_zero width state clean)
  have root : ((SelectionFrame.frame width).stack ⟨0, by omega⟩).get state = false := disabled
  rw [root] at actual
  simp only [Bool.false_and] at actual
  have projection : ∀ label, (family width stage).payload label =
      payload width stage label.val := fun _ => rfl
  simp only [projection] at actual
  rw [callbacks_disabled width stage _ state zero] at actual
  exact actual

/-- The initial paid CNOT also acts trivially, with no address-range premise. -/
lemma forwardProgram_apply_disabled (width : Nat) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (forwardProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  have prepare := (GateSpec.realizes (QubitLayout.canonical _) .empty
    (startGate width) environment).apply_encoded_ket state
  have same : (startGate width).step state = state := by
    change (if state.1.control then (conjunctionBit width).flip state else state) = state
    rw [disabled]
    rfl
  rw [same] at prepare
  exact UnitaryCircuit.applyNormalized_seq_of_eq prepare
    (program_apply_disabled width stage environment state clean zero disabled)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
