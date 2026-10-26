/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap

/-! # Actual one-Toffoli controlled exchanges of complete encoded words -/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding) (left right : Word encoding width)
    (controlLeft : ∀ index, control.wire ≠ (left.bit index).wire)
    (controlRight : ∀ index, control.wire ≠ (right.bit index).wire)
    (leftRight : ∀ index, (left.bit index).wire ≠ (right.bit index).wire)

/-- Every matching pair emits a real CNOT, Toffoli and CNOT on its existing systems. -/
def fredkinGates : List (GateSpec encoding) :=
  (List.ofFn fun index : Fin width => index).flatMap fun index =>
    EncodedBit.fredkinGates control (left.bit index) (right.bit index)
      (controlLeft index) (controlRight index) (leftRight index)

private lemma indices_step (indices : List (Fin width)) (state : Data) :
    GateSpec.stepList (indices.flatMap fun index =>
      EncodedBit.fredkinGates control (left.bit index) (right.bit index)
        (controlLeft index) (controlRight index) (leftRight index)) state =
      controlledSwapIndicesStep control left right controlLeft controlRight leftRight
        indices state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append,
        EncodedBit.fredkin_step_eq_controlledSwap, ih]
      rfl

/-- The full actual native word has precisely the complete original controlled exchange action. -/
lemma fredkinGates_step (state : Data) :
    GateSpec.stepList (fredkinGates control left right controlLeft controlRight leftRight) state =
      controlledSwapStep control left right controlLeft controlRight leftRight state := by
  rw [controlledSwapStep_eq_indicesStep]
  exact indices_step control left right controlLeft controlRight leftRight _ state

private lemma indices_events (indices : List (Fin width)) :
    ((indices.flatMap fun index =>
      EncodedBit.fredkinGates control (left.bit index) (right.bit index)
        (controlLeft index) (controlRight index) (leftRight index)).map
          (GateSpec.event .empty)) =
      indices.flatMap (fun _ => [.gate .cnot, .gate .toffoli, .gate .cnot]) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [List.flatMap_cons, List.map_append, ih]
      rfl

/-- Exact native coordinates, including both paid CNOTs for each exchanged pair. -/
lemma fredkinGates_counts :
    ((fredkinGates control left right controlLeft controlRight leftRight).map
      (GateSpec.event .empty)).count (.gate .toffoli) = width ∧
    ((fredkinGates control left right controlLeft controlRight leftRight).map
      (GateSpec.event .empty)).count (.gate .cnot) = 2 * width ∧
    (fredkinGates control left right controlLeft controlRight leftRight).length = 3 * width := by
  have counts (indices : List (Fin width)) :
      (indices.flatMap (fun _ =>
        [Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot,
          .gate .toffoli, .gate .cnot])).count (.gate .toffoli) = indices.length ∧
      (indices.flatMap (fun _ =>
        [Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot,
          .gate .toffoli, .gate .cnot])).count (.gate .cnot) = 2 * indices.length ∧
      (indices.flatMap (fun _ =>
        [Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot,
          .gate .toffoli, .gate .cnot])).length = 3 * indices.length := by
    induction indices with
    | nil => simp
    | cons index rest ih =>
        simp [List.flatMap_cons, ih.1, ih.2.1, ih.2.2, Nat.mul_succ]
  have values := counts (List.ofFn fun index : Fin width => index)
  have events := indices_events control left right controlLeft controlRight leftRight
    (List.ofFn fun index : Fin width => index)
  have lengths := congrArg List.length events
  simp only [List.length_ofFn] at values
  simp only [List.length_map] at lengths
  exact ⟨(congrArg (List.count (.gate .toffoli)) events).trans values.1,
    (congrArg (List.count (.gate .cnot)) events).trans values.2.1,
    lengths.trans values.2.2⟩

end

end QuantumAlg.EncodedBit.Word
