/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Positive
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor

/-!
# Actual complete finite length XOR selected by active and no borrow

Two actual X gates mask the existing borrow output around the complete
native selected word copy. Every original length input is arbitrary.
The entire source, active, conjunction, other metadata, and dirty Iter
return with their original values; no classical length is loaded.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy

noncomputable section

open EncodedBit LengthCoordinates

private lemma xor_conjunction_flip (width : Nat) (field : Field) (state : Data width) :
    Word.xorIntoStep (source width) (target width field) (source_target width field)
        ((conjunctionBit width).flip state) =
      (conjunctionBit width).flip
        (Word.xorIntoStep (source width) (target width field) (source_target width field) state) :=
  by
  apply GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate present
  obtain ⟨bit, rfl⟩ := List.mem_ofFn.mp present
  exact ⟨prefix_conjunction_ne width bit.rev.succ, source_conjunction_ne width _⟩

/-- The two paid masks surround the complete word, rather than each individual target bit. -/
def gates (width : Nat) (poolFlag : Bool) (field : Field) : List (GateSpec (encoding width)) :=
  [.x (conjunctionBit width)] ++ positiveGates width poolFlag field ++ [.x (conjunctionBit width)]

/-- Complete original-frame XOR under active and no borrow, including actual mask cleanup. -/
def step (width : Nat) (poolFlag : Bool) (field : Field) (state : Data width) : Data width :=
  if (active width poolFlag).get state && !(conjunctionBit width).get state then
    Word.xorIntoStep (source width) (target width field) (source_target width field) state
  else state

/-- Actual instructions have exactly the selected complete finite-word action on every label. -/
lemma gates_step (width : Nat) (poolFlag : Bool) (field : Field) (state : Data width) :
    GateSpec.stepList (gates width poolFlag field) state = step width poolFlag field state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append]
  simp only [GateSpec.stepList, GateSpec.step, id_eq]
  rw [positiveGates_step]
  simp only [selectedWord, get_flip_of_wire_ne (conjunctionBit width) (active width poolFlag)
    (active_conjunction width poolFlag).symm, get_flip_self]
  unfold step
  split_ifs
  · rw [xor_conjunction_flip, EncodedBit.flip_flip]
  · exact EncodedBit.flip_flip _ _

/-- The actual coherent circuit stays on the same original full physical frame. -/
def program (width : Nat) (poolFlag : Bool) (field : Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width poolFlag field)

/-- Exact full encoded ket semantics retain arbitrary reference amplitudes and dirty Iter. -/
lemma program_realizes (width : Nat) (poolFlag : Bool) (field : Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width poolFlag field) environment
      (step width poolFlag field) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step width poolFlag field) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy
