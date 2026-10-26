/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Layout
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Actual four-Toffoli length-bit XOR with arbitrary restored Iter -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Four native Toffolis use only the actual three controls, original target and dirty Iter. -/
def bitGates (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size) :
    List (GateSpec (encoding width)) :=
  (layout width poolFlag field bit).gates

private lemma selected (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size)
    (state : Data width) :
    (∀ index, ((layout width poolFlag field bit).source.bit index).get state = true) ↔
      (active width poolFlag).get state = true ∧
        (conjunctionBit width).get state = true ∧ (dataBit width bit).get state = true := by
  constructor
  · intro all
    exact ⟨all 0, all 1, all 2⟩
  · rintro ⟨first, second, third⟩ index
    fin_cases index
    · exact first
    · exact second
    · exact third

/-- The full physical action changes exactly its original arbitrary target under three controls. -/
lemma bitGates_step (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size)
    (state : Data width) :
    GateSpec.stepList (bitGates width poolFlag field bit) state =
      if (active width poolFlag).get state && (conjunctionBit width).get state &&
          (dataBit width bit).get state
      then (targetBit width field bit).flip state else state := by
  rw [bitGates, Word.OneDirtyLayout.gates_step]
  simp only [selected, Bool.and_eq_true_iff, and_assoc]
  rfl

/-- Every other original physical coordinate retains its arbitrary input value. -/
lemma bitGates_observed (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size)
    (observed : EncodedBit (encoding width))
    (different : (targetBit width field bit).wire ≠ observed.wire) (state : Data width) :
    observed.get (GateSpec.stepList (bitGates width poolFlag field bit) state) =
      observed.get state :=
  (layout width poolFlag field bit).gates_get_of_output_ne observed different state

/-- The original arbitrary Iter is returned within each actual native copy bit. -/
lemma bitGates_work (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size)
    (state : Data width) :
    (sourceBit width (SharedEEA.iterationBit width)).get
      (GateSpec.stepList (bitGates width poolFlag field bit) state) =
        (sourceBit width (SharedEEA.iterationBit width)).get state :=
  (layout width poolFlag field bit).gates_work_restored state

/-- These are exactly four native Toffoli events, without hidden CNOT or measurement events. -/
lemma bitGates_events (width : Nat) (poolFlag : Bool) (field : Field) (bit : Fin width.size) :
    (bitGates width poolFlag field bit).map (GateSpec.event .empty) =
      List.replicate 4 (.gate .toffoli) :=
  (layout width poolFlag field bit).gates_events_of_two_le .empty (by decide)

/-- All four physical native dependencies are charged on this same unchanged carrier. -/
lemma bitGates_quantumTime (width : Nat) (poolFlag : Bool) (field : Field)
    (bit : Fin width.size) :
    (GateSpec.programList (QubitLayout.canonical _) .empty
      (bitGates width poolFlag field bit)).evaluatedEventDepth Resource.Event.quantumDuration =
        4 := by
  rw [GateSpec.programList_quantumTime]
  exact (layout width poolFlag field bit).gates_length

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy
