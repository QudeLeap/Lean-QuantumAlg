/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Value

/-! # Independent finite mask of the actual selected native quantum length copy -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy

noncomputable section

open EncodedBit LengthCoordinates

/-- Mathematical readout of the actual controls and low prefix, not a circuit parameter. -/
def mask (width : Nat) (poolFlag : Bool) (state : Data width) : BitVec width.size :=
  if (active width poolFlag).get state && !(conjunctionBit width).get state then value width state
  else 0

private lemma xorConstantStep_zero (width : Nat) (field : Field) (state : Data width) :
    Word.xorConstantStep (target width field) (0 : Fin (2 ^ width.size)) state = state := by
  simp [Word.xorConstantStep, Word.xorConstantGates, Word.constantOneIndices, GateSpec.stepList]

/-- The real all-label copy is exactly XOR of this finite mask into the original output. -/
lemma step_eq_mask (width : Nat) (poolFlag : Bool) (field : Field) (state : Data width) :
    step width poolFlag field state =
      Word.xorConstantStep (target width field) (mask width poolFlag state).toFin state := by
  rw [step_eq_constant]
  unfold mask
  split
  · rfl
  · exact (xorConstantStep_zero width field state).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy
