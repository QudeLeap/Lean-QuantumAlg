/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Active
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.High
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor.Action

/-! # Complete actual clipping preparation commutes with the original finite output XOR -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private lemma activeGates_output_flip (width : Nat) (field : Field)
    (bit : Fin width.size) (state : Data width) :
    GateSpec.stepList (activeGates width) (((LengthCopy.target width field).bit bit).flip state) =
      ((LengthCopy.target width field).bit bit).flip
        (GateSpec.stepList (activeGates width) state) := by
  let observed := (LengthCopy.target width field).bit bit
  have controlOutside : observed.wire ≠
      (sourceBit width (SharedEEA.controlBit width)).wire :=
    (LengthCopy.active_target width false field bit).symm
  have controlRead : (observed.flip state).1.control = state.1.control :=
    EncodedBit.get_flip_of_wire_ne observed (sourceBit width (SharedEEA.controlBit width))
      controlOutside state
  have highRead : (highBit width).get (observed.flip state) = (highBit width).get state :=
    EncodedBit.get_flip_of_wire_ne observed (highBit width)
      (source_prefix_ne width (outputBit width field bit) _) state
  change GateSpec.stepList (activeGates width) (observed.flip state) = _
  rw [activeGates_step, activeGates_step]
  unfold predicateFlip
  dsimp only
  simp only [controlRead, highRead]
  split
  · exact EncodedBit.flip_comm _ _ state
  · rfl

/-- Static activation commutes with any complete finite original length mask on all inputs. -/
lemma activationStep_output_comm (width : Nat) (field : Field)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    activationStep width (Word.xorConstantStep (LengthCopy.target width field) mask state) =
      Word.xorConstantStep (LengthCopy.target width field) mask
        (activationStep width state) := by
  unfold activationStep activationGates
  split
  · exact Word.action_xorConstantStep_comm _ _ mask (activeGates_output_flip width field) state
  · rfl

/-- Native clipping returns exactly the preparation of the changed original state. -/
lemma prepareStep_output_comm (width : Nat) (field : Field)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    prepareStep width field (Word.xorConstantStep (LengthCopy.target width field) mask state) =
      Word.xorConstantStep (LengthCopy.target width field) mask
        (prepareStep width field state) := by
  unfold prepareStep
  rw [LengthBoundary.prepareStep_output_comm, activationStep_output_comm,
    LengthDifference.step_output_comm]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
