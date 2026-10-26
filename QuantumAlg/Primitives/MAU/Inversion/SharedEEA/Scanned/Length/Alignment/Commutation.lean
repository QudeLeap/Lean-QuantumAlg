/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Positive
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Commutation

/-! # Complete actual terminal alignment commutes with its independent original length output -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private lemma word_output (width : Nat) (field : Field) (first : Bool)
    (input : Fin (width + 3)) (output : Fin width.size) :
    (ArithmeticRotation.bit width first input).wire ≠
      (sourceBit width (outputBit width field output)).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value, sourceBit_wire] at values
  have before := input.isLt
  have within := output.rev.isLt
  cases field <;> cases first <;>
    simp only [outputBit, SharedEEA.coefficientLengthBit_wire, SharedEEA.divisorLengthBit_wire,
      Bool.false_eq_true, if_false, if_true] at values <;> omega

private lemma control_output (width : Nat) (field : Field) (first : Bool)
    (control output : Fin width.size) :
    (sourceBit width (outputBit width field output)).wire ≠
      ((ArithmeticAlignment.barrel width first (metadataField field)).control control).wire := by
  have original : (ArithmeticAlignment.barrel width first (metadataField field)).control control =
      sourceBit width (boundaryBit width field control.rev) := by
    cases field <;> rfl
  rw [original]
  exact (source_source_ne width _ _ (boundary_output_ne width field control.rev output)).symm

/-- Full native alignment commutes with an original output flip on every finite input label. -/
lemma gates_output_flip (width : Nat) (field : Field) (first : Bool)
    (output : Fin width.size) (state : Data width) :
    GateSpec.stepList (gates width field first)
        (((LengthCopy.target width field).bit output).flip state) =
      ((LengthCopy.target width field).bit output).flip
        (GateSpec.stepList (gates width field first) state) := by
  let observed := (LengthCopy.target width field).bit output
  have outside : ∀ index, (ArithmeticRotation.bit width first index).wire ≠ observed.wire :=
    fun index => word_output width field first index output
  have barrel : GateSpec.stepList (barrelGates width field first) (observed.flip state) =
      observed.flip (GateSpec.stepList (barrelGates width field first) state) := by
    apply PermutationBarrel.gates_flip_outside
    · exact outside
    · exact fun control => control_output width field first control output
  have publicAction (value : Data width) :
      GateSpec.stepList (publicGates width field first) (observed.flip value) =
        observed.flip (GateSpec.stepList (publicGates width field first) value) := by
    cases field with
    | coefficient => rfl
    | divisor =>
        have actual := (ArithmeticRotation.frame width first (SharedEEA.controlBit width)
          (by rw [SharedEEA.controlBit_wire]; omega)).swapAction_flip_outside
          (Permutation.transpositions (finRotate (width + 3))) observed outside value
        simpa only [publicGates, PermutationFrame.uncontrolledGates_step] using actual
  change GateSpec.stepList (gates width field first) (observed.flip state) = _
  simp only [gates, GateSpec.stepList_append]
  rw [barrel, publicAction]

/-- A complete arbitrary original length XOR commutes with the full actual alignment. -/
lemma gates_output_comm (width : Nat) (field : Field) (first : Bool)
    (constant : Fin (2 ^ width.size)) (state : Data width) :
    GateSpec.stepList (gates width field first)
        (Word.xorConstantStep (LengthCopy.target width field) constant state) =
      Word.xorConstantStep (LengthCopy.target width field) constant
        (GateSpec.stepList (gates width field first) state) :=
  Word.action_xorConstantStep_comm _ _ constant
    (gates_output_flip width field first) state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment
