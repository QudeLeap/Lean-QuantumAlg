/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding

/-!
# Load a constant basis word through its actual X gates

The constant's set bits select the existing constant-XOR gate list. The
explicit little-endian-to-physical position map addresses each bit once.
The typed layout retains the complete register. No system is allocated;
the zero-input theorem is an internal composition fact after preparation or
an actual reset. Counts and depth describe this same literal gate list.
-/

namespace QuantumAlg.EncodedBit.Word.BasisLoad

noncomputable section

open BinaryLabelEncoding
open EncodedBit.GateSpec

private def bit (width : Nat) (index : Fin width) : EncodedBit (finIdentity width) :=
  finIdentityBit width (WireAddress.littleEndianWire index)

private def word (width : Nat) : EncodedBit.Word (finIdentity width) width := ⟨bit width⟩

private lemma bit_get (width : Nat) (index : Fin width) (state : Fin (2 ^ width)) :
    (bit width index).get state = state.val.testBit index.val := by
  change state.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private lemma bit_disjoint (width : Nat) (left right : Fin width) (different : left ≠ right) :
    (bit width left).wire ≠ (bit width right).wire := by
  intro same
  have values := congrArg Fin.val same
  change width - 1 - left.val = width - 1 - right.val at values
  apply different
  apply Fin.ext
  omega

/-- The literal X sequence acts on exactly the fixed constant's set-bit positions. -/
def gates {width : Nat} (constant : Fin (2 ^ width)) :
    List (EncodedBit.GateSpec (finIdentity width)) :=
  EncodedBit.Word.xorConstantGates (word width) constant

/-- Load the constant on the existing complete physical register, without preparation. -/
def program {width : Nat} (physical : QubitLayout width) (oracles : OracleModel)
    (constant : Fin (2 ^ width)) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  programList physical oracles (gates constant)

private lemma step_zero {width : Nat} (constant : Fin (2 ^ width)) :
    stepList (gates constant) 0 = constant := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have action := EncodedBit.Word.xorConstantStep_get_target (word width) constant index
    (fun other different => bit_disjoint width other index different) 0
  change (bit width index).get (stepList (gates constant) 0) =
    ((bit width index).get 0 ^^ constant.val.testBit index.val) at action
  simpa only [bit_get, Fin.val_zero, Nat.zero_testBit, Bool.false_xor] using action

/-- The actual X sequence maps the internally established zero state to the specified basis word. -/
lemma basisLoad_apply_zero {width : Nat} (physical : QubitLayout width)
    (oracles : OracleModel) {environment : oracles.Interpretation}
    (constant : Fin (2 ^ width)) :
    (program physical oracles constant).applyNormalized environment
        (NormalizedVector.ket (R := physical.toQuantum.register) (physical.basisEquiv.symm 0)) =
      NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm constant) := by
  have action := (realizesList physical oracles (gates constant) environment).apply_encoded_ket 0
  change (programList physical oracles (gates constant)).applyNormalized environment
      (NormalizedVector.ket (R := physical.toQuantum.register) (physical.basisEquiv.symm 0)) =
      NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (stepList (gates constant) 0)) at action
  rw [step_zero] at action
  exact action

/-- Independent number of set-bit positions in the constant, including zero-width words. -/
def xCount {width : Nat} (constant : Fin (2 ^ width)) : Nat :=
  (EncodedBit.Word.constantOneIndices constant).length

/-- Every actual event is one X gate at a selected position of the fixed constant. -/
lemma basisLoad_eventCost {width : Nat} (physical : QubitLayout width)
    (oracles : OracleModel) (constant : Fin (2 ^ width)) :
    (program physical oracles constant).eventCost =
      xCount constant • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [program, programList_eventCost]
  have nativeX (target : EncodedBit (finIdentity width)) :
      event oracles (.x target) = .gate .singleQubit := rfl
  have events : (gates constant).map (event oracles) =
      List.replicate (xCount constant) (.gate .singleQubit) := by
    simp [gates, EncodedBit.Word.xorConstantGates, xCount, Function.comp_def, nativeX]
  rw [events, ResourcePool.ofList_replicate]
  rfl

/-- The literal sequential loading depth equals its exact number of selected X gates. -/
lemma basisLoad_unitDepth {width : Nat} (physical : QubitLayout width)
    (oracles : OracleModel) (constant : Fin (2 ^ width)) :
    (program physical oracles constant).evaluatedEventDepth (fun _ => 1) = xCount constant := by
  rw [program, programList_evaluatedEventDepth_unit]
  exact EncodedBit.Word.xorConstantGates_length _ _

/-- Actual constant loading never requires more than one X gate per existing bit. -/
lemma basisLoad_count_le {width : Nat} (constant : Fin (2 ^ width)) :
    xCount constant ≤ width := EncodedBit.Word.constantOneIndices_length_le _

end

end QuantumAlg.EncodedBit.Word.BasisLoad
