/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Correctness
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual first-one XOR on arbitrary coherent states and external references

Only the supplied future prefixes start zero. All old output values and
arbitrary work/reference correlations retain their original amplitudes.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- Independent original-root selected XOR of the original first position or full-count sentinel. -/
def positionXorStep (state : Data) : Data :=
  if (frame.stack.bit ⟨0, by omega⟩).get state then
    Word.xorConstantStep frame.output
      (BitVec.ofNat outputWidth (frame.firstPosition state)).toFin state else state

/-- The complete actual encoder has its independent XOR action
on every admitted basis state. -/
lemma encoderProgram_apply_encoded_ket (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    (frame.encoderProgram height capacity fits).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical encoding.width).basisEquiv.symm (encoding.encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical encoding.width).basisEquiv.symm
        (encoding.encode (frame.positionXorStep state))) := by
  have actual := (GateSpec.realizesList (QubitLayout.canonical _) .empty
    (frame.encoderGates height capacity fits) environment).apply_encoded_ket state
  rw [frame.encoderGates_step height capacity fits state clean] at actual
  exact actual

/-- Only the actual encoder matrix is tensored beside the untouched external reference. -/
def encoderReferenceOperator (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical encoding.width).toQuantum.register.prod Reference) :=
  UnitaryOperator.prodTensor
    ((frame.encoderProgram height capacity fits).matrix environment) (1 : UnitaryOperator Reference)

/-- Every reference basis label accompanies the same exact dirty-output XOR action. -/
lemma encoder_reference_ket (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    (state : Data) (clean : frame.CleanFrom 0 state)
    {Reference : Register} (reference : Reference.Index) :
    (frame.encoderReferenceOperator height capacity fits environment Reference).applyVec
        (NormalizedVector.ket (R := (QubitLayout.canonical encoding.width).toQuantum.register.prod
          Reference) ((QubitLayout.canonical encoding.width).basisEquiv.symm
            (encoding.encode state), reference)).vec =
      (NormalizedVector.ket (R := (QubitLayout.canonical encoding.width).toQuantum.register.prod
        Reference) ((QubitLayout.canonical encoding.width).basisEquiv.symm
          (encoding.encode (frame.positionXorStep state)), reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (frame.encoderProgram_apply_encoded_ket height capacity fits environment state clean)
  change UnitaryOperator.applyVec ((frame.encoderProgram height capacity fits).matrix environment)
    (NormalizedVector.ket ((QubitLayout.canonical encoding.width).basisEquiv.symm
      (encoding.encode state))).vec = _ at actual
  change (UnitaryOperator.prodTensor
    ((frame.encoderProgram height capacity fits).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- Arbitrary coherent amplitudes and all work/reference correlations
retain this same actual XOR. -/
lemma encoder_coherent_reference (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (clean : ∀ index, frame.CleanFrom 0 (state index)) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    (frame.encoderReferenceOperator height capacity fits environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket (R := (QubitLayout.canonical encoding.width).toQuantum.register.prod
            Reference) ((QubitLayout.canonical encoding.width).basisEquiv.symm
              (encoding.encode (state index)), reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := (QubitLayout.canonical encoding.width).toQuantum.register.prod
          Reference) ((QubitLayout.canonical encoding.width).basisEquiv.symm
            (encoding.encode (frame.positionXorStep (state index))), reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    frame.encoder_reference_ket height capacity fits environment (state index) (clean index)]

end

end QuantumAlg.EncodedBit.FirstOne.Frame
