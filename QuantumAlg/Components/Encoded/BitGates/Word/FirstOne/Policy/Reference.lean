/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy.Encoder
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual policy encoder on arbitrary dirty-output and external-reference families

Every complete native physical test restores its original bank. The same
original source position is XORed with unchanged coherent amplitudes.
-/

namespace QuantumAlg.EncodedBit.FirstOne.TestPolicy

noncomputable section

open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  {frame : Frame encoding count outputWidth depth} (policy : TestPolicy frame)

/-- Only the actual encoder matrix is tensored beside the untouched external reference. -/
def policyEncoderReferenceOperator (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical encoding.width).toQuantum.register.prod Reference) :=
  UnitaryOperator.prodTensor
    ((policy.encoderProgram height capacity fits).matrix environment)
    (1 : UnitaryOperator Reference)

/-- Every reference basis label accompanies the same exact dirty-output XOR action. -/
lemma policyEncoder_reference_ket (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    (state : Data) (clean : frame.CleanFrom 0 state)
    {Reference : Register} (reference : Reference.Index) :
    (policy.policyEncoderReferenceOperator height capacity fits environment Reference).applyVec
        (NormalizedVector.ket (R := (QubitLayout.canonical encoding.width).toQuantum.register.prod
          Reference) ((QubitLayout.canonical encoding.width).basisEquiv.symm
            (encoding.encode state), reference)).vec =
      (NormalizedVector.ket (R := (QubitLayout.canonical encoding.width).toQuantum.register.prod
        Reference) ((QubitLayout.canonical encoding.width).basisEquiv.symm
          (encoding.encode (frame.positionXorStep state)), reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (policy.policyEncoderProgram_apply_encoded_ket height capacity fits environment state clean)
  change UnitaryOperator.applyVec ((policy.encoderProgram height capacity fits).matrix environment)
    (NormalizedVector.ket ((QubitLayout.canonical encoding.width).basisEquiv.symm
      (encoding.encode state))).vec = _ at actual
  change (UnitaryOperator.prodTensor
    ((policy.encoderProgram height capacity fits).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- Arbitrary coherent amplitudes and all work/reference correlations
retain this same actual XOR. -/
lemma policyEncoder_coherent_reference (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (clean : ∀ index, frame.CleanFrom 0 (state index)) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    (policy.policyEncoderReferenceOperator height capacity fits environment Reference).applyVec
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
    policy.policyEncoder_reference_ket height capacity fits environment (state index) (clean index)]

end

end QuantumAlg.EncodedBit.FirstOne.TestPolicy
