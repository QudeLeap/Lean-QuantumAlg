/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Phase.Program
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact masked parity phases beside an arbitrary entangled reference

The operator is the actual native phase word tensored with identity. Every
encoded computational label retains its original physical systems and its
original reference label, multiplied only by the proved parity character.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}

/-- The actual native phase operator leaves the arbitrary external reference untouched. -/
def maskedParityPhaseReferenceOperator (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (environment : oracles.Interpretation) (Reference : Register) :
    UnitaryOperator (Register.prod physical.toQuantum.register Reference) :=
  UnitaryOperator.prodTensor
    ((maskedParityPhaseProgram physical oracles target distinct selector outside height).matrix
      environment) (1 : UnitaryOperator Reference)

/-- The exact phase retains each original joint local/reference computational label. -/
lemma maskedParityPhase_reference_ket (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (covered : count ≤ 2 ^ height) (environment : oracles.Interpretation)
    (state : Data) {Reference : Register} (reference : Reference.Index) :
    (maskedParityPhaseReferenceOperator physical oracles target distinct selector outside height
      environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      (if selector.get state = true ∧ bitParity (prefixBits target count) state = true
        then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec := by
  have actual := maskedParityPhaseProgram_applyVec physical oracles target distinct selector outside
    height covered environment state
  change UnitaryOperator.applyVec
    ((maskedParityPhaseProgram physical oracles target distinct selector outside height).matrix
      environment) _ = _ at actual
  rw [maskedParityPhaseReferenceOperator, ← HilbertVector.prodTensor_ket,
    UnitaryOperator.prodTensor_applyVec_prodTensor, actual, UnitaryOperator.one_applyVec]
  ext index
  simp only [HilbertVector.prodTensor_apply, PiLp.smul_apply, smul_eq_mul]
  exact mul_assoc _ _ _

/-- Linearity gives the same exact character on arbitrary entanglement, with no phase loss. -/
lemma maskedParityPhase_coherent_reference (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (covered : count ≤ 2 ^ height) (environment : oracles.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (maskedParityPhaseReferenceOperator physical oracles target distinct selector outside height
      environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec) =
      ∑ index, (amplitude index *
        (if selector.get (state index) = true ∧
            bitParity (prefixBits target count) (state index) = true then (-1 : ℂ) else 1)) •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec := by
  change HilbertOperator.applyVec
    (maskedParityPhaseReferenceOperator physical oracles target distinct selector outside height
      environment Reference : HilbertOperator (Register.prod physical.toQuantum.register Reference))
        _ = _
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have actual := maskedParityPhase_reference_ket physical oracles target distinct selector outside
    height covered environment (state index) (reference index)
  change HilbertOperator.applyVec _ _ = _ at actual
  rw [actual, smul_smul]

end

end QuantumAlg.EncodedBit.WindowLookup
