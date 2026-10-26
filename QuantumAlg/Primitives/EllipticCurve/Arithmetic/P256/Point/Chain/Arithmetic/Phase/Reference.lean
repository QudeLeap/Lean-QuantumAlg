/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Phase
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # The same paid phase on coherent active and inactive Reference families -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Phase

noncomputable section

open scoped BigOperators

private lemma reference_ket {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation) (state : layout.register.Index)
    (coefficient : ℂ)
    (action : body.applyVec environment (NormalizedVector.ket state).vec =
      coefficient • (NormalizedVector.ket state).vec)
    {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference) :
        HilbertOperator (layout.register.prod Reference))
      (NormalizedVector.ket (R := layout.register.prod Reference) (state, reference)).vec =
        coefficient •
          (NormalizedVector.ket (R := layout.register.prod Reference) (state, reference)).vec := by
  change UnitaryOperator.applyVec (body.matrix environment) _ = _ at action
  change (UnitaryOperator.prodTensor (body.matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    action, UnitaryOperator.one_applyVec]
  ext index
  simp only [HilbertVector.prodTensor_apply, PiLp.smul_apply, smul_eq_mul]
  exact mul_assoc _ _ _

/-- The exact phase retains every original state and external-reference coherence. -/
lemma program_reference (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (outcome : Word)
    {Reference : Register} {Index : Type} [Fintype Index]
    (source saved : Index → Word) (retained : Index → Placement.Rest assignment)
    (admitted : ∀ index, (selectorBit assignment selection).get (retained index) = true →
      Canonical (source index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (Native.referenceOperator (program assignment selection outcome) environment Reference)
      (Native.referenceVector (fun index => Native.arithmeticState assignment (source index)
        Horner.zeroWord (saved index) (retained index)) reference amplitude) =
      Native.referenceVector (fun index => Native.arithmeticState assignment (source index)
        Horner.zeroWord (saved index) (retained index)) reference
        (fun index => amplitude index * WalshHadamard.walshSign outcome
          (Save.savedWord (source index) (saved index)
            ((selectorBit assignment selection).get (retained index)))) := by
  unfold Native.referenceVector
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have action := reference_ket (program assignment selection outcome) environment _ _
    (program_applyVec assignment selection environment (source index) (saved index) outcome
      (retained index) (admitted index)) (reference index)
  exact (congrArg (fun vector => amplitude index • vector) action).trans (smul_smul _ _ _)

/-- The actual correction cancels the same physical outcome's complete measured character. -/
lemma program_cancel (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (source saved outcome : Word)
    (retained : Placement.Rest assignment)
    (admitted : (selectorBit assignment selection).get retained = true → Canonical source) :
    (program assignment selection outcome).applyVec environment
      (WalshHadamard.walshSign outcome
        (Save.savedWord source saved ((selectorBit assignment selection).get retained)) •
        (Native.ket
          (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec) =
      (Native.ket
        (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec := by
  rw [UnitaryCircuit.applyVec_smul, program_applyVec assignment selection environment source
    saved outcome retained admitted, smul_smul]
  have square := @WalshHadamard.walshSign_mul_self width outcome
    (Save.savedWord source saved ((selectorBit assignment selection).get retained))
  exact (congrArg (fun coefficient : ℂ => coefficient •
    (Native.ket
      (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec)
      square).trans (one_smul _ _)

end

end Arithmetic.Phase

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
