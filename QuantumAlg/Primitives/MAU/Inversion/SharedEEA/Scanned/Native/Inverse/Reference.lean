/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Inverse
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # Entire actual pruned inverse on coherent input, arbitrary target and external reference -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInverse

noncomputable section

open scoped BigOperators

/-- The actual complete compute/copy/native-adjoint matrix beside an unchanged Reference. -/
def referenceOperator (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator
      ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum.register.prod
        Reference) :=
  UnitaryOperator.prodTensor ((program modulus nontrivial).matrix environment)
    (1 : UnitaryOperator Reference)

/-- Complete inverse and whole-pool restoration beside any external reference label. -/
lemma reference_ket (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    {Reference : Register} (reference : Reference.Index) :
    (referenceOperator modulus nontrivial environment Reference).applyVec
        (NormalizedVector.ket
          (R := (QubitLayout.canonical
            (OutputCopy.encoding modulus.size).width).toQuantum.register.prod Reference)
          ((QubitLayout.canonical _).basisEquiv.symm
            ((OutputCopy.encoding modulus.size).encode
              ((InitialFrame.initial modulus input, pool), target)), reference)).vec =
      (NormalizedVector.ket
        (R := (QubitLayout.canonical
          (OutputCopy.encoding modulus.size).width).toQuantum.register.prod Reference)
        ((QubitLayout.canonical _).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            ((InitialFrame.initial modulus input, pool),
              output modulus input.val positive bounded target)), reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (program_initial modulus nontrivial environment input target coprime positive bounded pool
      addressZero prefixZero borrowZero)
  change UnitaryOperator.applyVec ((program modulus nontrivial).matrix environment)
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((OutputCopy.encoding modulus.size).encode
        ((InitialFrame.initial modulus input, pool), target)))).vec = _ at actual
  change (UnitaryOperator.prodTensor ((program modulus nontrivial).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- Every coherent input, dirty-target and Reference correlation has the exact inverse action. -/
lemma coherent_reference (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (input target : Index → Fin (2 ^ modulus.size))
    (coprime : ∀ index, Nat.Coprime (input index).val modulus)
    (positive : ∀ index, 0 < (input index).val) (bounded : ∀ index, (input index).val < modulus)
    (pool : Index → Pool modulus.size) (addressZero : ∀ index, (pool index).1 = 0)
    (prefixZero : ∀ index, (pool index).2.1 = 0) (borrowZero : ∀ index, (pool index).2.2 = false)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (referenceOperator modulus nontrivial environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket
            (R := (QubitLayout.canonical
              (OutputCopy.encoding modulus.size).width).toQuantum.register.prod Reference)
            ((QubitLayout.canonical _).basisEquiv.symm
              ((OutputCopy.encoding modulus.size).encode
                ((InitialFrame.initial modulus (input index), pool index), target index)),
                  reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket
          (R := (QubitLayout.canonical
            (OutputCopy.encoding modulus.size).width).toQuantum.register.prod Reference)
          ((QubitLayout.canonical _).basisEquiv.symm
            ((OutputCopy.encoding modulus.size).encode
              ((InitialFrame.initial modulus (input index), pool index),
                output modulus (input index).val (positive index) (bounded index) (target index))),
                  reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    reference_ket modulus nontrivial environment (input index) (target index) (coprime index)
      (positive index) (bounded index) (pool index) (addressZero index) (prefixZero index)
        (borrowZero index)]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInverse
