/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Program
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # Complete actual scanned microstep with arbitrary coherent external reference -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

open scoped BigOperators

/-- Tensor only the actual full native microstep matrix beside an unchanged external reference. -/
def referenceOperator (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical (encoding width).width).toQuantum.register.prod
      Reference) :=
  UnitaryOperator.prodTensor ((program width enough).matrix environment)
    (1 : UnitaryOperator Reference)

/-- Every actual original-frame ket and reference label have the exact complete endpoint. -/
lemma reference_ket (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false) (control : state.1.control = false)
    {Reference : Register} (reference : Reference.Index) :
    (referenceOperator width enough environment Reference).applyVec
        (NormalizedVector.ket
          (R := (QubitLayout.canonical (encoding width).width).toQuantum.register.prod Reference)
          ((QubitLayout.canonical _).basisEquiv.symm
            ((encoding width).encode state), reference)).vec =
      (NormalizedVector.ket
        (R := (QubitLayout.canonical (encoding width).width).toQuantum.register.prod Reference)
        ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode (SharedEEA.NativeMicrostep.step width state.1, state.2)),
            reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (program_apply_source width enough environment state prefixZero addressZero borrowZero control)
  change UnitaryOperator.applyVec ((program width enough).matrix environment)
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode state))).vec = _ at actual
  change (UnitaryOperator.prodTensor ((program width enough).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- All amplitudes, dirty Iter and original-work/reference correlations retain the full action. -/
lemma coherent_reference (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data width)
    (prefixZero : ∀ index, (state index).2.2.1 = 0)
    (addressZero : ∀ index, (state index).2.1 = 0)
    (borrowZero : ∀ index, (state index).2.2.2 = false)
    (control : ∀ index, (state index).1.control = false)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (referenceOperator width enough environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket
            (R := (QubitLayout.canonical (encoding width).width).toQuantum.register.prod Reference)
            ((QubitLayout.canonical _).basisEquiv.symm ((encoding width).encode (state index)),
              reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket
          (R := (QubitLayout.canonical (encoding width).width).toQuantum.register.prod Reference)
          ((QubitLayout.canonical _).basisEquiv.symm
            ((encoding width).encode
              (SharedEEA.NativeMicrostep.step width (state index).1, (state index).2)),
                reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    reference_ket width enough environment (state index) (prefixZero index) (addressZero index)
      (borrowZero index) (control index)]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep
