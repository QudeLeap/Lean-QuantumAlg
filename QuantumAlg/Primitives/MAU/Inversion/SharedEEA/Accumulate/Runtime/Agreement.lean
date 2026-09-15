/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Runtime
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Target

/-!
# Complete prepared columns agree with independent modular-add inversion

The actual nontrivial program restores every prepared field and preserves
the original input and flag. Its target word is the independently defined
modular sum. The prepared identity branch has the same mathematical action
modulo one. All allowed columns agree exactly, including their amplitudes,
before the separate proof for arbitrary supported joint density operators.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AccumulateAgreement

noncomputable section

open Execution AccumulateRuntime

/-- The actual word result equals the independent modular data permutation on canonical targets. -/
theorem accumulateAgreement_output (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index)
    (targetBounded : (inputBasisEquiv modulus.size old).2.1.val < modulus) :
    outputOld modulus modulusPositive old =
      AccumulateTarget.inputPermutation modulus modulusPositive old := by
  have fields := AccumulateSpecification.accumulateSpecification_valid modulus modulusPositive
    (inputBasisEquiv modulus.size old) targetBounded
  apply (inputBasisEquiv modulus.size).injective
  rw [outputOld, Equiv.apply_symm_apply, AccumulateTarget.accumulateTarget_input_read]
  apply Prod.ext
  · exact fields.1.symm
  · apply Prod.ext
    · apply Fin.ext
      exact fields.2.1.symm
    · exact fields.2.2.symm

/-- The entire prepared ket agrees with the independent full target at every positive modulus. -/
theorem accumulateAgreement_prepared_ket (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old)) :
    (program modulus).applyNormalized
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (modulus.size + 1)
            ((InputPreparation.preparation modulus).value, old))) =
      (AccumulateTarget.operator modulus modulusPositive).apply
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (modulus.size + 1)
            ((InputPreparation.preparation modulus).value, old))) := by
  by_cases nontrivial : 1 < modulus
  · have actual := accumulateRuntime_prepared_ket modulus nontrivial old allowed
    have same := accumulateAgreement_output modulus modulusPositive old allowed.2.2
    have output := congrArg
      (fun value => NormalizedVector.ket (R := (after modulus.size).register)
        (PayloadPreparation.assembly modulus.size (modulus.size + 1)
          ((InputPreparation.preparation modulus).value, value))) same
    exact (actual.trans output).trans
      (AccumulateTarget.accumulateTarget_ket modulus modulusPositive
        (InputPreparation.preparation modulus).value old).symm
  · have one : modulus = 1 := by omega
    subst modulus
    rw [AccumulateTarget.accumulateTarget_ket, AccumulateTarget.accumulateTarget_input_one]
    exact accumulateRuntime_trivial_ket 1 (by omega) _

/-- Exact prepared-column agreement keeps every output row and hence every reference coherence. -/
theorem accumulateAgreement_prepared_column (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old))
    (row : (after modulus.size).register.Index) :
    (program modulus).matrix row
        (PayloadPreparation.assembly modulus.size (modulus.size + 1)
          ((InputPreparation.preparation modulus).value, old)) =
      (AccumulateTarget.operator modulus modulusPositive) row
        (PayloadPreparation.assembly modulus.size (modulus.size + 1)
          ((InputPreparation.preparation modulus).value, old)) := by
  have values := congrArg (fun vector : NormalizedVector (after modulus.size).register =>
    vector.vec row) (accumulateAgreement_prepared_ket modulus modulusPositive old allowed)
  let basis : (after modulus.size).register.Index :=
    PayloadPreparation.assembly modulus.size (modulus.size + 1)
      ((InputPreparation.preparation modulus).value, old)
  change HilbertOperator.applyVec
      ((program modulus).matrix : HilbertOperator (after modulus.size).register)
      (NormalizedVector.ket basis) row =
    HilbertOperator.applyVec
      ((AccumulateTarget.operator modulus modulusPositive) :
        HilbertOperator (after modulus.size).register) (NormalizedVector.ket basis) row at values
  simpa only [HilbertOperator.applyVec_ket] using values

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateAgreement
