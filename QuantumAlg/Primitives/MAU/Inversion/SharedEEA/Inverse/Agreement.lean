/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Runtime
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Target

/-!
# The actual native inverse agrees with its independent canonical columns

The complete compute-copy-dagger realization restores every prepared field
and the original input. Its source corrected coefficient is proved equal
to the independently defined canonical `ZMod` inverse. Consequently each
admitted prepared basis column agrees exactly with the mathematical target
[LYL+26, sec_EEA/sub_4phase.tex:104-128].

These equalities retain amplitudes and arbitrary target values. They are
the basis evidence for the subsequent full supported-density proof; they
do not themselves replace that quantum-reference obligation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseAgreement

noncomputable section

open Execution InversePreparation NumberTheory.SharedEEA

/-- The source-derived XOR output equals the independent canonical arithmetic permutation. -/
theorem outputOld_eq_permutation (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index)
    (coprime : Nat.Coprime (inputBasisEquiv modulus.size old).1.val modulus)
    (positive : 0 < (inputBasisEquiv modulus.size old).1.val)
    (bounded : (inputBasisEquiv modulus.size old).1.val < modulus) :
    InverseRuntime.outputOld modulus old positive bounded =
      InverseSpecification.permutation modulus modulusPositive old := by
  apply (inputBasisEquiv modulus.size).injective
  rw [InverseRuntime.outputOld, Equiv.apply_symm_apply, InverseSpecification.permutation_read]
  apply Prod.ext
  · rfl
  · apply Fin.ext
    exact congrArg
      (fun word : Fin (2 ^ modulus.size) => (inputBasisEquiv modulus.size old).2.val ^^^ word.val)
      (CanonicalInverse.source_eq_word modulus (inputBasisEquiv modulus.size old).1.val
        coprime positive bounded)

/-- Every valid prepared input ket has the complete independent mathematical output amplitude. -/
theorem prepared_ket (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : InverseSpecification.admissible modulus old) :
    (InverseRuntime.program modulus).applyNormalized
        (NormalizedVector.ket (R := (after modulus.size).register)
          (assembly modulus.size ((InputPreparation.preparation modulus).value, old))) =
      (InverseTarget.operator modulus modulusPositive).apply
        (NormalizedVector.ket (R := (after modulus.size).register)
          (assembly modulus.size ((InputPreparation.preparation modulus).value, old))) := by
  by_cases nontrivial : 1 < modulus
  · have positive := InverseSpecification.admissible_positive modulus nontrivial old allowed
    have actual := InverseRuntime.program_prepared_input modulus nontrivial old
      allowed.2 positive allowed.1
    have same := outputOld_eq_permutation modulus modulusPositive old
      allowed.2 positive allowed.1
    have output : InverseRuntime.outputBasis modulus old positive allowed.1 =
        assembly modulus.size ((InputPreparation.preparation modulus).value,
          InverseSpecification.permutation modulus modulusPositive old) :=
      congrArg (fun value =>
        assembly modulus.size ((InputPreparation.preparation modulus).value, value)) same
    exact (actual.trans (congrArg (NormalizedVector.ket (R := (after modulus.size).register))
      output)).trans (InverseTarget.operator_ket modulus modulusPositive
        (InputPreparation.preparation modulus).value old).symm
  · have one : modulus = 1 := by omega
    subst modulus
    rw [InverseTarget.operator_ket, InverseSpecification.permutation_one]
    exact InverseRuntime.program_trivial_ket 1 (by omega) _

/-- Actual and independent matrices agree on every valid prepared column and every output row. -/
theorem prepared_column (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : InverseSpecification.admissible modulus old)
    (row : (after modulus.size).register.Index) :
    (InverseRuntime.program modulus).matrix row
        (assembly modulus.size ((InputPreparation.preparation modulus).value, old)) =
      (InverseTarget.operator modulus modulusPositive) row
        (assembly modulus.size ((InputPreparation.preparation modulus).value, old)) := by
  have values := congrArg (fun vector : NormalizedVector (after modulus.size).register =>
    vector.vec row) (prepared_ket modulus modulusPositive old allowed)
  let basis : (after modulus.size).register.Index :=
    assembly modulus.size ((InputPreparation.preparation modulus).value, old)
  change HilbertOperator.applyVec
      ((InverseRuntime.program modulus).matrix :
        HilbertOperator (after modulus.size).register) (NormalizedVector.ket basis) row =
    HilbertOperator.applyVec
      ((InverseTarget.operator modulus modulusPositive) :
        HilbertOperator (after modulus.size).register)
      (NormalizedVector.ket basis) row at values
  simpa only [HilbertOperator.applyVec_ket] using values

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseAgreement
