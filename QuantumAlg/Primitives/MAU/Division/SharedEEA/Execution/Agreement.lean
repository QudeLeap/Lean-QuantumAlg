/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.Runtime
import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Agreement

/-!
# Actual prepared division columns agree with independent modular arithmetic

The mathematical permutation changes only the old modular target, preserves
every original source/flag and every prepared auxiliary coordinate, and
contains no circuit or run. Every allowed prepared column of the actual
complete program equals this independent operator, with no phase quotient.
The local support covers unit denominators, arbitrary modular numerators and
targets, and either supplied flag value. Modulus one keeps the actual fixed
preparation and fixes the whole prepared frame. Full supported mixed-state
and endpoint proofs remain separate obligations.
-/

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionTarget

noncomputable section

open Execution ExecutionLayout Inversion.SharedEEA

/-- Independent modular arithmetic on the actual supplied basis labels. -/
def oldPermutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).trans
    ((ExecutionSpecification.permutation modulus modulusPositive).trans
      (inputBasisEquiv modulus.size).symm)

/-- The independently specified original fields use the same actual supplied binary labels. -/
lemma divisionTarget_old_read (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) :
    inputBasisEquiv modulus.size (oldPermutation modulus modulusPositive old) =
      ExecutionSpecification.permutation modulus modulusPositive
        (inputBasisEquiv modulus.size old) :=
  (inputBasisEquiv modulus.size).apply_symm_apply _

/-- Modulus one fixes every supplied binary label and flag. -/
lemma divisionTarget_old_one (old : (before (1 : Nat).size).register.Index) :
    oldPermutation 1 (by decide) old = old := by
  apply (inputBasisEquiv (1 : Nat).size).injective
  rw [divisionTarget_old_read, ExecutionSpecification.divisionSpecification_one]

/-- Preserve every auxiliary basis value while applying only the independent old-data arithmetic. -/
def permutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (after modulus.size).register.Index :=
  (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (oldPermutation modulus modulusPositive)).trans
      (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)))

/-- Complete mathematical assembly preserves every fresh coordinate and all unchanged old data. -/
lemma divisionTarget_permutation_assembly (modulus : Nat) (modulusPositive : 0 < modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (old : (before modulus.size).register.Index) :
    permutation modulus modulusPositive
        (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size) (fresh, old)) =
      PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
        (fresh, oldPermutation modulus modulusPositive old) := by
  let update : ((InputPreparation.auxiliaryLayout modulus.size).register.Index ×
      (before modulus.size).register.Index) → (after modulus.size).register.Index :=
    fun pair => PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
      (pair.1, oldPermutation modulus modulusPositive pair.2)
  change update ((PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)).symm
    (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size) (fresh, old))) =
      update (fresh, old)
  exact congrArg update
    ((PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)).symm_apply_apply
      (fresh, old))

/-- Metadata-free mathematical unitary on every actual prepared output system. -/
def operator (modulus : Nat) (modulusPositive : 0 < modulus) :
    UnitaryOperator (after modulus.size).register :=
  UnitaryOperator.ofPerm (R := (after modulus.size).register)
    (permutation modulus modulusPositive).symm

/-- Every independent mathematical basis column retains its complete exact amplitude. -/
lemma divisionTarget_operator_ket (modulus : Nat) (modulusPositive : 0 < modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (old : (before modulus.size).register.Index) :
    (operator modulus modulusPositive).apply
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size) (fresh, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
          (fresh, oldPermutation modulus modulusPositive old)) := by
  have actual := UnitaryOperator.ofPerm_apply_ket (R := (after modulus.size).register)
    (permutation modulus modulusPositive).symm
    (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size) (fresh, old))
  exact actual.trans (congrArg (NormalizedVector.ket (R := (after modulus.size).register))
    (divisionTarget_permutation_assembly modulus modulusPositive fresh old))

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionTarget

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionAgreement

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution ExecutionLayout Inversion.SharedEEA

/-- Actual word output equals independent modular addition for every canonical target. -/
lemma divisionAgreement_outputOld (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index)
    (targetBounded : (inputBasisEquiv modulus.size old).2.1.2.val < modulus) :
    ExecutionRuntime.outputOld modulus modulusPositive old =
      ExecutionTarget.oldPermutation modulus modulusPositive old := by
  apply (inputBasisEquiv modulus.size).injective
  rw [ExecutionRuntime.outputOld, Equiv.apply_symm_apply, ExecutionTarget.divisionTarget_old_read]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        have actual := (ExecutionSpecification.divisionSpecification_valid modulus modulusPositive
          (inputBasisEquiv modulus.size old) targetBounded).2.2.1
        rw [actual]
        change ((inputBasisEquiv modulus.size old).2.1.2.val +
          (NumberTheory.SharedEEA.CanonicalInverse.word modulus modulusPositive
            (inputBasisEquiv modulus.size old).1.val).val *
              (inputBasisEquiv modulus.size old).2.1.1.val) % modulus = _
        rw [Nat.mul_comm]
    · rfl

/-- Each allowed actual prepared ket agrees with the complete independent mathematical operator. -/
lemma divisionAgreement_prepared_ket (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) (allowed : admissible modulus old) :
    (ExecutionRuntime.program modulus).applyNormalized environment
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
            ((InputPreparation.preparation modulus).value, old))) =
      (ExecutionTarget.operator modulus modulusPositive).apply
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
            ((InputPreparation.preparation modulus).value, old))) := by
  by_cases nontrivial : 1 < modulus
  · have actual := ExecutionRuntime.divisionExecution_program_prepared
      (environment := environment) modulus nontrivial old allowed
    have same := divisionAgreement_outputOld modulus modulusPositive old allowed.2.2.2
    have output : ExecutionRuntime.outputBasis modulus modulusPositive old =
        PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
          ((InputPreparation.preparation modulus).value,
            ExecutionTarget.oldPermutation modulus modulusPositive old) :=
      congrArg (fun value => PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
        ((InputPreparation.preparation modulus).value, value)) same
    exact (actual.trans (congrArg (NormalizedVector.ket (R := (after modulus.size).register))
      output)).trans (ExecutionTarget.divisionTarget_operator_ket modulus modulusPositive
        (InputPreparation.preparation modulus).value old).symm
  · have one : modulus = 1 := by omega
    subst modulus
    rw [ExecutionTarget.divisionTarget_operator_ket, ExecutionTarget.divisionTarget_old_one]
    exact ExecutionRuntime.divisionExecution_program_trivial_ket
      (environment := environment) 1 (by omega) _

/-- Native and independent matrices agree on each allowed prepared column and every output row. -/
lemma divisionAgreement_prepared_column (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) (allowed : admissible modulus old)
    (row : (after modulus.size).register.Index) :
    (ExecutionRuntime.program modulus).matrix environment row
        (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
          ((InputPreparation.preparation modulus).value, old)) =
      (ExecutionTarget.operator modulus modulusPositive) row
        (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
          ((InputPreparation.preparation modulus).value, old)) := by
  have values := congrArg (fun vector : NormalizedVector (after modulus.size).register =>
    vector.vec row) (divisionAgreement_prepared_ket
      (environment := environment) modulus modulusPositive old allowed)
  let basis : (after modulus.size).register.Index :=
    PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
      ((InputPreparation.preparation modulus).value, old)
  change HilbertOperator.applyVec
      ((ExecutionRuntime.program modulus).matrix environment :
        HilbertOperator (after modulus.size).register)
      (NormalizedVector.ket basis) row =
    HilbertOperator.applyVec
      ((ExecutionTarget.operator modulus modulusPositive) :
        HilbertOperator (after modulus.size).register) (NormalizedVector.ket basis) row at values
  simpa only [HilbertOperator.applyVec_ket] using values

/-- Encode the original Data fields without assuming a zero target, numerator, or flag. -/
def dataInput (modulus : Nat) (modulusPositive : 0 < modulus) (value : Data modulus) :
    (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).symm
    (Accumulate.residueWord modulus modulusPositive value.denominator,
      ((Accumulate.residueWord modulus modulusPositive value.numerator,
        Accumulate.residueWord modulus modulusPositive value.target), value.flag))

/-- Every original unit-denominator Data value satisfies the local support at any positive
  modulus. -/
lemma divisionAgreement_data_admissible (modulus : Nat) (modulusPositive : 0 < modulus)
    (value : Data modulus) : admissible modulus (dataInput modulus modulusPositive value) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  simp only [admissible, dataInput, Equiv.apply_symm_apply, ExecutionSpecification.admissible]
  exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime value.denominator,
    ZMod.val_lt _, ZMod.val_lt _⟩

/-- The actual output word action is exactly the unchanged original modular-add Data contract. -/
lemma divisionAgreement_output_data (modulus : Nat) (modulusPositive : 0 < modulus)
    (value : Data modulus) :
    ExecutionRuntime.outputOld modulus modulusPositive (dataInput modulus modulusPositive value) =
      dataInput modulus modulusPositive value.addQuotientIntoTarget := by
  apply (inputBasisEquiv modulus.size).injective
  simp only [ExecutionRuntime.outputOld, dataInput, Equiv.apply_symm_apply]
  rw [divisionOutput_unit]
  rfl

/-- The independent target also realizes exactly the original Data map, including modulus one. -/
lemma divisionAgreement_target_data (modulus : Nat) (modulusPositive : 0 < modulus)
    (value : Data modulus) :
    ExecutionTarget.oldPermutation modulus modulusPositive
        (dataInput modulus modulusPositive value) =
      dataInput modulus modulusPositive value.addQuotientIntoTarget :=
  (divisionAgreement_outputOld modulus modulusPositive _
    (divisionAgreement_data_admissible modulus modulusPositive value).2.2.2).symm.trans
      (divisionAgreement_output_data modulus modulusPositive value)

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionAgreement
