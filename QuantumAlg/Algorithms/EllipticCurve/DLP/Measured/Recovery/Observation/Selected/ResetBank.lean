/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.ReferenceFamily
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.History.Columns

/-!
# The same selected actual reset coefficient and seed-bank density

Selection fixes the complete actual reset Store and an arbitrary predicate
of the original History. The Reference family retains Hidden, that full Store,
the original History and the actual reset Path. Its selected quantum marginal
is exactly the seed entry of C7's density from the same selected actual output.
The old bank coordinates differ only by the empty quantum result-cell factor.

The complete reset Store is essential: its ready projection alone can identify different
dirty result-cell histories. A borrowed classical-frame condition can be included in the
arbitrary History predicate; no frame value is removed. All Reference coherences,
zero-mass fibers and exponent width zero are retained. No normalization, clean-input or
positive-mass premise is used. These are mathematical input coordinates, not a free
permutation or a second execution. Neither the final block reversal nor an old
virtual-input fiber is constructed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace SelectedResetBank

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma selected_mapped_slice_entry {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {Joint Reference : Register}
    (source : ExecutionState C Joint) {slices : ExecutionState C Reference}
    (update : C → D) (first second : C → Prop) (selected : D → Prop)
    [DecidablePred first] [DecidablePred second] [DecidablePred selected]
    (selected_eq : ∀ record, selected (update record) ↔ first record ∧ second record)
    (row column : Joint.Index) (left right : Reference.Index)
    (slice_entry : ∀ record, (slices.block record).matrix left right =
      (source.block record).matrix row column) :
    ((slices.mapClassical update).filterClassical selected).quantumMarginal.matrix left right =
      ((source.filterClassical second).filterClassical first).quantumMarginal.matrix
        row column := by
  rw [ExecutionState.filterClassical_matrix_weighted,
    ExecutionState.weightedMatrixEntry_mapClassical,
    ExecutionState.filterClassical_matrix_weighted]
  unfold ExecutionState.weightedMatrixEntry
  apply Finset.sum_congr rfl
  intro record _
  change (if selected (update record) then (1 : ℂ) else 0) *
      (slices.block record).matrix left right =
    (if first record then (1 : ℂ) else 0) *
      ((source.filterClassical second).block record).matrix row column
  rw [slice_entry record]
  by_cases same : first record <;> by_cases chosen : second record <;>
    simp only [selected_eq record, same, chosen, and_self, and_false, false_and, if_true,
      if_false,
      ExecutionState.filterClassical_block, DensityOperator.zero_matrix, Matrix.zero_apply,
      one_mul, zero_mul]

private lemma supported_columns_sandwich_entry {Row Column : Type} [Fintype Column]
    [columnDecision : DecidableEq Column]
    (columns : Matrix Row Column ℂ) (reference : Row → Column) (supported : Row → Prop)
    [DecidablePred supported]
    (columns_entry : ∀ row column, columns row column =
      if supported row then (if column = reference row then 1 else 0) else 0)
    (density : Matrix Column Column ℂ) (left right : Row) :
    (columns * density * columns.conjTranspose) left right =
      if supported left ∧ supported right then density (reference left) (reference right)
      else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, columns_entry,
    apply_ite (fun value : ℂ => star value), star_one, star_zero]
  by_cases first : supported left <;> by_cases second : supported right <;>
    simp only [first, second, and_self, and_false, false_and, if_true, if_false,
      ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq', Finset.sum_const_zero]

open Recovery.Stage.PointCoordinates (coordinates coordinates_symm)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths (initializedBasis joint)
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion (storeDensity)
open Recovery.Initialization (newReset newResetLabel newResetLabel_initializedBasis)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)

variable {Reference : Register} {History : Type} [Fintype History]

/-- Keep the entire actual reset Store, original History and reset Path in the selected family. -/
def selectedCoefficients
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (original : Store (Recovery.Layout.terminal p.size m)) (predicate : History → Prop) :
    ExecutionState (ClassicalOracleModel.empty.HiddenState ×
      Initialization.ReferenceFamily.CoefficientHistory E fieldTail m seed History) Reference :=
  (Initialization.ReferenceFamily.coefficients (environment := environment) E fieldTail m seed
    state).filterClassical
    (fun record => record.2.1 = original ∧ predicate record.2.2.1)

section SelectedCoefficientEntries

attribute [local irreducible] newReset

/-- The selected coefficient is the exact seed slice of the same actual selected Store density. -/
lemma selectedCoefficients_quantumMarginal_entry
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (original : Store (Recovery.Layout.terminal p.size m)) (predicate : History → Prop)
    (left right : Reference.Index) :
    (selectedCoefficients (environment := environment) E fieldTail m seed state original
      predicate).quantumMarginal.matrix
        left right =
      storeDensity (((newReset E fieldTail m seed).execute environment Reference
        state).filterClassical
        (fun record => predicate record.2.2.1)) original
          (newResetLabel E fieldTail m seed, left) (newResetLabel E fieldTail m seed, right) := by
  unfold selectedCoefficients Initialization.ReferenceFamily.coefficients storeDensity
  exact selected_mapped_slice_entry
    ((newReset E fieldTail m seed).execute environment Reference state)
    (Initialization.ReferenceFamily.recordCoordinates E fieldTail m seed History)
    (fun record => record.1 = original) (fun record => predicate record.2.2.1)
    (fun record => record.2.1 = original ∧ predicate record.2.2.1)
    (fun _ => Iff.rfl)
    (newResetLabel E fieldTail m seed, left) (newResetLabel E fieldTail m seed, right)
    left right (fun _ => rfl)

end SelectedCoefficientEntries

omit [Fact p.Prime] in
private lemma initialized_oldBank_reference
    (bank : Recovery.Reference.Measured.CommonBank.Bank p.size Reference) :
    (initializedBasis p.size m Reference
      ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm bank)).2 = bank.2.2 := by
  change ((coordinates p.size m Reference).symm
    (0, (0, (Recovery.Layout.Reference.bankBasis p.size m Reference).symm bank))).2 = _
  rw [coordinates_symm]
  rfl

omit [Fact p.Prime] in
private lemma initialized_oldBank_injective :
    Function.Injective (fun bank : Recovery.Reference.Measured.CommonBank.Bank p.size Reference =>
      initializedBasis p.size m Reference
        ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm bank)) := by
  intro first second same
  apply (Recovery.Layout.Reference.bankBasis p.size m Reference).symm.injective
  have projected := congrArg (joint p.size m Reference) same
  simpa only [initializedBasis, Equiv.apply_symm_apply, Prod.mk.injEq, true_and] using projected

private lemma initialized_oldBank_seed_iff
    (bank : Recovery.Reference.Measured.CommonBank.Bank p.size Reference) :
    (initializedBasis p.size m Reference
      ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm bank)).1 =
        newResetLabel E fieldTail m seed ↔
      bank = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference bank.2.2 := by
  constructor
  · intro same
    apply initialized_oldBank_injective (p := p) (m := m) (Reference := Reference)
    exact (Prod.ext same (initialized_oldBank_reference (p := p) (m := m) bank)).trans
      (newResetLabel_initializedBasis E fieldTail m seed Reference bank.2.2).symm
  · intro same
    exact (congrArg (fun value : Recovery.Reference.Measured.CommonBank.Bank p.size Reference =>
      (initializedBasis p.size m Reference
        ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm value)).1) same).trans
      (congrArg Prod.fst (newResetLabel_initializedBasis E fieldTail m seed Reference bank.2.2))

/-- The original arithmetic/selector reset seed is a column for each unchanged Reference label. -/
def resetBankColumns (Reference : Register) :
    Matrix (Recovery.Reference.Measured.CommonBank.Bank p.size Reference) Reference.Index ℂ :=
  fun bank reference =>
    if bank = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference reference
      then 1 else 0

private lemma resetBankColumns_entry (Reference : Register)
    (bank : Recovery.Reference.Measured.CommonBank.Bank p.size Reference) (reference :
      Reference.Index) :
    resetBankColumns E fieldTail m seed Reference bank reference =
      if bank = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference
        bank.2.2 then
        (if reference = bank.2.2 then 1 else 0) else 0 := by
  have same : bank = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference
    reference ↔
      bank = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference bank.2.2 ∧
        reference = bank.2.2 := by
    constructor
    · intro equal
      have referenceSame : bank.2.2 = reference := congrArg
        (fun value : Recovery.Reference.Measured.CommonBank.Bank p.size Reference => value.2.2)
          equal
      exact ⟨equal.trans (congrArg
        (Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference)
          referenceSame.symm),
        referenceSame.symm⟩
    · rintro ⟨supported, referenceSame⟩
      exact supported.trans (congrArg
        (Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference)
          referenceSame.symm)
  simp only [resetBankColumns, same, ite_and]

section SeedBankSandwich

attribute [local irreducible] Recovery.Reference.Initialization.resetBank resetBankColumns

private lemma resetBankColumns_sandwich_entry (Reference : Register)
    (density : Matrix Reference.Index Reference.Index ℂ)
    (left right : Recovery.Reference.Measured.CommonBank.Bank p.size Reference) :
    (resetBankColumns E fieldTail m seed Reference * density *
        (resetBankColumns E fieldTail m seed Reference).conjTranspose) left right =
      if left = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference left.2.2 ∧
          right = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference
            right.2.2 then
        density left.2.2 right.2.2 else 0 := by
  exact supported_columns_sandwich_entry
    (columnDecision := Reference.decEq)
    (resetBankColumns E fieldTail m seed Reference)
    (fun bank : Recovery.Reference.Measured.CommonBank.Bank p.size Reference => bank.2.2)
    (fun bank => bank = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference
      bank.2.2)
    (resetBankColumns_entry E fieldTail m seed Reference) density left right

end SeedBankSandwich

/-- Every old-bank entry uses the same full-Store selected actual Reference coefficient. -/
lemma actualHistoryBankDensity_seed_entry
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (original : Store (Recovery.Layout.terminal p.size m)) (predicate : History → Prop)
    (left right : Recovery.Reference.Measured.CommonBank.Bank p.size Reference) :
    ((Initialization.HistoryColumns.actualHistoryBankDensity (environment := environment) E
      fieldTail m seed state
      predicate original).submatrix
      (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
      (Recovery.Layout.Reference.bankBasis p.size m Reference).symm) left right =
      if left = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference left.2.2 ∧
          right = Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference
            right.2.2 then
        (selectedCoefficients (environment := environment) E fieldTail m seed state original
          predicate).quantumMarginal.matrix
          left.2.2 right.2.2 else 0 := by
  have supported := Initialization.HistoryColumns.actual_history_store_seeded (environment :=
    environment) E fieldTail m seed
    state predicate original
    (initializedBasis p.size m Reference
      ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm left)).1
    (initializedBasis p.size m Reference
      ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm right)).1
    (initializedBasis p.size m Reference
      ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm left)).2
    (initializedBasis p.size m Reference
      ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm right)).2
  change storeDensity (((newReset E fieldTail m seed).execute environment Reference
    state).filterClassical
      (fun record => predicate record.2.2.1)) original
      (initializedBasis p.size m Reference
        ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm left))
      (initializedBasis p.size m Reference
        ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm right)) = _
  change storeDensity (((newReset E fieldTail m seed).execute environment Reference
    state).filterClassical
      (fun record => predicate record.2.2.1)) original
      (initializedBasis p.size m Reference
        ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm left))
      (initializedBasis p.size m Reference
        ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm right)) =
    if (initializedBasis p.size m Reference
          ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm left)).1 =
            newResetLabel E fieldTail m seed ∧
        (initializedBasis p.size m Reference
          ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm right)).1 =
            newResetLabel E fieldTail m seed then
      storeDensity (((newReset E fieldTail m seed).execute environment Reference
        state).filterClassical
        (fun record => predicate record.2.2.1)) original
        (newResetLabel E fieldTail m seed, (initializedBasis p.size m Reference
          ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm left)).2)
        (newResetLabel E fieldTail m seed, (initializedBasis p.size m Reference
          ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm right)).2)
    else 0 at supported
  rw [initialized_oldBank_reference, initialized_oldBank_reference] at supported
  exact supported.trans (if_congr
    (and_congr (initialized_oldBank_seed_iff E fieldTail m seed left)
      (initialized_oldBank_seed_iff E fieldTail m seed right))
    (selectedCoefficients_quantumMarginal_entry E fieldTail m seed state original predicate
      left.2.2 right.2.2).symm rfl)

/-- The C7 density in old bank coordinates is the seed-column sandwich of that same selection. -/
lemma actualHistoryBankDensity_eq_seedBank
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (original : Store (Recovery.Layout.terminal p.size m)) (predicate : History → Prop) :
    (Initialization.HistoryColumns.actualHistoryBankDensity (environment := environment) E
      fieldTail m seed state
      predicate original).submatrix
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm =
      resetBankColumns E fieldTail m seed Reference *
        (selectedCoefficients (environment := environment) E fieldTail m seed state original
          predicate).quantumMarginal.matrix *
        (resetBankColumns E fieldTail m seed Reference).conjTranspose := by
  ext left right
  exact (actualHistoryBankDensity_seed_entry E fieldTail m seed state original predicate
    left right).trans
      (resetBankColumns_sandwich_entry E fieldTail m seed Reference
        (selectedCoefficients (environment := environment) E fieldTail m seed state original
          predicate).quantumMarginal.matrix
        left right).symm

end

end SelectedResetBank
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
