/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Initialized.Execution
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Intrinsic initialized bank densities of the actual leading reset

Each bank matrix below is a principal submatrix of one complete Store fiber
of the actual reset output. The reset theorem supplies the support needed to
reconstruct that fiber through the existing initialized columns. No input
initialization certificate, positive-mass branch or clean-bank hypothesis is
used. Original history, the complete reset path and arbitrary Reference remain
in the actual State; summation over them is the existing storeDensity operation.

 It does not construct a
public initializer or assert a common terminal output density.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
namespace InitializedOutput

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

private lemma sandwich_entry_from_factors {Index Basis : Type}
    [Fintype Basis] [DecidableEq Basis]
    (columns : Matrix Index Basis ℂ) (density : Matrix Basis Basis ℂ)
    (row column : Index) (rowBasis columnBasis : Basis) (first second : Prop)
    [Decidable first] [Decidable second]
    (left : ∀ middle, (columns * density) row middle =
      if first then density rowBasis middle else 0)
    (right : ∀ middle, columns column middle =
      if second then (if columnBasis = middle then 1 else 0) else 0) :
    (columns * density * columns.conjTranspose) row column =
      if first then (if second then density rowBasis columnBasis else 0) else 0 := by
  rw [Matrix.mul_apply]
  simp only [left, Matrix.conjTranspose_apply, right]
  by_cases selectedLeft : first
  · by_cases selectedRight : second
    · simp only [if_pos selectedLeft, if_pos selectedRight,
        apply_ite (fun value : ℂ => star value), star_one, star_zero,
        mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
    · simp only [if_pos selectedLeft, if_neg selectedRight, star_zero, mul_zero,
        Finset.sum_const_zero]
  · simp only [if_neg selectedLeft, zero_mul, Finset.sum_const_zero]

/-- Seed support gives the exact selected-coordinate matrix entry. -/
private lemma seeded_selected_entry {Local Frame Selector BankIndex : Type}
    [localDecision : DecidableEq Local] [selectorDecision : DecidableEq Selector]
    (coordinates : Local × Frame ≃ Selector × BankIndex)
    (basis : BankIndex → Local × Frame) (entry : Local × Frame → Local × Frame → ℂ)
    (seed : Local) (selected : Selector)
    (basis_eq : ∀ bank : BankIndex, basis bank = coordinates.invFun (selected, bank))
    (supported : ∀ (left right : Local) (leftRef rightRef : Frame),
      entry (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then entry (seed, leftRef) (seed, rightRef) else 0)
    (outside_seed : ∀ (selector : Selector) (bank : BankIndex), selector ≠ selected →
      (coordinates.invFun (selector, bank)).1 ≠ seed)
    (rowSelector columnSelector : Selector) (rowBank columnBank : BankIndex) :
    entry (coordinates.invFun (rowSelector, rowBank))
        (coordinates.invFun (columnSelector, columnBank)) =
      if rowSelector = selected then
        (if columnSelector = selected then entry (basis rowBank) (basis columnBank) else 0)
      else 0 := by
  by_cases row_selected : rowSelector = selected
  · subst rowSelector
    by_cases column_selected : columnSelector = selected
    · subst columnSelector
      simpa using
        congrArg₂ entry (basis_eq rowBank).symm (basis_eq columnBank).symm
    · simp only [if_neg column_selected]
      have actual := supported
        (coordinates.invFun (selected, rowBank)).1
        (coordinates.invFun (columnSelector, columnBank)).1
        (coordinates.invFun (selected, rowBank)).2
        (coordinates.invFun (columnSelector, columnBank)).2
      exact actual.trans (if_neg (fun both =>
        outside_seed columnSelector columnBank column_selected both.2))
  · simp only [if_neg row_selected]
    have actual := supported
      (coordinates.invFun (rowSelector, rowBank)).1
      (coordinates.invFun (columnSelector, columnBank)).1
      (coordinates.invFun (rowSelector, rowBank)).2
      (coordinates.invFun (columnSelector, columnBank)).2
    exact actual.trans (if_neg (fun both =>
      outside_seed rowSelector rowBank row_selected both.1))

/-- A supported full matrix is reconstructed from its actual selected principal submatrix. -/
private lemma seeded_selected_sandwich {Local Frame Selector BankIndex : Type}
    [Fintype BankIndex] [localDecision : DecidableEq Local]
    [selectorDecision : DecidableEq Selector]
    (coordinates : Local × Frame ≃ Selector × BankIndex)
    (basis : BankIndex → Local × Frame) (columns : Matrix (Local × Frame) BankIndex ℂ)
    (matrix : Matrix (Local × Frame) (Local × Frame) ℂ) (seed : Local) (selected : Selector)
    (basis_eq : ∀ bank : BankIndex, basis bank = coordinates.invFun (selected, bank))
    (supported : ∀ (left right : Local) (leftRef rightRef : Frame),
      matrix (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then matrix (seed, leftRef) (seed, rightRef) else 0)
    (outside_seed : ∀ (selector : Selector) (bank : BankIndex), selector ≠ selected →
      (coordinates.invFun (selector, bank)).1 ≠ seed)
    (sandwich_entry : ∀ (density : Matrix BankIndex BankIndex ℂ)
      (rowSelector columnSelector : Selector) (rowBank columnBank : BankIndex),
      (columns * density * columns.conjTranspose)
          (coordinates.invFun (rowSelector, rowBank))
          (coordinates.invFun (columnSelector, columnBank)) =
        if rowSelector = selected then
          (if columnSelector = selected then density rowBank columnBank else 0) else 0) :
    matrix = columns * matrix.submatrix basis basis * columns.conjTranspose := by
  apply Matrix.ext
  intro row column
  obtain ⟨⟨rowSelector, rowBank⟩, rfl⟩ := coordinates.symm.surjective row
  obtain ⟨⟨columnSelector, columnBank⟩, rfl⟩ := coordinates.symm.surjective column
  have entry := seeded_selected_entry (localDecision := localDecision)
    (selectorDecision := selectorDecision) coordinates basis matrix seed selected
    basis_eq supported outside_seed rowSelector columnSelector rowBank columnBank
  exact entry.trans (sandwich_entry (matrix.submatrix basis basis)
    rowSelector columnSelector rowBank columnBank).symm



open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Recovery.Stage (stages)
open Recovery.Stage.PointCoordinates (Bank)
open Recovery.Stage.PointCoordinates.StageWord (bitBasis)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
  (joint joint_symm initializedBasis initializedColumns initializedColumns_mul bankWord)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
  (actual_initialized_store_density)
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion (storeDensity)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open scoped BigOperators ComplexOrder

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma storeDensity_history_sum {width m : Nat} (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal width m) Reference History)
    (stored : Store (Recovery.Layout.terminal width m)) :
    storeDensity state stored = ∑ history : History, (state.block (stored, history)).matrix := by
  change (∑ record : Store (Recovery.Layout.terminal width m) × History,
    (if record.1 = stored then state.block record else DensityOperator.zero _).matrix) = _
  simp only [apply_ite DensityOperator.matrix, DensityOperator.zero_matrix, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']

private lemma initializedColumns_entry {width m : Nat} (Reference : Register)
    (control : Fin 2) (memory : Bool) (rowBank columnBank : Bank width m Reference) :
    initializedColumns width m Reference
        ((joint width m Reference).symm (control, (memory, rowBank))) columnBank =
      if control = 0 ∧ memory = false then
        (if rowBank = columnBank then (1 : ℂ) else 0) else 0 := by
  simpa only [Matrix.mul_one, Matrix.one_apply] using
    initializedColumns_mul (width := width) (m := m) Reference
      (1 : Matrix (Bank width m Reference)
      (Bank width m Reference) ℂ) control memory rowBank columnBank

private lemma initialized_sandwich_entry {width m : Nat} (Reference : Register)
    (density : Matrix (Bank width m Reference) (Bank width m Reference) ℂ)
    (control columnControl : Fin 2) (memory columnMemory : Bool)
    (rowBank columnBank : Bank width m Reference) :
    (initializedColumns width m Reference * density *
        (initializedColumns width m Reference).conjTranspose)
      ((joint width m Reference).symm (control, (memory, rowBank)))
      ((joint width m Reference).symm (columnControl, (columnMemory, columnBank))) =
      if control = 0 ∧ memory = false then
        (if columnControl = 0 ∧ columnMemory = false then density rowBank columnBank else 0)
      else 0 := by
  exact sandwich_entry_from_factors
    (Index := ((Recovery.Layout.terminal width m).register.prod Reference).Index)
    (Basis := Bank width m Reference)
    (initializedColumns width m Reference) density
    ((joint width m Reference).symm (control, (memory, rowBank)))
    ((joint width m Reference).symm (columnControl, (columnMemory, columnBank)))
    rowBank columnBank (control = 0 ∧ memory = false)
    (columnControl = 0 ∧ columnMemory = false)
    (fun middle : Bank width m Reference =>
      initializedColumns_mul (width := width) (m := m) Reference
      density control memory rowBank middle)
    (fun middle : Bank width m Reference =>
      initializedColumns_entry (width := width) (m := m) Reference
      columnControl columnMemory columnBank middle)


variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)

variable {Reference : Register} {History : Type} [Fintype History]

/-- The bank density is extracted from the actual positive reset output at this complete Store. -/
def actualBankDensity
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Recovery.Layout.terminal p.size m)) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  (storeDensity ((newReset E fieldTail m seed).execute environment Reference state)
    stored).submatrix
    (initializedBasis p.size m Reference) (initializedBasis p.size m Reference)

/-- Positivity is inherited from the same actual Store fiber, including zero-mass fibers. -/
lemma actualBankDensity_positive
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Recovery.Layout.terminal p.size m)) :
    (actualBankDensity (environment := environment) E fieldTail m seed state stored).PosSemidef :=
  ((((newReset E fieldTail m seed).execute environment Reference state).filterClassical
    (fun record => record.1 = stored)).quantumMarginal.positive).submatrix
      (initializedBasis p.size m Reference)

/-- The complete legal-path CP sum extracted from the same actual reset output. -/
private def resetTraceDensity (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Recovery.Layout.terminal p.size m)) :
    HilbertOperator ((Recovery.Layout.terminal p.size m).register.prod Reference) :=
  ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m (2 * m) id path original final then
            initializedColumns p.size m Reference *
              (bankWord (environment := environment) (m := m) E r points Reference path *
                actualBankDensity (environment := environment) (Reference := Reference) (History
                  := History)
                  E fieldTail m seed state original *
                (bankWord (environment := environment) (m := m) E r points Reference
                  path).conjTranspose) *
              (initializedColumns p.size m Reference).conjTranspose
          else 0

private lemma actual_store_seeded
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    BasisSeeded.Holds (newResetLabel E fieldTail m seed)
      ((newReset E fieldTail m seed).execute environment Reference state) := by
  apply BasisSeeded.of_entries (newResetLabel E fieldTail m seed)
    ((newReset E fieldTail m seed).execute environment Reference state)
    (fun stored left right =>
      ∑ history : ClassicalOracleModel.empty.HiddenState ×
          (History × (newReset E fieldTail m seed).Path),
        (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
          (stored, history)).matrix left right)
  intro stored left right leftRef rightRef
  change storeDensity ((newReset E fieldTail m seed).execute environment Reference state) stored
    (left, leftRef) (right, rightRef) = _
  rw [storeDensity_history_sum]
  simp only [Matrix.sum_apply]
  exact newReset_store_factor E fieldTail m seed state stored left right leftRef rightRef

private lemma uninitialized_not_resetLabel (control : Fin 2) (memory : Bool)
    (bank : Bank p.size m Reference) (outside : ¬ (control = 0 ∧ memory = false)) :
    ((joint p.size m Reference).symm (control, (memory, bank))).1 ≠
      newResetLabel E fieldTail m seed := by
  let row := (joint p.size m Reference).symm (control, (memory, bank))
  intro same
  have fullSame : row = (newResetLabel E fieldTail m seed, row.2) := Prod.ext same rfl
  let raw := Recovery.Stage.PointCoordinates.coordinates p.size m Reference
  have atRow := (congrArg raw.toFun
    (joint_symm p.size m Reference control memory bank)).trans
      (Equiv.apply_symm_apply raw (control, (bitBasis memory, bank)))
  have coordinateEq := atRow.symm.trans ((congrArg raw.toFun fullSame).trans
    (newResetLabel_coordinates E fieldTail m seed Reference row.2))
  exact outside ⟨congrArg Prod.fst coordinateEq,
    bitBasis.injective (congrArg (fun value => value.2.1) coordinateEq)⟩

section InitializedStore

attribute [local irreducible] newReset joint

/-- Every actual complete Store fiber has the existing initialized-column form without a premise.
The matrix on the right is extracted from that same output; the arithmetic seed is unchanged. -/
lemma newReset_store_initialized
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity ((newReset E fieldTail m seed).execute environment Reference state) stored =
      initializedColumns p.size m Reference * actualBankDensity (environment := environment) E
        fieldTail m seed state stored *
        (initializedColumns p.size m Reference).conjTranspose := by
  let coordinates := (joint p.size m Reference).trans
    (Equiv.prodAssoc (Fin 2) Bool (Bank p.size m Reference)).symm
  apply seeded_selected_sandwich
    (Local := (Recovery.Layout.terminal p.size m).register.Index) (Frame := Reference.Index)
    (Selector := Fin 2 × Bool) (BankIndex := Bank p.size m Reference)
    (localDecision := (Recovery.Layout.terminal p.size m).register.decEq)
    coordinates (initializedBasis p.size m Reference) (initializedColumns p.size m Reference)
    (storeDensity ((newReset E fieldTail m seed).execute environment Reference state) stored)
    (newResetLabel E fieldTail m seed) (0, false) (fun _ => rfl)
    (actual_store_seeded E fieldTail m seed state stored)
  · intro selector bank outside
    apply uninitialized_not_resetLabel E fieldTail m seed selector.1 selector.2 bank
    intro same
    exact outside (Prod.ext same.1 same.2)
  · intro density rowSelector columnSelector rowBank columnBank
    rcases rowSelector with ⟨control, memory⟩
    rcases columnSelector with ⟨columnControl, columnMemory⟩
    change (initializedColumns p.size m Reference * density *
        (initializedColumns p.size m Reference).conjTranspose)
        ((joint p.size m Reference).symm (control, (memory, rowBank)))
        ((joint p.size m Reference).symm (columnControl, (columnMemory, columnBank))) =
      if (control, memory) = ((0 : Fin 2), false) then
        (if (columnControl, columnMemory) = ((0 : Fin 2), false) then
          density rowBank columnBank else 0) else 0
    simpa only [Prod.mk.injEq] using
      initialized_sandwich_entry (width := p.size) (m := m) Reference density
        control columnControl memory columnMemory rowBank columnBank


end InitializedStore

/-- The existing complete legal-path execution theorem now starts from the actual leading reset.
Its sampler-domain bounds are unchanged; there is no separate initialized-density premise. -/
lemma actual_reset_initialized_store_density (r : Nat)
    (points : Fin (2 * m) → AffinePoint E)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity ((stages (m := m) E r points (Recovery.Layout.order m)).execute environment
      Reference
      ((newReset E fieldTail m seed).execute environment Reference state)) final =
      resetTraceDensity (environment := environment) (Reference := Reference) (History := History)
        E fieldTail m seed r points state final :=
  actual_initialized_store_density (m := m)
    (History := History × (newReset E fieldTail m seed).Path) E r points Reference
    ((newReset E fieldTail m seed).execute environment Reference state)
    (actualBankDensity (environment := environment) (Reference := Reference) (History := History)
      E fieldTail m seed state)
    (newReset_store_initialized E fieldTail m seed state) positive fits final

end

end InitializedOutput
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
