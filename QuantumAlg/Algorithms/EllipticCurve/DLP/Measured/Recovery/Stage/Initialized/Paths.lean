/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Word
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.TwoBlocks

/-!
# Full physical initialized columns and complete legal-path sandwiches

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.InitializedPaths

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open StoredRecursion PathDensity TwoBlocks
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

private def joint (width m : Nat) (Reference : Register) :
    ((Interface width m).register.prod Reference).Index ≃
      Fin 2 × (Bool × Bank width m Reference) :=
  (coordinates width m Reference).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr bitBasis.symm (Equiv.refl _)))

private lemma joint_symm (width m : Nat) (Reference : Register)
    (control : Fin 2) (memory : Bool) (bank : Bank width m Reference) :
    (joint width m Reference).symm (control, (memory, bank)) =
      (coordinates width m Reference).symm (control, (bitBasis memory, bank)) := rfl

private lemma freshBlock_entry {width m : Nat} (Reference : Register)
    (operator : HilbertOperator ((Interface width m).register.prod Reference))
    (rowMemory columnMemory : Bool) (rowBank columnBank : Bank width m Reference) :
    ((freshBlock (width := width) (m := m) Reference operator).submatrix
      (Prod.mk rowMemory) (Prod.mk columnMemory)) rowBank columnBank =
      operator ((joint width m Reference).symm (0, (rowMemory, rowBank)))
        ((joint width m Reference).symm (0, (columnMemory, columnBank))) := by
  rw [joint_symm, joint_symm]
  rfl

def initializedBasis (width m : Nat) (Reference : Register)
    (bank : Bank width m Reference) : ((Interface width m).register.prod Reference).Index :=
  (joint width m Reference).symm (0, (false, bank))

def initializedColumns (width m : Nat) (Reference : Register) :
    Matrix ((Interface width m).register.prod Reference).Index (Bank width m Reference) ℂ :=
  fun row column => if row = initializedBasis width m Reference column then 1 else 0

private def pathOperator {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m) :
    Matrix ((Interface p.size m).register.prod Reference).Index
      ((Interface p.size m).register.prod Reference).Index ℂ :=
  pathProduct (environment := environment) E r points Reference (fun index => (path index).2.2)
    (fun index => (path index).1) (fun index => (path index).2.1) (Recovery.Layout.order m)

def bankWord {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  ∑ secondWord ∈ Finset.range (2 ^ m), ∑ firstWord ∈ Finset.range (2 ^ m),
    (((if secondWord < r then invSqrt r else 0 : ℝ) : ℂ) *
      ((if firstWord < r then invSqrt r else 0 : ℝ) : ℂ)) •
      OrderedBankWord.exponentPair
        (blockAction (environment := environment)
          E points Reference false (fun index => (path index).2.2)
          (fun index => (path index).1) (fun index => (path index).2.1))
        (blockAction (environment := environment)
          E points Reference true (fun index => (path index).2.2)
          (fun index => (path index).1) (fun index => (path index).2.1))
        m firstWord secondWord

private lemma mul_initializedColumns {width m : Nat} (Reference : Register)
    (operator : Matrix ((Interface width m).register.prod Reference).Index
      ((Interface width m).register.prod Reference).Index ℂ)
    (row : ((Interface width m).register.prod Reference).Index)
    (bank : Bank width m Reference) :
    (operator * initializedColumns width m Reference) row bank =
      operator row (initializedBasis width m Reference bank) := by
  rw [Matrix.mul_apply]
  simp only [initializedColumns, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']

private lemma initializedColumns_mul {width m : Nat} (Reference : Register)
    (operator : Matrix (Bank width m Reference) (Bank width m Reference) ℂ)
    (control : Fin 2) (memory : Bool) (rowBank columnBank : Bank width m Reference) :
    (initializedColumns width m Reference * operator)
        ((joint width m Reference).symm (control, (memory, rowBank))) columnBank =
      if control = 0 ∧ memory = false then operator rowBank columnBank else 0 := by
  have same (bank : Bank width m Reference) :
      (joint width m Reference).symm (control, (memory, rowBank)) =
          initializedBasis width m Reference bank ↔
        control = 0 ∧ memory = false ∧ rowBank = bank := by
    constructor
    · intro equal
      have coordinates := congrArg (joint width m Reference) equal
      simpa only [initializedBasis, Equiv.apply_symm_apply, Prod.mk.injEq] using coordinates
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  rw [Matrix.mul_apply]
  simp only [initializedColumns, same, ite_mul, one_mul, zero_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq]

attribute [local irreducible] Nat.size stageMatrix pathOperator bankWord

private lemma product_zero_row {A I : Type} [Fintype A] [DecidableEq A]
    (product : List I → Matrix A A ℂ) (action : I → Matrix A A ℂ)
    (empty : product [] = 1)
    (step : ∀ index tail, product (index :: tail) = product tail * action index)
    (row : A) (zero : ∀ index column, action index row column = 0)
    (indices : List I) : indices ≠ [] → ∀ column, product indices row column = 0 := by
  induction indices with
  | nil => intro nonempty; exact False.elim (nonempty rfl)
  | cons index tail ih =>
      intro _ column
      cases tail with
      | nil =>
          rw [step, empty, Matrix.one_mul]
          exact zero index column
      | cons next rest =>
          rw [step, Matrix.mul_apply]
          apply Finset.sum_eq_zero
          intro middle _
          rw [ih (List.cons_ne_nil next rest) middle, zero_mul]

private lemma columns_intertwine_of_entries {width m : Nat} (Reference : Register)
    (operator : HilbertOperator ((Interface width m).register.prod Reference))
    (word : Matrix (Bank width m Reference) (Bank width m Reference) ℂ)
    (entries : ∀ control memory rowBank columnBank,
      operator ((joint width m Reference).symm (control, (memory, rowBank)))
          (initializedBasis width m Reference columnBank) =
        if control = 0 ∧ memory = false then word rowBank columnBank else 0) :
    operator * initializedColumns width m Reference =
      initializedColumns width m Reference * word := by
  ext row columnBank
  obtain ⟨⟨control, memory, rowBank⟩, rfl⟩ := (joint width m Reference).symm.surjective row
  rw [mul_initializedColumns, initializedColumns_mul]
  exact entries control memory rowBank columnBank

private lemma matrix_sandwich_intertwine {A B : Type} [Fintype A] [Fintype B]
    (operator : Matrix A A ℂ) (columns : Matrix A B ℂ) (word density : Matrix B B ℂ)
    (intertwine : operator * columns = columns * word) :
    operator * (columns * density * columns.conjTranspose) * operator.conjTranspose =
      columns * (word * density * word.conjTranspose) * columns.conjTranspose := by
  calc
    _ = (operator * columns) * density * (operator * columns).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (columns * word) * density * (columns * word).conjTranspose := by rw [intertwine]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

private lemma conditional_sandwich_sum {Samples Records A B : Type}
    [Fintype Samples] [Fintype Records] [Fintype A] [Fintype B]
    (operators : Samples → Matrix A A ℂ) (columns : Matrix A B ℂ)
    (words : Samples → Matrix B B ℂ) (density : Records → Matrix B B ℂ)
    (valid : Samples → Records → Prop)
    (intertwine : ∀ sample, operators sample * columns = columns * words sample) :
    (∑ sample : Samples, ∑ original : Records,
      if valid sample original then
        operators sample * (columns * density original * columns.conjTranspose) *
          (operators sample).conjTranspose else 0) =
      ∑ sample : Samples, ∑ original : Records,
        if valid sample original then
          columns * (words sample * density original * (words sample).conjTranspose) *
            columns.conjTranspose else 0 := by
  apply Finset.sum_congr rfl
  intro sample _
  apply Finset.sum_congr rfl
  intro original _
  by_cases selected : valid sample original
  · rw [if_pos selected, if_pos selected]
    exact matrix_sandwich_intertwine (operators sample) columns (words sample)
      (density original) (intertwine sample)
  · rw [if_neg selected, if_neg selected]

private lemma nonempty_path_zero_control {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (control : Fin 2) (memory : Bool) (bank : Bank p.size m Reference)
    (nonzero : control ≠ 0) (indices : List (Fin (2 * m))) :
    indices ≠ [] → ∀ column,
      pathProduct (environment := environment) E r points Reference (fun index => (path index).2.2)
        (fun index => (path index).1) (fun index => (path index).2.1) indices
        ((joint p.size m Reference).symm (control, (memory, bank))) column = 0 := by
  exact product_zero_row
    (fun tail => pathProduct (environment := environment) E r points Reference (fun index => (path
      index).2.2)
      (fun index => (path index).1) (fun index => (path index).2.1) tail)
    (fun index => stageMatrix (environment := environment) E r points index Reference (path index).1
      (path index).2.1 (path index).2.2)
    rfl (fun _ _ => rfl)
    ((joint p.size m Reference).symm (control, (memory, bank)))
    (fun index column => by
      rw [joint_symm]
      exact stageMatrix_zero_control E r points index Reference (path index).1
        (path index).2.1 (path index).2.2 control (bitBasis memory) bank column nonzero)
    indices

private lemma initialized_path_zero_control {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (control : Fin 2) (memory : Bool) (rowBank columnBank : Bank p.size m Reference)
    (nonzero : control ≠ 0) :
    pathOperator (environment := environment) E r points Reference path
      ((joint p.size m Reference).symm (control, (memory, rowBank)))
      (initializedBasis p.size m Reference columnBank) = 0 := by
  by_cases empty : Recovery.Layout.order m = []
  · have different :
        (joint p.size m Reference).symm (control, (memory, rowBank)) ≠
          initializedBasis p.size m Reference columnBank := by
      intro same
      have projected := congrArg (fun value => (joint p.size m Reference value).1) same
      apply nonzero
      simpa only [initializedBasis, Equiv.apply_symm_apply] using projected
    simp only [pathOperator, empty, pathProduct, Matrix.one_apply, if_neg different]
  · simpa only [pathOperator] using
      nonempty_path_zero_control E r points Reference path control memory rowBank nonzero
        (Recovery.Layout.order m) empty (initializedBasis p.size m Reference columnBank)

private lemma initialized_false_block {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) :
    (freshBlock (width := p.size) (m := m) Reference
      (pathOperator (environment := environment) E r points Reference path)).submatrix (Prod.mk
        false) (Prod.mk false) =
      bankWord (environment := environment) E r points Reference path := by
  have actual := actual_two_block_words (environment := environment) E r points Reference
    (fun index => (path index).2.2) (fun index => (path index).1)
    (fun index => (path index).2.1) positive fits false
  simpa only [pathOperator, bankWord, and_true] using actual

private lemma initialized_true_block {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) :
    (freshBlock (width := p.size) (m := m) Reference
      (pathOperator (environment := environment) E r points Reference path)).submatrix (Prod.mk
        true) (Prod.mk false) = 0 := by
  have actual := actual_two_block_words (environment := environment) E r points Reference
    (fun index => (path index).2.2) (fun index => (path index).1)
    (fun index => (path index).2.1) positive fits true
  simpa only [pathOperator, Bool.true_eq_false, and_false, if_false,
    Complex.ofReal_zero,
    zero_mul, zero_smul, Finset.sum_const_zero] using actual

private lemma initialized_column_entry {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (control : Fin 2) (memory : Bool) (rowBank columnBank : Bank p.size m Reference) :
    pathOperator (environment := environment) E r points Reference path
        ((joint p.size m Reference).symm (control, (memory, rowBank)))
        (initializedBasis p.size m Reference columnBank) =
      if control = 0 ∧ memory = false then
        bankWord (environment := environment) E r points Reference path rowBank columnBank else 0
          := by
  by_cases zero : control = 0
  · subst control
    cases memory with
    | false =>
        rw [if_pos ⟨rfl, rfl⟩]
        have entry := congrArg (fun matrix : Matrix (Bank p.size m Reference)
            (Bank p.size m Reference) ℂ => matrix rowBank columnBank)
          (initialized_false_block (environment := environment)
            E r points Reference path positive fits)
        exact (freshBlock_entry Reference (pathOperator (environment := environment) E r points
          Reference path)
          false false rowBank columnBank).symm.trans entry
    | true =>
        rw [if_neg (by intro same; cases same.2)]
        have entry := congrArg (fun matrix : Matrix (Bank p.size m Reference)
            (Bank p.size m Reference) ℂ => matrix rowBank columnBank)
          (initialized_true_block (environment := environment)
            E r points Reference path positive fits)
        exact (freshBlock_entry Reference (pathOperator (environment := environment) E r points
          Reference path)
          true false rowBank columnBank).symm.trans entry
  · rw [if_neg (fun same => zero same.1)]
    exact initialized_path_zero_control E r points Reference path control memory rowBank
      columnBank zero

lemma initialized_columns_intertwine {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) :
    pathOperator (environment := environment) E r points Reference path * initializedColumns
      p.size m Reference =
      initializedColumns p.size m Reference * bankWord (environment := environment) E r points
        Reference path := by
  exact columns_intertwine_of_entries Reference (pathOperator (environment := environment) E r
    points Reference path)
    (bankWord (environment := environment) E r points Reference path)
    (initialized_column_entry E r points Reference path positive fits)

lemma initialized_path_sandwich {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (density : Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ) :
    pathOperator (environment := environment) E r points Reference path *
        (initializedColumns p.size m Reference * density *
          (initializedColumns p.size m Reference).conjTranspose) *
        (pathOperator (environment := environment) E r points Reference path).conjTranspose =
      initializedColumns p.size m Reference *
        (bankWord (environment := environment) E r points Reference path * density *
          (bankWord (environment := environment) E r points Reference path).conjTranspose) *
        (initializedColumns p.size m Reference).conjTranspose := by
  exact matrix_sandwich_intertwine (pathOperator (environment := environment) E r points Reference
    path)
    (initializedColumns p.size m Reference) (bankWord (environment := environment) E r points
      Reference path) density
    (initialized_columns_intertwine E r points Reference path positive fits)

private lemma full_traceKraus {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m) :
    traceKraus (environment := environment) E r points Reference (2 * m) id path =
      pathOperator (environment := environment) E r points Reference path := by
  simpa only [pathOperator, Recovery.Layout.order, List.ofFn_id,
    id_eq] using
    traceKraus_of_indexed_path E r points Reference path (2 * m) id

private lemma traceKraus_initialized_intertwine {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) :
    traceKraus (environment := environment) E r points Reference (2 * m) id path *
      initializedColumns p.size m Reference =
      initializedColumns p.size m Reference * bankWord (environment := environment) E r points
        Reference path := by
  have product := full_traceKraus (environment := environment) E r points Reference path
  exact (congrArg (fun operator : HilbertOperator ((Interface p.size m).register.prod Reference) =>
    operator * initializedColumns p.size m Reference) product).trans
    (initialized_columns_intertwine E r points Reference path positive fits)

lemma initialized_trace_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (density : Store (Interface p.size m) →
      Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ)
    (final : Store (Interface p.size m)) :
    traceDensity (environment := environment) E r points Reference (2 * m) id
        (fun original => initializedColumns p.size m Reference * density original *
          (initializedColumns p.size m Reference).conjTranspose) final =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Interface p.size m),
          if traceValid p.size m (2 * m) id path original final then
            initializedColumns p.size m Reference *
              (bankWord (environment := environment) E r points Reference path * density original *
                (bankWord (environment := environment) E r points Reference path).conjTranspose) *
              (initializedColumns p.size m Reference).conjTranspose
          else 0 := by
  unfold traceDensity
  exact conditional_sandwich_sum
    (fun path => traceKraus (environment := environment) E r points Reference (2 * m) id path)
    (initializedColumns p.size m Reference) (fun path => bankWord (environment := environment) E r
      points Reference path)
    density (fun path original => traceValid p.size m (2 * m) id path original final)
    (fun path => traceKraus_initialized_intertwine E r points Reference path positive fits)

end

end PointCoordinates.StageWord.PathWord.InitializedPaths
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
