/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Classical.Arithmetic
public import Mathlib.Data.ZMod.Defs

import QuantumAlg.Init
import all QuantumAlg.Util.Classical.Arithmetic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Executable fixed-width GF(2) row reduction

This quantum-free module gives a finite, ordered row-reduction semantics for
fixed-width binary words.  Samples are functions indexed by `Fin rowCount`, so
their order and multiplicity are retained.  In particular, this module never
converts samples to a `Finset`.

Rows and candidates are `FixedWidth.Word width`.  Logical column zero is the
most significant word bit: logical column `i` reads physical `Nat.testBit`
position `width - 1 - i`.  This is the same coordinate used by the closed
word-bit read primitive.  The reducer visits logical columns in that order,
chooses the first unused row with a set pivot bit, and XORs that pivot into
every other currently set row.  Its trace records the actual search probes,
the selected pivot, or the exhausted no-pivot decision for every column.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace GF2

open scoped BigOperators

/-- The two-element field used for binary dot products. -/
public abbrev F2 := ZMod 2

/-- Ordered samples.  Repeated equal words remain distinct at their indices. -/
abbrev Samples (rowCount width : Nat) := Fin rowCount → Word width

/-- Read one in-range word bit. -/
def testBit {width : Nat} (word : Word width) (column : Fin width) : Bool :=
  word.val.testBit (Fin.rev column).val

/-- The logical GF(2) coordinate is exactly the machine MSB-first word bit. -/
theorem testBit_machine_coordinate {width : Nat} (word : Word width)
    (column : Fin width) :
    testBit word column = word.val.testBit (width - 1 - column.val) :=
  by
    unfold testBit
    rw [Fin.val_rev]
    congr 1
    omega

/-- The physical bit position of a logical column is its finite reversal.

This remains a named bridge rather than a global simp rule so higher-level
logical-coordinate lemmas stay in simp-normal form. -/
theorem testBit_eq_rev {width : Nat} (word : Word width)
    (column : Fin width) :
    testBit word column = word.val.testBit (Fin.rev column).val :=
  rfl

/-- Assemble a word from MSB-first logical coordinates. -/
def wordOfLogicalBits {width : Nat} (bits : Fin width → Bool) : Word width :=
  ⟨Nat.ofBits (bits ∘ Fin.rev), Nat.ofBits_lt_two_pow _⟩

/-- Reading an assembled word recovers the same logical coordinate. -/
@[simp] theorem testBit_wordOfLogicalBits {width : Nat} (bits : Fin width → Bool)
    (column : Fin width) :
    testBit (wordOfLogicalBits bits) column = bits column := by
  unfold testBit wordOfLogicalBits
  rw [Nat.testBit_ofBits_lt (bits ∘ Fin.rev) (Fin.rev column).val
    (Fin.rev column).isLt]
  change bits (Fin.rev (Fin.rev column)) = bits column
  exact congrArg bits (Fin.rev_rev column)

/-- Interpret one Boolean word bit as an element of GF(2). -/
public def bitValue {width : Nat} (word : Word width) (column : Fin width) : F2 :=
  (testBit word column).toNat

/-- Width-preserving word XOR. -/
def rowXor {width : Nat} (left right : Word width) : Word width :=
  ⟨left.val ^^^ right.val, Nat.xor_lt_two_pow left.isLt right.isLt⟩

@[simp] theorem rowXor_val {width : Nat} (left right : Word width) :
    (rowXor left right).val = left.val ^^^ right.val :=
  rfl

@[simp] theorem testBit_rowXor {width : Nat} (left right : Word width)
    (column : Fin width) :
    testBit (rowXor left right) column =
      (testBit left column ^^ testBit right column) := by
  change
    (left.val ^^^ right.val).testBit (Fin.rev column).val =
      (left.val.testBit (Fin.rev column).val ^^
        right.val.testBit (Fin.rev column).val)
  exact Nat.testBit_xor left.val right.val (Fin.rev column).val

/-- One GF(2) dot product, evaluated over all in-range word positions. -/
public def dot {width : Nat} (row candidate : Word width) : F2 :=
  ∑ column : Fin width, bitValue row column * bitValue candidate column

/-- A candidate satisfies every ordered sample equation. -/
def satisfies {rowCount width : Nat} (samples : Samples rowCount width)
    (candidate : Word width) : Prop :=
  ∀ row, dot (samples row) candidate = 0

/-- Executable check for all ordered sample equations. -/
def satisfies? {rowCount width : Nat} (samples : Samples rowCount width)
    (candidate : Word width) : Bool :=
  (List.finRange rowCount).all fun row =>
    decide (dot (samples row) candidate = 0)

/-- The executable check is equivalent to semantic satisfaction. -/
@[simp] theorem satisfies?_eq_true {rowCount width : Nat}
    (samples : Samples rowCount width) (candidate : Word width) :
    satisfies? samples candidate = true ↔ satisfies samples candidate := by
  simp [satisfies?, satisfies]

/-- The finite equation system has a computable decision procedure. -/
instance decidableSatisfies {rowCount width : Nat} (samples : Samples rowCount width)
    (candidate : Word width) : Decidable (satisfies samples candidate) := by
  unfold satisfies
  infer_instance

/-- Boolean XOR is addition after embedding its bits into `ZMod 2`. -/
theorem boolToF2_xor (left right : Bool) :
    ((left ^^ right).toNat : F2) =
      (left.toNat : F2) + (right.toNat : F2) := by
  cases left <;> cases right <;> decide

/-- Boolean conjunction is multiplication after embedding its bits into
`ZMod 2`. -/
theorem boolToF2_and (left right : Bool) :
    ((left && right).toNat : F2) =
      (left.toNat : F2) * (right.toNat : F2) := by
  cases left <;> cases right <;> decide

private theorem logicalParity_fold_toF2 {width : Nat}
    (row candidate : Word width) (columns : List (Fin width)) (parity : Bool) :
    ((columns.foldl
      (fun current column =>
        current ^^ (testBit row column && testBit candidate column))
      parity).toNat : F2) =
      (parity.toNat : F2) +
        (columns.map fun column =>
          bitValue row column * bitValue candidate column).sum := by
  induction columns generalizing parity with
  | nil => simp
  | cons column columns inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, boolToF2_xor, boolToF2_and]
      unfold bitValue
      simp only [List.map_cons, List.sum_cons]
      ring

/-- The ordered machine-style Boolean parity fold is false exactly when the
corresponding GF(2) dot product is zero. -/
theorem logicalParity_eq_false_iff_dot_eq_zero {width : Nat}
    (row candidate : Word width) :
    (List.finRange width).foldl
        (fun parity column =>
          parity ^^ (testBit row column && testBit candidate column))
        false = false ↔
      dot row candidate = 0 := by
  have sumEq :
      ((List.finRange width).map fun column =>
        bitValue row column * bitValue candidate column).sum =
        dot row candidate := by
    unfold dot
    rw [← List.sum_toFinset _ (List.nodup_finRange width)]
    rw [List.toFinset_finRange]
  have parityValue :
      (((List.finRange width).foldl
        (fun parity column =>
          parity ^^ (testBit row column && testBit candidate column))
        false).toNat : F2) = dot row candidate := by
    calc
      (((List.finRange width).foldl
          (fun parity column =>
            parity ^^ (testBit row column && testBit candidate column))
          false).toNat : F2) =
          (false.toNat : F2) +
            ((List.finRange width).map fun column =>
              bitValue row column * bitValue candidate column).sum :=
        logicalParity_fold_toF2 row candidate (List.finRange width) false
      _ = ((List.finRange width).map fun column =>
          bitValue row column * bitValue candidate column).sum := by simp
      _ = dot row candidate := sumEq
  have boolToF2_eq_zero (value : Bool) :
      value = false ↔ (value.toNat : F2) = 0 := by
    cases value <;> decide
  rw [← parityValue]
  exact boolToF2_eq_zero _

/-- XOR is addition in the GF(2) bit representation. -/
theorem bitValue_rowXor {width : Nat} (left right : Word width)
    (column : Fin width) :
    bitValue (rowXor left right) column =
      bitValue left column + bitValue right column := by
  unfold bitValue
  rw [show testBit (rowXor left right) column =
      (testBit left column ^^ testBit right column) from
    testBit_rowXor left right column]
  exact boolToF2_xor _ _

/-- A row XOR distributes through the GF(2) dot product. -/
theorem dot_rowXor {width : Nat} (left right candidate : Word width) :
    dot (rowXor left right) candidate =
      dot left candidate + dot right candidate := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro column _
  rw [bitValue_rowXor, add_mul]

/-- Replace a non-pivot target row by its XOR with a retained pivot row. -/
def rowXorAt {rowCount width : Nat} (samples : Samples rowCount width)
    (pivot target : Fin rowCount) : Samples rowCount width :=
  if target = pivot then samples else
    Function.update samples target (rowXor (samples target) (samples pivot))

/-- One elementary row XOR preserves the complete solution set. -/
theorem satisfies_rowXorAt {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot target : Fin rowCount)
    (candidate : Word width) :
    satisfies (rowXorAt samples pivot target) candidate ↔
      satisfies samples candidate := by
  by_cases same : target = pivot
  · simp [rowXorAt, same]
  constructor
  · intro after row
    by_cases rowTarget : row = target
    · subst row
      have changed :
          dot (rowXor (samples target) (samples pivot)) candidate = 0 := by
        simpa [rowXorAt, same] using after target
      have pivotEquation : dot (samples pivot) candidate = 0 := by
        simpa [rowXorAt, same, Function.update_of_ne (Ne.symm same)] using after pivot
      rw [dot_rowXor, pivotEquation] at changed
      simpa using changed
    · simpa [rowXorAt, same, Function.update_of_ne rowTarget] using after row
  · intro before row
    by_cases rowTarget : row = target
    · subst row
      simp [rowXorAt, same, dot_rowXor, before target, before pivot]
    · simpa [rowXorAt, same, Function.update_of_ne rowTarget] using before row

/-- One target-row decision made while eliminating a fixed pivot column. -/
def eliminateStep {rowCount width : Nat} (pivot : Fin rowCount)
    (column : Fin width) (samples : Samples rowCount width)
    (target : Fin rowCount) : Samples rowCount width :=
  if target = pivot then samples else
    if testBit (samples target) column = true then
      rowXorAt samples pivot target
    else samples

/-- Every target-row decision preserves the solution set. -/
theorem satisfies_eliminateStep {rowCount width : Nat} (pivot : Fin rowCount)
    (column : Fin width) (samples : Samples rowCount width)
    (target : Fin rowCount) (candidate : Word width) :
    satisfies (eliminateStep pivot column samples target) candidate ↔
      satisfies samples candidate := by
  by_cases same : target = pivot
  · simp [eliminateStep, same]
  by_cases active : testBit (samples target) column = true
  · simp only [eliminateStep, if_neg same, if_pos active]
    exact satisfies_rowXorAt samples pivot target candidate
  · simp only [eliminateStep, if_neg same, if_neg active]

/-- The independent update of one target row for a selected pivot column. -/
def eliminateRow {rowCount width : Nat} (pivot : Fin rowCount)
    (column : Fin width) (samples : Samples rowCount width)
    (target : Fin rowCount) : Word width :=
  if target = pivot then samples target else
    if testBit (samples target) column = true then
      rowXor (samples target) (samples pivot)
    else samples target

/-- XOR the pivot row into every other currently set row.

The target-row updates are independent: each reads the retained pivot row and
the target's pre-elimination value. -/
def eliminateRows {rowCount width : Nat} (samples : Samples rowCount width)
    (pivot : Fin rowCount) (column : Fin width) : Samples rowCount width :=
  fun target => eliminateRow pivot column samples target

/-- The selected pivot row is retained by one full elimination. -/
theorem eliminateRows_pivot {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Fin rowCount) (column : Fin width) :
    eliminateRows samples pivot column pivot = samples pivot := by
  simp [eliminateRows, eliminateRow]

/-- Every non-pivot target has a cleared pivot-column bit after elimination. -/
theorem testBit_eliminateRows_other {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Fin rowCount) (column : Fin width)
    (pivotBit : testBit (samples pivot) column = true)
    {target : Fin rowCount} (targetNe : target ≠ pivot) :
    testBit (eliminateRows samples pivot column target) column = false := by
  unfold eliminateRows eliminateRow
  rw [if_neg targetNe]
  by_cases targetBit : testBit (samples target) column = true
  · rw [if_pos targetBit, testBit_rowXor, targetBit, pivotBit]
    rfl
  · rw [if_neg targetBit]
    exact Bool.eq_false_of_not_eq_true targetBit

/-- A zero retained-pivot coefficient preserves another logical column. -/
theorem testBit_eliminateRows_preserves {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Fin rowCount) (column preserved : Fin width)
    (pivotZero : testBit (samples pivot) preserved = false) (target : Fin rowCount) :
    testBit (eliminateRows samples pivot column target) preserved =
      testBit (samples target) preserved := by
  unfold eliminateRows eliminateRow
  by_cases targetPivot : target = pivot
  · subst target
    rw [if_pos rfl]
  · rw [if_neg targetPivot]
    by_cases targetBit : testBit (samples target) column = true
    · rw [if_pos targetBit, testBit_rowXor, pivotZero, Bool.xor_false]
    · rw [if_neg targetBit]

/-- A finite sequence of elementary row XORs preserves every solution. -/
theorem satisfies_foldl_eliminate {rowCount width : Nat}
    (targets : List (Fin rowCount)) (pivot : Fin rowCount) (column : Fin width)
    (samples : Samples rowCount width) (candidate : Word width) :
    satisfies (targets.foldl (eliminateStep pivot column) samples) candidate ↔
      satisfies samples candidate := by
  induction targets generalizing samples with
  | nil => rfl
  | cons target targets inductionHypothesis =>
      change
        satisfies
            (targets.foldl (eliminateStep pivot column)
              (eliminateStep pivot column samples target)) candidate ↔
          satisfies samples candidate
      exact
        (inductionHypothesis (eliminateStep pivot column samples target)).trans
          (satisfies_eliminateStep pivot column samples target candidate)

/-- One full pivot-column elimination preserves the solution set. -/
theorem satisfies_eliminateRows {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Fin rowCount)
    (column : Fin width) (candidate : Word width) :
    satisfies (eliminateRows samples pivot column) candidate ↔
      satisfies samples candidate := by
  constructor
  · intro after row
    by_cases rowPivot : row = pivot
    · subst row
      have afterPivot := after pivot
      change
        dot
            (if pivot = pivot then samples pivot else
              if (samples pivot).val.testBit (Fin.rev column).val = true then
                rowXor (samples pivot) (samples pivot)
              else samples pivot)
            candidate = 0 at afterPivot
      rw [if_pos rfl] at afterPivot
      exact afterPivot
    · by_cases active : testBit (samples row) column = true
      · have changed :
          dot (rowXor (samples row) (samples pivot)) candidate = 0 := by
          change (samples row).val.testBit (Fin.rev column).val = true at active
          have afterRow := after row
          change
            dot
                (if row = pivot then samples row else
                  if (samples row).val.testBit (Fin.rev column).val = true then
                    rowXor (samples row) (samples pivot)
                  else samples row)
                candidate = 0 at afterRow
          rw [if_neg rowPivot, if_pos active] at afterRow
          exact afterRow
        have pivotEquation : dot (samples pivot) candidate = 0 := by
          have afterPivot := after pivot
          change
            dot
                (if pivot = pivot then samples pivot else
                  if (samples pivot).val.testBit (Fin.rev column).val = true then
                    rowXor (samples pivot) (samples pivot)
                  else samples pivot)
                candidate = 0 at afterPivot
          rw [if_pos rfl] at afterPivot
          exact afterPivot
        rw [dot_rowXor, pivotEquation] at changed
        simpa using changed
      · change (samples row).val.testBit (Fin.rev column).val ≠ true at active
        have afterRow := after row
        change
          dot
              (if row = pivot then samples row else
                if (samples row).val.testBit (Fin.rev column).val = true then
                  rowXor (samples row) (samples pivot)
                else samples row)
              candidate = 0 at afterRow
        rw [if_neg rowPivot, if_neg active] at afterRow
        exact afterRow
  · intro before row
    by_cases rowPivot : row = pivot
    · subst row
      change
        dot
            (if pivot = pivot then samples pivot else
              if (samples pivot).val.testBit (Fin.rev column).val = true then
                rowXor (samples pivot) (samples pivot)
              else samples pivot)
            candidate = 0
      rw [if_pos rfl]
      exact before pivot
    · by_cases active : testBit (samples row) column = true
      · change (samples row).val.testBit (Fin.rev column).val = true at active
        change
          dot
              (if row = pivot then samples row else
                if (samples row).val.testBit (Fin.rev column).val = true then
                  rowXor (samples row) (samples pivot)
                else samples row)
              candidate = 0
        rw [if_neg rowPivot, if_pos active]
        calc
          dot (rowXor (samples row) (samples pivot)) candidate =
              dot (samples row) candidate + dot (samples pivot) candidate :=
            dot_rowXor _ _ _
          _ = 0 + 0 := by rw [before row, before pivot]
          _ = 0 := zero_add 0
      · change (samples row).val.testBit (Fin.rev column).val ≠ true at active
        change
          dot
              (if row = pivot then samples row else
                if (samples row).val.testBit (Fin.rev column).val = true then
                  rowXor (samples row) (samples pivot)
                else samples row)
              candidate = 0
        rw [if_neg rowPivot, if_neg active]
        exact before row

/-- A chosen pivot position. -/
structure Pivot (rowCount width : Nat) where
  /-- The distinct source row chosen for this pivot. -/
  row : Fin rowCount
  /-- The column processed when the row was chosen. -/
  column : Fin width
deriving Repr, DecidableEq

attribute [nolint unusedArguments] instReprPivot.repr

/-- The ordered row indices occurring in a pivot record. -/
def pivotRows {rowCount width : Nat} (pivots : List (Pivot rowCount width)) :
    List (Fin rowCount) :=
  pivots.map Pivot.row

/-- The logical columns occurring in a pivot record. -/
def pivotColumns {rowCount width : Nat} (pivots : List (Pivot rowCount width)) :
    List (Fin width) :=
  pivots.map Pivot.column

/-- The data-dependent event emitted for one processed column. -/
inductive TraceEvent (rowCount width : Nat) where
  /-- A row was probed and rejected before the first pivot. -/
  | rejected (row : Fin rowCount) (column : Fin width)
  /-- The first unused row with a set bit became the pivot. -/
  | pivot (row : Fin rowCount) (column : Fin width)
  /-- No unused row had a set bit in this column. -/
  | noPivot (column : Fin width)
deriving Repr, DecidableEq

/-- Mutable semantic state for the ordered column pass. -/
structure State (rowCount width : Nat) where
  /-- The current row system. -/
  rows : Samples rowCount width
  /-- Rows already selected as pivots. -/
  used : Finset (Fin rowCount)
  /-- Pivot coordinates in discovery order. -/
  pivots : List (Pivot rowCount width)
  /-- The executable pivot count. -/
  pivotCount : Nat
  /-- Actual pivot/no-pivot decisions processed so far. -/
  trace : List (TraceEvent rowCount width)

/-- Initial state: unchanged ordered samples, no pivots, and no events. -/
def initial {rowCount width : Nat} (samples : Samples rowCount width) :
    State rowCount width where
  rows := samples
  used := ∅
  pivots := []
  pivotCount := 0
  trace := []

/-- The Boolean predicate used by the ordered first-pivot search. -/
def pivotPredicate {rowCount width : Nat} (state : State rowCount width)
    (column : Fin width) (row : Fin rowCount) : Bool :=
  decide (row ∉ state.used ∧ testBit (state.rows row) column = true)

/-- The first unused row with a set entry in the requested column. -/
def firstUnusedPivot {rowCount width : Nat} (state : State rowCount width)
    (column : Fin width) : Option (Fin rowCount) :=
  Fin.find? (pivotPredicate state column)

/-- A returned pivot is unused and has the requested set bit. -/
theorem firstUnusedPivot_spec {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width} {pivot : Fin rowCount}
    (choice : firstUnusedPivot state column = some pivot) :
    pivot ∉ state.used ∧ testBit (state.rows pivot) column = true := by
  have membership : pivot ∈ firstUnusedPivot state column := by
    simp [choice]
  have rawMembership : pivot ∈ Fin.find? (pivotPredicate state column) := by
    simpa [firstUnusedPivot] using membership
  have predicate : pivotPredicate state column pivot :=
    (Fin.mem_find?_iff.mp rawMembership).1
  simpa [pivotPredicate] using predicate

/-- No lower row index satisfies the pivot predicate before a returned pivot. -/
theorem firstUnusedPivot_is_first {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width} {pivot row : Fin rowCount}
    (choice : firstUnusedPivot state column = some pivot) (lower : row < pivot) :
    ¬ (row ∉ state.used ∧ testBit (state.rows row) column = true) := by
  have membership : pivot ∈ firstUnusedPivot state column := by
    simp [choice]
  have rawMembership : pivot ∈ Fin.find? (pivotPredicate state column) := by
    simpa [firstUnusedPivot] using membership
  have minimal : ¬ pivotPredicate state column row :=
    (Fin.mem_find?_iff.mp rawMembership).2 row lower
  simpa [pivotPredicate] using minimal

/-- The complete ordered row-search trace for one column.

Every listed rejection is a genuine probe strictly before the selected first
pivot.  If no pivot exists, every row is probed and rejected before the final
`noPivot` event. -/
def searchTrace {rowCount width : Nat} (state : State rowCount width)
    (column : Fin width) : List (TraceEvent rowCount width) :=
  match firstUnusedPivot state column with
  | none =>
      (List.finRange rowCount).map (fun row => .rejected row column) ++
        [.noPivot column]
  | some pivot =>
      ((List.finRange rowCount).filter fun row => decide (row < pivot)).map
        (fun row => .rejected row column) ++
          [.pivot pivot column]

/-- An exhausted search means that every row probe fails the pivot predicate. -/
theorem firstUnusedPivot_none_rejects {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width}
    (choice : firstUnusedPivot state column = none) (row : Fin rowCount) :
    ¬ (row ∉ state.used ∧ testBit (state.rows row) column = true) := by
  have rawChoice : Fin.find? (pivotPredicate state column) = none := by
    simpa [firstUnusedPivot] using choice
  have failed : pivotPredicate state column row = false :=
    Fin.eq_false_of_find?_eq_none rawChoice row
  simpa [pivotPredicate] using failed

/-- An exhausted pivot search gives zero in that column for every unused row. -/
theorem firstUnusedPivot_none_bit_eq_false {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width}
    (choice : firstUnusedPivot state column = none) {row : Fin rowCount}
    (unused : row ∉ state.used) :
    testBit (state.rows row) column = false := by
  by_cases bit : testBit (state.rows row) column = true
  · exact (firstUnusedPivot_none_rejects choice row ⟨unused, bit⟩).elim
  · exact Bool.eq_false_of_not_eq_true bit

/-- The no-pivot branch exposes every ordered row rejection explicitly. -/
theorem searchTrace_none {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width}
    (choice : firstUnusedPivot state column = none) :
    searchTrace state column =
      (List.finRange rowCount).map (fun row => .rejected row column) ++
        [.noPivot column] := by
  simp [searchTrace, choice]

/-- The pivot branch exposes precisely the probes preceding its first pivot. -/
theorem searchTrace_some {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width} {pivot : Fin rowCount}
    (choice : firstUnusedPivot state column = some pivot) :
    searchTrace state column =
      ((List.finRange rowCount).filter fun row => decide (row < pivot)).map
        (fun row => .rejected row column) ++
          [.pivot pivot column] := by
  simp [searchTrace, choice]

/-- Every rejection retained in a search trace is a genuinely failed probe. -/
theorem searchTrace_rejected_sound {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width} {row : Fin rowCount}
    (event : TraceEvent.rejected row column ∈ searchTrace state column) :
    ¬ (row ∉ state.used ∧ testBit (state.rows row) column = true) := by
  cases choice : firstUnusedPivot state column with
  | none => exact firstUnusedPivot_none_rejects choice row
  | some pivot =>
      have lower : row < pivot := by
        simpa [searchTrace, choice] using event
      exact firstUnusedPivot_is_first choice lower

/-- Process one column: record no pivot, or eliminate with the first unused one. -/
def stepColumn {rowCount width : Nat} (column : Fin width)
    (state : State rowCount width) : State rowCount width :=
  match firstUnusedPivot state column with
  | none =>
      { state with trace := state.trace ++ searchTrace state column }
  | some pivot =>
      { state with
        rows := eliminateRows state.rows pivot column
        used := insert pivot state.used
        pivots := state.pivots ++ [⟨pivot, column⟩]
        pivotCount := state.pivotCount + 1
        trace := state.trace ++ searchTrace state column }

/-- Each processed column preserves the complete solution set. -/
theorem satisfies_stepColumn {rowCount width : Nat} (column : Fin width)
    (state : State rowCount width) (candidate : Word width) :
    satisfies (stepColumn column state).rows candidate ↔
      satisfies state.rows candidate := by
  cases choice : firstUnusedPivot state column with
  | none => simp [stepColumn, choice]
  | some pivot =>
      simpa [stepColumn, choice] using
        (satisfies_eliminateRows state.rows pivot column candidate)

/-- Run a supplied ordered column list. -/
def runColumns {rowCount width : Nat} :
    List (Fin width) → State rowCount width → State rowCount width
  | [], state => state
  | column :: columns, state => runColumns columns (stepColumn column state)

/-- The pre-state path of every actual column decision, with no padded states. -/
def pathColumns {rowCount width : Nat} :
    List (Fin width) → State rowCount width → List (State rowCount width)
  | [], _state => []
  | column :: columns, state =>
      state :: pathColumns columns (stepColumn column state)

/-- The full low-to-high column execution path for ordered samples. -/
def path {rowCount width : Nat} (samples : Samples rowCount width) :
    List (State rowCount width) :=
  pathColumns (List.finRange width) (initial samples)

/-- The final state after processing every in-range column. -/
def finalState {rowCount width : Nat} (samples : Samples rowCount width) :
    State rowCount width :=
  runColumns (List.finRange width) (initial samples)

/-- Public reduction output, without the internal used-row set. -/
structure Result (rowCount width : Nat) where
  /-- The Gauss-Jordan-reduced row system. -/
  reduced : Samples rowCount width
  /-- Pivot coordinates in processing order. -/
  pivots : List (Pivot rowCount width)
  /-- The executable pivot count. -/
  pivotCount : Nat
  /-- Actual pivot/no-pivot events. -/
  trace : List (TraceEvent rowCount width)

/-- Execute the fixed-domain low-to-high GF(2) reduction. -/
def reduce {rowCount width : Nat} (samples : Samples rowCount width) :
    Result rowCount width :=
  let final := finalState samples
  { reduced := final.rows
    pivots := final.pivots
    pivotCount := final.pivotCount
    trace := final.trace }

/-- Look up the recorded pivot for one logical column. -/
def pivotForColumn? {rowCount width : Nat} (result : Result rowCount width)
    (column : Fin width) : Option (Pivot rowCount width) :=
  result.pivots.find? fun pivot => decide (pivot.column = column)

/-- Whether a logical column occurs in the recorded pivot coordinates. -/
def isPivotColumn {rowCount width : Nat} (result : Result rowCount width)
    (column : Fin width) : Bool :=
  (pivotForColumn? result column).isSome

/-- The MSB-first word mask of recorded logical pivot columns. -/
def pivotColumnMask {rowCount width : Nat} (result : Result rowCount width) :
    Word width :=
  wordOfLogicalBits (isPivotColumn result)

/-- A pivot-column mask reads the pivot decision at every logical
coordinate. -/
theorem testBit_pivotColumnMask {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    testBit (pivotColumnMask result) column = isPivotColumn result column := by
  simp [pivotColumnMask]

/-- The logical columns not represented by a recorded pivot, in column order. -/
def freeColumns {rowCount width : Nat} (result : Result rowCount width) :
    List (Fin width) :=
  (List.finRange width).filter fun column => !isPivotColumn result column

/-- The MSB-first word mask of logical columns with no recorded pivot. -/
def freeColumnMask {rowCount width : Nat} (result : Result rowCount width) :
    Word width :=
  wordOfLogicalBits fun column =>
    decide (pivotForColumn? result column = none)

/-- A free-column mask reads the failed-pivot-lookup decision at every
logical coordinate. -/
theorem testBit_freeColumnMask {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    testBit (freeColumnMask result) column =
      decide (pivotForColumn? result column = none) := by
  simp [freeColumnMask]

/-- Every free-column mask bit is the Boolean complement of the corresponding
pivot-column decision. -/
theorem testBit_freeColumnMask_eq_not_isPivotColumn {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    testBit (freeColumnMask result) column = !isPivotColumn result column := by
  cases lookup : pivotForColumn? result column <;>
    simp [testBit_freeColumnMask, isPivotColumn, lookup]

/-- The canonical free-column mask is the logical word formed by complementing
the pivot-column decisions coordinatewise. -/
theorem freeColumnMask_eq_wordOfLogicalBits_not_isPivotColumn
    {rowCount width : Nat} (result : Result rowCount width) :
    freeColumnMask result =
      wordOfLogicalBits (fun column => !isPivotColumn result column) := by
  apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
  intro physical
  have logical :
      testBit (freeColumnMask result) (Fin.rev physical) =
        testBit
          (wordOfLogicalBits
            (fun column : Fin width => !isPivotColumn result column))
          (Fin.rev physical) := by
    rw [testBit_freeColumnMask_eq_not_isPivotColumn]
    simp
  have revRev : (Fin.rev (Fin.rev physical)).val = physical.val :=
    congrArg Fin.val (Fin.rev_rev physical)
  rw [← revRev]
  exact logical

/-- Free- and pivot-column masks are Boolean complements at every logical
coordinate. -/
theorem testBit_freeColumnMask_eq_not_testBit_pivotColumnMask
    {rowCount width : Nat} (result : Result rowCount width)
    (column : Fin width) :
    testBit (freeColumnMask result) column =
      !testBit (pivotColumnMask result) column := by
  rw [testBit_freeColumnMask_eq_not_isPivotColumn, testBit_pivotColumnMask]

/-- The free-column mask is the logical-bit complement of the canonical
pivot-column mask. -/
theorem freeColumnMask_eq_wordOfLogicalBits_not_testBit_pivotColumnMask
    {rowCount width : Nat} (result : Result rowCount width) :
    freeColumnMask result =
      wordOfLogicalBits
        (fun column => !testBit (pivotColumnMask result) column) := by
  calc
    freeColumnMask result =
        wordOfLogicalBits (fun column => !isPivotColumn result column) :=
      freeColumnMask_eq_wordOfLogicalBits_not_isPivotColumn result
    _ = wordOfLogicalBits
          (fun column => !testBit (pivotColumnMask result) column) := by
      congr 1
      funext column
      rw [testBit_pivotColumnMask]

/-- Select the single free column exactly when the pivot record leaves one. -/
def soleFreeColumn? {rowCount width : Nat} (result : Result rowCount width) :
    Option (Fin width) :=
  match freeColumns result with
  | [column] => some column
  | _ => none

/-- The MSB-first coordinate of the one-free-variable back-substitution word.

At the free column it is one.  At a pivot column it reads the corresponding
reduced pivot-row coefficient; a malformed or additional free column is given
zero so this total executable helper never fabricates an out-of-domain bit. -/
def backSubstituteBit {rowCount width : Nat} (result : Result rowCount width)
    (free column : Fin width) : Bool :=
  if column = free then true else
    match pivotForColumn? result column with
    | none => false
    | some pivot => testBit (result.reduced pivot.row) free

/-- Build the one-free-variable candidate directly from reduced rows and pivots. -/
def backSubstitute {rowCount width : Nat} (result : Result rowCount width)
    (free : Fin width) : Word width :=
  wordOfLogicalBits (backSubstituteBit result free)

/-- The back-substitution word has exactly its declared logical coordinates. -/
@[simp] theorem testBit_backSubstitute {rowCount width : Nat}
    (result : Result rowCount width) (free column : Fin width) :
    testBit (backSubstitute result free) column =
      backSubstituteBit result free column := by
  simp [backSubstitute]

/-- The chosen free coordinate of a back-substitution word is one. -/
theorem testBit_backSubstitute_free {rowCount width : Nat}
    (result : Result rowCount width) (free : Fin width) :
    testBit (backSubstitute result free) free = true := by
  rw [testBit_backSubstitute]
  simp [backSubstituteBit]

/-- Polynomial recovery from a reduction result.

This does not enumerate words.  It accepts only a one-free-column projection
which is nonzero and verifies against the original ordered equations; the
finite exhaustive `uniqueNonzero?` below remains a specification oracle. -/
def recover? {rowCount width : Nat} (samples : Samples rowCount width) :
    Option (Word width) :=
  let result := reduce samples
  match soleFreeColumn? result with
  | none => none
  | some free =>
      let candidate := backSubstitute result free
      if candidate = 0 then none else
        if satisfies? samples candidate = true then some candidate else none

/-- Every successful polynomial recovery is nonzero and satisfies the originals. -/
theorem recover?_sound {rowCount width : Nat}
    (samples : Samples rowCount width) {candidate : Word width}
    (output : recover? samples = some candidate) :
    candidate ≠ 0 ∧ satisfies samples candidate := by
  cases freeChoice : soleFreeColumn? (reduce samples) with
  | none =>
      simp [recover?, freeChoice] at output
  | some free =>
      let projected := backSubstitute (reduce samples) free
      by_cases zero : projected = 0
      · simp [recover?, freeChoice, projected, zero] at output
      · cases checked : satisfies? samples projected with
        | false =>
            simp [recover?, freeChoice, projected, zero, checked] at output
        | true =>
            have sat : satisfies samples projected :=
              (satisfies?_eq_true samples projected).mp checked
            have same : candidate = projected := by
              simpa [recover?, freeChoice, projected, zero, checked] using output.symm
            subst candidate
            exact ⟨zero, sat⟩

/-- A run over any ordered column list preserves the complete solution set. -/
theorem satisfies_runColumns {rowCount width : Nat}
    (columns : List (Fin width)) (state : State rowCount width)
    (candidate : Word width) :
    satisfies (runColumns columns state).rows candidate ↔
      satisfies state.rows candidate := by
  induction columns generalizing state with
  | nil => rfl
  | cons column columns inductionHypothesis =>
      change
        satisfies (runColumns columns (stepColumn column state)).rows candidate ↔
          satisfies state.rows candidate
      exact
        (inductionHypothesis (stepColumn column state)).trans
          (satisfies_stepColumn column state candidate)

/-- The reduced equations have exactly the same kernel as the original samples. -/
theorem reduce_kernel_equiv {rowCount width : Nat}
    (samples : Samples rowCount width) (candidate : Word width) :
    satisfies samples candidate ↔ satisfies (reduce samples).reduced candidate := by
  simpa [reduce, finalState, initial] using
    (satisfies_runColumns (List.finRange width) (initial samples) candidate).symm

/-- One column step preserves the pivotCount/pivot-list counting invariant. -/
theorem stepColumn_pivotCount_eq_pivots_length {rowCount width : Nat}
    (column : Fin width) (state : State rowCount width)
    (invariant : state.pivotCount = state.pivots.length) :
    (stepColumn column state).pivotCount = (stepColumn column state).pivots.length := by
  cases choice : firstUnusedPivot state column with
  | none => simp [stepColumn, choice, invariant]
  | some pivot => simp [stepColumn, choice, invariant]

/-- The pivot-count invariant is preserved over any ordered column list. -/
theorem runColumns_pivotCount_eq_pivots_length {rowCount width : Nat}
    (columns : List (Fin width)) (state : State rowCount width)
    (invariant : state.pivotCount = state.pivots.length) :
    (runColumns columns state).pivotCount =
      (runColumns columns state).pivots.length := by
  induction columns generalizing state with
  | nil => exact invariant
  | cons column columns inductionHypothesis =>
      change
        (runColumns columns (stepColumn column state)).pivotCount =
          (runColumns columns (stepColumn column state)).pivots.length
      exact inductionHypothesis (stepColumn column state)
        (stepColumn_pivotCount_eq_pivots_length column state invariant)

/-- The initial pivotCount is the length of its empty pivot list. -/
@[simp] theorem initial_pivotCount_eq_pivots_length {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (initial samples).pivotCount = (initial samples).pivots.length :=
  rfl

/-- The executable final pivotCount is exactly the number of recorded pivots. -/
theorem finalState_pivotCount_eq_pivots_length {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalState samples).pivotCount = (finalState samples).pivots.length := by
  exact runColumns_pivotCount_eq_pivots_length (List.finRange width) (initial samples)
    (initial_pivotCount_eq_pivots_length samples)

/-- The public pivotCount is exactly the length of the public pivot list. -/
theorem reduce_pivotCount_eq_pivots_length {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (reduce samples).pivotCount = (reduce samples).pivots.length := by
  simpa [reduce] using finalState_pivotCount_eq_pivots_length samples

/-- One column can increase the executable pivotCount by at most one. -/
theorem stepColumn_pivotCount_le_succ {rowCount width : Nat}
    (column : Fin width) (state : State rowCount width) :
    (stepColumn column state).pivotCount ≤ state.pivotCount + 1 := by
  cases choice : firstUnusedPivot state column with
  | none => simp [stepColumn, choice]
  | some pivot => simp [stepColumn, choice]

/-- Processing `k` supplied columns increases pivotCount by at most `k`. -/
theorem runColumns_pivotCount_le_add_length {rowCount width : Nat}
    (columns : List (Fin width)) (state : State rowCount width) :
    (runColumns columns state).pivotCount ≤ state.pivotCount + columns.length := by
  induction columns generalizing state with
  | nil => simp [runColumns]
  | cons column columns inductionHypothesis =>
      calc
        (runColumns (column :: columns) state).pivotCount =
            (runColumns columns (stepColumn column state)).pivotCount := rfl
        _ ≤ (stepColumn column state).pivotCount + columns.length :=
          inductionHypothesis (stepColumn column state)
        _ ≤ (state.pivotCount + 1) + columns.length :=
          Nat.add_le_add_right (stepColumn_pivotCount_le_succ column state) _
        _ = state.pivotCount + (column :: columns).length := by
          rw [List.length_cons, Nat.add_assoc, Nat.add_comm 1 columns.length]

/-- The final executable pivotCount is bounded by the number of processed columns. -/
theorem finalState_pivotCount_le_width {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalState samples).pivotCount ≤ width := by
  simpa [finalState, initial] using
    (runColumns_pivotCount_le_add_length (List.finRange width) (initial samples))

/-- The public executable pivotCount is bounded by the word width. -/
theorem reduce_pivotCount_le_width {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (reduce samples).pivotCount ≤ width := by
  simpa [reduce] using finalState_pivotCount_le_width samples

/-- A returned first pivot is not already in the used-row set. -/
theorem firstUnusedPivot_not_mem_used {rowCount width : Nat}
    {state : State rowCount width} {column : Fin width} {pivot : Fin rowCount}
    (choice : firstUnusedPivot state column = some pivot) :
    pivot ∉ state.used :=
  (firstUnusedPivot_spec choice).1

/-- One column step preserves the pivotCount/used-row-cardinality invariant. -/
theorem stepColumn_pivotCount_eq_used_card {rowCount width : Nat}
    (column : Fin width) (state : State rowCount width)
    (invariant : state.pivotCount = state.used.card) :
    (stepColumn column state).pivotCount = (stepColumn column state).used.card := by
  cases choice : firstUnusedPivot state column with
  | none => simp [stepColumn, choice, invariant]
  | some pivot =>
      have unused : pivot ∉ state.used := firstUnusedPivot_not_mem_used choice
      simp only [stepColumn, choice]
      rw [Finset.card_insert_of_notMem unused]
      rw [invariant]

/-- The pivotCount/used-row-cardinality invariant survives any ordered column list. -/
theorem runColumns_pivotCount_eq_used_card {rowCount width : Nat}
    (columns : List (Fin width)) (state : State rowCount width)
    (invariant : state.pivotCount = state.used.card) :
    (runColumns columns state).pivotCount = (runColumns columns state).used.card := by
  induction columns generalizing state with
  | nil => exact invariant
  | cons column columns inductionHypothesis =>
      change
        (runColumns columns (stepColumn column state)).pivotCount =
          (runColumns columns (stepColumn column state)).used.card
      exact inductionHypothesis (stepColumn column state)
        (stepColumn_pivotCount_eq_used_card column state invariant)

/-- A column step keeps `used` equal to the distinct row indices in its pivots. -/
theorem stepColumn_used_eq_pivotRows_toFinset {rowCount width : Nat}
    (column : Fin width) (state : State rowCount width)
    (invariant : state.used = (pivotRows state.pivots).toFinset) :
    (stepColumn column state).used =
      (pivotRows (stepColumn column state).pivots).toFinset := by
  cases choice : firstUnusedPivot state column with
  | none => simp [stepColumn, choice, invariant]
  | some pivot => simp [stepColumn, choice, pivotRows, invariant]

/-- The used-row/pivot-row correspondence survives an ordered column pass. -/
theorem runColumns_used_eq_pivotRows_toFinset {rowCount width : Nat}
    (columns : List (Fin width)) (state : State rowCount width)
    (invariant : state.used = (pivotRows state.pivots).toFinset) :
    (runColumns columns state).used =
      (pivotRows (runColumns columns state).pivots).toFinset := by
  induction columns generalizing state with
  | nil => exact invariant
  | cons column columns inductionHypothesis =>
      change
        (runColumns columns (stepColumn column state)).used =
          (pivotRows (runColumns columns (stepColumn column state)).pivots).toFinset
      exact inductionHypothesis (stepColumn column state)
        (stepColumn_used_eq_pivotRows_toFinset column state invariant)

/-- The initial state records no used or pivot row. -/
@[simp] theorem initial_used_eq_pivotRows_toFinset {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (initial samples).used = (pivotRows (initial samples).pivots).toFinset := by
  simp [initial, pivotRows]

/-- The final used set is exactly the distinct list of selected pivot rows. -/
theorem finalState_used_eq_pivotRows_toFinset {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalState samples).used =
      (pivotRows (finalState samples).pivots).toFinset := by
  exact runColumns_used_eq_pivotRows_toFinset (List.finRange width) (initial samples)
    (initial_used_eq_pivotRows_toFinset samples)

/-- The final pivotCount equals the number of distinct used pivot rows. -/
theorem finalState_pivotCount_eq_used_card {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalState samples).pivotCount = (finalState samples).used.card := by
  exact runColumns_pivotCount_eq_used_card (List.finRange width) (initial samples) (by
    simp [initial])

/-- The final executable pivotCount counts distinct selected pivot-row indices. -/
theorem finalState_pivotCount_eq_distinct_pivot_rows {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalState samples).pivotCount =
      (pivotRows (finalState samples).pivots).toFinset.card := by
  rw [finalState_pivotCount_eq_used_card samples,
    finalState_used_eq_pivotRows_toFinset samples]

/-- The public executable pivotCount counts distinct recorded pivot rows. -/
theorem reduce_pivotCount_eq_distinct_pivot_rows {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (reduce samples).pivotCount =
      (pivotRows (reduce samples).pivots).toFinset.card := by
  simpa [reduce] using finalState_pivotCount_eq_distinct_pivot_rows samples

/-- Pivot row records in a completed reduction are pairwise distinct. -/
theorem finalState_pivotRows_nodup {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (pivotRows (finalState samples).pivots).Nodup := by
  let rows := pivotRows (finalState samples).pivots
  have cardEq : rows.toFinset.card = rows.length := by
    calc
      rows.toFinset.card = (finalState samples).pivotCount := by
        simpa [rows] using (finalState_pivotCount_eq_distinct_pivot_rows samples).symm
      _ = (finalState samples).pivots.length :=
        finalState_pivotCount_eq_pivots_length samples
      _ = rows.length := by simp [rows, pivotRows]
  have multisetCardEq :
      (↑rows : Multiset (Fin rowCount)).toFinset.card =
        (↑rows : Multiset (Fin rowCount)).card := by
    simpa using cardEq
  exact Multiset.coe_nodup.mp
    (Multiset.toFinset_card_eq_card_iff_nodup.mp multisetCardEq)

/-- Public pivot records retain pairwise distinct row indices. -/
theorem reduce_pivotRows_nodup {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (pivotRows (reduce samples).pivots).Nodup := by
  simpa [reduce] using finalState_pivotRows_nodup samples

/-- The final executable pivotCount cannot exceed the number of ordered sample rows. -/
theorem finalState_pivotCount_le_rowCount {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalState samples).pivotCount ≤ rowCount := by
  calc
    (finalState samples).pivotCount = (finalState samples).used.card :=
      finalState_pivotCount_eq_used_card samples
    _ ≤ rowCount := card_finset_fin_le _

/-- The public executable pivotCount cannot exceed the number of ordered sample rows. -/
theorem reduce_pivotCount_le_rowCount {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (reduce samples).pivotCount ≤ rowCount := by
  simpa [reduce] using finalState_pivotCount_le_rowCount samples

/-- The actual reduced-state invariant maintained by the ordered column pass.

`pivotColumns_unit` says that every recorded pivot column is a unit column in
the current rows.  Thus a later pivot elimination may change a pivot row, but
it cannot change any already-recorded pivot column. -/
structure ReducedStateInvariant {rowCount width : Nat}
    (state : State rowCount width) : Prop where
  used_eq_pivotRows :
    state.used = (pivotRows state.pivots).toFinset
  pivotRows_nodup :
    (pivotRows state.pivots).Nodup
  pivotColumns_nodup :
    (pivotColumns state.pivots).Nodup
  pivotColumns_unit :
    ∀ pivot, pivot ∈ state.pivots → ∀ row,
      testBit (state.rows row) pivot.column =
        if row = pivot.row then true else false

/-- Recorded pivot columns that must not occur in a remaining column pass. -/
def PivotColumnsAvoid {rowCount width : Nat} (state : State rowCount width)
    (columns : List (Fin width)) : Prop :=
  ∀ ⦃column⦄, column ∈ pivotColumns state.pivots → column ∉ columns

/-- A recorded pivot row is present in the corresponding used-row set. -/
theorem pivotRow_mem_used {rowCount width : Nat} {state : State rowCount width}
    (invariant : ReducedStateInvariant state) {pivot : Pivot rowCount width}
    (member : pivot ∈ state.pivots) :
    pivot.row ∈ state.used := by
  rw [invariant.used_eq_pivotRows]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pivot, member, rfl⟩)

/-- A later column step leaves every already-recorded pivot column unchanged. -/
theorem stepColumn_preserves_recorded_pivot_column {rowCount width : Nat}
    (column : Fin width) (state : State rowCount width)
    (invariant : ReducedStateInvariant state) {recorded : Pivot rowCount width}
    (recordedMem : recorded ∈ state.pivots) (target : Fin rowCount) :
    testBit ((stepColumn column state).rows target) recorded.column =
      testBit (state.rows target) recorded.column := by
  cases choice : firstUnusedPivot state column with
  | none => simp [stepColumn, choice]
  | some pivot =>
      have pivotUnused : pivot ∉ state.used := (firstUnusedPivot_spec choice).1
      have recordedUsed : recorded.row ∈ state.used :=
        pivotRow_mem_used invariant recordedMem
      have pivotNeRecorded : pivot ≠ recorded.row := by
        intro same
        apply pivotUnused
        simpa [same] using recordedUsed
      have pivotZero : testBit (state.rows pivot) recorded.column = false := by
        rw [invariant.pivotColumns_unit recorded recordedMem pivot,
          if_neg pivotNeRecorded]
      simpa [stepColumn, choice] using
        (testBit_eliminateRows_preserves state.rows pivot column recorded.column
          pivotZero target)

/-- A column step keeps all recorded pivot columns outside the remaining pass. -/
theorem stepColumn_pivotColumnsAvoid_tail {rowCount width : Nat}
    (column : Fin width) (state : State rowCount width)
    (columns : List (Fin width))
    (avoid : PivotColumnsAvoid state (column :: columns))
    (columnNotMem : column ∉ columns) :
    PivotColumnsAvoid (stepColumn column state) columns := by
  intro recordedColumn recordedMem remainingMem
  cases choice : firstUnusedPivot state column with
  | none =>
      have oldMem : recordedColumn ∈ pivotColumns state.pivots := by
        simpa [stepColumn, choice] using recordedMem
      exact avoid oldMem (by simp [remainingMem])
  | some pivot =>
      have cases :
          recordedColumn ∈ pivotColumns state.pivots ∨ recordedColumn = column := by
        simpa [stepColumn, choice, pivotColumns] using recordedMem
      rcases cases with oldMem | rfl
      · exact avoid oldMem (by simp [remainingMem])
      · exact columnNotMem remainingMem

/-- One fresh column step preserves the full reduced-state invariant. -/
theorem stepColumn_reducedStateInvariant {rowCount width : Nat}
    (column : Fin width) (state : State rowCount width)
    (invariant : ReducedStateInvariant state)
    (fresh : column ∉ pivotColumns state.pivots) :
    ReducedStateInvariant (stepColumn column state) := by
  cases choice : firstUnusedPivot state column with
  | none =>
      have stepEq :
          stepColumn column state =
            { state with trace := state.trace ++ searchTrace state column } := by
        unfold stepColumn
        rw [choice]
      rw [stepEq]
      refine
        { used_eq_pivotRows := ?_
          pivotRows_nodup := ?_
          pivotColumns_nodup := ?_
          pivotColumns_unit := ?_ }
      · change state.used = (pivotRows state.pivots).toFinset
        exact invariant.used_eq_pivotRows
      · change (pivotRows state.pivots).Nodup
        exact invariant.pivotRows_nodup
      · change (pivotColumns state.pivots).Nodup
        exact invariant.pivotColumns_nodup
      · intro pivot member row
        change testBit (state.rows row) pivot.column =
          if row = pivot.row then true else false
        exact invariant.pivotColumns_unit pivot member row
  | some pivot =>
      have pivotSpec := firstUnusedPivot_spec choice
      refine
        { used_eq_pivotRows :=
            stepColumn_used_eq_pivotRows_toFinset column state
              invariant.used_eq_pivotRows
          pivotRows_nodup := ?_
          pivotColumns_nodup := ?_
          pivotColumns_unit := ?_ }
      · have rowFresh : pivot ∉ pivotRows state.pivots := by
          intro rowMem
          apply pivotSpec.1
          rw [invariant.used_eq_pivotRows]
          exact List.mem_toFinset.mpr rowMem
        have nodup : ((pivotRows state.pivots).concat pivot).Nodup :=
          (List.nodup_concat (pivotRows state.pivots) pivot).mpr
            ⟨rowFresh, invariant.pivotRows_nodup⟩
        simpa [stepColumn, choice, pivotRows] using nodup
      · have nodup : ((pivotColumns state.pivots).concat column).Nodup :=
          (List.nodup_concat (pivotColumns state.pivots) column).mpr
            ⟨fresh, invariant.pivotColumns_nodup⟩
        simpa [stepColumn, choice, pivotColumns] using nodup
      · intro recorded recordedMem target
        have recordedCases :
            recorded ∈ state.pivots ∨ recorded = ⟨pivot, column⟩ := by
          simpa [stepColumn, choice] using recordedMem
        rcases recordedCases with oldMem | rfl
        · calc
            testBit ((stepColumn column state).rows target) recorded.column =
                testBit (state.rows target) recorded.column :=
              stepColumn_preserves_recorded_pivot_column column state invariant
                oldMem target
            _ = if target = recorded.row then true else false :=
              invariant.pivotColumns_unit recorded oldMem target
        · by_cases targetPivot : target = pivot
          · subst target
            simpa [stepColumn, choice, eliminateRows_pivot] using pivotSpec.2
          · have cleared :=
              testBit_eliminateRows_other state.rows pivot column pivotSpec.2 targetPivot
            simpa [stepColumn, choice, targetPivot] using cleared

/-- An ordered pass of pairwise distinct fresh columns preserves reduced form. -/
theorem runColumns_reducedStateInvariant {rowCount width : Nat}
    (columns : List (Fin width)) (state : State rowCount width)
    (invariant : ReducedStateInvariant state) (columnsNodup : columns.Nodup)
    (avoid : PivotColumnsAvoid state columns) :
    ReducedStateInvariant (runColumns columns state) := by
  induction columns generalizing state with
  | nil => simpa [runColumns] using invariant
  | cons column columns inductionHypothesis =>
      have fresh : column ∉ pivotColumns state.pivots := by
        intro columnMem
        exact avoid columnMem (by simp)
      have nextInvariant : ReducedStateInvariant (stepColumn column state) :=
        stepColumn_reducedStateInvariant column state invariant fresh
      have columnNotMem : column ∉ columns := (List.nodup_cons.mp columnsNodup).1
      have nextAvoid : PivotColumnsAvoid (stepColumn column state) columns :=
        stepColumn_pivotColumnsAvoid_tail column state columns avoid columnNotMem
      change ReducedStateInvariant (runColumns columns (stepColumn column state))
      exact inductionHypothesis (stepColumn column state) nextInvariant
        (List.nodup_cons.mp columnsNodup).2 nextAvoid

/-- The initial state satisfies the reduced-state invariant vacuously. -/
theorem initial_reducedStateInvariant {rowCount width : Nat}
    (samples : Samples rowCount width) :
    ReducedStateInvariant (initial samples) := by
  refine
    { used_eq_pivotRows := by simp [initial, pivotRows]
      pivotRows_nodup := by simp [initial, pivotRows]
      pivotColumns_nodup := by simp [initial, pivotColumns]
      pivotColumns_unit := ?_ }
  intro pivot member
  simp [initial] at member

/-- Initially every column is fresh for the empty pivot record. -/
theorem initial_pivotColumnsAvoid {rowCount width : Nat}
    (samples : Samples rowCount width) (columns : List (Fin width)) :
  PivotColumnsAvoid (initial samples) columns := by
  intro column member
  simp [initial, pivotColumns] at member

/-- The completed ordered reduction has unit recorded pivot columns. -/
theorem finalState_reducedStateInvariant {rowCount width : Nat}
    (samples : Samples rowCount width) :
    ReducedStateInvariant (finalState samples) := by
  unfold finalState
  exact runColumns_reducedStateInvariant (List.finRange width) (initial samples)
    (initial_reducedStateInvariant samples) (List.nodup_finRange width)
    (initial_pivotColumnsAvoid samples (List.finRange width))

/-- Completed pivot columns are pairwise distinct. -/
theorem finalState_pivotColumns_nodup {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (pivotColumns (finalState samples).pivots).Nodup :=
  (finalState_reducedStateInvariant samples).pivotColumns_nodup

/-- Every completed pivot coordinate is a unit column of the final row system. -/
theorem finalState_pivotColumn_unit {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Pivot rowCount width)
    (member : pivot ∈ (finalState samples).pivots) (row : Fin rowCount) :
    testBit ((finalState samples).rows row) pivot.column =
      if row = pivot.row then true else false :=
  (finalState_reducedStateInvariant samples).pivotColumns_unit pivot member row

/-- Public reduction records pairwise distinct pivot columns. -/
theorem reduce_pivotColumns_nodup {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (pivotColumns (reduce samples).pivots).Nodup := by
  simpa [reduce] using finalState_pivotColumns_nodup samples

/-- Every public recorded pivot coordinate is a unit column of the reduced rows. -/
theorem reduce_pivotColumn_unit {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Pivot rowCount width)
    (member : pivot ∈ (reduce samples).pivots) (row : Fin rowCount) :
    testBit ((reduce samples).reduced row) pivot.column =
      if row = pivot.row then true else false := by
  simpa [reduce] using finalState_pivotColumn_unit samples pivot member row

/-- On columns already visited by the ordered pass, each still-unused row is
zero.  This is the second half of the reduced-row invariant: a pivot selected
later was unused at every earlier column, so it has a zero there and its row
XOR cannot disturb an earlier processed column. -/
def ProcessedColumnsZero {rowCount width : Nat} (processed : List (Fin width))
    (state : State rowCount width) : Prop :=
  ∀ row, row ∉ state.used → ∀ column, column ∈ processed →
    testBit (state.rows row) column = false

/-- Processing one more column extends the unused-row zero invariant. -/
theorem stepColumn_processedColumnsZero {rowCount width : Nat}
    (processed : List (Fin width)) (column : Fin width)
    (state : State rowCount width)
    (invariant : ProcessedColumnsZero processed state) :
    ProcessedColumnsZero (processed ++ [column]) (stepColumn column state) := by
  cases choice : firstUnusedPivot state column with
  | none =>
      intro row unused processedColumn member
      have rowUnused : row ∉ state.used := by
        simpa [stepColumn, choice] using unused
      rcases List.mem_append.mp member with oldMember | newMember
      · simpa [stepColumn, choice] using
          invariant row rowUnused processedColumn oldMember
      · have same : processedColumn = column := by simpa using newMember
        subst processedColumn
        simpa [stepColumn, choice] using
          (firstUnusedPivot_none_bit_eq_false choice rowUnused)
  | some pivot =>
      have pivotSpec := firstUnusedPivot_spec choice
      intro row unused processedColumn member
      have rowUnused : row ∉ state.used := by
        intro rowUsed
        apply unused
        simpa [stepColumn, choice] using
          (Finset.mem_insert_of_mem rowUsed : row ∈ insert pivot state.used)
      have rowNePivot : row ≠ pivot := by
        intro same
        subst row
        apply unused
        simp [stepColumn, choice]
      rcases List.mem_append.mp member with oldMember | newMember
      · have pivotZero : testBit (state.rows pivot) processedColumn = false :=
          invariant pivot pivotSpec.1 processedColumn oldMember
        calc
          testBit ((stepColumn column state).rows row) processedColumn =
              testBit (state.rows row) processedColumn := by
            simpa [stepColumn, choice] using
              (testBit_eliminateRows_preserves state.rows pivot column
                processedColumn pivotZero row)
          _ = false := invariant row rowUnused processedColumn oldMember
      · have same : processedColumn = column := by simpa using newMember
        subst processedColumn
        simpa [stepColumn, choice] using
          (testBit_eliminateRows_other state.rows pivot column pivotSpec.2 rowNePivot)

/-- Extending an ordered pass extends its set of certified processed columns. -/
theorem runColumns_processedColumnsZero {rowCount width : Nat}
    (processed columns : List (Fin width)) (state : State rowCount width)
    (invariant : ProcessedColumnsZero processed state) :
    ProcessedColumnsZero (processed ++ columns) (runColumns columns state) := by
  induction columns generalizing processed state with
  | nil => simpa [runColumns] using invariant
  | cons column columns inductionHypothesis =>
      have nextInvariant :
          ProcessedColumnsZero (processed ++ [column]) (stepColumn column state) :=
        stepColumn_processedColumnsZero processed column state invariant
      have completed := inductionHypothesis (processed ++ [column])
        (stepColumn column state) nextInvariant
      change ProcessedColumnsZero (processed ++ (column :: columns))
        (runColumns columns (stepColumn column state))
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using completed

/-- The initial pass has no processed columns, hence satisfies the invariant
vacuously. -/
theorem initial_processedColumnsZero {rowCount width : Nat}
    (samples : Samples rowCount width) :
    ProcessedColumnsZero [] (initial samples) := by
  intro row unused column member
  simp at member

/-- At completion, every row that was never selected as a pivot is the zero
row in every logical coordinate. -/
theorem finalState_unusedRows_zero {rowCount width : Nat}
    (samples : Samples rowCount width) (row : Fin rowCount)
    (unused : row ∉ (finalState samples).used) (column : Fin width) :
    testBit ((finalState samples).rows row) column = false := by
  have completed :
      ProcessedColumnsZero (List.finRange width) (finalState samples) := by
    unfold finalState
    simpa using
      (runColumns_processedColumnsZero [] (List.finRange width) (initial samples)
        (initial_processedColumnsZero samples))
  exact completed row unused column (by simp)

/-- A final row is either its recorded pivot row or is the all-zero row. -/
theorem finalState_row_is_pivot_or_zero {rowCount width : Nat}
    (samples : Samples rowCount width) (row : Fin rowCount) :
    (∃ pivot, pivot ∈ (finalState samples).pivots ∧ pivot.row = row) ∨
      ∀ column, testBit ((finalState samples).rows row) column = false := by
  by_cases used : row ∈ (finalState samples).used
  · left
    rw [finalState_used_eq_pivotRows_toFinset] at used
    have rowMember : row ∈ pivotRows (finalState samples).pivots :=
      List.mem_toFinset.mp used
    rcases List.mem_map.mp rowMember with ⟨pivot, pivotMember, rowEq⟩
    exact ⟨pivot, pivotMember, rowEq⟩
  · right
    exact finalState_unusedRows_zero samples row used

/-- Public reduced rows are exactly the recorded pivot rows together with
zero rows. -/
theorem reduce_row_is_pivot_or_zero {rowCount width : Nat}
    (samples : Samples rowCount width) (row : Fin rowCount) :
    (∃ pivot, pivot ∈ (reduce samples).pivots ∧ pivot.row = row) ∨
      ∀ column, testBit ((reduce samples).reduced row) column = false := by
  simpa [reduce] using finalState_row_is_pivot_or_zero samples row

/-- The GF(2) coordinate vector represented by one fixed-width word. -/
def rowVector {width : Nat} (word : Word width) : Fin width → F2 :=
  fun column => bitValue word column

/-- The concrete GF(2) matrix whose rows are the ordered input samples. -/
def sampleMatrix {rowCount width : Nat} (samples : Samples rowCount width) :
    Matrix (Fin rowCount) (Fin width) F2 :=
  fun row column => bitValue (samples row) column

/-- The row space of an ordered fixed-width binary system. -/
def rowSpan {rowCount width : Nat} (samples : Samples rowCount width) :
    Submodule F2 (Fin width → F2) :=
  Submodule.span F2 (Set.range (fun row => rowVector (samples row)))

/-- A matrix row is exactly the coordinate vector of the corresponding sample. -/
@[simp] theorem sampleMatrix_row {rowCount width : Nat}
    (samples : Samples rowCount width) (row : Fin rowCount) :
    (sampleMatrix samples).row row = rowVector (samples row) :=
  rfl

/-- Word XOR is vector addition in the concrete GF(2) row representation. -/
theorem rowVector_rowXor {width : Nat} (left right : Word width) :
    rowVector (rowXor left right) = rowVector left + rowVector right := by
  funext column
  exact bitValue_rowXor left right column

/-- A concrete sample row belongs to its declared row space. -/
theorem rowVector_mem_rowSpan {rowCount width : Nat}
    (samples : Samples rowCount width) (row : Fin rowCount) :
    rowVector (samples row) ∈ rowSpan samples := by
  exact Submodule.subset_span ⟨row, rfl⟩

/-- One output row of an elimination is in the span of its input rows. -/
theorem rowVector_eliminateRows_mem_rowSpan {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Fin rowCount) (column : Fin width)
    (target : Fin rowCount) :
    rowVector (eliminateRows samples pivot column target) ∈ rowSpan samples := by
  unfold eliminateRows eliminateRow
  by_cases targetPivot : target = pivot
  · rw [if_pos targetPivot]
    exact rowVector_mem_rowSpan samples target
  · rw [if_neg targetPivot]
    by_cases active : testBit (samples target) column = true
    · rw [if_pos active, rowVector_rowXor]
      exact Submodule.add_mem _ (rowVector_mem_rowSpan samples target)
        (rowVector_mem_rowSpan samples pivot)
    · rw [if_neg active]
      exact rowVector_mem_rowSpan samples target

/-- Over GF(2), adding a vector to itself gives the zero vector. -/
theorem rowVector_add_self {width : Nat} (vector : Fin width → F2) :
    vector + vector = 0 := by
  funext column
  calc
    vector column + vector column = (2 : F2) * vector column :=
      (two_mul (vector column)).symm
    _ = 0 * vector column := by
      rw [show (2 : F2) = 0 from ZMod.natCast_self 2]
    _ = 0 := zero_mul (vector column)

/-- Every input row is in the span of the rows after one elimination. -/
theorem rowVector_mem_rowSpan_eliminateRows {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Fin rowCount) (column : Fin width)
    (target : Fin rowCount) :
    rowVector (samples target) ∈ rowSpan (eliminateRows samples pivot column) := by
  by_cases targetPivot : target = pivot
  · subst target
    rw [← eliminateRows_pivot samples pivot column]
    exact rowVector_mem_rowSpan (eliminateRows samples pivot column) pivot
  · by_cases active : testBit (samples target) column = true
    · have targetMember :
        rowVector (eliminateRows samples pivot column target) ∈
          rowSpan (eliminateRows samples pivot column) :=
        rowVector_mem_rowSpan (eliminateRows samples pivot column) target
      have pivotMember :
          rowVector (eliminateRows samples pivot column pivot) ∈
            rowSpan (eliminateRows samples pivot column) :=
        rowVector_mem_rowSpan (eliminateRows samples pivot column) pivot
      have targetRow :
          eliminateRows samples pivot column target =
            rowXor (samples target) (samples pivot) := by
        unfold eliminateRows eliminateRow
        rw [if_neg targetPivot, if_pos active]
      have pivotRow :
          eliminateRows samples pivot column pivot = samples pivot :=
        eliminateRows_pivot samples pivot column
      have recoverRow :
          rowVector (samples target) =
            rowVector (eliminateRows samples pivot column target) +
              rowVector (eliminateRows samples pivot column pivot) := by
        calc
          rowVector (samples target) = rowVector (samples target) + 0 :=
            (add_zero _).symm
          _ = rowVector (samples target) +
                (rowVector (samples pivot) + rowVector (samples pivot)) := by
              rw [rowVector_add_self]
          _ = (rowVector (samples target) + rowVector (samples pivot)) +
                rowVector (samples pivot) := (add_assoc _ _ _).symm
          _ = rowVector (rowXor (samples target) (samples pivot)) +
                rowVector (samples pivot) := by rw [rowVector_rowXor]
          _ = rowVector (eliminateRows samples pivot column target) +
                rowVector (eliminateRows samples pivot column pivot) := by
              rw [targetRow, pivotRow]
      rw [recoverRow]
      exact Submodule.add_mem _ targetMember pivotMember
    · have targetRow :
          eliminateRows samples pivot column target = samples target := by
        unfold eliminateRows eliminateRow
        rw [if_neg targetPivot, if_neg active]
      rw [← targetRow]
      exact rowVector_mem_rowSpan (eliminateRows samples pivot column) target

/-- A full XOR elimination preserves the concrete GF(2) row space. -/
theorem rowSpan_eliminateRows {rowCount width : Nat}
    (samples : Samples rowCount width) (pivot : Fin rowCount) (column : Fin width) :
    rowSpan (eliminateRows samples pivot column) = rowSpan samples := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨target, rfl⟩
    exact rowVector_eliminateRows_mem_rowSpan samples pivot column target
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨target, rfl⟩
    exact rowVector_mem_rowSpan_eliminateRows samples pivot column target

/-- One ordered column decision preserves the concrete GF(2) row space. -/
theorem rowSpan_stepColumn {rowCount width : Nat} (column : Fin width)
    (state : State rowCount width) :
    rowSpan (stepColumn column state).rows = rowSpan state.rows := by
  cases choice : firstUnusedPivot state column with
  | none => simp [stepColumn, choice]
  | some pivot =>
      simpa [stepColumn, choice] using
        (rowSpan_eliminateRows state.rows pivot column)

/-- Any ordered sequence of column decisions preserves the row space. -/
theorem rowSpan_runColumns {rowCount width : Nat}
    (columns : List (Fin width)) (state : State rowCount width) :
    rowSpan (runColumns columns state).rows = rowSpan state.rows := by
  induction columns generalizing state with
  | nil => rfl
  | cons column columns inductionHypothesis =>
      calc
        rowSpan (runColumns (column :: columns) state).rows =
            rowSpan (runColumns columns (stepColumn column state)).rows := rfl
        _ = rowSpan (stepColumn column state).rows :=
          inductionHypothesis (stepColumn column state)
        _ = rowSpan state.rows := rowSpan_stepColumn column state

/-- The completed ordered reduction has the same row space as its input samples. -/
theorem rowSpan_finalState {rowCount width : Nat}
    (samples : Samples rowCount width) :
    rowSpan (finalState samples).rows = rowSpan samples := by
  simpa [finalState, initial] using
    (rowSpan_runColumns (List.finRange width) (initial samples))

/-- The public reduced rows span exactly the row space of the input samples. -/
theorem rowSpan_reduce {rowCount width : Nat}
    (samples : Samples rowCount width) :
    rowSpan (reduce samples).reduced = rowSpan samples := by
  simpa [reduce] using rowSpan_finalState samples

/-- Mathlib's matrix rank is the finrank of the concrete ordered sample row space. -/
theorem sampleMatrix_rank_eq_finrank_rowSpan {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (sampleMatrix samples).rank = Module.finrank F2 (rowSpan samples) := by
  change (sampleMatrix samples).rank =
    Module.finrank F2 (Submodule.span F2 (Set.range (sampleMatrix samples).row))
  exact Matrix.rank_eq_finrank_span_row (sampleMatrix samples)

/-- A successful pivot lookup returns a pivot actually recorded in the result. -/
theorem pivotForColumn?_some_mem {rowCount width : Nat}
    {result : Result rowCount width} {column : Fin width}
    {pivot : Pivot rowCount width}
    (lookup : pivotForColumn? result column = some pivot) :
    pivot ∈ result.pivots := by
  unfold pivotForColumn? at lookup
  exact List.mem_of_find?_eq_some lookup

/-- The pivot returned by a successful lookup has the requested column. -/
theorem pivotForColumn?_some_column {rowCount width : Nat}
    {result : Result rowCount width} {column : Fin width}
    {pivot : Pivot rowCount width}
    (lookup : pivotForColumn? result column = some pivot) :
    pivot.column = column := by
  unfold pivotForColumn? at lookup
  simpa using List.find?_some lookup

/-- A failed pivot lookup means that no record has the requested column. -/
theorem pivotForColumn?_eq_none_iff {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    pivotForColumn? result column = none ↔
      ∀ pivot, pivot ∈ result.pivots → pivot.column ≠ column := by
  constructor
  · intro lookup pivot member same
    unfold pivotForColumn? at lookup
    have rejected := (List.find?_eq_none.mp lookup) pivot member
    subst column
    simp at rejected
  · intro absent
    unfold pivotForColumn?
    apply List.find?_eq_none.mpr
    intro pivot member
    simpa using absent pivot member

/-- Free columns are exactly the columns whose pivot lookup fails. -/
theorem mem_freeColumns_iff {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    column ∈ freeColumns result ↔ pivotForColumn? result column = none := by
  simp [freeColumns, isPivotColumn]

/-- A free-column mask bit is set exactly at a failed pivot lookup. -/
theorem testBit_freeColumnMask_eq_true_iff {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    testBit (freeColumnMask result) column = true ↔
      pivotForColumn? result column = none := by
  rw [testBit_freeColumnMask]
  simp

/-- A free-column mask bit is set exactly at a member of `freeColumns`. -/
theorem testBit_freeColumnMask_eq_true_iff_mem_freeColumns {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    testBit (freeColumnMask result) column = true ↔
      column ∈ freeColumns result := by
  rw [testBit_freeColumnMask_eq_true_iff]
  exact (mem_freeColumns_iff result column).symm

/-- The Boolean free-column mask coordinate is the membership decision for
the ordered free-column list. -/
theorem testBit_freeColumnMask_eq_decide_mem_freeColumns {rowCount width : Nat}
    (result : Result rowCount width) (column : Fin width) :
    testBit (freeColumnMask result) column =
      decide (column ∈ freeColumns result) := by
  by_cases member : column ∈ freeColumns result
  · have lookup : pivotForColumn? result column = none :=
      (mem_freeColumns_iff result column).mp member
    simp [testBit_freeColumnMask, lookup, member]
  · have lookup : pivotForColumn? result column ≠ none := by
      intro noneLookup
      exact member ((mem_freeColumns_iff result column).mpr noneLookup)
    simp [testBit_freeColumnMask, lookup, member]

/-- A one-free-column decision exposes the exact singleton free-column list. -/
theorem freeColumns_eq_singleton_of_soleFreeColumn {rowCount width : Nat}
    {result : Result rowCount width} {free : Fin width}
    (choice : soleFreeColumn? result = some free) :
    freeColumns result = [free] := by
  cases hcolumns : freeColumns result with
  | nil => simp [soleFreeColumn?, hcolumns] at choice
  | cons first rest =>
      cases rest with
      | nil =>
          have same : first = free := by
            simpa [soleFreeColumn?, hcolumns] using choice
          exact congrArg (fun column => [column]) same
      | cons second rest => simp [soleFreeColumn?, hcolumns] at choice

/-- The selected free coordinate really has no recorded pivot. -/
theorem soleFreeColumn_lookup_none {rowCount width : Nat}
    {result : Result rowCount width} {free : Fin width}
    (choice : soleFreeColumn? result = some free) :
    pivotForColumn? result free = none := by
  apply (mem_freeColumns_iff result free).mp
  rw [freeColumns_eq_singleton_of_soleFreeColumn choice]
  simp

/-- Every coordinate other than a selected sole free coordinate has a pivot
record. -/
theorem exists_pivotForColumn_of_soleFreeColumn {rowCount width : Nat}
    {result : Result rowCount width} {free column : Fin width}
    (choice : soleFreeColumn? result = some free) (different : column ≠ free) :
    ∃ pivot, pivotForColumn? result column = some pivot := by
  cases lookup : pivotForColumn? result column with
  | some pivot =>
      refine ⟨pivot, ?_⟩
      rfl
  | none =>
      have member : column ∈ freeColumns result :=
        (mem_freeColumns_iff result column).mpr lookup
      have freeColumnsEq := freeColumns_eq_singleton_of_soleFreeColumn choice
      have same : column = free := by simpa [freeColumnsEq] using member
      exact (different same).elim

/-- Distinct recorded pivot columns make the record at a given column unique. -/
theorem pivot_eq_of_mem_same_column {rowCount width : Nat}
    {result : Result rowCount width} {left right : Pivot rowCount width}
    (columnsNodup : (pivotColumns result.pivots).Nodup)
    (leftMember : left ∈ result.pivots) (rightMember : right ∈ result.pivots)
    (sameColumn : left.column = right.column) :
    left = right := by
  apply List.inj_on_of_nodup_map (f := Pivot.column)
    (by simpa [pivotColumns] using columnsNodup) leftMember rightMember
  exact sameColumn

/-- Looking up a recorded pivot returns that very pivot when columns are
pairwise distinct. -/
theorem pivotForColumn?_eq_some_of_mem {rowCount width : Nat}
    {result : Result rowCount width} {pivot : Pivot rowCount width}
    (columnsNodup : (pivotColumns result.pivots).Nodup)
    (member : pivot ∈ result.pivots) :
    pivotForColumn? result pivot.column = some pivot := by
  cases lookup : pivotForColumn? result pivot.column with
  | none =>
      have absent := (pivotForColumn?_eq_none_iff result pivot.column).mp lookup
      exact (absent pivot member rfl).elim
  | some found =>
      have foundMember : found ∈ result.pivots :=
        pivotForColumn?_some_mem lookup
      have foundColumn : found.column = pivot.column :=
        pivotForColumn?_some_column lookup
      have same : found = pivot := pivot_eq_of_mem_same_column columnsNodup
        foundMember member foundColumn
      exact congrArg some same

/-- Addition in the concrete coefficient field has characteristic two. -/
theorem f2_add_self (value : F2) : value + value = 0 := by
  calc
    value + value = (2 : F2) * value := (two_mul value).symm
    _ = 0 * value := by rw [show (2 : F2) = 0 from ZMod.natCast_self 2]
    _ = 0 := zero_mul value

/-- A false logical bit has zero GF(2) coefficient. -/
theorem bitValue_eq_zero_of_testBit_eq_false {width : Nat}
    (word : Word width) (column : Fin width)
    (bit : testBit word column = false) :
    bitValue word column = 0 := by
  unfold bitValue
  rw [bit]
  rfl

/-- A true logical bit has unit GF(2) coefficient. -/
theorem bitValue_eq_one_of_testBit_eq_true {width : Nat}
    (word : Word width) (column : Fin width)
    (bit : testBit word column = true) :
    bitValue word column = 1 := by
  unfold bitValue
  rw [bit]
  rfl

/-- A row whose logical bits are all zero has zero dot product with every
candidate. -/
theorem dot_eq_zero_of_all_testBit_eq_false {width : Nat}
    (row candidate : Word width)
    (zeroBits : ∀ column, testBit row column = false) :
    dot row candidate = 0 := by
  unfold dot
  apply Finset.sum_eq_zero
  intro column _
  rw [bitValue_eq_zero_of_testBit_eq_false row column (zeroBits column), zero_mul]

/-- If every summand except two distinguished coordinates is zero, the finite
sum is exactly the sum of those two coordinates. -/
theorem sum_eq_pivot_add_free {width : Nat} (term : Fin width → F2)
    (pivot free : Fin width) (different : pivot ≠ free)
    (zeroOther : ∀ column, column ≠ pivot → column ≠ free → term column = 0) :
    (∑ column, term column) = term pivot + term free := by
  classical
  have freeMember : free ∈ (Finset.univ.erase pivot : Finset (Fin width)) :=
    Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
  have remainingZero :
      ∀ column ∈ (Finset.univ.erase pivot).erase free, term column = 0 := by
    intro column member
    have columnNeFree : column ≠ free := (Finset.mem_erase.mp member).1
    have afterPivot : column ∈ Finset.univ.erase pivot :=
      (Finset.mem_erase.mp member).2
    have columnNePivot : column ≠ pivot := (Finset.mem_erase.mp afterPivot).1
    exact zeroOther column columnNePivot columnNeFree
  calc
    (∑ column, term column) =
        term pivot + (∑ column ∈ Finset.univ.erase pivot, term column) :=
      (Finset.add_sum_erase Finset.univ term (Finset.mem_univ pivot)).symm
    _ = term pivot +
        (term free +
          (∑ column ∈ (Finset.univ.erase pivot).erase free, term column)) := by
      rw [← Finset.add_sum_erase (Finset.univ.erase pivot) term freeMember]
    _ = term pivot + term free := by
      rw [Finset.sum_eq_zero remainingZero, add_zero]

/-- Distinct recorded pivot rows make the record at a given row unique. -/
theorem pivot_eq_of_mem_same_row {rowCount width : Nat}
    {result : Result rowCount width} {left right : Pivot rowCount width}
    (rowsNodup : (pivotRows result.pivots).Nodup)
    (leftMember : left ∈ result.pivots) (rightMember : right ∈ result.pivots)
    (sameRow : left.row = right.row) :
    left = right := by
  apply List.inj_on_of_nodup_map (f := Pivot.row)
    (by simpa [pivotRows] using rowsNodup) leftMember rightMember
  exact sameRow

/-- The finite set of pivot records retained by the completed ordered pass. -/
def finalPivotSet {rowCount width : Nat} (samples : Samples rowCount width) :
    Finset (Pivot rowCount width) :=
  (finalState samples).pivots.toFinset

/-- The completed pivot rows, indexed by their distinct pivot records. -/
def finalPivotFamily {rowCount width : Nat} (samples : Samples rowCount width) :
    finalPivotSet samples → Fin width → F2 :=
  fun pivot => rowVector ((finalState samples).rows pivot.val.row)

/-- The completed pivot list itself has no duplicate records. -/
theorem finalState_pivots_nodup {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalState samples).pivots.Nodup := by
  apply List.Nodup.of_map Pivot.row
  simpa [pivotRows] using finalState_pivotRows_nodup samples

/-- The indexed pivot rows have unit values in one another's pivot columns. -/
theorem finalPivotFamily_unit {rowCount width : Nat}
    (samples : Samples rowCount width) (left right : finalPivotSet samples) :
    finalPivotFamily samples left right.val.column =
      if left = right then 1 else 0 := by
  classical
  have leftInSet : left.val ∈ (finalState samples).pivots.toFinset := left.property
  have leftMember : left.val ∈ (finalState samples).pivots :=
    List.mem_toFinset.mp leftInSet
  have rightInSet : right.val ∈ (finalState samples).pivots.toFinset := right.property
  have rightMember : right.val ∈ (finalState samples).pivots :=
    List.mem_toFinset.mp rightInSet
  by_cases same : left = right
  · subst right
    have bit :
        testBit ((finalState samples).rows left.val.row) left.val.column = true := by
      have unit :=
        finalState_pivotColumn_unit samples left.val leftMember left.val.row
      rw [if_pos rfl] at unit
      exact unit
    change bitValue ((finalState samples).rows left.val.row) left.val.column =
      if left = left then 1 else 0
    rw [if_pos rfl]
    exact bitValue_eq_one_of_testBit_eq_true _ _ bit
  · have rowNe : left.val.row ≠ right.val.row := by
      intro sameRow
      apply same
      apply Subtype.ext
      exact pivot_eq_of_mem_same_row (result := reduce samples)
        (reduce_pivotRows_nodup samples)
        (by simpa [reduce] using leftMember)
        (by simpa [reduce] using rightMember) sameRow
    have bit :
        testBit ((finalState samples).rows left.val.row) right.val.column = false := by
      have unit := finalState_pivotColumn_unit samples right.val rightMember left.val.row
      rw [if_neg rowNe] at unit
      exact unit
    change bitValue ((finalState samples).rows left.val.row) right.val.column =
      if left = right then 1 else 0
    rw [if_neg same]
    exact bitValue_eq_zero_of_testBit_eq_false _ _ bit

/-- Distinct pivot columns make the retained final pivot rows linearly independent. -/
theorem finalPivotFamily_linearIndependent {rowCount width : Nat}
    (samples : Samples rowCount width) :
    LinearIndependent F2 (finalPivotFamily samples) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients total pivot
  have coordinate := congrFun total pivot.val.column
  have coordinateSum :
      (∑ index, (coefficients index • finalPivotFamily samples index)
        pivot.val.column) = 0 := by
    simpa only [Finset.sum_apply, Pi.zero_apply] using coordinate
  simpa only [Pi.smul_apply, smul_eq_mul, finalPivotFamily_unit, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using coordinateSum

/-- The final row space is generated exactly by the retained pivot-row family. -/
theorem rowSpan_finalState_eq_finalPivotSpan {rowCount width : Nat}
    (samples : Samples rowCount width) :
    rowSpan (finalState samples).rows =
      Submodule.span F2 (Set.range (finalPivotFamily samples)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨row, rfl⟩
    rcases finalState_row_is_pivot_or_zero samples row with pivotCase | zeroCase
    · rcases pivotCase with ⟨pivot, pivotMember, rowEq⟩
      subst row
      exact Submodule.subset_span
        ⟨⟨pivot, List.mem_toFinset.mpr pivotMember⟩, rfl⟩
    · have zeroRow : rowVector ((finalState samples).rows row) = 0 := by
        funext column
        change bitValue ((finalState samples).rows row) column = 0
        exact bitValue_eq_zero_of_testBit_eq_false _ _ (zeroCase column)
      change rowVector ((finalState samples).rows row) ∈
        Submodule.span F2 (Set.range (finalPivotFamily samples))
      rw [zeroRow]
      exact Submodule.zero_mem _
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨pivot, rfl⟩
    exact rowVector_mem_rowSpan (finalState samples).rows pivot.val.row

/-- The finite pivot-record index has exactly the executable number of pivots. -/
theorem finalPivotSet_card_eq_pivotCount {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (finalPivotSet samples).card = (finalState samples).pivotCount := by
  calc
    (finalPivotSet samples).card = (finalState samples).pivots.length := by
      simpa [finalPivotSet] using
        (List.toFinset_card_of_nodup (finalState_pivots_nodup samples))
    _ = (finalState samples).pivotCount :=
      (finalState_pivotCount_eq_pivots_length samples).symm

/-- The final row-space finrank equals the number of actual recorded pivots. -/
theorem finrank_rowSpan_finalState_eq_pivotCount {rowCount width : Nat}
    (samples : Samples rowCount width) :
    Module.finrank F2 (rowSpan (finalState samples).rows) =
      (finalState samples).pivotCount := by
  classical
  rw [rowSpan_finalState_eq_finalPivotSpan]
  calc
    Module.finrank F2 (Submodule.span F2 (Set.range (finalPivotFamily samples))) =
        Fintype.card (finalPivotSet samples) :=
      finrank_span_eq_card (finalPivotFamily_linearIndependent samples)
    _ = (finalPivotSet samples).card := by simp
    _ = (finalState samples).pivotCount :=
      finalPivotSet_card_eq_pivotCount samples

/-- The executable pivot count is the Mathlib matrix rank of the input GF(2) rows. -/
theorem sampleMatrix_rank_eq_reduce_pivotCount {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (sampleMatrix samples).rank = (reduce samples).pivotCount := by
  calc
    (sampleMatrix samples).rank = Module.finrank F2 (rowSpan samples) :=
      sampleMatrix_rank_eq_finrank_rowSpan samples
    _ = Module.finrank F2 (rowSpan (finalState samples).rows) := by
      rw [rowSpan_finalState samples]
    _ = (finalState samples).pivotCount :=
      finrank_rowSpan_finalState_eq_pivotCount samples
    _ = (reduce samples).pivotCount := rfl

/-- A recorded pivot coordinate cannot be a coordinate whose lookup fails. -/
theorem pivotColumn_ne_of_lookup_none {rowCount width : Nat}
    {result : Result rowCount width} {free : Fin width}
    {pivot : Pivot rowCount width}
    (columnsNodup : (pivotColumns result.pivots).Nodup)
    (member : pivot ∈ result.pivots)
    (freeLookup : pivotForColumn? result free = none) :
    pivot.column ≠ free := by
  intro same
  have pivotLookup := pivotForColumn?_eq_some_of_mem columnsNodup member
  rw [same, freeLookup] at pivotLookup
  simp at pivotLookup

/-- A back-substitution coordinate with a failed pivot lookup is zero unless
it is the distinguished free coordinate. -/
theorem testBit_backSubstitute_of_lookup_none {rowCount width : Nat}
    (result : Result rowCount width) (free column : Fin width)
    (different : column ≠ free)
    (lookup : pivotForColumn? result column = none) :
    testBit (backSubstitute result free) column = false := by
  rw [testBit_backSubstitute]
  simp [backSubstituteBit, different, lookup]

/-- A back-substitution pivot coordinate is read from that pivot's reduced
row at the distinguished free coordinate. -/
theorem testBit_backSubstitute_pivotColumn {rowCount width : Nat}
    {result : Result rowCount width} {free : Fin width}
    {pivot : Pivot rowCount width}
    (columnsNodup : (pivotColumns result.pivots).Nodup)
    (member : pivot ∈ result.pivots)
    (freeLookup : pivotForColumn? result free = none) :
    testBit (backSubstitute result free) pivot.column =
      testBit (result.reduced pivot.row) free := by
  have different : pivot.column ≠ free :=
    pivotColumn_ne_of_lookup_none columnsNodup member freeLookup
  rw [testBit_backSubstitute]
  unfold backSubstituteBit
  rw [if_neg different, pivotForColumn?_eq_some_of_mem columnsNodup member]

/-- Back substitution always carries a one at its distinguished coordinate,
and is therefore nonzero. -/
theorem backSubstitute_ne_zero {rowCount width : Nat}
    (result : Result rowCount width) (free : Fin width) :
    backSubstitute result free ≠ 0 := by
  intro zero
  have freeBit := testBit_backSubstitute_free result free
  rw [zero] at freeBit
  simp [testBit] at freeBit

/-- In a completed reduction, a pivot row has zero at every other recorded
pivot coordinate. -/
theorem reduce_pivotRow_other_pivotColumn_eq_false {rowCount width : Nat}
    (samples : Samples rowCount width) {pivot other : Pivot rowCount width}
    (pivotMember : pivot ∈ (reduce samples).pivots)
    (otherMember : other ∈ (reduce samples).pivots)
    (different : other.column ≠ pivot.column) :
    testBit ((reduce samples).reduced pivot.row) other.column = false := by
  have rowDifferent : pivot.row ≠ other.row := by
    intro sameRow
    have samePivot : pivot = other := pivot_eq_of_mem_same_row
      (reduce_pivotRows_nodup samples) pivotMember otherMember sameRow
    apply different
    exact (congrArg Pivot.column samePivot).symm
  rw [reduce_pivotColumn_unit samples other otherMember pivot.row, if_neg rowDifferent]

/-- Every summand outside a pivot coordinate and a selected free coordinate
vanishes in that pivot row. -/
theorem reducedPivotRow_backSubstitute_term_eq_zero {rowCount width : Nat}
    (samples : Samples rowCount width) {pivot : Pivot rowCount width}
    {free column : Fin width}
    (pivotMember : pivot ∈ (reduce samples).pivots)
    (columnNePivot : column ≠ pivot.column) (columnNeFree : column ≠ free) :
    bitValue ((reduce samples).reduced pivot.row) column *
      bitValue (backSubstitute (reduce samples) free) column = 0 := by
  cases lookup : pivotForColumn? (reduce samples) column with
  | none =>
      have candidateZero :
          testBit (backSubstitute (reduce samples) free) column = false :=
        testBit_backSubstitute_of_lookup_none (reduce samples) free column
          columnNeFree lookup
      rw [bitValue_eq_zero_of_testBit_eq_false
        (backSubstitute (reduce samples) free) column candidateZero, mul_zero]
  | some other =>
      have otherMember : other ∈ (reduce samples).pivots :=
        pivotForColumn?_some_mem lookup
      have otherColumn : other.column = column :=
        pivotForColumn?_some_column lookup
      have otherNePivot : other.column ≠ pivot.column := by
        intro same
        apply columnNePivot
        exact otherColumn.symm.trans same
      have rowZero :
          testBit ((reduce samples).reduced pivot.row) other.column = false :=
        reduce_pivotRow_other_pivotColumn_eq_false samples pivotMember otherMember
          otherNePivot
      have rowZeroAtColumn :
          testBit ((reduce samples).reduced pivot.row) column = false := by
        rw [← otherColumn]
        exact rowZero
      rw [bitValue_eq_zero_of_testBit_eq_false
        ((reduce samples).reduced pivot.row) column rowZeroAtColumn, zero_mul]

/-- The back-substitution word for any genuine free coordinate satisfies the
equation represented by each recorded pivot row. -/
theorem dot_reduce_pivotRow_backSubstitute_eq_zero {rowCount width : Nat}
    (samples : Samples rowCount width) {free : Fin width}
    {pivot : Pivot rowCount width}
    (pivotMember : pivot ∈ (reduce samples).pivots)
    (freeLookup : pivotForColumn? (reduce samples) free = none) :
    dot ((reduce samples).reduced pivot.row)
      (backSubstitute (reduce samples) free) = 0 := by
  have columnsNodup : (pivotColumns (reduce samples).pivots).Nodup :=
    reduce_pivotColumns_nodup samples
  have pivotNeFree : pivot.column ≠ free :=
    pivotColumn_ne_of_lookup_none columnsNodup pivotMember freeLookup
  have pivotBit :
      testBit ((reduce samples).reduced pivot.row) pivot.column = true := by
    simpa using reduce_pivotColumn_unit samples pivot pivotMember pivot.row
  have candidatePivot :
      testBit (backSubstitute (reduce samples) free) pivot.column =
        testBit ((reduce samples).reduced pivot.row) free :=
    testBit_backSubstitute_pivotColumn columnsNodup pivotMember freeLookup
  have candidatePivotValue :
      bitValue (backSubstitute (reduce samples) free) pivot.column =
        bitValue ((reduce samples).reduced pivot.row) free := by
    unfold bitValue
    exact congrArg (fun bit : Bool => (bit.toNat : F2)) candidatePivot
  have candidateFreeValue :
      bitValue (backSubstitute (reduce samples) free) free = 1 :=
    bitValue_eq_one_of_testBit_eq_true _ _
      (testBit_backSubstitute_free (reduce samples) free)
  unfold dot
  calc
    (∑ column, bitValue ((reduce samples).reduced pivot.row) column *
        bitValue (backSubstitute (reduce samples) free) column) =
        bitValue ((reduce samples).reduced pivot.row) pivot.column *
          bitValue (backSubstitute (reduce samples) free) pivot.column +
        bitValue ((reduce samples).reduced pivot.row) free *
          bitValue (backSubstitute (reduce samples) free) free :=
      sum_eq_pivot_add_free _ pivot.column free pivotNeFree
        (fun column columnNePivot columnNeFree =>
          reducedPivotRow_backSubstitute_term_eq_zero samples pivotMember
            columnNePivot columnNeFree)
    _ = (1 : F2) * bitValue ((reduce samples).reduced pivot.row) free +
        bitValue ((reduce samples).reduced pivot.row) free * (1 : F2) := by
      rw [bitValue_eq_one_of_testBit_eq_true
        ((reduce samples).reduced pivot.row) pivot.column pivotBit,
        candidatePivotValue, candidateFreeValue]
    _ = 0 := by
      rw [one_mul, mul_one]
      exact f2_add_self _

/-- A back-substitution word for a free coordinate satisfies every reduced
equation, including the final zero rows. -/
theorem backSubstitute_satisfies_reduced_of_lookup_none {rowCount width : Nat}
    (samples : Samples rowCount width) (free : Fin width)
    (freeLookup : pivotForColumn? (reduce samples) free = none) :
    satisfies (reduce samples).reduced (backSubstitute (reduce samples) free) := by
  intro row
  rcases reduce_row_is_pivot_or_zero samples row with pivotCase | zeroCase
  · rcases pivotCase with ⟨pivot, pivotMember, rowEq⟩
    rw [← rowEq]
    exact dot_reduce_pivotRow_backSubstitute_eq_zero samples pivotMember freeLookup
  · exact dot_eq_zero_of_all_testBit_eq_false
      ((reduce samples).reduced row) (backSubstitute (reduce samples) free) zeroCase

/-- A back-substitution word for any actual free coordinate satisfies the
original ordered equations. -/
theorem backSubstitute_satisfies_of_lookup_none {rowCount width : Nat}
    (samples : Samples rowCount width) (free : Fin width)
    (freeLookup : pivotForColumn? (reduce samples) free = none) :
    satisfies samples (backSubstitute (reduce samples) free) :=
  (reduce_kernel_equiv samples (backSubstitute (reduce samples) free)).mpr
    (backSubstitute_satisfies_reduced_of_lookup_none samples free freeLookup)

/-- Membership in the computed free-column list gives a nonzero semantic
solution directly from the reducer, without enumerating words. -/
theorem backSubstitute_sound_of_mem_freeColumns {rowCount width : Nat}
    (samples : Samples rowCount width) (free : Fin width)
    (freeMember : free ∈ freeColumns (reduce samples)) :
    backSubstitute (reduce samples) free ≠ 0 ∧
      satisfies samples (backSubstitute (reduce samples) free) := by
  have freeLookup : pivotForColumn? (reduce samples) free = none :=
    (mem_freeColumns_iff (reduce samples) free).mp freeMember
  exact ⟨backSubstitute_ne_zero (reduce samples) free,
    backSubstitute_satisfies_of_lookup_none samples free freeLookup⟩

/-- All nonzero solutions enumerated in fixed word-value order. -/
def nonzeroSolutions {rowCount width : Nat} (samples : Samples rowCount width) :
    List (Word width) :=
  (List.finRange (2 ^ width)).filter
    fun candidate => decide (candidate ≠ 0 ∧ satisfies samples candidate)

/-- Membership in the executable candidate list is exactly the semantic contract. -/
theorem mem_nonzeroSolutions {rowCount width : Nat}
    (samples : Samples rowCount width) (candidate : Word width) :
    candidate ∈ nonzeroSolutions samples ↔
      candidate ≠ 0 ∧ satisfies samples candidate := by
  simp [nonzeroSolutions]

/-- The fixed-domain candidate enumeration has no duplicate words. -/
theorem nonzeroSolutions_nodup {rowCount width : Nat}
    (samples : Samples rowCount width) :
    (nonzeroSolutions samples).Nodup := by
  unfold nonzeroSolutions
  exact List.Nodup.filter _ (List.nodup_finRange _)

/-- A semantic statement that a particular word is the sole nonzero solution. -/
def HasUniqueNonzeroSolution {rowCount width : Nat}
    (samples : Samples rowCount width) (candidate : Word width) : Prop :=
  candidate ≠ 0 ∧ satisfies samples candidate ∧
    ∀ other, other ≠ 0 → satisfies samples other → other = candidate

/-- The finite unique-solution contract is decidable without any classical choice. -/
instance decidableHasUniqueNonzeroSolution {rowCount width : Nat}
    (samples : Samples rowCount width) (candidate : Word width) :
    Decidable (HasUniqueNonzeroSolution samples candidate) := by
  unfold HasUniqueNonzeroSolution
  infer_instance

/-- The ordered free-column list has no duplicate coordinates. -/
theorem freeColumns_nodup {rowCount width : Nat}
    (result : Result rowCount width) :
    (freeColumns result).Nodup := by
  unfold freeColumns
  exact List.Nodup.filter _ (List.nodup_finRange _)

/-- Equality of GF(2) bit coefficients reflects equality of the underlying
logical Boolean bits. -/
theorem testBit_eq_of_bitValue_eq {width : Nat}
    {left right : Word width} {column : Fin width}
    (valueEq : bitValue left column = bitValue right column) :
    testBit left column = testBit right column := by
  cases leftBit : testBit left column with
  | false =>
      cases rightBit : testBit right column with
      | false => rfl
      | true =>
          have leftValue : bitValue left column = 0 :=
            bitValue_eq_zero_of_testBit_eq_false left column leftBit
          have rightValue : bitValue right column = 1 :=
            bitValue_eq_one_of_testBit_eq_true right column rightBit
          exact ((by decide : (0 : F2) ≠ 1)
            (leftValue.symm.trans (valueEq.trans rightValue))).elim
  | true =>
      cases rightBit : testBit right column with
      | false =>
          have leftValue : bitValue left column = 1 :=
            bitValue_eq_one_of_testBit_eq_true left column leftBit
          have rightValue : bitValue right column = 0 :=
            bitValue_eq_zero_of_testBit_eq_false right column rightBit
          exact ((by decide : (0 : F2) ≠ 1)
            (rightValue.symm.trans (valueEq.symm.trans leftValue))).elim
      | true => rfl

/-- A word is zero if all of its MSB-first logical bits are false. -/
theorem word_eq_zero_of_all_testBit_eq_false {width : Nat} (word : Word width)
    (zeroBits : ∀ column, testBit word column = false) :
    word = 0 := by
  apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
  intro physical
  simpa [testBit] using zeroBits (Fin.rev physical)

/-- A zero GF(2) bit coefficient is represented by a false Boolean bit. -/
theorem testBit_eq_false_of_bitValue_eq_zero {width : Nat}
    (word : Word width) (column : Fin width)
    (valueZero : bitValue word column = 0) :
    testBit word column = false := by
  cases bit : testBit word column with
  | false => rfl
  | true =>
      have valueOne : bitValue word column = 1 :=
        bitValue_eq_one_of_testBit_eq_true word column bit
      exact ((by decide : (1 : F2) ≠ 0) (valueOne.symm.trans valueZero)).elim

/-- The free-column mask is zero exactly when the ordered free-column list is
empty. -/
theorem freeColumnMask_eq_zero_iff_freeColumns_eq_nil {rowCount width : Nat}
    (result : Result rowCount width) :
    freeColumnMask result = 0 ↔ freeColumns result = [] := by
  constructor
  · intro maskZero
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro column member
    have lookup : pivotForColumn? result column = none :=
      (mem_freeColumns_iff result column).mp member
    have bitTrue : testBit (freeColumnMask result) column = true :=
      (testBit_freeColumnMask_eq_true_iff result column).mpr lookup
    have bitFalse : testBit (freeColumnMask result) column = false := by
      rw [maskZero]
      simp [testBit]
    exact ((by decide : (true : Bool) ≠ false)
      (bitTrue.symm.trans bitFalse)).elim
  · intro noFree
    apply word_eq_zero_of_all_testBit_eq_false
    intro column
    have noMember : column ∉ freeColumns result := by
      simp [noFree]
    have noLookup : pivotForColumn? result column ≠ none := by
      intro lookup
      exact noMember ((mem_freeColumns_iff result column).mpr lookup)
    rw [testBit_freeColumnMask]
    simp [noLookup]

/-- Under a one-free-column result, the free-column mask has exactly that
one logical bit set. -/
theorem testBit_freeColumnMask_of_soleFreeColumn {rowCount width : Nat}
    {result : Result rowCount width} {free : Fin width}
    (choice : soleFreeColumn? result = some free) (column : Fin width) :
    testBit (freeColumnMask result) column = decide (column = free) := by
  rw [testBit_freeColumnMask]
  by_cases same : column = free
  · subst column
    rw [soleFreeColumn_lookup_none choice]
    simp
  · rcases exists_pivotForColumn_of_soleFreeColumn choice same with
      ⟨pivot, lookup⟩
    simp [lookup, same]

/-- Under a sole-free-column decision, back substitution is exactly the initial
free-column mask OR the coefficient selected by the pivot lookup. -/
theorem testBit_backSubstitute_eq_freeMask_or_lookup
    {rowCount width : Nat} {result : Result rowCount width}
    {free : Fin width} (choice : soleFreeColumn? result = some free)
    (column : Fin width) :
    testBit (backSubstitute result free) column =
      (testBit (freeColumnMask result) column ||
        match pivotForColumn? result column with
        | none => false
        | some pivot => testBit (result.reduced pivot.row) free) := by
  rw [testBit_backSubstitute, testBit_freeColumnMask_of_soleFreeColumn choice]
  by_cases same : column = free <;> simp [backSubstituteBit, same]

/-- A sole free column makes the canonical free-column mask exactly the
one-hot logical word at that coordinate. -/
theorem freeColumnMask_eq_wordOfLogicalBits_of_soleFreeColumn
    {rowCount width : Nat} {result : Result rowCount width}
    {free : Fin width} (choice : soleFreeColumn? result = some free) :
    freeColumnMask result =
      wordOfLogicalBits (fun column => decide (column = free)) := by
  apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
  intro physical
  have logical :
      testBit (freeColumnMask result) (Fin.rev physical) =
        testBit
          (wordOfLogicalBits (fun column : Fin width => decide (column = free)))
          (Fin.rev physical) := by
    rw [testBit_freeColumnMask_of_soleFreeColumn choice]
    simp
  have revRev : (Fin.rev (Fin.rev physical)).val = physical.val :=
    congrArg Fin.val (Fin.rev_rev physical)
  rw [← revRev]
  exact logical

/-- The sole free coordinate is set in the canonical free-column mask. -/
theorem testBit_freeColumnMask_free_of_soleFreeColumn
    {rowCount width : Nat} {result : Result rowCount width}
    {free : Fin width} (choice : soleFreeColumn? result = some free) :
    testBit (freeColumnMask result) free = true := by
  rw [testBit_freeColumnMask_of_soleFreeColumn choice]
  simp

/-- Every coordinate other than the sole free column is clear in the
canonical free-column mask. -/
theorem testBit_freeColumnMask_other_of_soleFreeColumn
    {rowCount width : Nat} {result : Result rowCount width}
    {free : Fin width} (choice : soleFreeColumn? result = some free)
    (column : Fin width) (different : column ≠ free) :
    testBit (freeColumnMask result) column = false := by
  rw [testBit_freeColumnMask_of_soleFreeColumn choice]
  simp [different]

/-- A one-free-column result has a nonzero free-column mask. -/
theorem freeColumnMask_ne_zero_of_soleFreeColumn {rowCount width : Nat}
    {result : Result rowCount width} {free : Fin width}
    (choice : soleFreeColumn? result = some free) :
    freeColumnMask result ≠ 0 := by
  intro maskZero
  have noFree : freeColumns result = [] :=
    (freeColumnMask_eq_zero_iff_freeColumns_eq_nil result).mp maskZero
  have singleton : freeColumns result = [free] :=
    freeColumns_eq_singleton_of_soleFreeColumn choice
  rw [singleton] at noFree
  simp at noFree

/-- The logical one-hot word at `free` has its unique physical bit at the
finite reversal of that MSB-first coordinate. -/
theorem wordOfLogicalBits_singleton_val {width : Nat} (free : Fin width) :
    (wordOfLogicalBits (fun column => decide (column = free))).val =
      2 ^ (Fin.rev free).val := by
  let power : Word width :=
    ⟨2 ^ (Fin.rev free).val,
      Nat.pow_lt_pow_right (by decide : 1 < 2) (Fin.rev free).isLt⟩
  have wordEq :
      wordOfLogicalBits (fun column => decide (column = free)) = power := by
    apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
    intro physical
    have assembled := testBit_wordOfLogicalBits
      (fun column : Fin width => decide (column = free)) (Fin.rev physical)
    change
      (wordOfLogicalBits
        (fun column : Fin width => decide (column = free))).val.testBit
          (Fin.rev (Fin.rev physical)).val =
        decide (Fin.rev physical = free) at assembled
    rw [Fin.rev_rev] at assembled
    calc
      (wordOfLogicalBits
          (fun column : Fin width => decide (column = free))).val.testBit
            physical.val =
          decide (Fin.rev physical = free) := assembled
      _ = (2 ^ (Fin.rev free).val).testBit physical.val := by
        rw [Nat.testBit_two_pow]
        by_cases same : Fin.rev physical = free
        · subst free
          simp
        · have exponentNe : (Fin.rev free).val ≠ physical.val := by
            intro exponentEq
            have reversed : Fin.rev free = physical := Fin.ext exponentEq
            have restored := congrArg Fin.rev reversed
            apply same
            have restoredEq : free = Fin.rev physical := by
              simpa using restored
            exact restoredEq.symm
          have exponentNeVal :
              width - (free.val + 1) ≠ physical.val := by
            simpa only [Fin.val_rev] using exponentNe
          simp [same, exponentNeVal]
      _ = power.val.testBit physical.val := rfl
  simpa [power] using congrArg Fin.val wordEq

/-- A selected sole free column gives the exact physical power-of-two value of
the canonical free-column mask. -/
theorem freeColumnMask_val_eq_twoPow_of_soleFreeColumn
    {rowCount width : Nat} {result : Result rowCount width}
    {free : Fin width} (choice : soleFreeColumn? result = some free) :
    (freeColumnMask result).val = 2 ^ (Fin.rev free).val := by
  rw [freeColumnMask_eq_wordOfLogicalBits_of_soleFreeColumn choice,
    wordOfLogicalBits_singleton_val]

/-- AND with a sole-free-column mask is zero exactly when the corresponding
MSB-first logical row bit is false. -/
theorem land_freeColumnMask_eq_zero_iff_testBit_eq_false
    {rowCount width : Nat} {result : Result rowCount width}
    {free : Fin width} (choice : soleFreeColumn? result = some free)
    (row : Word width) :
    row.val &&& (freeColumnMask result).val = 0 ↔ testBit row free = false := by
  rw [freeColumnMask_val_eq_twoPow_of_soleFreeColumn choice, Nat.and_two_pow]
  change
    (row.val.testBit (Fin.rev free).val).toNat * 2 ^ (Fin.rev free).val = 0 ↔
      row.val.testBit (Fin.rev free).val = false
  cases bit : row.val.testBit (Fin.rev free).val <;> simp

/-- AND with a sole-free-column mask is nonzero exactly when the corresponding
MSB-first logical row bit is true. -/
theorem land_freeColumnMask_ne_zero_iff_testBit_eq_true
    {rowCount width : Nat} {result : Result rowCount width}
    {free : Fin width} (choice : soleFreeColumn? result = some free)
    (row : Word width) :
    row.val &&& (freeColumnMask result).val ≠ 0 ↔ testBit row free = true := by
  have zeroIff := land_freeColumnMask_eq_zero_iff_testBit_eq_false choice row
  constructor
  · intro nonzero
    cases bit : testBit row free with
    | false => exact (nonzero (zeroIff.mpr bit)).elim
    | true => rfl
  · intro bitTrue zero
    have bitFalse := zeroIff.mp zero
    rw [bitTrue] at bitFalse
    simp at bitFalse

/-- Conversely, a power-of-two free-column mask value determines a genuine
sole free logical coordinate. -/
theorem exists_soleFreeColumn_of_freeColumnMask_val_eq_twoPow
    {rowCount width : Nat} (result : Result rowCount width) {exponent : Nat}
    (power : (freeColumnMask result).val = 2 ^ exponent) :
    ∃ free, soleFreeColumn? result = some free := by
  have powerLt : 2 ^ exponent < 2 ^ width := by
    rw [← power]
    exact (freeColumnMask result).isLt
  have exponentLt : exponent < width :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp powerLt
  let physical : Fin width := ⟨exponent, exponentLt⟩
  let free : Fin width := Fin.rev physical
  have allFreeEq :
      ∀ column, column ∈ freeColumns result → column = free := by
    intro column member
    have bitTrue : testBit (freeColumnMask result) column = true :=
      (testBit_freeColumnMask_eq_true_iff_mem_freeColumns result column).2 member
    have powerBit :
        (2 ^ exponent).testBit (Fin.rev column).val = true := by
      change (freeColumnMask result).val.testBit (Fin.rev column).val = true at bitTrue
      rw [power] at bitTrue
      exact bitTrue
    have physicalValue : (Fin.rev column).val = exponent := by
      rw [Nat.testBit_two_pow] at powerBit
      simp only [decide_eq_true_eq] at powerBit
      omega
    have reversed : Fin.rev column = physical := by
      apply Fin.ext
      exact physicalValue
    calc
      column = Fin.rev (Fin.rev column) := (Fin.rev_rev column).symm
      _ = Fin.rev physical := congrArg Fin.rev reversed
      _ = free := rfl
  have maskNonzero : freeColumnMask result ≠ 0 := by
    intro maskZero
    have valueZero : (freeColumnMask result).val = 0 :=
      congrArg Fin.val maskZero
    rw [power] at valueZero
    have positive := Nat.two_pow_pos exponent
    omega
  have columnsNonempty : freeColumns result ≠ [] := by
    intro columnsEmpty
    exact maskNonzero
      ((freeColumnMask_eq_zero_iff_freeColumns_eq_nil result).2 columnsEmpty)
  cases columnsEq : freeColumns result with
  | nil =>
      exact (columnsNonempty columnsEq).elim
  | cons first rest =>
      have firstMember : first ∈ freeColumns result := by
        rw [columnsEq]
        simp
      have firstEq : first = free := allFreeEq first firstMember
      have restEmpty : rest = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro column member
        have columnMember : column ∈ freeColumns result := by
          rw [columnsEq]
          exact List.mem_cons_of_mem first member
        have columnEq : column = free := allFreeEq column columnMember
        have same : column = first := columnEq.trans firstEq.symm
        have firstInRest : first ∈ rest := by
          rw [← same]
          exact member
        have nodup := freeColumns_nodup result
        rw [columnsEq] at nodup
        exact (List.nodup_cons.mp nodup).1 firstInRest
      have singleton : freeColumns result = [free] := by
        rw [columnsEq, restEmpty, firstEq]
      exact ⟨free, by simp [soleFreeColumn?, singleton]⟩

/-- A natural has exactly one set bit precisely when it is a power of two. -/
private theorem exactOneBit_iff_exists_twoPow (value : Nat) :
    value ≠ 0 ∧ value &&& (value - 1) = 0 ↔ ∃ exponent, value = 2 ^ exponent := by
  induction value using Nat.binaryRec with
  | zero =>
      constructor
      · rintro ⟨nonzero, _⟩
        exact (nonzero rfl).elim
      · rintro ⟨exponent, impossible⟩
        have positive : 0 < 2 ^ exponent := Nat.two_pow_pos exponent
        omega
  | bit bit rest inductionHypothesis =>
      cases bit with
      | false =>
          simp only [Nat.bit_false]
          constructor
          · rintro ⟨nonzero, cleared⟩
            have restNonzero : rest ≠ 0 := by omega
            have landEq : (2 * rest) &&& (2 * rest - 1) =
                2 * (rest &&& (rest - 1)) := by
              change Nat.bit false rest &&& (Nat.bit false rest - 1) =
                2 * (rest &&& (rest - 1))
              rw [show Nat.bit false rest - 1 = Nat.bit true (rest - 1) by
                simp [Nat.bit]
                omega]
              rw [Nat.land_bit]
              simp [Nat.bit]
            have inner : rest &&& (rest - 1) = 0 := by
              rw [landEq] at cleared
              omega
            rcases inductionHypothesis.mp ⟨restNonzero, inner⟩ with
              ⟨exponent, rfl⟩
            exact ⟨exponent + 1, by simp [pow_succ, Nat.mul_comm]⟩
          · rintro ⟨exponent, power⟩
            cases exponent with
            | zero => simp at power
            | succ exponent =>
                have restPower : rest = 2 ^ exponent := by
                  rw [pow_succ] at power
                  omega
                subst rest
                have landEq : (2 * 2 ^ exponent) &&& (2 * 2 ^ exponent - 1) =
                    2 * (2 ^ exponent &&& (2 ^ exponent - 1)) := by
                  change Nat.bit false (2 ^ exponent) &&&
                      (Nat.bit false (2 ^ exponent) - 1) =
                    2 * (2 ^ exponent &&& (2 ^ exponent - 1))
                  rw [show Nat.bit false (2 ^ exponent) - 1 =
                      Nat.bit true (2 ^ exponent - 1) by
                    simp [Nat.bit]
                    have positive : 0 < 2 ^ exponent := Nat.two_pow_pos exponent
                    omega]
                  rw [Nat.land_bit]
                  simp [Nat.bit]
                constructor
                · simp
                · rw [landEq]
                  rw [(inductionHypothesis.mpr ⟨exponent, rfl⟩).2]
      | true =>
          simp only [Nat.bit_true]
          have landEq : (2 * rest + 1) &&& (2 * rest + 1 - 1) = 2 * rest := by
            change Nat.bit true rest &&& (Nat.bit true rest - 1) = 2 * rest
            rw [show Nat.bit true rest - 1 = Nat.bit false rest by simp [Nat.bit]]
            rw [Nat.land_bit]
            simp [Nat.bit]
          constructor
          · rintro ⟨_nonzero, cleared⟩
            have restZero : rest = 0 := by
              rw [landEq] at cleared
              omega
            subst rest
            exact ⟨0, by simp⟩
          · rintro ⟨exponent, power⟩
            cases exponent with
            | zero =>
                have restZero : rest = 0 := by simpa using power
                subst rest
                simp
            | succ exponent =>
                rw [pow_succ] at power
                omega

/-- The canonical free-column mask has exactly one set bit precisely when the
reducer exposes a sole free logical coordinate. -/
theorem freeColumnMask_singleBit_iff_exists_soleFreeColumn
    {rowCount width : Nat} (result : Result rowCount width) :
    freeColumnMask result ≠ 0 ∧
        (freeColumnMask result).val &&& ((freeColumnMask result).val - 1) = 0 ↔
      ∃ free, soleFreeColumn? result = some free := by
  constructor
  · rintro ⟨maskNonzero, cleared⟩
    have valueNonzero : (freeColumnMask result).val ≠ 0 := by
      intro valueZero
      apply maskNonzero
      apply Fin.ext
      exact valueZero
    rcases (exactOneBit_iff_exists_twoPow (freeColumnMask result).val).mp
        ⟨valueNonzero, cleared⟩ with ⟨exponent, power⟩
    exact exists_soleFreeColumn_of_freeColumnMask_val_eq_twoPow result power
  · rintro ⟨free, choice⟩
    have power : (freeColumnMask result).val = 2 ^ (Fin.rev free).val :=
      freeColumnMask_val_eq_twoPow_of_soleFreeColumn choice
    have singleBit :=
      (exactOneBit_iff_exists_twoPow (freeColumnMask result).val).mpr
        ⟨(Fin.rev free).val, power⟩
    refine ⟨?_, singleBit.2⟩
    intro maskZero
    apply singleBit.1
    exact congrArg Fin.val maskZero

/-- If every summand except a distinguished coordinate is zero, the finite sum
is exactly that distinguished summand. -/
theorem sum_eq_pivot_of_all_other_zero {width : Nat} (term : Fin width → F2)
    (pivot : Fin width)
    (zeroOther : ∀ column, column ≠ pivot → term column = 0) :
    (∑ column, term column) = term pivot := by
  classical
  have remainingZero :
      ∀ column ∈ Finset.univ.erase pivot, term column = 0 := by
    intro column member
    exact zeroOther column (Finset.mem_erase.mp member).1
  calc
    (∑ column, term column) =
        term pivot + (∑ column ∈ Finset.univ.erase pivot, term column) :=
      (Finset.add_sum_erase Finset.univ term (Finset.mem_univ pivot)).symm
    _ = term pivot := by rw [Finset.sum_eq_zero remainingZero, add_zero]

/-- If the reducer reports no free coordinate, every logical coordinate has a
recorded pivot lookup. -/
theorem exists_pivotForColumn_of_freeColumns_eq_nil {rowCount width : Nat}
    (samples : Samples rowCount width)
    (noFree : freeColumns (reduce samples) = []) (column : Fin width) :
    ∃ pivot, pivotForColumn? (reduce samples) column = some pivot := by
  cases lookup : pivotForColumn? (reduce samples) column with
  | none =>
      have member : column ∈ freeColumns (reduce samples) :=
        (mem_freeColumns_iff (reduce samples) column).mpr lookup
      rw [noFree] at member
      simp at member
  | some pivot => exact ⟨pivot, rfl⟩

/-- With no free column, a reduced pivot-row equation is exactly its candidate
pivot-coordinate coefficient. -/
theorem dot_reduce_pivotRow_eq_candidateBit_of_freeColumns_eq_nil
    {rowCount width : Nat} (samples : Samples rowCount width)
    (noFree : freeColumns (reduce samples) = [])
    {pivot : Pivot rowCount width}
    (pivotMember : pivot ∈ (reduce samples).pivots)
    (candidate : Word width) :
    dot ((reduce samples).reduced pivot.row) candidate =
      bitValue candidate pivot.column := by
  have pivotBit :
      testBit ((reduce samples).reduced pivot.row) pivot.column = true := by
    simpa using reduce_pivotColumn_unit samples pivot pivotMember pivot.row
  unfold dot
  calc
    (∑ column, bitValue ((reduce samples).reduced pivot.row) column *
        bitValue candidate column) =
        bitValue ((reduce samples).reduced pivot.row) pivot.column *
          bitValue candidate pivot.column :=
      sum_eq_pivot_of_all_other_zero _ pivot.column (fun column columnNePivot => by
        rcases exists_pivotForColumn_of_freeColumns_eq_nil samples noFree column with
          ⟨other, lookup⟩
        have otherMember : other ∈ (reduce samples).pivots :=
          pivotForColumn?_some_mem lookup
        have otherColumn : other.column = column :=
          pivotForColumn?_some_column lookup
        have otherNePivot : other.column ≠ pivot.column := by
          intro same
          apply columnNePivot
          exact otherColumn.symm.trans same
        have rowZero :
            testBit ((reduce samples).reduced pivot.row) other.column = false :=
          reduce_pivotRow_other_pivotColumn_eq_false samples pivotMember otherMember
            otherNePivot
        have rowZeroAtColumn :
            testBit ((reduce samples).reduced pivot.row) column = false := by
          rw [← otherColumn]
          exact rowZero
        rw [bitValue_eq_zero_of_testBit_eq_false
          ((reduce samples).reduced pivot.row) column rowZeroAtColumn, zero_mul])
    _ = bitValue candidate pivot.column := by
      rw [bitValue_eq_one_of_testBit_eq_true
        ((reduce samples).reduced pivot.row) pivot.column pivotBit, one_mul]

/-- If there is no free column, the original system has only the zero kernel
word. -/
theorem candidate_eq_zero_of_freeColumns_eq_nil {rowCount width : Nat}
    (samples : Samples rowCount width)
    (noFree : freeColumns (reduce samples) = [])
    (candidate : Word width) (candidateSatisfies : satisfies samples candidate) :
    candidate = 0 := by
  have reducedSatisfies : satisfies (reduce samples).reduced candidate :=
    (reduce_kernel_equiv samples candidate).mp candidateSatisfies
  apply word_eq_zero_of_all_testBit_eq_false
  intro column
  rcases exists_pivotForColumn_of_freeColumns_eq_nil samples noFree column with
    ⟨pivot, lookup⟩
  have pivotMember : pivot ∈ (reduce samples).pivots :=
    pivotForColumn?_some_mem lookup
  have pivotColumn : pivot.column = column :=
    pivotForColumn?_some_column lookup
  have equation :
      dot ((reduce samples).reduced pivot.row) candidate = 0 :=
    reducedSatisfies pivot.row
  have dotEq :
      dot ((reduce samples).reduced pivot.row) candidate =
        bitValue candidate pivot.column :=
    dot_reduce_pivotRow_eq_candidateBit_of_freeColumns_eq_nil samples noFree
      pivotMember candidate
  have valueZero : bitValue candidate pivot.column = 0 := by
    rw [← dotEq]
    exact equation
  have bitZero : testBit candidate pivot.column = false :=
    testBit_eq_false_of_bitValue_eq_zero candidate pivot.column valueZero
  rw [← pivotColumn]
  exact bitZero

/-- Back-substitution words for distinct genuine free coordinates are distinct. -/
theorem backSubstitute_ne_of_distinct_freeColumns {rowCount width : Nat}
    (samples : Samples rowCount width) {left right : Fin width}
    (leftMember : left ∈ freeColumns (reduce samples))
    (different : left ≠ right) :
    backSubstitute (reduce samples) left ≠
      backSubstitute (reduce samples) right := by
  have leftLookup : pivotForColumn? (reduce samples) left = none :=
    (mem_freeColumns_iff (reduce samples) left).mp leftMember
  have rightAtLeft :
      testBit (backSubstitute (reduce samples) right) left = false :=
    testBit_backSubstitute_of_lookup_none (reduce samples) right left different leftLookup
  intro same
  have leftAtLeft :
      testBit (backSubstitute (reduce samples) left) left = true :=
    testBit_backSubstitute_free (reduce samples) left
  rw [same, rightAtLeft] at leftAtLeft
  simp at leftAtLeft

/-- A semantic unique nonzero solution forces the actual reducer to expose one
and only one free coordinate. -/
theorem exists_soleFreeColumn_of_unique {rowCount width : Nat}
    (samples : Samples rowCount width) (expected : Word width)
    (unique : HasUniqueNonzeroSolution samples expected) :
    ∃ free, soleFreeColumn? (reduce samples) = some free := by
  cases hfree : freeColumns (reduce samples) with
  | nil =>
      have expectedZero := candidate_eq_zero_of_freeColumns_eq_nil samples hfree
        expected unique.2.1
      exact (unique.1 expectedZero).elim
  | cons first rest =>
      cases rest with
      | nil =>
          exact ⟨first, by simp [soleFreeColumn?, hfree]⟩
      | cons second tail =>
          have nodup : (freeColumns (reduce samples)).Nodup :=
            freeColumns_nodup (reduce samples)
          rw [hfree] at nodup
          have different : first ≠ second := by
            intro same
            exact (List.nodup_cons.mp nodup).1 (by simp [same])
          have firstMember : first ∈ freeColumns (reduce samples) := by
            rw [hfree]
            simp
          have secondMember : second ∈ freeColumns (reduce samples) := by
            rw [hfree]
            simp
          have firstSound := backSubstitute_sound_of_mem_freeColumns samples first firstMember
          have secondSound := backSubstitute_sound_of_mem_freeColumns samples second secondMember
          have firstEq : backSubstitute (reduce samples) first = expected :=
            unique.2.2 _ firstSound.1 firstSound.2
          have secondEq : backSubstitute (reduce samples) second = expected :=
            unique.2.2 _ secondSound.1 secondSound.2
          have differentWords := backSubstitute_ne_of_distinct_freeColumns samples
            firstMember different
          exact (differentWords (firstEq.trans secondEq.symm)).elim

/-- A one-free-column decision makes the polynomial recovery path return its
direct back-substitution candidate. -/
theorem recover?_of_soleFreeColumn {rowCount width : Nat}
    (samples : Samples rowCount width) {free : Fin width}
    (choice : soleFreeColumn? (reduce samples) = some free) :
    recover? samples = some (backSubstitute (reduce samples) free) := by
  have freeLookup : pivotForColumn? (reduce samples) free = none :=
    soleFreeColumn_lookup_none choice
  have candidateSatisfies :
      satisfies samples (backSubstitute (reduce samples) free) :=
    backSubstitute_satisfies_of_lookup_none samples free freeLookup
  have candidateNonzero : backSubstitute (reduce samples) free ≠ 0 :=
    backSubstitute_ne_zero (reduce samples) free
  have checked :
      satisfies? samples (backSubstitute (reduce samples) free) = true :=
    (satisfies?_eq_true samples (backSubstitute (reduce samples) free)).mpr
      candidateSatisfies
  simp [recover?, choice, candidateNonzero, checked]

/-- Polynomial recovery is complete for the semantic unique-nonzero-solution
contract, without consulting the exhaustive specification. -/
theorem recover?_complete {rowCount width : Nat}
    (samples : Samples rowCount width) (expected : Word width)
    (unique : HasUniqueNonzeroSolution samples expected) :
    recover? samples = some expected := by
  rcases exists_soleFreeColumn_of_unique samples expected unique with ⟨free, choice⟩
  have output := recover?_of_soleFreeColumn samples choice
  have candidateSound := recover?_sound samples output
  have candidateEq : backSubstitute (reduce samples) free = expected :=
    unique.2.2 _ candidateSound.1 candidateSound.2
  simpa [candidateEq] using output

/-- A successful reduced-row recovery agrees with any semantic unique solution.

The hypothesis is semantic rather than an exhaustive computation: `recover?`
itself is the polynomial reduction/back-substitution program above. -/
theorem recover?_equals_unique {rowCount width : Nat}
    (samples : Samples rowCount width) {recovered expected : Word width}
    (output : recover? samples = some recovered)
    (unique : HasUniqueNonzeroSolution samples expected) :
    recovered = expected := by
  have sound := recover?_sound samples output
  exact unique.2.2 recovered sound.1 sound.2

/-- Semantic uniqueness gives the exact singleton executable candidate list. -/
theorem nonzeroSolutions_eq_singleton {rowCount width : Nat}
    (samples : Samples rowCount width) (candidate : Word width)
    (unique : HasUniqueNonzeroSolution samples candidate) :
    nonzeroSolutions samples = [candidate] := by
  have candidateMember : candidate ∈ nonzeroSolutions samples :=
    mem_nonzeroSolutions samples candidate |>.mpr ⟨unique.1, unique.2.1⟩
  have nodup : (nonzeroSolutions samples).Nodup := nonzeroSolutions_nodup samples
  by_contra notSingleton
  rcases (nodup.ne_singleton_iff candidate).mp notSingleton with empty | otherExists
  · simp [empty] at candidateMember
  · rcases otherExists with ⟨other, otherMember, different⟩
    have otherContract := (mem_nonzeroSolutions samples other).mp otherMember
    exact different (unique.2.2 other otherContract.1 otherContract.2)

/-- Finite specification: return the candidate exactly when enumeration finds
one nonzero solution. -/
def uniqueNonzero? {rowCount width : Nat}
    (samples : Samples rowCount width) : Option (Word width) :=
  match nonzeroSolutions samples with
  | candidate :: [] => some candidate
  | _ => none

/-- A successful result means that the candidate list was exactly a singleton. -/
theorem uniqueNonzero?_some_exact {rowCount width : Nat}
    (samples : Samples rowCount width) {candidate : Word width}
    (output : uniqueNonzero? samples = some candidate) :
    nonzeroSolutions samples = [candidate] := by
  cases hsolutions : nonzeroSolutions samples with
  | nil => simp [uniqueNonzero?, hsolutions] at output
  | cons head tail =>
      cases tail with
      | nil =>
          have hsome : some head = some candidate := by
            simpa [uniqueNonzero?, hsolutions] using output
          cases hsome
          rfl
      | cons next tail => simp [uniqueNonzero?, hsolutions] at output

/-- Every successful result is nonzero and satisfies all original equations. -/
theorem uniqueNonzero?_sound {rowCount width : Nat}
    (samples : Samples rowCount width) {candidate : Word width}
    (output : uniqueNonzero? samples = some candidate) :
    candidate ≠ 0 ∧ satisfies samples candidate := by
  have member : candidate ∈ nonzeroSolutions samples := by
    rw [uniqueNonzero?_some_exact samples output]
    simp
  exact (mem_nonzeroSolutions samples candidate).mp member

/-- Every successful result is the unique nonzero solution. -/
theorem uniqueNonzero?_some_unique {rowCount width : Nat}
    (samples : Samples rowCount width) {candidate : Word width}
    (output : uniqueNonzero? samples = some candidate) :
    HasUniqueNonzeroSolution samples candidate := by
  have sound := uniqueNonzero?_sound samples output
  refine ⟨sound.1, sound.2, ?_⟩
  intro other otherNonzero otherSatisfies
  have otherMember : other ∈ nonzeroSolutions samples :=
    (mem_nonzeroSolutions samples other).mpr ⟨otherNonzero, otherSatisfies⟩
  rw [uniqueNonzero?_some_exact samples output] at otherMember
  simpa using otherMember

/-- A semantic unique nonzero solution is returned by finite enumeration. -/
theorem uniqueNonzero?_complete {rowCount width : Nat}
    (samples : Samples rowCount width) (candidate : Word width)
    (unique : HasUniqueNonzeroSolution samples candidate) :
    uniqueNonzero? samples = some candidate := by
  unfold uniqueNonzero?
  rw [nonzeroSolutions_eq_singleton samples candidate unique]

/-- Failure is equivalent to the absence of any unique nonzero solution. -/
theorem uniqueNonzero?_none_iff {rowCount width : Nat}
    (samples : Samples rowCount width) :
    uniqueNonzero? samples = none ↔
      ∀ candidate, ¬ HasUniqueNonzeroSolution samples candidate := by
  constructor
  · intro noCandidate candidate unique
    have returned := uniqueNonzero?_complete samples candidate unique
    rw [noCandidate] at returned
    simp at returned
  · intro noUnique
    cases choice : uniqueNonzero? samples with
    | none => rfl
    | some candidate =>
        have success : uniqueNonzero? samples = some candidate := choice
        exact (noUnique candidate (uniqueNonzero?_some_unique samples success)).elim

/-- No nonzero solution forces explicit failure. -/
theorem uniqueNonzero?_none_of_no_nonzero {rowCount width : Nat}
    (samples : Samples rowCount width)
    (noneExists : ∀ candidate, candidate ≠ 0 → ¬ satisfies samples candidate) :
    uniqueNonzero? samples = none := by
  refine (uniqueNonzero?_none_iff samples).mpr ?_
  intro candidate unique
  exact noneExists candidate unique.1 unique.2.1

/-- Two distinct nonzero solutions force explicit failure. -/
theorem uniqueNonzero?_none_of_multiple {rowCount width : Nat}
    (samples : Samples rowCount width)
    (multiple : ∃ first second : Word width,
      first ≠ second ∧ first ≠ 0 ∧ satisfies samples first ∧
        second ≠ 0 ∧ satisfies samples second) :
    uniqueNonzero? samples = none := by
  refine (uniqueNonzero?_none_iff samples).mpr ?_
  intro candidate unique
  rcases multiple with
    ⟨first, second, different, firstNonzero, firstSatisfies,
      secondNonzero, secondSatisfies⟩
  have firstEq := unique.2.2 first firstNonzero firstSatisfies
  have secondEq := unique.2.2 second secondNonzero secondSatisfies
  exact different (firstEq.trans secondEq.symm)

/-- At width zero every fixed-width word is the zero word. -/
theorem word_width_zero_eq_zero (word : Word 0) : word = 0 := by
  apply Fin.ext
  have range : word.val < 1 := by simpa only [pow_zero] using word.isLt
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ range)

/-- Width zero has no nonzero candidate, independently of the row count. -/
theorem uniqueNonzero?_width_zero {rowCount : Nat}
    (samples : Samples rowCount 0) :
    uniqueNonzero? samples = none := by
  apply uniqueNonzero?_none_of_no_nonzero
  intro candidate nonzero
  exact (nonzero (word_width_zero_eq_zero candidate)).elim

/-- Width zero leaves no free coordinate for the polynomial recovery path. -/
theorem recover?_width_zero {rowCount : Nat}
    (samples : Samples rowCount 0) :
    recover? samples = none := by
  rfl

/-- The ordered system with no rows. -/
def noSamples (width : Nat) : Samples 0 width := fun row => Fin.elim0 row

/-- Every candidate satisfies an empty ordered system. -/
theorem satisfies_noSamples (width : Nat) (candidate : Word width) :
    satisfies (noSamples width) candidate := by
  intro row
  exact Fin.elim0 row

/-- One free bit and no rows has the sole nonzero word as its solution. -/
theorem uniqueNonzero?_noSamples_one :
    uniqueNonzero? (noSamples 1) = some (wordOfNat 1 1) := by
  decide

/-- A concrete one-equation, two-bit system whose sole nonzero solution is `3`. -/
def uniqueFixture : Samples 1 2 := fun _row => wordOfNat 2 3

/-- The concrete two-bit fixture has exactly one nonzero solution. -/
theorem uniqueFixture_unique :
    HasUniqueNonzeroSolution uniqueFixture (wordOfNat 2 3) := by
  decide

/-- The unique fixture returns its unique nonzero solution. -/
theorem uniqueNonzero?_uniqueFixture :
    uniqueNonzero? uniqueFixture = some (wordOfNat 2 3) :=
  uniqueNonzero?_complete uniqueFixture (wordOfNat 2 3) uniqueFixture_unique

/-- The empty two-bit system has at least two distinct nonzero solutions. -/
theorem noSamples_two_multiple :
    ∃ first second : Word 2,
      first ≠ second ∧ first ≠ 0 ∧ satisfies (noSamples 2) first ∧
        second ≠ 0 ∧ satisfies (noSamples 2) second := by
  refine ⟨wordOfNat 2 1, wordOfNat 2 2, by decide, by decide,
    satisfies_noSamples 2 (wordOfNat 2 1), by decide,
    satisfies_noSamples 2 (wordOfNat 2 2)⟩

/-- The empty two-bit system exercises the explicit ambiguous-result branch. -/
theorem uniqueNonzero?_noSamples_two :
    uniqueNonzero? (noSamples 2) = none :=
  uniqueNonzero?_none_of_multiple (noSamples 2) noSamples_two_multiple

end GF2

end ClassicalAlgorithms
end QuantumAlg

end
