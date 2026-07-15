/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.Arithmetic.BitSlice
public import Mathlib.Data.List.TakeDrop

/-!
# Borrow-chain comparator schedule shells

This module assembles local subtract-borrow bit slices into reusable schedule
shells for future word-comparison circuits. It deliberately stops at folded
`BaseGateProgram` and bit-lens endpoint facts; the word-level comparator
invariant is supplied by downstream modules that instantiate a concrete layout.
-/

@[expose] public section

namespace QuantumAlg
namespace Comparator

noncomputable section

variable {Carrier : Type} {encoding : BinaryLabelEncoding Carrier}

/-- Boolean borrow sequence for natural-number subtraction, ordered from least
significant to most significant bit. -/
def natSubBorrow (a b : Nat) (borrow0 : Bool) : Nat -> Bool
  | 0 => borrow0
  | i + 1 =>
      Bool.carry (!(a.testBit i)) (b.testBit i)
        (natSubBorrow a b borrow0 i)

/-- Natural subtract-borrow recurrence with a clean incoming borrow. -/
def natBorrow (a b : Nat) : Nat -> Bool :=
  natSubBorrow a b false

/-- Low-bit decomposition for the next power-of-two prefix. -/
theorem mod_two_pow_succ_decomp (x i : Nat) :
    x % 2 ^ (i + 1) =
      x % 2 ^ i + (x.testBit i).toNat * 2 ^ i := by
  rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]

/-- The clean subtract-borrow recurrence computes comparison of the low `n`
bits of the two natural numbers. -/
theorem natBorrow_eq_decide_mod_lt (a b n : Nat) :
    natBorrow a b n = decide (a % 2 ^ n < b % 2 ^ n) := by
  induction n with
  | zero =>
      simp [natBorrow, natSubBorrow]
      omega
  | succ n ih =>
      change
        Bool.carry (!(a.testBit n)) (b.testBit n)
            (natSubBorrow a b false n) =
          decide (a % 2 ^ (n + 1) < b % 2 ^ (n + 1))
      rw [show natSubBorrow a b false n = natBorrow a b n by rfl]
      rw [ih]
      rw [mod_two_pow_succ_decomp a n, mod_two_pow_succ_decomp b n]
      have haLow : a % 2 ^ n < 2 ^ n :=
        Nat.mod_lt a (Nat.two_pow_pos n)
      have hbLow : b % 2 ^ n < 2 ^ n :=
        Nat.mod_lt b (Nat.two_pow_pos n)
      cases a.testBit n <;>
        cases b.testBit n <;>
        simp [Bool.carry] <;> omega

/-- Within an `n`-bit range, the clean subtract-borrow endpoint is the ordinary
natural-number comparison. -/
theorem natBorrow_eq_decide_lt_of_lt_two_pow
    {a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    natBorrow a b n = decide (a < b) := by
  rw [natBorrow_eq_decide_mod_lt]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- Concatenate staged encoded-bit gate lists while preserving stage order. -/
def concatStages (stages : List (List (EncodedBit.GateSpec encoding))) :
    List (EncodedBit.GateSpec encoding) :=
  stages.foldr (fun gates rest => gates ++ rest) []

/-- The semantic action of concatenated stages is the left-to-right fold of
the individual stage actions. -/
theorem stepList_concatStages
    (stages : List (List (EncodedBit.GateSpec encoding))) (x : Carrier) :
    EncodedBit.GateSpec.stepList (concatStages stages) x =
      stages.foldl
        (fun y gates => EncodedBit.GateSpec.stepList gates y) x := by
  induction stages generalizing x with
  | nil =>
      rfl
  | cons gates rest ih =>
      change
        EncodedBit.GateSpec.stepList (gates ++ concatStages rest) x =
          rest.foldl
            (fun y gates => EncodedBit.GateSpec.stepList gates y)
            (EncodedBit.GateSpec.stepList gates x)
      rw [EncodedBit.GateSpec.stepList_append]
      exact ih (EncodedBit.GateSpec.stepList gates x)

/-- If every stage is disjoint from an observed bit, then the concatenated
stage list is disjoint from that observed bit. -/
theorem concatStages_bitDisjoint
    (stages : List (List (EncodedBit.GateSpec encoding)))
    (observed : EncodedBit encoding)
    (h :
      ∀ gates, gates ∈ stages ->
        ∀ gate, gate ∈ gates ->
          EncodedBit.GateSpec.bitDisjoint observed gate) :
    ∀ gate, gate ∈ concatStages stages ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  induction stages with
  | nil =>
      intro gate hmem
      change gate ∈ ([] : List (EncodedBit.GateSpec encoding)) at hmem
      cases hmem
  | cons gates rest ih =>
      intro gate hmem
      change gate ∈ gates ++ concatStages rest at hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact h gates (by simp) gate hmem
      · exact ih
          (by
            intro next hnext
            exact h next (by simp [hnext]))
          gate hmem

/-- Wire layout for a subtract-borrow chain comparing two encoded words. -/
structure BorrowWorkLayout (n : Nat) where
  /-- Input word used as the subtract-borrow minuend. -/
  minuend : EncodedBit.Word encoding n
  /-- Input word used as the subtract-borrow subtrahend. -/
  subtrahend : EncodedBit.Word encoding n
  /-- Clean external borrow input for the least-significant stage. -/
  initialBorrow : EncodedBit encoding
  /-- Work bits that store the borrow output of each stage. -/
  workBorrow : EncodedBit.Word encoding n
  minuendMinuend_ne :
    ∀ i j, i ≠ j → (minuend.bit i).wire ≠ (minuend.bit j).wire
  subtrahendSubtrahend_ne :
    ∀ i j, i ≠ j → (subtrahend.bit i).wire ≠ (subtrahend.bit j).wire
  minuendSubtrahend_ne :
    ∀ i j, (minuend.bit i).wire ≠ (subtrahend.bit j).wire
  minuendInitialBorrow_ne :
    ∀ i, (minuend.bit i).wire ≠ initialBorrow.wire
  subtrahendInitialBorrow_ne :
    ∀ i, (subtrahend.bit i).wire ≠ initialBorrow.wire
  minuendWork_ne :
    ∀ i j, (minuend.bit i).wire ≠ (workBorrow.bit j).wire
  subtrahendWork_ne :
    ∀ i j, (subtrahend.bit i).wire ≠ (workBorrow.bit j).wire
  initialBorrowWork_ne :
    ∀ j, initialBorrow.wire ≠ (workBorrow.bit j).wire
  workWork_ne :
    ∀ i j, i ≠ j → (workBorrow.bit i).wire ≠ (workBorrow.bit j).wire

namespace BorrowWorkLayout

variable {n : Nat} (layout : BorrowWorkLayout (encoding := encoding) n)

/-- Work-borrow index carrying the previous stage's borrow output. -/
@[nolint unusedArguments]
def previousWorkIndex (j : Fin n) (_h : j.val ≠ 0) : Fin n :=
  ⟨j.val - 1, by
    have hj := j.isLt
    omega⟩

@[simp] theorem previousWorkIndex_val (j : Fin n) (h : j.val ≠ 0) :
    (previousWorkIndex j h).val = j.val - 1 :=
  rfl

/-- Borrow input for bit `j`: the clean external input at `0`, then the previous work bit. -/
def borrowInput (j : Fin n) : EncodedBit encoding :=
  if h : j.val = 0 then layout.initialBorrow
  else layout.workBorrow.bit (previousWorkIndex j h)

theorem minuend_borrowInput_ne (j : Fin n) :
    (layout.minuend.bit j).wire ≠ (borrowInput layout j).wire := by
  unfold borrowInput
  by_cases h : j.val = 0
  · simpa [h] using layout.minuendInitialBorrow_ne j
  · simpa [h] using layout.minuendWork_ne j (previousWorkIndex j h)

theorem subtrahend_borrowInput_ne (j : Fin n) :
    (layout.subtrahend.bit j).wire ≠ (borrowInput layout j).wire := by
  unfold borrowInput
  by_cases h : j.val = 0
  · simpa [h] using layout.subtrahendInitialBorrow_ne j
  · simpa [h] using layout.subtrahendWork_ne j (previousWorkIndex j h)

theorem borrowInput_work_ne (j : Fin n) :
    (borrowInput layout j).wire ≠ (layout.workBorrow.bit j).wire := by
  unfold borrowInput
  by_cases h : j.val = 0
  · simpa [h] using layout.initialBorrowWork_ne j
  · have hprev : previousWorkIndex j h ≠ j := by
      intro hp
      have hv := congrArg Fin.val hp
      dsimp [previousWorkIndex] at hv
      omega
    simpa [h] using layout.workWork_ne (previousWorkIndex j h) j hprev

/-- Gate list computing one borrow-output bit into the work-borrow word. -/
def borrowOutGatesAt (j : Fin n) :
    List (EncodedBit.GateSpec encoding) :=
  BitSlice.Encoded.borrowOutGates
    (layout.minuend.bit j) (layout.subtrahend.bit j)
    (borrowInput layout j) (layout.workBorrow.bit j)
    (layout.minuendSubtrahend_ne j j)
    (minuend_borrowInput_ne layout j)
    (layout.minuendWork_ne j j)
    (subtrahend_borrowInput_ne layout j)
    (layout.subtrahendWork_ne j j)
    (borrowInput_work_ne layout j)

/-- A local borrow-output stage is disjoint from an observed bit when all of
its participating wires are disjoint from that bit. -/
theorem borrowOutGatesAt_bitDisjoint
    (j : Fin n) (observed : EncodedBit encoding)
    (hminuend : (layout.minuend.bit j).wire ≠ observed.wire)
    (hsubtrahend : (layout.subtrahend.bit j).wire ≠ observed.wire)
    (hborrowInput : (borrowInput layout j).wire ≠ observed.wire)
    (hwork : (layout.workBorrow.bit j).wire ≠ observed.wire) :
    ∀ gate, gate ∈ borrowOutGatesAt layout j ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  simpa [borrowOutGatesAt] using
    BitSlice.Encoded.borrowOutGates_bitDisjoint
      (layout.minuend.bit j) (layout.subtrahend.bit j)
      (borrowInput layout j) (layout.workBorrow.bit j) observed
      (layout.minuendSubtrahend_ne j j)
      (minuend_borrowInput_ne layout j)
      (layout.minuendWork_ne j j)
      (subtrahend_borrowInput_ne layout j)
      (layout.subtrahendWork_ne j j)
      (borrowInput_work_ne layout j)
      hminuend hsubtrahend hborrowInput hwork

/-- Base-gate program computing the borrow output for stage `j`. -/
def borrowOutProgramAt (j : Fin n) : BaseGateProgram encoding.width :=
  EncodedBit.GateSpec.programList (borrowOutGatesAt layout j)

/-- State transformer induced by the borrow-output program at stage `j`. -/
def borrowOutStepAt (j : Fin n) : Carrier → Carrier :=
  EncodedBit.GateSpec.stepList (borrowOutGatesAt layout j)

theorem borrowOut_realizesAt (j : Fin n) :
    BaseGateProgram.Realizes encoding (borrowOutProgramAt layout j)
      (borrowOutStepAt layout j) :=
  EncodedBit.GateSpec.realizesList (borrowOutGatesAt layout j)

/-- Same-circuit witness for the borrow-output stage at bit `j`. -/
def borrowOutSameCircuitAt (j : Fin n) :
    BaseGateSameCircuitWitness Carrier (borrowOutStepAt layout j) where
  encoding := encoding
  program := borrowOutProgramAt layout j
  realizes := borrowOut_realizesAt layout j

theorem borrowOutGatesAt_get_workBorrow_clean
    (j : Fin n) (x : Carrier)
    (hclean : (layout.workBorrow.bit j).get x = false) :
    (layout.workBorrow.bit j).get
        (borrowOutStepAt layout j x) =
      Bool.carry (!(layout.minuend.bit j).get x)
        ((layout.subtrahend.bit j).get x)
        ((borrowInput layout j).get x) := by
  simpa [borrowOutStepAt, borrowOutGatesAt, BitSlice.Encoded.borrowOutStep]
    using BitSlice.Encoded.borrowOutStep_get_borrowOut_clean
      (layout.minuend.bit j) (layout.subtrahend.bit j)
      (borrowInput layout j) (layout.workBorrow.bit j)
      (layout.minuendSubtrahend_ne j j)
      (minuend_borrowInput_ne layout j)
      (layout.minuendWork_ne j j)
      (subtrahend_borrowInput_ne layout j)
      (layout.subtrahendWork_ne j j)
      (borrowInput_work_ne layout j) x hclean

theorem borrowOutGatesAt_get_minuend
    (j : Fin n) (x : Carrier) :
    (layout.minuend.bit j).get (borrowOutStepAt layout j x) =
      (layout.minuend.bit j).get x := by
  simpa [borrowOutStepAt, borrowOutGatesAt, BitSlice.Encoded.borrowOutStep]
    using BitSlice.Encoded.borrowOutStep_get_minuend
      (layout.minuend.bit j) (layout.subtrahend.bit j)
      (borrowInput layout j) (layout.workBorrow.bit j)
      (layout.minuendSubtrahend_ne j j)
      (minuend_borrowInput_ne layout j)
      (layout.minuendWork_ne j j)
      (subtrahend_borrowInput_ne layout j)
      (layout.subtrahendWork_ne j j)
      (borrowInput_work_ne layout j) x

theorem borrowOutGatesAt_get_subtrahend
    (j : Fin n) (x : Carrier) :
    (layout.subtrahend.bit j).get (borrowOutStepAt layout j x) =
      (layout.subtrahend.bit j).get x := by
  simpa [borrowOutStepAt, borrowOutGatesAt, BitSlice.Encoded.borrowOutStep]
    using BitSlice.Encoded.borrowOutStep_get_subtrahend
      (layout.minuend.bit j) (layout.subtrahend.bit j)
      (borrowInput layout j) (layout.workBorrow.bit j)
      (layout.minuendSubtrahend_ne j j)
      (minuend_borrowInput_ne layout j)
      (layout.minuendWork_ne j j)
      (subtrahend_borrowInput_ne layout j)
      (layout.subtrahendWork_ne j j)
      (borrowInput_work_ne layout j) x

theorem borrowOutGatesAt_get_borrowInput
    (j : Fin n) (x : Carrier) :
    (borrowInput layout j).get (borrowOutStepAt layout j x) =
      (borrowInput layout j).get x := by
  simpa [borrowOutStepAt, borrowOutGatesAt, BitSlice.Encoded.borrowOutStep]
    using BitSlice.Encoded.borrowOutStep_get_borrowIn
      (layout.minuend.bit j) (layout.subtrahend.bit j)
      (borrowInput layout j) (layout.workBorrow.bit j)
      (layout.minuendSubtrahend_ne j j)
      (minuend_borrowInput_ne layout j)
      (layout.minuendWork_ne j j)
      (subtrahend_borrowInput_ne layout j)
      (layout.subtrahendWork_ne j j)
      (borrowInput_work_ne layout j) x

/-- A local borrow-output stage preserves any readout whose wire is distinct
from the stage's temporary minuend flip and work-borrow output. -/
theorem borrowOutGatesAt_get_of_minuend_work_ne
    (j : Fin n) (observed : EncodedBit encoding)
    (hminuend : (layout.minuend.bit j).wire ≠ observed.wire)
    (hwork : (layout.workBorrow.bit j).wire ≠ observed.wire) (x : Carrier) :
    observed.get (borrowOutStepAt layout j x) = observed.get x := by
  simpa [borrowOutStepAt, borrowOutGatesAt, BitSlice.Encoded.borrowOutStep]
    using
      BitSlice.Encoded.borrowOutStep_get_of_minuend_borrowOut_ne
        (layout.minuend.bit j) (layout.subtrahend.bit j)
        (borrowInput layout j) (layout.workBorrow.bit j) observed
        (layout.minuendSubtrahend_ne j j)
        (minuend_borrowInput_ne layout j)
        (layout.minuendWork_ne j j)
        (subtrahend_borrowInput_ne layout j)
        (layout.subtrahendWork_ne j j)
        (borrowInput_work_ne layout j)
        hminuend hwork x

/-- A local borrow-output stage preserves any other work-borrow bit. -/
theorem borrowOutGatesAt_get_workBorrow_of_ne
    (j k : Fin n) (hne : j ≠ k) (x : Carrier) :
    (layout.workBorrow.bit k).get (borrowOutStepAt layout j x) =
      (layout.workBorrow.bit k).get x := by
  exact borrowOutGatesAt_get_of_minuend_work_ne layout j
    (layout.workBorrow.bit k) (layout.minuendWork_ne j k)
    (layout.workWork_ne j k hne) x

/-- A local borrow-output stage preserves every minuend readout. -/
theorem borrowOutGatesAt_get_minuend_any
    (j i : Fin n) (x : Carrier) :
    (layout.minuend.bit i).get (borrowOutStepAt layout j x) =
      (layout.minuend.bit i).get x := by
  by_cases hji : j = i
  · simpa [hji] using borrowOutGatesAt_get_minuend layout j x
  · exact borrowOutGatesAt_get_of_minuend_work_ne layout j
      (layout.minuend.bit i) (layout.minuendMinuend_ne j i hji)
      (Ne.symm (layout.minuendWork_ne i j)) x

/-- A local borrow-output stage preserves every subtrahend readout. -/
theorem borrowOutGatesAt_get_subtrahend_any
    (j i : Fin n) (x : Carrier) :
    (layout.subtrahend.bit i).get (borrowOutStepAt layout j x) =
      (layout.subtrahend.bit i).get x := by
  exact borrowOutGatesAt_get_of_minuend_work_ne layout j
    (layout.subtrahend.bit i) (layout.minuendSubtrahend_ne j i)
    (Ne.symm (layout.subtrahendWork_ne i j)) x

/-- A local borrow-output stage preserves the external initial-borrow readout. -/
theorem borrowOutGatesAt_get_initialBorrow
    (j : Fin n) (x : Carrier) :
    layout.initialBorrow.get (borrowOutStepAt layout j x) =
      layout.initialBorrow.get x := by
  exact borrowOutGatesAt_get_of_minuend_work_ne layout j layout.initialBorrow
    (layout.minuendInitialBorrow_ne j)
    (Ne.symm (layout.initialBorrowWork_ne j)) x

/-- Indices used by the forward subtract-borrow stage. -/
def borrowStageIndices : List (Fin n) :=
  List.ofFn fun j : Fin n => j

/-- Indexed local borrow-output stages, in increasing bit-index order. -/
def borrowStageStages : List (List (EncodedBit.GateSpec encoding)) :=
  (borrowStageIndices (n := n)).map fun j => borrowOutGatesAt layout j

/-- Folded forward borrow stage, in increasing bit-index order. -/
def borrowStage : List (EncodedBit.GateSpec encoding) :=
  concatStages (borrowStageStages layout)

/-- The folded borrow-stage gate list is disjoint from an observed bit when the
minuend, subtrahend, initial-borrow, and work-borrow wires are all disjoint
from that bit. -/
theorem borrowStage_bitDisjoint
    (observed : EncodedBit encoding)
    (hminuend : ∀ j : Fin n, (layout.minuend.bit j).wire ≠ observed.wire)
    (hsubtrahend :
      ∀ j : Fin n, (layout.subtrahend.bit j).wire ≠ observed.wire)
    (hinitial : layout.initialBorrow.wire ≠ observed.wire)
    (hwork : ∀ j : Fin n, (layout.workBorrow.bit j).wire ≠ observed.wire) :
    ∀ gate, gate ∈ borrowStage layout ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  have hborrowInput :
      ∀ j : Fin n, (borrowInput layout j).wire ≠ observed.wire := by
    intro j
    unfold borrowInput
    by_cases h : j.val = 0
    · simpa [h] using hinitial
    · simpa [h] using hwork (previousWorkIndex j h)
  unfold borrowStage
  apply concatStages_bitDisjoint
  intro gates hgates gate hgate
  unfold borrowStageStages at hgates
  simp only [List.mem_map] at hgates
  rcases hgates with ⟨j, _hj, rfl⟩
  exact borrowOutGatesAt_bitDisjoint layout j observed
    (hminuend j) (hsubtrahend j) (hborrowInput j) (hwork j) gate hgate

/-- Base-gate program for the folded forward borrow stage. -/
def borrowStageProgram : BaseGateProgram encoding.width :=
  EncodedBit.GateSpec.programList (borrowStage layout)

/-- Folded semantic action of the forward borrow stage over the index list. -/
def borrowStageIndexStep : Carrier -> Carrier :=
  (borrowStageIndices (n := n)).foldl
    (fun y j => borrowOutStepAt layout j y)

/-- Prefix of the forward borrow stage, retaining the concrete increasing
`List.ofFn` order. -/
def borrowStagePrefixStep (t : Nat) : Carrier -> Carrier :=
  ((borrowStageIndices (n := n)).take t).foldl
    (fun y j => borrowOutStepAt layout j y)

/-- Semantic action of the folded forward borrow gate list. -/
def borrowStageStep : Carrier -> Carrier :=
  EncodedBit.GateSpec.stepList (borrowStage layout)

/-- The folded forward borrow stage is a concrete base-gate realization. -/
theorem borrowStage_realizes :
    BaseGateProgram.Realizes encoding (borrowStageProgram layout)
      (borrowStageStep layout) :=
  EncodedBit.GateSpec.realizesList (borrowStage layout)

/-- Same-Circuit witness for the folded forward borrow stage. -/
def borrowStageSameCircuit :
    BaseGateSameCircuitWitness Carrier (borrowStageStep layout) where
  encoding := encoding
  program := borrowStageProgram layout
  realizes := borrowStage_realizes layout

/-- Folded semantic action of the forward borrow stage as a fold over its
local stage actions. -/
theorem borrowStage_stepList_eq_fold (x : Carrier) :
    EncodedBit.GateSpec.stepList (borrowStage layout) x =
      (borrowStageStages layout).foldl
        (fun y gates => EncodedBit.GateSpec.stepList gates y) x := by
  exact stepList_concatStages (borrowStageStages layout) x

/-- Folded semantic action of the forward borrow stage as a fold over the
stage indices. -/
theorem borrowStage_stepList_eq_indexStep (x : Carrier) :
    borrowStageStep layout x = borrowStageIndexStep layout x := by
  rw [borrowStageStep, borrowStage_stepList_eq_fold]
  unfold borrowStageStages borrowStageIndexStep borrowOutStepAt
  generalize borrowStageIndices = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (EncodedBit.GateSpec.stepList (borrowOutGatesAt layout j) x)

/-- Any fold of local borrow-output stages preserves a work bit whose index is
absent from the folded stage list. -/
theorem foldl_borrowOutGatesAt_get_workBorrow_of_forall_ne
    (indices : List (Fin n)) (k : Fin n)
    (hne : forall j, j ∈ indices -> j ≠ k) (x : Carrier) :
    (layout.workBorrow.bit k).get
        (indices.foldl (fun y j => borrowOutStepAt layout j y) x) =
      (layout.workBorrow.bit k).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.workBorrow.bit k).get
            (rest.foldl (fun y j => borrowOutStepAt layout j y)
              (borrowOutStepAt layout j x)) =
          (layout.workBorrow.bit k).get x
      rw [ih]
      · exact borrowOutGatesAt_get_workBorrow_of_ne layout j k
          (hne j (by simp)) x
      · intro i hi
        exact hne i (by simp [hi])

/-- Any fold of local borrow-output stages preserves every minuend readout. -/
theorem foldl_borrowOutGatesAt_get_minuend
    (indices : List (Fin n)) (i : Fin n) (x : Carrier) :
    (layout.minuend.bit i).get
        (indices.foldl (fun y j => borrowOutStepAt layout j y) x) =
      (layout.minuend.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.minuend.bit i).get
            (rest.foldl (fun y j => borrowOutStepAt layout j y)
              (borrowOutStepAt layout j x)) =
          (layout.minuend.bit i).get x
      rw [ih]
      exact borrowOutGatesAt_get_minuend_any layout j i x

/-- Any fold of local borrow-output stages preserves every subtrahend readout. -/
theorem foldl_borrowOutGatesAt_get_subtrahend
    (indices : List (Fin n)) (i : Fin n) (x : Carrier) :
    (layout.subtrahend.bit i).get
        (indices.foldl (fun y j => borrowOutStepAt layout j y) x) =
      (layout.subtrahend.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.subtrahend.bit i).get
            (rest.foldl (fun y j => borrowOutStepAt layout j y)
              (borrowOutStepAt layout j x)) =
          (layout.subtrahend.bit i).get x
      rw [ih]
      exact borrowOutGatesAt_get_subtrahend_any layout j i x

/-- Any fold of local borrow-output stages preserves the initial-borrow readout. -/
theorem foldl_borrowOutGatesAt_get_initialBorrow
    (indices : List (Fin n)) (x : Carrier) :
    layout.initialBorrow.get
        (indices.foldl (fun y j => borrowOutStepAt layout j y) x) =
      layout.initialBorrow.get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        layout.initialBorrow.get
            (rest.foldl (fun y j => borrowOutStepAt layout j y)
              (borrowOutStepAt layout j x)) =
          layout.initialBorrow.get x
      rw [ih]
      exact borrowOutGatesAt_get_initialBorrow layout j x

/-- Any fold of local borrow-output stages preserves an observed readout whose
wire is never a stage minuend target or work-borrow target. -/
theorem foldl_borrowOutGatesAt_get_of_minuend_work_ne
    (indices : List (Fin n)) (observed : EncodedBit encoding)
    (hminuend :
      forall j, j ∈ indices → (layout.minuend.bit j).wire ≠ observed.wire)
    (hwork :
      forall j, j ∈ indices → (layout.workBorrow.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get
        (indices.foldl (fun y j => borrowOutStepAt layout j y) x) =
      observed.get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        observed.get
            (rest.foldl (fun y j => borrowOutStepAt layout j y)
              (borrowOutStepAt layout j x)) =
          observed.get x
      rw [ih]
      · exact borrowOutGatesAt_get_of_minuend_work_ne layout j observed
          (hminuend j (by simp)) (hwork j (by simp)) x
      · intro i hi
        exact hminuend i (by simp [hi])
      · intro i hi
        exact hwork i (by simp [hi])

@[simp] theorem borrowStageIndices_length :
    (borrowStageIndices (n := n)).length = n := by
  simp [borrowStageIndices]

theorem borrowStageIndices_getElem_val {i : Nat}
    (hi : i < (borrowStageIndices (n := n)).length) :
    ((borrowStageIndices (n := n))[i]'hi).val = i := by
  simp [borrowStageIndices]

/-- Every member of the first `j.val` borrow-stage indices is strictly before
`j`. -/
theorem borrowStageIndices_mem_take_val_lt {j k : Fin n}
    (hmem : k ∈ (borrowStageIndices (n := n)).take j.val) :
    k.val < j.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hki⟩
  have htakeLen :
      ((borrowStageIndices (n := n)).take j.val).length = j.val := by
    rw [List.length_take, borrowStageIndices_length]
    exact Nat.min_eq_left (le_of_lt j.isLt)
  have hij : i < j.val := by simpa [htakeLen] using hi
  have hiOrig : i < (borrowStageIndices (n := n)).length := by
    rw [borrowStageIndices_length]
    exact lt_trans hij j.isLt
  rw [← List.getElem_take' hiOrig hij] at hki
  have hkval : k.val = i := by
    rw [← hki]
    exact borrowStageIndices_getElem_val (n := n) hiOrig
  omega

/-- Every member of the suffix after index `j` is strictly after `j`. -/
theorem borrowStageIndices_mem_drop_succ_val_gt {j k : Fin n}
    (hmem : k ∈ (borrowStageIndices (n := n)).drop (j.val + 1)) :
    j.val < k.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hki⟩
  have hiOrig : j.val + 1 + i < (borrowStageIndices (n := n)).length := by
    have h := hi
    have hjLe : j.val + 1 <= n := Nat.succ_le_of_lt j.isLt
    rw [borrowStageIndices_length]
    rw [List.length_drop, borrowStageIndices_length] at h
    omega
  rw [List.getElem_drop] at hki
  have hkval : k.val = j.val + 1 + i := by
    rw [← hki]
    exact borrowStageIndices_getElem_val (n := n) hiOrig
  omega

theorem borrowStagePrefixStep_get_minuend
    (t : Nat) (i : Fin n) (x : Carrier) :
    (layout.minuend.bit i).get (borrowStagePrefixStep layout t x) =
      (layout.minuend.bit i).get x := by
  unfold borrowStagePrefixStep
  exact foldl_borrowOutGatesAt_get_minuend layout
    ((borrowStageIndices (n := n)).take t) i x

theorem borrowStagePrefixStep_get_subtrahend
    (t : Nat) (i : Fin n) (x : Carrier) :
    (layout.subtrahend.bit i).get (borrowStagePrefixStep layout t x) =
      (layout.subtrahend.bit i).get x := by
  unfold borrowStagePrefixStep
  exact foldl_borrowOutGatesAt_get_subtrahend layout
    ((borrowStageIndices (n := n)).take t) i x

theorem borrowStagePrefixStep_get_initialBorrow
    (t : Nat) (x : Carrier) :
    layout.initialBorrow.get (borrowStagePrefixStep layout t x) =
      layout.initialBorrow.get x := by
  unfold borrowStagePrefixStep
  exact foldl_borrowOutGatesAt_get_initialBorrow layout
    ((borrowStageIndices (n := n)).take t) x

theorem borrowStagePrefixStep_get_workBorrow_before
    (j : Fin n) (x : Carrier) :
    (layout.workBorrow.bit j).get (borrowStagePrefixStep layout j.val x) =
      (layout.workBorrow.bit j).get x := by
  unfold borrowStagePrefixStep
  exact foldl_borrowOutGatesAt_get_workBorrow_of_forall_ne layout
    ((borrowStageIndices (n := n)).take j.val) j
    (by
      intro k hmem hkj
      have hklt : k.val < j.val :=
        borrowStageIndices_mem_take_val_lt (n := n) hmem
      have hval := congrArg Fin.val hkj
      omega)
    x

/-- After the prefix ending at stage `j`, the selected work bit stores the
local subtract-borrow recurrence for that stage, assuming the work register was
initially clean. -/
theorem borrowStagePrefixStep_get_workBorrow_current
    (j : Fin n) (x : Carrier)
    (hclean : forall k, (layout.workBorrow.bit k).get x = false) :
    (layout.workBorrow.bit j).get
        (borrowStagePrefixStep layout (j.val + 1) x) =
      Bool.carry (!(layout.minuend.bit j).get x)
        ((layout.subtrahend.bit j).get x)
        ((borrowInput layout j).get
          (borrowStagePrefixStep layout j.val x)) := by
  have hjLt : j.val < (borrowStageIndices (n := n)).length := by
    rw [borrowStageIndices_length]
    exact j.isLt
  have hget : (borrowStageIndices (n := n))[j.val]'hjLt = j := by
    apply Fin.ext
    exact borrowStageIndices_getElem_val (n := n) hjLt
  have htake :
      (borrowStageIndices (n := n)).take (j.val + 1) =
        (borrowStageIndices (n := n)).take j.val ++ [j] := by
    rw [← List.take_concat_get' (borrowStageIndices (n := n)) j.val hjLt]
    rw [hget]
  have hcleanBefore :
      (layout.workBorrow.bit j).get (borrowStagePrefixStep layout j.val x) =
        false := by
    rw [borrowStagePrefixStep_get_workBorrow_before]
    exact hclean j
  have hlocal :=
    borrowOutGatesAt_get_workBorrow_clean layout j
      (borrowStagePrefixStep layout j.val x) hcleanBefore
  rw [borrowStagePrefixStep_get_minuend,
    borrowStagePrefixStep_get_subtrahend] at hlocal
  change
    (layout.workBorrow.bit j).get
        (((borrowStageIndices (n := n)).take (j.val + 1)).foldl
          (fun y j => borrowOutStepAt layout j y) x) =
      Bool.carry (!(layout.minuend.bit j).get x)
        ((layout.subtrahend.bit j).get x)
        ((borrowInput layout j).get
          (borrowStagePrefixStep layout j.val x))
  rw [htake, List.foldl_append]
  change
    (layout.workBorrow.bit j).get
        (borrowOutStepAt layout j (borrowStagePrefixStep layout j.val x)) =
      Bool.carry (!(layout.minuend.bit j).get x)
        ((layout.subtrahend.bit j).get x)
        ((borrowInput layout j).get
          (borrowStagePrefixStep layout j.val x))
  simpa [List.foldl] using hlocal

/-- The suffix after stage `j` does not modify work bit `j`. -/
theorem borrowStageIndexStep_get_workBorrow_from_prefix
    (j : Fin n) (x : Carrier) :
    (layout.workBorrow.bit j).get (borrowStageIndexStep layout x) =
      (layout.workBorrow.bit j).get
        (borrowStagePrefixStep layout (j.val + 1) x) := by
  unfold borrowStageIndexStep borrowStagePrefixStep
  nth_rw 1 [← List.take_append_drop (j.val + 1)
    (borrowStageIndices (n := n))]
  rw [List.foldl_append]
  exact foldl_borrowOutGatesAt_get_workBorrow_of_forall_ne layout
    ((borrowStageIndices (n := n)).drop (j.val + 1)) j
    (by
      intro k hmem hkj
      have hkgt : j.val < k.val :=
        borrowStageIndices_mem_drop_succ_val_gt (n := n) hmem
      have hval := congrArg Fin.val hkj
      omega)
    (((borrowStageIndices (n := n)).take (j.val + 1)).foldl
      (fun y j => borrowOutStepAt layout j y) x)

/-- Full forward borrow-stage readout for work bit `j`, stated with the
borrow input at the prefix time. -/
theorem borrowStageIndexStep_get_workBorrow_prefix_recurrence
    (j : Fin n) (x : Carrier)
    (hclean : forall k, (layout.workBorrow.bit k).get x = false) :
    (layout.workBorrow.bit j).get (borrowStageIndexStep layout x) =
      Bool.carry (!(layout.minuend.bit j).get x)
        ((layout.subtrahend.bit j).get x)
        ((borrowInput layout j).get
          (borrowStagePrefixStep layout j.val x)) := by
  rw [borrowStageIndexStep_get_workBorrow_from_prefix]
  exact borrowStagePrefixStep_get_workBorrow_current layout j x hclean

theorem borrowStageIndexStep_get_initialBorrow (x : Carrier) :
    layout.initialBorrow.get (borrowStageIndexStep layout x) =
      layout.initialBorrow.get x := by
  unfold borrowStageIndexStep
  exact foldl_borrowOutGatesAt_get_initialBorrow layout
    (borrowStageIndices (n := n)) x

/-- The full forward borrow stage preserves an observed readout whose wire is
never a minuend target or work-borrow target. -/
theorem borrowStageIndexStep_get_of_minuend_work_ne
    (observed : EncodedBit encoding)
    (hminuend :
      forall j : Fin n, (layout.minuend.bit j).wire ≠ observed.wire)
    (hwork :
      forall j : Fin n, (layout.workBorrow.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get (borrowStageIndexStep layout x) = observed.get x := by
  unfold borrowStageIndexStep
  exact foldl_borrowOutGatesAt_get_of_minuend_work_ne layout
    (borrowStageIndices (n := n)) observed
    (by
      intro j _hmem
      exact hminuend j)
    (by
      intro j _hmem
      exact hwork j)
    x

/-- The borrow input used at stage `j` has the same readout at the prefix time
and after the full forward borrow pass. -/
theorem borrowStagePrefixStep_borrowInput_eq_indexStep
    (j : Fin n) (x : Carrier) :
    (borrowInput layout j).get (borrowStagePrefixStep layout j.val x) =
      (borrowInput layout j).get (borrowStageIndexStep layout x) := by
  unfold borrowInput
  by_cases h : j.val = 0
  · have hfull := borrowStageIndexStep_get_initialBorrow layout x
    simp [h, borrowStagePrefixStep_get_initialBorrow, hfull]
  · have hp :
        (previousWorkIndex j h).val + 1 = j.val := by
      dsimp [previousWorkIndex]
      omega
    have hfull :=
      borrowStageIndexStep_get_workBorrow_from_prefix layout
        (previousWorkIndex j h) x
    rw [hp] at hfull
    simpa [h] using hfull.symm

/-- Full forward borrow-stage recurrence for each temporary borrow bit.  The
resource and correctness object is still the same ordered gate list. -/
theorem borrowStageIndexStep_get_workBorrow_recurrence
    (j : Fin n) (x : Carrier)
    (hclean : forall k, (layout.workBorrow.bit k).get x = false) :
    (layout.workBorrow.bit j).get (borrowStageIndexStep layout x) =
      Bool.carry (!(layout.minuend.bit j).get x)
        ((layout.subtrahend.bit j).get x)
        ((borrowInput layout j).get (borrowStageIndexStep layout x)) := by
  rw [borrowStageIndexStep_get_workBorrow_prefix_recurrence layout j x hclean]
  rw [borrowStagePrefixStep_borrowInput_eq_indexStep]

/-- On clean borrow work, the folded gate-list action computes the pure natural
subtract-borrow recurrence for the selected bit. -/
theorem borrowStageIndexStep_get_workBorrow_natSubBorrow
    (a b : Nat) (borrow0 : Bool) (j : Fin n) (x : Carrier)
    (hclean : forall k, (layout.workBorrow.bit k).get x = false)
    (hinitial : layout.initialBorrow.get x = borrow0)
    (hminuend :
      forall k : Fin n, (layout.minuend.bit k).get x = a.testBit k.val)
    (hsubtrahend :
      forall k : Fin n, (layout.subtrahend.bit k).get x = b.testBit k.val) :
    (layout.workBorrow.bit j).get (borrowStageIndexStep layout x) =
      natSubBorrow a b borrow0 (j.val + 1) := by
  let stage := borrowStageIndexStep layout x
  change
    (layout.workBorrow.bit j).get stage =
      natSubBorrow a b borrow0 (j.val + 1)
  have hmain : forall m, forall j : Fin n, j.val = m ->
      (layout.workBorrow.bit j).get stage =
        natSubBorrow a b borrow0 (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          borrowStageIndexStep_get_workBorrow_recurrence layout j x hclean
        change
          (layout.workBorrow.bit j).get stage =
            natSubBorrow a b borrow0 (j.val + 1)
        rw [hrec, hminuend j, hsubtrahend j]
        unfold borrowInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hinit := borrowStageIndexStep_get_initialBorrow layout x
          rw [hinit, hinitial]
          simp [natSubBorrow, hzero]
        · rw [dif_neg hzero]
          let p := previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, previousWorkIndex]
            omega
          change
            Bool.carry (!(a.testBit j.val)) (b.testBit j.val)
              ((layout.workBorrow.bit p).get stage) =
                natSubBorrow a b borrow0 (j.val + 1)
          rw [hpRec, hpSucc]
          simp [natSubBorrow]
  exact hmain j.val j rfl

/-- Clean-initial-borrow specialization of the natural subtract-borrow bridge. -/
theorem borrowStageIndexStep_get_workBorrow_natBorrow
    (a b : Nat) (j : Fin n) (x : Carrier)
    (hclean : forall k, (layout.workBorrow.bit k).get x = false)
    (hinitial : layout.initialBorrow.get x = false)
    (hminuend :
      forall k : Fin n, (layout.minuend.bit k).get x = a.testBit k.val)
    (hsubtrahend :
      forall k : Fin n, (layout.subtrahend.bit k).get x = b.testBit k.val) :
    (layout.workBorrow.bit j).get (borrowStageIndexStep layout x) =
      natBorrow a b (j.val + 1) := by
  simpa [natBorrow] using
    borrowStageIndexStep_get_workBorrow_natSubBorrow layout a b false j x
      hclean hinitial hminuend hsubtrahend

end BorrowWorkLayout

end

end Comparator
end QuantumAlg
