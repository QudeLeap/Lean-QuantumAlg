/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Factor.Program

/-!
# Actual reusable pair-recovery entry reset

Thirteen charged self-XOR instructions clear the original two-width reset
list before every pair. The same actual stores establish all thirteen zero
values, including the four unchanged basis words and third target coordinate
required by the current source-to-LLL circuit, without caller initialization.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryReset

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Every physical word whose zero value is required at pair entry. -/
inductive Cell where
  | firstFull
  | secondFull
  | basis13
  | basis21
  | basis32
  | basis22
  | basis23
  | basis31
  | basis33
  | targetFirstScratch
  | targetSecondScratch
  | targetThird
  | denominatorMagnitude
deriving DecidableEq

/-- The exact width of one reset word. -/
def cellWidth (N : Nat) : Cell → Nat
  | .firstFull | .secondFull => measurementBits N
  | _ => LatticePairCandidateRecovery.Width N

/-- The wide pair-to-LLL reference package inside one factor-recovery slot. -/
abbrev wideRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) :=
  refs.pair.pair.pairNearest.wide

/-- Resolve one typed reset index to its real writable word. -/
def cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) :
    (cell : Cell) → CWriteRef ctx (.unsignedWord (cellWidth N cell))
  | .firstFull => (wideRefs refs).initialization.pair.first.full
  | .secondFull => (wideRefs refs).initialization.pair.second.full
  | .basis13 => (wideRefs refs).initialization.raw.b13
  | .basis21 => (wideRefs refs).initialization.raw.b21
  | .basis32 => (wideRefs refs).initialization.raw.b32
  | .basis22 => (wideRefs refs).initialization.raw.b22
  | .basis23 => (wideRefs refs).initialization.raw.b23
  | .basis31 => (wideRefs refs).initialization.raw.b31
  | .basis33 => (wideRefs refs).initialization.raw.b33
  | .targetFirstScratch => (wideRefs refs).target.target.first.scratch
  | .targetSecondScratch => (wideRefs refs).target.target.second.scratch
  | .targetThird => (wideRefs refs).target.target.point.third
  | .denominatorMagnitude => refs.pair.pair.pairNearest.third.denominatorMagnitude

/-- Storage-key projection of one reset word. -/
def cellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) (cell : Cell) : StorageKey :=
  (cellRef refs cell).toCStorageRef.key

/-- Canonical order of the thirteen pair-entry words. -/
def cells : List Cell :=
  [.firstFull, .secondFull, .basis13, .basis21, .basis32, .basis22,
    .basis23, .basis31, .basis33, .targetFirstScratch,
    .targetSecondScratch, .targetThird, .denominatorMagnitude]

private lemma cells_nodup : cells.Nodup := by simp [cells]

private lemma cell_mem_cells (cell : Cell) : cell ∈ cells := by
  cases cell <;> simp [cells]

/-- Physical reset words are pairwise distinct. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) : Prop where
  keyInjective : Function.Injective (cellKey refs)

/-- A caller read avoids every reset word. -/
def CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop :=
  ∀ cell, cellKey refs cell ∉ other.storageKeys

/-- One charged self-XOR on the original dependently typed reset destination. -/
def clearOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairFactorRecovery.Refs ctx N) (cell : Cell) :=
  ClassicalOp.wordBinary .bitXor (cellWidth N cell) ctx
    (.product (FirstAccepted.cellRead (cellRef refs cell))
      (FirstAccepted.cellRead (cellRef refs cell))) (cellRef refs cell)

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Execute the original list of reset destinations in order. -/
def clearCells (refs : LatticePairFactorRecovery.Refs ctx N) :
    List Cell → Circuit model ctx ctx
  | [] => .id ctx
  | head :: tail =>
      .seq (BitWord.instruction (execution := model) (clearOp refs head))
        (clearCells refs tail)

/-- Actual store and complete chronological path of the dependent reset list. -/
def clearCellsStep (refs : LatticePairFactorRecovery.Refs ctx N) :
    (selected : List Cell) → Store ctx → Store ctx × (clearCells refs selected).Path
  | [], store => (store, ())
  | head :: tail, store =>
      let first := BitWord.instructionStep (execution := model) (clearOp refs head) store
      let rest := clearCellsStep refs tail first.1
      (rest.1, (first.2, rest.2))

/-- Every listed reset instruction executes on the same full classical-reference record. -/
lemma clearCells_execute (refs : LatticePairFactorRecovery.Refs ctx N) (selected : List Cell) :
    ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (clearCells refs selected).execute environment Reference state
        = state.mapClassical (fun entry =>
        let actual := clearCellsStep refs selected entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  induction selected with
  | nil =>
      intro Reference History _ state
      exact (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons head tail ih =>
      intro Reference History _ state
      exact Circuit.execute_sequenceStoreRecord (environment := environment) _ _ _ _
        (fun _reference _history _ current => BitWord.bitWord_instruction_execute
          (environment := environment) _ current)
        ih Reference state

/-- The original thirteen-word reset always runs in full before another pair. -/
def into (refs : LatticePairFactorRecovery.Refs ctx N) : Circuit model ctx ctx :=
  clearCells refs cells

/-- The actual thirteen-write result and its complete path. -/
def step (refs : LatticePairFactorRecovery.Refs ctx N) (store : Store ctx) :
    Store ctx × (into refs).Path := clearCellsStep refs cells store

/-- Actual reset execution preserves complete incoming histories and reference blocks. -/
lemma into_execute (refs : LatticePairFactorRecovery.Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  clearCells_execute refs cells Reference state

omit [BitWord.Selected model] in
/-- One listed instruction writes its canonical zero from arbitrary incoming contents. -/
private lemma clear_value (refs : LatticePairFactorRecovery.Refs ctx N) (cell : Cell)
    (store : Store ctx) :
    (store.applyOp (clearOp refs cell)).read (FirstAccepted.cellRead (cellRef refs cell)) =
      CShape.initialValue (.unsignedWord (cellWidth N cell)) := by
  change (store.applyOp (clearOp refs cell)).read
    (.storage (clearOp refs cell).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change CShape.wordBitXor (cellWidth N cell)
    (store.read (FirstAccepted.cellRead (cellRef refs cell)))
    (store.read (FirstAccepted.cellRead (cellRef refs cell))) = _
  simp [CShape.wordBitXor, CShape.initialValue]

/-- The actual dependent reset list preserves every structural read outside its destinations. -/
lemma clearCells_callerFrame (refs : LatticePairFactorRecovery.Refs ctx N)
    (selected : List Cell) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell ∈ selected, cellKey refs cell ∉ other.storageKeys) :
    (clearCellsStep refs selected store).1.read other = store.read other := by
  induction selected generalizing store with
  | nil => rfl
  | cons head tail ih =>
      exact (ih (store.applyOp (clearOp refs head))
        (fun cell member => avoids cell (List.mem_cons_of_mem head member))).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (clearOp refs head) other
          (avoids head List.mem_cons_self))

/-- Every caller read avoiding the original thirteen keys survives the complete reset. -/
lemma into_callerFrame (refs : LatticePairFactorRecovery.Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other :=
  clearCells_callerFrame refs cells store other (fun cell _ => avoids cell)

private lemma clearCells_zero (refs : LatticePairFactorRecovery.Refs ctx N)
    (separation : Separation refs) (selected : List Cell) (nodup : selected.Nodup)
    (store : Store ctx) : ∀ cell ∈ selected,
      (clearCellsStep refs selected store).1.read (FirstAccepted.cellRead (cellRef refs cell)) =
        CShape.initialValue (.unsignedWord (cellWidth N cell)) := by
  induction selected generalizing store with
  | nil => intro cell member; exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      intro cell member
      rcases List.mem_cons.mp member with same | member
      · subst cell
        have frame := clearCells_callerFrame refs tail (store.applyOp (clearOp refs head))
          (FirstAccepted.cellRead (cellRef refs head)) (by
            intro target targetMember
            change cellKey refs target ∉ [cellKey refs head]
            simp only [List.mem_singleton]
            intro same
            have equal := separation.keyInjective same
            subst target
            exact (List.nodup_cons.mp nodup).1 targetMember)
        exact frame.trans (clear_value refs head store)
      · exact ih nodup.tail (store.applyOp (clearOp refs head)) cell member

/-- All thirteen words are zero, and the existing LLL entry contract and caller frame hold. -/
structure Relation (refs : LatticePairFactorRecovery.Refs ctx N)
    (before after : Store ctx) : Prop where
  cleared : ∀ cell, after.read (FirstAccepted.cellRead (cellRef refs cell)) =
    CShape.initialValue (.unsignedWord (cellWidth N cell))
  initial : LatticePairNearestPlaneSavedTarget.InitialConditions after refs.pair.pair
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- The full paid reset establishes the required source zeros without any caller initialization. -/
lemma into_correct (refs : LatticePairFactorRecovery.Refs ctx N)
    (separation : Separation refs) (store : Store ctx) :
    Relation refs store (step refs store).1 := by
  have cleared := clearCells_zero refs separation cells cells_nodup store
  have fresh (cell : Cell) : (step refs store).1.read
      (FirstAccepted.cellRead (cellRef refs cell)) =
        CShape.initialValue (.unsignedWord (cellWidth N cell)) := cleared cell (cell_mem_cells cell)
  have rawZero (cell : Cell) : RawSignedRepresents
      ((step refs store).1.read (FirstAccepted.cellRead (cellRef refs cell))) 0 := by
    rw [fresh, CShape.initialValue_unsignedWord]
    exact rawSignedWordRepresents_wordOfNat (cellWidth N cell) 0
  refine ⟨fresh, ?_, into_callerFrame refs store⟩
  refine ⟨?_, rawZero .targetThird⟩
  intro zeroCell
  cases zeroCell with
  | b22 => exact rawZero .basis22
  | b23 => exact rawZero .basis23
  | b31 => exact rawZero .basis31
  | b33 => exact rawZero .basis33

/-- Independent native label of each original dependently typed reset word. -/
def cellEvent (N : Nat) (cell : Cell) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordBinary .bitXor (cellWidth N cell)))

/-- Independent chronological trace of an ordered reset list. -/
def nativeTrace (N : Nat) (selected : List Cell) : List (Resource.Event model) :=
  selected.map (cellEvent N)

/-- Independent native allowance of the original thirteen reset writes. -/
def resetEventEnvelope (N : Nat) : ResourcePool model :=
  ResourcePool.ofList (nativeTrace N cells)

/-- Each actual listed instruction contributes exactly its original native label. -/
lemma clearCells_events (refs : LatticePairFactorRecovery.Refs ctx N) (selected : List Cell) :
    ∀ path : (clearCells refs selected).Path,
      (clearCells refs selected).eventTrace path = nativeTrace N selected := by
  induction selected with
  | nil => intro path; rfl
  | cons head tail ih =>
      intro path
      change (BitWord.instruction (execution := model) (clearOp refs head)).eventTrace
        path.1 ++ (clearCells refs tail).eventTrace path.2 = _
      rw [BitWord.bitWord_instruction_eventTrace]
      change cellEvent N head :: (clearCells refs tail).eventTrace path.2 =
        cellEvent N head :: nativeTrace N tail
      rw [ih]

/-- The complete actual reset emits the thirteen original typed clear instructions. -/
lemma into_events (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path) :
    (into refs).eventTrace path = nativeTrace N cells := clearCells_events refs cells path

/-- The native ledger equals the independent complete thirteen-write allowance. -/
lemma into_resourcePool (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path) :
    (into refs).resourcePool path = resetEventEnvelope N :=
  congrArg ResourcePool.ofList (into_events refs path)

/-- Every actual reset path meets that same independent native allowance. -/
lemma into_pool_le (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ resetEventEnvelope N := (into_resourcePool refs path).le

/-- Every original reset word is charged once in the actual chronological trace. -/
lemma into_eventCount (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path) :
    ((into refs).eventTrace path).length = 13 := by
  rw [into_events]
  rfl

private lemma clearCells_depth (refs : LatticePairFactorRecovery.Refs ctx N)
    (selected : List Cell) : ∀ path : (clearCells refs selected).Path,
      (clearCells refs selected).depth (fun _ => 1) path = selected.length := by
  induction selected with
  | nil => intro path; rfl
  | cons head tail ih =>
      intro path
      change 1 + (clearCells refs tail).depth (fun _ => 1) path.2 = tail.length + 1
      rw [ih, Nat.add_comm]

/-- The full reset has exactly thirteen sequential native dependencies. -/
lemma into_depth (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path = 13 := clearCells_depth refs cells path

private lemma clearCells_visited (refs : LatticePairFactorRecovery.Refs ctx N)
    (selected : List Cell) : ∀ (path : (clearCells refs selected).Path)
      (visited : RuntimeCtx model.kind),
        visited ∈ (clearCells refs selected).visitedContexts path →
        visited = ctx := by
  induction selected with
  | nil => intro path visited present; exact List.mem_singleton.mp present
  | cons head tail ih =>
      intro path visited present
      change visited ∈ [ctx] ++ (clearCells refs tail).visitedContexts path.2 at present
      rcases List.mem_append.mp present with current | later
      · exact List.mem_singleton.mp current
      · exact ih path.2 visited later

/-- Every supplied classical and quantum runtime entry remains live throughout reset. -/
lemma into_visited (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := clearCells_visited refs cells path visited present

/-- The thirteen paid clears allocate no additional runtime storage. -/
lemma into_resident_le (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- The reset keeps every existing workspace role in its actual auxiliary accounting. -/
lemma into_auxiliary_le (refs : LatticePairFactorRecovery.Refs ctx N) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

private lemma clearCells_borrowedRestored (refs : LatticePairFactorRecovery.Refs ctx N)
    (selected : List Cell) : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (clearCells refs selected).BorrowedRestored Reference state
        ((clearCells refs selected).execute environment Reference state) := by
  induction selected with
  | nil =>
      intro Reference History _ state
      exact Circuit.borrowedRestored_id (environment := environment) (model := model) (ctx := ctx)
        (Reference := Reference) (H := History) state
  | cons head tail ih =>
      intro Reference History _ state
      exact Circuit.borrowedRestored_seq (environment := environment) _ _ state
        (Circuit.borrowedRestored_classical (environment := environment)
          (BitWord.selectedApplication (execution := model) (clearOp refs head)) state)
        (ih Reference _)

/-- Every actual reset instruction restores borrowed systems jointly with arbitrary references. -/
lemma into_borrowedRestored (refs : LatticePairFactorRecovery.Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).BorrowedRestored
      Reference state ((into refs).execute environment Reference state) :=
  clearCells_borrowedRestored refs cells Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryReset
