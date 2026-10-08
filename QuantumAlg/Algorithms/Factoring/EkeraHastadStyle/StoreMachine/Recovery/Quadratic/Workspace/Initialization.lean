/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Widths

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Views
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources

/-!
# Persistent quadratic-scratch initialization

The reusable quadratic package contains three values that survive every
candidate invocation: the public modulus, one, and zero.  This module widens
the already materialized modular-setup word and initializes both literals with
real fixed-width routines.  No value-sized callback is introduced.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticScratchInitialization

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Layout

/-- Abbreviation for the local cell interface. -/
abbrev Cell := QuadraticScratchLayout.Cell

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  QuadraticScratchLayout.Cells ctx N

/-- Abbreviation for the local short width interface. -/
abbrev ShortWidth (N : Nat) := QuadraticScratchLayout.ShortWidth N

/-- Abbreviation for the local discriminant width interface. -/
abbrev DiscriminantWidth (N : Nat) :=
  QuadraticScratchLayout.DiscriminantWidth N

/-- Abbreviation for the local candidate width interface. -/
abbrev CandidateWidth (N : Nat) := QuadraticScratchLayout.CandidateWidth N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  QuadraticScratchLayout.cellRef cells cell

end Layout

/-- Typed writable view of the physical wide-modulus cell. -/
def modulusCell {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    CWriteRef ctx (.unsignedWord (Layout.DiscriminantWidth N)) :=
  Layout.cellRef cells .modulus

/-- The typed modulus cell is workspace-owned. -/
theorem modulusCell_role {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    (modulusCell cells).toCStorageRef.role = .workspace :=
  QuadraticScratchLayout.cellRef_role cells .modulus

/-- The typed modulus input is the shared scratch view. -/
theorem modulusInput_eq {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    FirstAccepted.cellRead (modulusCell cells) =
      QuadraticScratchViews.modulusInput cells := by
  rfl

/-- The ordinary public modulus width fits the quadratic discriminant word. -/
theorem modulusBits_lt_discriminantWidth (N : Nat) :
    modulusBits N < Layout.DiscriminantWidth N := by
  have modulusBitsLeSize : modulusBits N ≤ Nat.size N :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_size_self N))
  have sizeLeInput : Nat.size N ≤
      RSA.shortLogRecoveryInputBits N (shortLogBits N) (tradeoffBits N) := by
    simp only [RSA.shortLogRecoveryInputBits]
    omega
  have modulusBitsLeInput := modulusBitsLeSize.trans sizeLeInput
  simp only [Layout.DiscriminantWidth,
    QuadraticScratchLayout.DiscriminantWidth,
    QuadraticPrefix.discriminantWidth, QuadraticPrefix.centerWidth,
    QuadraticScratchLayout.ShortWidth,
    LatticePairCandidateRecovery.Width, LatticeWideLllMachine.Width,
    RSA.ShortLogWidths.coordinateWidth, RSA.ShortLogWidths.operandWidthBound,
    RSA.ShortLogWidths.inputBitWidth]
  omega

/-- The public modulus fits strictly in the widened quadratic word. -/
theorem modulus_fits_discriminantWidth {N : Nat} (input : Input N) :
    N < CShape.wordModulus (Layout.DiscriminantWidth N) := by
  change N < 2 ^ Layout.DiscriminantWidth N
  exact input.samplerInput.register_fits.trans_lt
    (Nat.pow_lt_pow_right (by norm_num : 1 < 2)
      (modulusBits_lt_discriminantWidth N))

/-- Entry equality for the already materialized public-modulus source. -/
def InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (before : Store ctx)
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1))) : Prop :=
  (before.read source).toNat = N

/-- Original source separation and separation of the three constant destinations. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) : Prop where
  sourceAvoidsModulus : (modulusCell cells).key ∉ source.storageKeys
  sourceAvoidsOne : (Layout.cellRef cells .one).key ∉ source.storageKeys
  sourceAvoidsZero : (Layout.cellRef cells .zero).key ∉ source.storageKeys
  modulusAvoidsOne : (Layout.cellRef cells .one).key ∉
    (FirstAccepted.cellRead (modulusCell cells)).storageKeys
  modulusAvoidsZero : (Layout.cellRef cells .zero).key ∉
    (FirstAccepted.cellRead (modulusCell cells)).storageKeys
  oneAvoidsZero : (Layout.cellRef cells .zero).key ∉
    (FirstAccepted.cellRead (Layout.cellRef cells .one)).storageKeys

/-- Physical distinctness and source avoidance supply the original initializer separation. -/
theorem separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (sourceAvoids : ∀ cell, (Layout.cellRef cells cell).key ∉ source.storageKeys) :
    Separation source cells := by
  have keyNe (left right : Layout.Cell) (different : left ≠ right) :
      (Layout.cellRef cells left).key ≠ (Layout.cellRef cells right).key := by
    intro equal
    exact different
      (QuadraticScratchLayout.cellRef_key_injective cells distinct equal)
  refine ⟨sourceAvoids .modulus, sourceAvoids .one, sourceAvoids .zero, ?_, ?_, ?_⟩
  · simpa [FirstAccepted.cellRead, CInputRef.storageKeys, modulusCell] using
      keyNe .one .modulus (by decide)
  · simpa [FirstAccepted.cellRead, CInputRef.storageKeys, modulusCell] using
      keyNe .zero .modulus (by decide)
  · simpa [FirstAccepted.cellRead, CInputRef.storageKeys] using keyNe .zero .one (by decide)

/-- A caller read avoids all three persistent constant destinations. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  modulus : (modulusCell cells).key ∉ other.storageKeys
  one : (Layout.cellRef cells .one).key ∉ other.storageKeys
  zero : (Layout.cellRef cells .zero).key ∉ other.storageKeys

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The existing native resize reads the actual public-modulus source word. -/
def resizeOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) :=
  ClassicalOp.wordResize (modulusBits N + 1) (Layout.DiscriminantWidth N)
    ctx source (modulusCell cells)

/-- Resize the modulus, self-initialize one, and clear zero with four actual instructions. -/
def into (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (resizeOp source cells))
    (.seq (Word.PowerOfTwo.seedInto (Layout.cellRef cells .one))
      (BitWord.instruction (execution := model)
        (Word.PowerOfTwo.clearOp (Layout.cellRef cells .zero))))

/-- Full actual store and native path after initializing the three persistent constants. -/
def step (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (store : Store ctx) : Store ctx × (into source cells).Path :=
  let resized := BitWord.instructionStep (execution := model) (resizeOp source cells) store
  let one := Word.PowerOfTwo.seedStep (Layout.cellRef cells .one) resized.1
  let zero := BitWord.instructionStep (execution := model)
    (Word.PowerOfTwo.clearOp (Layout.cellRef cells .zero)) one.1
  (zero.1, (resized.2, (one.2, zero.2)))

/-- The actual native sequence preserves complete quantum-reference blocks and history. -/
theorem into_execute (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into source cells).execute Reference state = state.mapClassical (fun entry =>
      let actual := step source cells entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, Word.PowerOfTwo.seedInto_execute,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every actual read outside all three destinations survives the four native writes. -/
theorem into_callerFrame (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (avoids : CallerFrameAvoids cells other) :
    (step source cells store).1.read other = store.read other := by
  simp only [step, Word.PowerOfTwo.seedStep, BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.zero,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.one,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.one,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.modulus]

/-- Exact actual constants and every caller read outside their destinations. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (before after : Store ctx) : Prop where
  modulus : (after.read (QuadraticScratchViews.modulusInput cells)).toNat = N
  one : (after.read (QuadraticScratchViews.oneInput cells)).toNat = 1
  zero : (after.read (QuadraticScratchViews.zeroInput cells)).toNat = 0
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids cells other → after.read other = before.read other

/-- Actual resizing and literal writes establish the constants without caller scratch premises. -/
theorem into_correct (input : Input N)
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (separated : Separation source cells)
    (store : Store ctx) (initial : InitialConditions store source) :
    Relation source cells store (step source cells store).1 := by
  let resized := store.applyOp (resizeOp source cells)
  let seeded := (Word.PowerOfTwo.seedStep (Layout.cellRef cells .one) resized).1
  have modulusAtSeed : seeded.read (FirstAccepted.cellRead (modulusCell cells)) =
      resized.read (FirstAccepted.cellRead (modulusCell cells)) := by
    dsimp only [seeded, Word.PowerOfTwo.seedStep, BitWord.instructionStep]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ separated.modulusAvoidsOne,
      Store.read_applyOp_of_not_mem_storageKeys _ _ _ separated.modulusAvoidsOne]
  have modulusAtEnd : (step source cells store).1.read
      (FirstAccepted.cellRead (modulusCell cells)) =
        resized.read (FirstAccepted.cellRead (modulusCell cells)) := by
    exact (Store.read_applyOp_of_not_mem_storageKeys seeded
      (Word.PowerOfTwo.clearOp (Layout.cellRef cells .zero)) _
      separated.modulusAvoidsZero).trans modulusAtSeed
  have modulusWritten := Store.read_applyOp_output store (resizeOp source cells)
  have oneFits : 1 < 2 ^ Layout.CandidateWidth N := by
    apply Nat.one_lt_two_pow
    simp only [Layout.CandidateWidth, QuadraticScratchLayout.CandidateWidth,
      QuadraticCandidateCheck.CandidateWidth, QuadraticPrefix.centerWidth]
    omega
  refine ⟨?_, ?_, ?_, into_callerFrame source cells store⟩
  · change ((step source cells store).1.read
      (FirstAccepted.cellRead (modulusCell cells))).toNat = N
    rw [modulusAtEnd]
    have written := congrArg CShape.Value.toNat modulusWritten
    change (resized.read (FirstAccepted.cellRead (modulusCell cells))).toNat =
      ((ClassicalOp.wordResize (modulusBits N + 1) (Layout.DiscriminantWidth N)
        ctx source (modulusCell cells)).eval (store.read source)).toNat at written
    rw [ClassicalOp.eval_wordResize_toNat] at written
    rw [written, initial, Nat.mod_eq_of_lt (modulus_fits_discriminantWidth input)]
  · change ((seeded.applyOp (Word.PowerOfTwo.clearOp (Layout.cellRef cells .zero))).read
      (FirstAccepted.cellRead (Layout.cellRef cells .one))).toNat = 1
    rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ separated.oneAvoidsZero]
    exact (Word.PowerOfTwo.seed_read (Layout.cellRef cells .one) resized).trans
      (Nat.mod_eq_of_lt oneFits)
  · exact Word.PowerOfTwo.clear_read (Layout.cellRef cells .zero) seeded

/-- Independent native formula for all four initialization instructions. -/
def events (N : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (modulusBits N + 1) (Layout.DiscriminantWidth N))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (Layout.CandidateWidth N))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (Layout.CandidateWidth N))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (Layout.CandidateWidth N)))]

/-- Independent coordinate budget for the three initialized constant destinations. -/
def eventEnvelope (N : Nat) : ResourcePool model := ResourcePool.ofList (events N)

/-- Every actual path emits the same four native instructions. -/
theorem into_events (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (path : (into source cells).Path) :
    (into source cells).eventTrace path = events N := by
  change (BitWord.instruction (execution := model) (resizeOp source cells)).eventTrace path.1 ++
    (((BitWord.instruction (execution := model)
        (Word.PowerOfTwo.clearOp (Layout.cellRef cells .one))).eventTrace path.2.1.1 ++
      (BitWord.instruction (execution := model)
        (Word.PowerOfTwo.incrementOp (Layout.cellRef cells .one))).eventTrace path.2.1.2) ++
      (BitWord.instruction (execution := model)
        (Word.PowerOfTwo.clearOp (Layout.cellRef cells .zero))).eventTrace path.2.2) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Native multiplicities equal the independent four-instruction formula. -/
theorem into_resourcePool (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (path : (into source cells).Path) :
    (into source cells).resourcePool path = eventEnvelope N := by
  change ResourcePool.ofList ((into source cells).eventTrace path) = _
  rw [into_events]
  rfl

/-- Initialization has exactly four serial native instructions. -/
theorem into_depth (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (path : (into source cells).Path) :
    (into source cells).depth (fun _ => 1) path = 4 := rfl

/-- Every original cell remains live during the complete native initializer. -/
theorem into_visited (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (path : (into source cells).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (into source cells).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++ ([ctx] ++ [ctx]) ++ [ctx] at present
  simpa using present

/-- Resident accounting retains all actual caller and workspace cells. -/
theorem into_resident_le (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (path : (into source cells).Path) :
    (into source cells).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited source cells path visited present]

/-- Auxiliary accounting retains every live workspace role throughout initialization. -/
theorem into_auxiliary_le (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (path : (into source cells).Path) :
    (into source cells).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited source cells path visited present]

/-- Every native initializer write restores borrowed storage jointly with any reference. -/
theorem into_borrowedRestored
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into source cells).BorrowedRestored Reference state
      ((into source cells).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical
      (BitWord.selectedApplication (execution := model) (resizeOp source cells)) _
  · apply Circuit.borrowedRestored_seq
    · apply Circuit.borrowedRestored_seq
      · exact Circuit.borrowedRestored_classical
          (BitWord.selectedApplication (execution := model)
            (Word.PowerOfTwo.clearOp (Layout.cellRef cells .one))) _
      · exact Circuit.borrowedRestored_classical
          (BitWord.selectedApplication (execution := model)
            (Word.PowerOfTwo.incrementOp (Layout.cellRef cells .one))) _
    · exact Circuit.borrowedRestored_classical
        (BitWord.selectedApplication (execution := model)
          (Word.PowerOfTwo.clearOp (Layout.cellRef cells .zero))) _

/-- The three actual constant values supply the guarded recovery entry contract. -/
theorem guardedInitialConditions_of_values {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (input : Input N) (cells : Layout.Cells ctx N)
    (shortLogSelection : FirstAccepted.Direct.Refs ctx (Layout.ShortWidth N))
    (factorSelection : FirstAccepted.Refs ctx (Layout.CandidateWidth N)) (store : Store ctx)
    (modulusValue : (store.read (QuadraticScratchViews.modulusInput cells)).toNat = N)
    (oneValue : (store.read (QuadraticScratchViews.oneInput cells)).toNat = 1)
    (zeroValue : (store.read (QuadraticScratchViews.zeroInput cells)).toNat = 0) :
    QuadraticRecoveryGuarded.InitialConditions N store
      (QuadraticScratchViews.guardedRefs cells shortLogSelection factorSelection) := by
  have modulusPositive : 0 < (store.read (QuadraticScratchViews.modulusInput cells)).toNat := by
    rw [modulusValue]
    exact input.modulus_pos
  exact ⟨⟨⟨oneValue, modulusPositive, zeroValue⟩, ⟨oneValue, modulusPositive, zeroValue⟩⟩,
    modulusValue⟩

/-- The same actual initializer establishes the downstream guarded recovery contract. -/
theorem guardedInitialConditions_of_relation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} (input : Input N)
    (source : CInputRef ctx (.unsignedWord (modulusBits N + 1)))
    (cells : Layout.Cells ctx N)
    (shortLogSelection : FirstAccepted.Direct.Refs ctx (Layout.ShortWidth N))
    (factorSelection : FirstAccepted.Refs ctx (Layout.CandidateWidth N))
    (before after : Store ctx) (holds : Relation source cells before after) :
    QuadraticRecoveryGuarded.InitialConditions N after
      (QuadraticScratchViews.guardedRefs cells shortLogSelection factorSelection) :=
  guardedInitialConditions_of_values input cells shortLogSelection factorSelection after
    holds.modulus holds.one holds.zero

end

end QuadraticScratchInitialization
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
