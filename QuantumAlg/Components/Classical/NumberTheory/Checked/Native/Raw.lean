/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

/-!
# Actual widened raw XGCD for checked number theory

The original denominator is copied by one real width-increasing instruction.
The existing raw engine then consumes the actual modulus as its left operand
and that widened denominator as its right operand. The temporary denominator
is released after the three real raw results have been produced.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution ClassicalWorkspace XGCD.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original temporary widened denominator context. -/
@[reducible] def widenedXgcdCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh

/-- Structural transport of the original modulus, denominator and caller destinations. -/
def widenedXgcdTransport (ctx : RuntimeCtx kind) (width : Nat) :
    Transport ctx (widenedXgcdCtx ctx width) :=
  (Transport.id ctx).underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- Actual widened denominator workspace cell. -/
def widenedDenominatorCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (widenedXgcdCtx ctx width) (.unsignedWord (width + 1)) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- The original width-increasing native instruction. -/
def widenedDenominatorOp (denominator : CInputRef ctx (.unsignedWord width))
    (widened : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx denominator widened

/-- Actual widening precedes the existing native raw engine without changing its operand order. -/
def widenedXgcdBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (widened : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (widenedDenominatorOp denominator widened))
    (rawEngine (model := model) (.product modulus (GCD.cellRead widened)) outputs)

/-- Mathematical input determined by the original two actual operand reads. -/
def widenedXgcdInput (modulus : CShape.Word (width + 1)) (denominator : CShape.Word width) :
    XGCD.PureXGCD.Input (width + 1) :=
  GCD.decodeOperands (.product modulus (CShape.wordResize (width + 1) denominator))

/-- Complete original denominator scope around widening and the actual reusable raw engine. -/
def withWidenedXgcd {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (widenedXgcdBody (model := model) ((widenedXgcdTransport ctx width).liftInput denominator)
      ((widenedXgcdTransport ctx width).liftInput modulus) (widenedDenominatorCell ctx width)
      (outputs.transport (widenedXgcdTransport ctx width)))

/-- The actual body produces the raw final state and changes only its scratch and raw outputs. -/
theorem widenedXgcdBody_actualRecord {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (widened : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (distinct : outputs.Distinct)
    (modulusFree : widened.key ∉ modulus.storageKeys) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (widenedXgcdBody (model := model) denominator modulus widened outputs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (widenedXgcdBody (model := model) denominator modulus widened outputs).execute
          Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          widened.key ∉ other.storageKeys → outputs.gcd.key ∉ other.storageKeys →
          outputs.leftCoefficient.key ∉ other.storageKeys →
          outputs.rightCoefficient.key ∉ other.storageKeys →
            (record before).1.1.read other = before.1.read other) ∧
        outputs.MatchesState (record before).1.1
          (XGCD.PureXGCD.finalState (widenedXgcdInput (before.1.read modulus)
            (before.1.read denominator))) := by
  obtain ⟨rawRecord, rawEquation, rawCorrect⟩ := xgcdNativeRawEngine_actualRecord
    (model := model) (.product modulus (GCD.cellRead widened)) outputs distinct
  let first := BitWord.instruction (execution := model) (widenedDenominatorOp denominator widened)
  let second := rawEngine (model := model) (.product modulus (GCD.cellRead widened)) outputs
  let firstRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × first.Path := fun before =>
    let result := BitWord.instructionStep (execution := model)
      (widenedDenominatorOp denominator widened) before.1
    ((result.1, before.2), result.2)
  refine ⟨Circuit.sequenceRecord first second firstRecord rawRecord, ?_, ?_⟩
  · intro reference history historyFinite state
    exact Circuit.execute_sequenceRecord first second firstRecord rawRecord (by
      intro reference history historyFinite state
      refine (BitWord.bitWord_instruction_execute (execution := model)
        (widenedDenominatorOp denominator widened) state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl) rawEquation reference state
  · intro before
    let enlarged := before.1.applyOp (widenedDenominatorOp denominator widened)
    have modulusRead : enlarged.read modulus = before.1.read modulus :=
      Store.read_applyOp_of_not_mem_storageKeys before.1
        (widenedDenominatorOp denominator widened) modulus modulusFree
    have denominatorRead : enlarged.read (GCD.cellRead widened) =
        CShape.wordResize (width + 1) (before.1.read denominator) :=
      Store.read_applyOp_output before.1 (widenedDenominatorOp denominator widened)
    constructor
    · intro shape other widenedFree gcdFree leftFree rightFree
      exact ((rawCorrect (enlarged, before.2)).1 other gcdFree leftFree rightFree).trans
        (Store.read_applyOp_of_not_mem_storageKeys before.1
          (widenedDenominatorOp denominator widened) other widenedFree)
    · have inputRead : enlarged.read (.product modulus (GCD.cellRead widened)) =
          .product (before.1.read modulus)
            (CShape.wordResize (width + 1) (before.1.read denominator)) :=
        congrArg₂ CShape.Value.product modulusRead denominatorRead
      have actual := (rawCorrect (enlarged, before.2)).2
      rw [inputRead] at actual
      exact actual

/-- Fresh widening leaves no scratch premise on the caller's original operands or state. -/
theorem withWidenedXgcd_actualRecord {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1)) (distinct : outputs.Distinct) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (withWidenedXgcd (model := model) denominator modulus outputs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withWidenedXgcd (model := model) denominator modulus outputs).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          outputs.gcd.key ∉ other.storageKeys → outputs.leftCoefficient.key ∉ other.storageKeys →
          outputs.rightCoefficient.key ∉ other.storageKeys →
            (record before).1.1.read other = before.1.read other) ∧
        outputs.MatchesState (record before).1.1
          (XGCD.PureXGCD.finalState (widenedXgcdInput (before.1.read modulus)
            (before.1.read denominator))) := by
  let transport := widenedXgcdTransport ctx width
  let widened := widenedDenominatorCell ctx width
  let body := widenedXgcdBody (model := model) (transport.liftInput denominator)
    (transport.liftInput modulus)
    widened (outputs.transport transport)
  have scratchFree : ∀ {shape : CShape} (input : CInputRef ctx shape),
      widened.key ∉ (transport.liftInput input).storageKeys := by
    intro shape input
    rw [transport.liftInput_storageKeys]
    exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)
  obtain ⟨bodyRecord, bodyEquation, bodyCorrect⟩ := widenedXgcdBody_actualRecord
    (model := model) (transport.liftInput denominator) (transport.liftInput modulus) widened
    (outputs.transport transport)
    (xgcdNativeRawOutputs_distinct_transport outputs transport distinct)
    (scratchFree modulus)
  refine ⟨Circuit.workspaceRecord ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh body bodyRecord, ?_, ?_⟩
  · intro reference history historyFinite state
    exact Circuit.execute_workspaceRecord _ _ _ body bodyRecord bodyEquation reference state
  · intro before
    let entered := before.1.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
    let final := (bodyRecord (entered, before.2)).1.1
    let returned := Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh final
    have enteredReads : transport.ReadsAs before.1 entered :=
      (Transport.id ctx).workspaceTransport_readsAs_pushWorkspace _ _ _
        (Transport.workspaceTransport_readsAs_id before.1)
    have returnedReads : transport.ReadsAs returned final :=
      ((Transport.id ctx).workspaceTransport_readsAs_underWorkspace_iff _ _ _).mpr
        (Transport.workspaceTransport_readsAs_id returned)
    constructor
    · intro shape other gcdFree leftFree rightFree
      have frame := (bodyCorrect (entered, before.2)).1
        (transport.liftInput other) (scratchFree other)
        (by simpa only [RawOutputs.transport, transport.liftWrite_key,
          transport.liftInput_storageKeys] using gcdFree)
        (by simpa only [RawOutputs.transport, transport.liftWrite_key,
          transport.liftInput_storageKeys] using leftFree)
        (by simpa only [RawOutputs.transport, transport.liftWrite_key,
          transport.liftInput_storageKeys] using rightFree)
      exact (returnedReads other).symm.trans (frame.trans (enteredReads other))
    · have actual := (bodyCorrect (entered, before.2)).2
      have result := (xgcdNativeRawOutputs_matches_transport outputs transport returned final
        returnedReads _).mp actual
      rw [enteredReads modulus, enteredReads denominator] at result
      exact result

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
