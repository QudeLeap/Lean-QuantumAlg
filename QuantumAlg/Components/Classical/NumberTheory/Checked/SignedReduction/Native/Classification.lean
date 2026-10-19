/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Word

/-!
# Actual signed-coefficient classification

Five native instructions construct the two's-complement sign threshold from
the actual zero work word, compare the original raw coefficient and negate
the stored comparison bit. Initialization and internal separation are supplied
by the enclosing lexical allocation. No inverse property is assumed here.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural read of an actual signed-reduction cell. -/
def signedRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- One original in-place unary operation on the signed-width work word. -/
def signUnaryOp (opcode : Resource.WordUnaryOpcode)
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) :
    ClassicalOp (.unsignedWord (signedWidth width)) (.unsignedWord (signedWidth width)) ctx ctx :=
  .wordUnary opcode (signedWidth width) ctx (signedRead work) work

/-- Compare the actual raw coefficient against the materialized sign threshold. -/
def signCompareOp (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord (signedWidth width))
      (.unsignedWord (signedWidth width))) .bit ctx ctx :=
  .wordBinary .lessThan (signedWidth width) ctx (.product raw (signedRead work)) negative

/-- Negate the actual stored less-than result. -/
def signNotOp (negative : CWriteRef ctx .bit) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (signedRead negative) negative

/-- The original five operations, in their original chronological order. -/
def signClassification {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (signUnaryOp .complement work))
    (.seq (BitWord.instruction (execution := model) (signUnaryOp .shiftRight work))
      (.seq (BitWord.instruction (execution := model) (signUnaryOp .increment work))
        (.seq (BitWord.instruction (execution := model) (signCompareOp raw work negative))
            (BitWord.instruction (execution := model) (signNotOp negative)))))

/-- Literal store update of those same five instructions. -/
def signClassificationStore (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (signUnaryOp .complement work)).applyOp
    (signUnaryOp .shiftRight work)).applyOp (signUnaryOp .increment work)).applyOp
      (signCompareOp raw work negative)).applyOp (signNotOp negative)

/-- The true store and native path are retained for later composition. -/
def signClassificationStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (signClassification (model := model) raw work negative).Path :=
  let first := BitWord.instructionStep (execution := model) (signUnaryOp .complement work) store
  let second := BitWord.instructionStep (execution := model) (signUnaryOp .shiftRight work) first.1
  let third := BitWord.instructionStep (execution := model) (signUnaryOp .increment work) second.1
  let fourth := BitWord.instructionStep (execution := model) (signCompareOp raw work negative)
      third.1
  let fifth := BitWord.instructionStep (execution := model) (signNotOp negative) fourth.1
  (fifth.1, (first.2, (second.2, (third.2, (fourth.2, fifth.2)))))

/-- Every complete quantum-reference block and old history survives the actual classifier. -/
lemma signClassification_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (signClassification (model := model) raw work negative).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := signClassificationStep (model := model) raw work negative entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [signClassification, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma signUnary_read (opcode : Resource.WordUnaryOpcode)
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (store : Store ctx) :
    (store.applyOp (signUnaryOp opcode work)).read (signedRead work) =
      opcode.eval (signedWidth width) (store.read (signedRead work)) :=
  Store.read_applyOp_output store (signUnaryOp opcode work)

/-- All structural reads outside the two written cells are preserved exactly. -/
lemma signClassification_read_other
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) {shape : CShape} (other : CInputRef ctx shape)
    (workFree : work.key ∉ other.storageKeys) (negativeFree : negative.key ∉ other.storageKeys)
    (store : Store ctx) :
    (signClassificationStore raw work negative store).read other = store.read other := by
  unfold signClassificationStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (signNotOp negative) other negativeFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (signCompareOp raw work negative) other negativeFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (signUnaryOp .increment work) other workFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (signUnaryOp .shiftRight work) other workFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (signUnaryOp .complement work) other workFree]

/-- Actual zero initialization and internal separation yield the original sign predicate. -/
lemma signClassification_values (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (store : Store ctx)
    (initialZero : (store.read (signedRead work)).toNat = 0)
    (rawFree : work.key ∉ raw.storageKeys) (distinct : negative.key ≠ work.key) :
    let final := signClassificationStore raw work negative store
    (final.read (signedRead negative)).toBool = rawIsNegative (store.read raw) ∧
      (final.read (signedRead work)).toNat = 2 ^ (signedWidth width - 1) := by
  let complemented := store.applyOp (signUnaryOp .complement work)
  let shifted := complemented.applyOp (signUnaryOp .shiftRight work)
  let incremented := shifted.applyOp (signUnaryOp .increment work)
  let compared := incremented.applyOp (signCompareOp raw work negative)
  have complementedValue : (complemented.read (signedRead work)).toNat =
      CShape.wordModulus (signedWidth width) - 1 := by
    rw [signUnary_read]
    exact wordComplement_zero_toNat _ initialZero
  have shiftedValue : (shifted.read (signedRead work)).toNat =
      2 ^ (signedWidth width - 1) - 1 := by
    rw [signUnary_read]
    exact wordShiftRight_fullMinusOne_toNat (signedWidth_pos width) _ complementedValue
  have incrementedValue : (incremented.read (signedRead work)).toNat =
      2 ^ (signedWidth width - 1) := by
    rw [signUnary_read]
    exact wordIncrement_belowThreshold_toNat (signedWidth_pos width) _ shiftedValue
  have rawValue : incremented.read raw = store.read raw := by
    dsimp only [incremented, shifted, complemented]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (signUnaryOp .increment work) raw rawFree,
      Store.read_applyOp_of_not_mem_storageKeys _ (signUnaryOp .shiftRight work) raw rawFree,
      Store.read_applyOp_of_not_mem_storageKeys _ (signUnaryOp .complement work) raw rawFree]
  have comparison : compared.read (signedRead negative) =
      .bit (decide ((incremented.read raw).toNat <
        (incremented.read (signedRead work)).toNat)) :=
    Store.read_applyOp_output incremented (signCompareOp raw work negative)
  have negation : (compared.applyOp (signNotOp negative)).read (signedRead negative) =
      Resource.BitOpcode.not.eval (compared.read (signedRead negative)) :=
    Store.read_applyOp_output compared (signNotOp negative)
  dsimp only
  constructor
  · change ((compared.applyOp (signNotOp negative)).read (signedRead negative)).toBool = _
    rw [negation, bitNotEval_toBool, comparison, rawValue, incrementedValue]
    simp only [CShape.Value.toBool]
    unfold rawIsNegative
    by_cases threshold : 2 ^ (signedWidth width - 1) ≤ (store.read raw).toNat <;> simp_all
  · change ((compared.applyOp (signNotOp negative)).read (signedRead work)).toNat = _
    have afterNot : (compared.applyOp (signNotOp negative)).read (signedRead work) =
        compared.read (signedRead work) :=
      Store.read_write_other compared negative work.toCStorageRef _ distinct
    have afterCompare : compared.read (signedRead work) = incremented.read (signedRead work) :=
      Store.read_write_other incremented negative work.toCStorageRef _ distinct
    rw [afterNot, afterCompare, incrementedValue]

/-- Independent original five-operation sign list. -/
def signClassificationEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .complement
      (signedWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
        .shiftRight (signedWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .increment
        (signedWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .lessThan
        (signedWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))]

/-- The trace is precisely the original classifier, including the stored-bit negation. -/
lemma signClassification_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (path : (signClassification (model := model) raw work
        negative).Path) :
    (signClassification (model := model) raw work negative).eventTrace path =
      signClassificationEvents model width := by
  change (BitWord.instruction (execution := model) (signUnaryOp .complement work)).eventTrace
    path.1 ++ ((BitWord.instruction (execution := model) (signUnaryOp .shiftRight work)).eventTrace
      path.2.1 ++ ((BitWord.instruction (execution := model) (signUnaryOp .increment
          work)).eventTrace
        path.2.2.1 ++ ((BitWord.instruction (execution := model)
          (signCompareOp raw work negative)).eventTrace path.2.2.2.1 ++
          (BitWord.instruction (execution := model) (signNotOp negative)).eventTrace
            path.2.2.2.2))) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual resources count the same five instructions. -/
lemma signClassification_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (path : (signClassification (model := model) raw work
        negative).Path) :
    (signClassification (model := model) raw work negative).resourcePool path =
      ResourcePool.ofList (signClassificationEvents model width) :=
  congrArg ResourcePool.ofList (signClassification_eventTrace raw work negative path)

/-- All five operations are sequential for any native duration assignment. -/
lemma signClassification_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (duration : Resource.Event model → Nat) (path : (signClassification (model := model) raw
        work negative).Path) :
    (signClassification (model := model) raw work negative).depth duration path =
      ((signClassificationEvents model width).map duration).sum := by
  rcases path with ⟨first, second, third, fourth, fifth⟩
  simp only [signClassification, Circuit.depth_seq, BitWord.bitWord_instruction_depth]
  rfl

/-- The literal classifier has five unit-duration operations. -/
lemma signClassification_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (path : (signClassification (model := model) raw work
        negative).Path) :
    (signClassification (model := model) raw work negative).depth (fun _ => 1) path = 5 := rfl

/-- The unplaced classifier retains exactly its complete resident context. -/
lemma signClassification_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (path : (signClassification (model := model) raw work
        negative).Path) :
    (signClassification (model := model) raw work negative).peakResidentSpace path =
        ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace
    (SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace
      (SpacePool.max ctx.residentSpace 0)))) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

/-- The unplaced classifier retains exactly its complete auxiliary context. -/
lemma signClassification_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CWriteRef ctx .bit) (path : (signClassification (model := model) raw work
        negative).Path) :
    (signClassification (model := model) raw work negative).peakAuxiliarySpace path =
        ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace
    (SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace
      (SpacePool.max ctx.auxiliarySpace 0)))) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
