/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Classification

/-!
# Actual conditional signed-coefficient magnitude

The stored sign bit selects the original copy-only or copy, complement,
increment instruction sequence. The raw input is read before the first
write; no initial output value or input/output separation is required.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The first actual instruction reads the original coefficient into the work word. -/
def magnitudeCopyOp (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) :
    ClassicalOp (.unsignedWord (signedWidth width)) (.unsignedWord (signedWidth width)) ctx ctx :=
  .wordUnary .copy (signedWidth width) ctx raw work

/-- The original branch has three instructions for a negative coefficient and one otherwise. -/
def magnitudeChoice {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (value : CShape.Value .bit) : Circuit model ctx ctx :=
  if value.toBool then
    .seq (BitWord.instruction (execution := model) (magnitudeCopyOp raw work))
      (.seq (BitWord.instruction (execution := model) (signUnaryOp .complement work))
        (BitWord.instruction (execution := model) (signUnaryOp .increment work)))
  else BitWord.instruction (execution := model) (magnitudeCopyOp raw work)

/-- The literal chosen store is obtained by the same actual operations. -/
def magnitudeChoiceStore (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (value : CShape.Value .bit) (store : Store ctx) : Store ctx :=
  if value.toBool then
    ((store.applyOp (magnitudeCopyOp raw work)).applyOp (signUnaryOp .complement work)).applyOp
      (signUnaryOp .increment work)
  else store.applyOp (magnitudeCopyOp raw work)

/-- The native path records precisely the selected sequence. -/
def magnitudeChoiceStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (magnitudeChoice (model := model) raw work value).Path :=
  match value with
  | .bit false => BitWord.instructionStep (execution := model) (magnitudeCopyOp raw work) store
  | .bit true =>
      let first := BitWord.instructionStep (execution := model) (magnitudeCopyOp raw work) store
      let second := BitWord.instructionStep (execution := model) (signUnaryOp .complement work)
        first.1
      let third := BitWord.instructionStep (execution := model) (signUnaryOp .increment work)
        second.1
      (third.1, (first.2, (second.2, third.2)))

/-- The branch selector is the actual retained stored sign bit. -/
def signedMagnitude {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CInputRef ctx .bit) : Circuit model ctx ctx :=
  .branch negative (magnitudeChoice (model := model) raw work)

/-- Complete actual selected store and classical branch history. -/
def signedMagnitudeStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CInputRef ctx .bit) (store : Store ctx) :
    Store ctx × (signedMagnitude (model := model) raw work negative).Path :=
  let value := store.read negative
  let chosen := magnitudeChoiceStep (model := model) raw work value store
  (chosen.1, ⟨value, chosen.2⟩)

/-- Both literal branches preserve complete quantum-reference blocks and the original history. -/
theorem magnitudeChoice_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (magnitudeChoice (model := model) raw work value).execute Reference state =
      state.mapClassical (fun entry =>
      ((magnitudeChoiceStep (model := model) raw work value entry.1).1,
        (entry.2.1, (entry.2.2, (magnitudeChoiceStep (model := model) raw work value
          entry.1).2)))) := by
  cases value with
  | bit value =>
      cases value
      · change (BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).execute
          Reference state = _
        exact (BitWord.bitWord_instruction_execute (execution := model)
          (magnitudeCopyOp raw work) state).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl)
      · change (Circuit.seq
          (BitWord.instruction (execution := model) (magnitudeCopyOp raw work))
          (.seq (BitWord.instruction (execution := model) (signUnaryOp .complement work))
            (BitWord.instruction (execution := model) (signUnaryOp .increment work)))).execute
              Reference state = _
        simp only [Circuit.execute_seq, BitWord.bitWord_instruction_execute, State.mapHistory,
          ExecutionState.executionState_mapClassical_comp, Function.comp_def]
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual stored-bit branch preserves the full reference-correlated execution state. -/
theorem signedMagnitude_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (signedMagnitude (model := model) raw work negative).execute Reference state =
      state.mapClassical (fun entry =>
      ((signedMagnitudeStep (model := model) raw work negative entry.1).1,
        (entry.2.1, (entry.2.2, (signedMagnitudeStep (model := model) raw work negative
          entry.1).2)))) := by
  refine (Circuit.execute_branch_mapClassical negative (magnitudeChoice (model := model) raw work)
    (fun value before =>
      let result := magnitudeChoiceStep (model := model) raw work value before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro value reference history _ initial
    exact (magnitudeChoice_execute (model := model) raw work value reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The selected exact fixed-width arithmetic, without a sign-correctness assumption. -/
def magnitudeWord (raw : CShape.Word (signedWidth width)) (negative : Bool) :
    CShape.Word (signedWidth width) :=
  if negative then Resource.WordUnaryOpcode.eval .increment (signedWidth width)
    (Resource.WordUnaryOpcode.eval .complement (signedWidth width) raw) else raw

/-- The actual chosen output equals its exact fixed-width word for arbitrary original stores. -/
theorem magnitudeChoice_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (value : CShape.Value .bit)
    (store : Store ctx) :
    (magnitudeChoiceStep (model := model) raw work value store).1.read (signedRead work) =
      magnitudeWord (store.read raw) value.toBool := by
  have copied : (store.applyOp (magnitudeCopyOp raw work)).read (signedRead work) =
      store.read raw := Store.read_applyOp_output store (magnitudeCopyOp raw work)
  cases value with
  | bit value =>
      cases value
      · exact copied
      · let entered := store.applyOp (magnitudeCopyOp raw work)
        let complemented := entered.applyOp (signUnaryOp .complement work)
        have complementValue : complemented.read (signedRead work) =
            Resource.WordUnaryOpcode.eval .complement (signedWidth width)
              (entered.read (signedRead work)) :=
          Store.read_applyOp_output entered (signUnaryOp .complement work)
        have incrementValue : (complemented.applyOp (signUnaryOp .increment work)).read
            (signedRead work) = Resource.WordUnaryOpcode.eval .increment (signedWidth width)
              (complemented.read (signedRead work)) :=
          Store.read_applyOp_output complemented (signUnaryOp .increment work)
        change (complemented.applyOp (signUnaryOp .increment work)).read (signedRead work) = _
        rw [incrementValue, complementValue, copied]
        rfl

/-- Correct classification yields the original mathematical magnitude. -/
theorem magnitudeWord_original_toNat (raw : CShape.Word (signedWidth width)) :
    (magnitudeWord raw (rawIsNegative raw)).toNat = rawMagnitude raw := by
  unfold magnitudeWord rawMagnitude
  by_cases negative : rawIsNegative raw = true
  · simp only [negative, if_true]
    exact complementIncrement_toNat raw (rawIsNegative_true_toNat_pos raw negative)
  · simp only [negative, Bool.false_eq_true, if_false]

/-- The actual selector yields the original magnitude after its preceding classification. -/
theorem signedMagnitude_original_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (store : Store ctx)
    (classified : (store.read negative).toBool = rawIsNegative (store.read raw)) :
    ((signedMagnitudeStep (model := model) raw work negative store).1.read (signedRead
      work)).toNat =
      rawMagnitude (store.read raw) := by
  change ((magnitudeChoiceStep (model := model) raw work (store.read negative) store).1.read
    (signedRead work)).toNat = _
  rw [magnitudeChoice_value, classified, magnitudeWord_original_toNat]

/-- Every actual branch preserves all reads outside its one work-word destination. -/
theorem magnitudeChoice_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape) (separate : work.key ∉ other.storageKeys)
    (store : Store ctx) :
    (magnitudeChoiceStep (model := model) raw work value store).1.read other = store.read other
      := by
  cases value with
  | bit value =>
      cases value
      · exact Store.read_applyOp_of_not_mem_storageKeys _
          (magnitudeCopyOp raw work) other separate
      · change (((store.applyOp (magnitudeCopyOp raw work)).applyOp
          (signUnaryOp .complement work)).applyOp (signUnaryOp .increment work)).read other = _
        rw [Store.read_applyOp_of_not_mem_storageKeys _
          (signUnaryOp .increment work) other separate,
          Store.read_applyOp_of_not_mem_storageKeys _
            (signUnaryOp .complement work) other separate,
          Store.read_applyOp_of_not_mem_storageKeys _ (magnitudeCopyOp raw work) other separate]

/-- The stored sign and all caller reads remain available after magnitude selection. -/
theorem signedMagnitude_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    {shape : CShape} (other : CInputRef ctx shape) (separate : work.key ∉ other.storageKeys)
    (store : Store ctx) :
    (signedMagnitudeStep (model := model) raw work negative store).1.read other = store.read
      other :=
  magnitudeChoice_read_other raw work (store.read negative) other separate store

/-- Independent original copy-only or copy, complement, increment event sequence. -/
def signedMagnitudeEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat)
  (negative : Bool) :
    List (Resource.Event model) :=
  if negative then
    [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy (signedWidth width))),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .complement (signedWidth width))),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (signedWidth width)))]
  else [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy (signedWidth width)))]

/-- The actual selected path emits precisely the original magnitude instructions. -/
theorem signedMagnitude_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude (model := model) raw work negative).Path) :
    (signedMagnitude (model := model) raw work negative).eventTrace path =
      signedMagnitudeEvents model width path.1.toBool := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).Path at path
        change (BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).eventTrace
          path = _
        rw [BitWord.bitWord_instruction_eventTrace]
        rfl
      · change ((BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).Path ×
          ((BitWord.instruction (execution := model) (signUnaryOp .complement work)).Path ×
            (BitWord.instruction (execution := model) (signUnaryOp .increment work)).Path)) at path
        change ((BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).eventTrace
          path.1 ++ ((BitWord.instruction (execution := model)
            (signUnaryOp .complement work)).eventTrace path.2.1 ++
              (BitWord.instruction (execution := model) (signUnaryOp .increment work)).eventTrace
                path.2.2)) = _
        rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
          BitWord.bitWord_instruction_eventTrace]
        rfl

/-- The resource pool is obtained from the same selected true event trace. -/
theorem signedMagnitude_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude (model := model) raw work negative).Path) :
    (signedMagnitude (model := model) raw work negative).resourcePool path =
      ResourcePool.ofList (signedMagnitudeEvents model width path.1.toBool) :=
  congrArg ResourcePool.ofList (signedMagnitude_eventTrace raw work negative path)

/-- Arbitrary native durations charge the selected sequential operations exactly. -/
theorem signedMagnitude_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (duration : Resource.Event model → Nat)
    (path : (signedMagnitude (model := model) raw work negative).Path) :
    (signedMagnitude (model := model) raw work negative).depth duration path =
      ((signedMagnitudeEvents model width path.1.toBool).map duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).Path at path
        change (BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).depth
          duration path = _
        rw [BitWord.bitWord_instruction_depth]
        rfl
      · change ((BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).Path ×
          ((BitWord.instruction (execution := model) (signUnaryOp .complement work)).Path ×
            (BitWord.instruction (execution := model) (signUnaryOp .increment work)).Path)) at path
        rcases path with ⟨first, second, third⟩
        change (Circuit.seq (BitWord.instruction (execution := model) (magnitudeCopyOp raw work))
          (.seq (BitWord.instruction (execution := model) (signUnaryOp .complement work))
            (BitWord.instruction (execution := model) (signUnaryOp .increment work)))).depth
              duration (first, (second, third)) = _
        simp only [Circuit.depth_seq, BitWord.bitWord_instruction_depth]
        rfl

/-- The original branch has depth three on a negative sign and one otherwise. -/
theorem signedMagnitude_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude (model := model) raw work negative).Path) :
    (signedMagnitude (model := model) raw work negative).depth (fun _ => 1) path =
      if path.1.toBool then 3 else 1 := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Both magnitude branches retain exactly the actual resident context. -/
theorem signedMagnitude_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude (model := model) raw work negative).Path) :
    (signedMagnitude (model := model) raw work negative).peakResidentSpace path =
      ctx.residentSpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.residentSpace 0 = _
        exact SpacePool.max_zero _
      · change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace
          (SpacePool.max ctx.residentSpace 0)) = _
        simp only [SpacePool.max_zero, SpacePool.max_self]

/-- Both magnitude branches retain exactly the actual auxiliary context. -/
theorem signedMagnitude_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude (model := model) raw work negative).Path) :
    (signedMagnitude (model := model) raw work negative).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.auxiliarySpace 0 = _
        exact SpacePool.max_zero _
      · change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace
          (SpacePool.max ctx.auxiliarySpace 0)) = _
        simp only [SpacePool.max_zero, SpacePool.max_self]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
