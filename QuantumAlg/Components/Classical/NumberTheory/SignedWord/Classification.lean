/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification.Values
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual sign classification and conditional magnitude

One native bit instruction writes the raw word's sign: a structural read
selects its most-significant bit at positive width, and self-XOR writes false
at width zero. No initialized work word or constructed threshold is needed.
Magnitude selection reads the stored sign and executes either one copy or
complement followed by increment. Every contract concerns the same actual
circuit and store updates, including arbitrary incoming quantum references.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural read of a caller-owned writable cell. -/
abbrev writeInput {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Actual copying of the most-significant raw bit into its writable flag. -/
def signBitOp (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (positive : 0 < width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .copy ctx (.wordBitGet raw ⟨0, positive⟩) negative

/-- Actual self-XOR clears the sign when no raw bits exist. -/
def clearSignOp (negative : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (writeInput negative) (writeInput negative)) negative

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- A single native instruction classifies every raw width, including zero. -/
def classifySign (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  match width, raw with
  | 0, _ => BitWord.instruction (execution := model) (clearSignOp negative)
  | n + 1, raw => BitWord.instruction (execution := model) (signBitOp raw negative (Nat.succ_pos n))

/-- The actual instruction's store update. -/
def signStore {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (store : Store ctx) : Store ctx :=
  match width, raw with
  | 0, _ => store.applyOp (clearSignOp negative)
  | n + 1, raw => store.applyOp (signBitOp raw negative (Nat.succ_pos n))

/-- Actual returned native output of the sign instruction on the incoming store. -/
def signPath (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (store : Store ctx) :
    (classifySign (model := model) raw negative).Path := by
  cases width with
  | zero => exact (BitWord.instructionStep (execution := model) (clearSignOp negative) store).2
  | succ width => exact (BitWord.instructionStep (execution := model)
      (signBitOp raw negative (Nat.succ_pos width)) store).2

/-- The actual sign write retains complete prior history and shared service state. -/
lemma classifySign_execute (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (classifySign (model := model) raw negative).execute environment Reference state =
      state.mapClassical (fun entry =>
        (signStore raw negative entry.1,
          (entry.2.1, (entry.2.2, signPath (model := model) raw negative entry.1)))) := by
  cases width
  all_goals exact BitWord.bitWord_instruction_execute (environment := environment) _ state

/-- The stored flag is exactly the raw sign, with no initialized-scratch premise. -/
lemma rawWord_classifySign_correct {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (store : Store ctx) :
    ((signStore raw negative store).read (writeInput negative)).toBool =
      rawIsNegative (store.read raw) := by
  cases width with
  | zero =>
      rw [rawIsNegative_zero]
      simp only [signStore]
      change ((store.applyOp (clearSignOp negative)).read
        (.storage (clearSignOp negative).outputRef.toCStorageRef)).toBool = false
      rw [Store.read_applyOp_output]
      change (Resource.BitOpcode.xor.eval
        (.product (store.read (writeInput negative))
          (store.read (writeInput negative)))).toBool = false
      cases value : store.read (writeInput negative) with
      | bit flag => exact Bool.xor_self flag
  | succ width =>
      simp only [signStore]
      change ((store.applyOp (signBitOp raw negative (Nat.succ_pos width))).read
        (.storage (signBitOp raw negative (Nat.succ_pos width)).outputRef.toCStorageRef)).toBool = _
      rw [Store.read_applyOp_output]
      exact rawIsNegative_eq_signBit (store.read raw)

/-- Sign classification changes only its actual writable flag. -/
lemma classifySign_callerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (separate : negative.key ∉ other.storageKeys) :
    (signStore raw negative store).read other = store.read other := by
  cases width <;> exact Store.read_applyOp_of_not_mem_storageKeys store _ other separate

/-- Native sign event selected by the static raw width. -/
def signTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.bit (if 0 < width then .copy else .xor)))]

/-- Every actual sign path records one native bit instruction. -/
lemma classifySign_events (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (path : (classifySign (model := model) raw negative).Path) :
    (classifySign (model := model) raw negative).eventTrace path = signTrace (model := model)
      width := by
  cases width with
  | zero =>
      change (BitWord.instruction (execution := model) (clearSignOp negative)).Path at path
      change (BitWord.instruction (execution := model) (clearSignOp negative)).eventTrace path = _
      rw [BitWord.bitWord_instruction_eventTrace]
      rfl
  | succ width =>
      change (BitWord.instruction (execution := model)
        (signBitOp raw negative (Nat.succ_pos width))).Path at path
      change (BitWord.instruction (execution := model)
        (signBitOp raw negative (Nat.succ_pos width))).eventTrace path = _
      rw [BitWord.bitWord_instruction_eventTrace]
      rfl

/-- The real sign write restores all borrowed values and their external correlations. -/
lemma classifySign_borrowedRestored (raw : CInputRef ctx (.unsignedWord width))
    (negative : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (classifySign (model := model) raw negative).BorrowedRestored Reference state
      ((classifySign (model := model) raw negative).execute environment Reference state) := by
  cases width <;> exact Circuit.borrowedRestored_classical (environment := environment) _ state

/-- The positive arm copies the raw operand into the actual magnitude cell. -/
def magnitudeCopyOp {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (raw : CInputRef ctx (.unsignedWord width))
    (work : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx raw work

/-- The negative arm first complements the original raw operand directly into the output. -/
def magnitudeComplementOp {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (raw : CInputRef ctx (.unsignedWord width))
    (work : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .complement width ctx raw work

/-- The negative arm increments the real complemented output. -/
def magnitudeIncrementOp {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (work : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (writeInput work) work

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The two actual closed instruction sequences selected by the stored flag. -/
def magnitudeArm (raw : CInputRef ctx (.unsignedWord width))
    (work : CWriteRef ctx (.unsignedWord width)) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => BitWord.instruction (execution := model) (magnitudeCopyOp raw work)
  | .bit true => .seq (BitWord.instruction (execution := model) (magnitudeComplementOp raw work))
      (BitWord.instruction (execution := model) (magnitudeIncrementOp work))

/-- The actual chosen arm's store updates and instruction record. -/
def magnitudeArmStep (raw : CInputRef ctx (.unsignedWord width))
    (work : CWriteRef ctx (.unsignedWord width)) (flag : CShape.Value .bit)
    (store : Store ctx) : Store ctx × (magnitudeArm (model := model) raw work flag).Path :=
  match flag with
  | .bit false => BitWord.instructionStep (execution := model) (magnitudeCopyOp raw work) store
  | .bit true =>
      let complemented := BitWord.instructionStep (execution := model)
        (magnitudeComplementOp raw work) store
      let incremented := BitWord.instructionStep (execution := model)
        (magnitudeIncrementOp work) complemented.1
      (incremented.1, (complemented.2, incremented.2))

/-- Read the actual stored flag and perform the corresponding native magnitude arm. -/
def selectMagnitude (raw : CInputRef ctx (.unsignedWord width))
    (negative : CInputRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .branch negative (magnitudeArm (model := model) raw work)

/-- The actual selected instruction path and its store result. -/
def magnitudeStep (raw : CInputRef ctx (.unsignedWord width))
    (negative : CInputRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx × (selectMagnitude (model := model) raw negative work).Path :=
  let chosen := magnitudeArmStep (model := model) raw work (store.read negative) store
  (chosen.1, ⟨store.read negative, chosen.2⟩)

private lemma magnitudeArm_execute (raw : CInputRef ctx (.unsignedWord width))
    (work : CWriteRef ctx (.unsignedWord width)) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (magnitudeArm (model := model) raw work flag).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := magnitudeArmStep (model := model) raw work flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
      cases flag
      · exact BitWord.bitWord_instruction_execute (environment := environment) _ state
      · simp only [magnitudeArm, magnitudeArmStep, Circuit.execute_seq,
          BitWord.bitWord_instruction_execute, State.mapHistory,
          ExecutionState.executionState_mapClassical_comp, Function.comp_def]
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Stored-result selection retains complete incoming history, service and reference blocks. -/
lemma selectMagnitude_execute (raw : CInputRef ctx (.unsignedWord width))
    (negative : CInputRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectMagnitude (model := model) raw negative work).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := magnitudeStep (model := model) raw negative work entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical
    (environment := environment) negative (magnitudeArm (model := model) raw work)
    (fun flag before =>
      let actual := magnitudeArmStep (model := model) raw work flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => magnitudeArm_execute raw work flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- An actual selected magnitude arm writes the exact unsigned magnitude. -/
lemma rawWord_selectMagnitude_correct (raw : CInputRef ctx (.unsignedWord width))
    (negative : CInputRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx)
    (correctSign : (store.read negative).toBool = rawIsNegative (store.read raw)) :
    (((magnitudeStep (model := model) raw negative work store).1).read (writeInput work)).toNat =
      rawMagnitude (store.read raw) := by
  unfold magnitudeStep
  cases stored : store.read negative with
  | bit flag =>
      cases flag
      · have sign : rawIsNegative (store.read raw) = false := by
          simpa only [stored, CShape.Value.toBool] using correctSign.symm
        simp only [magnitudeArmStep, rawMagnitude, sign, Bool.false_eq_true,
          ite_false]
        change ((store.applyOp (magnitudeCopyOp raw work)).read
          (.storage (magnitudeCopyOp raw work).outputRef.toCStorageRef)).toNat = _
        rw [Store.read_applyOp_output]
        rfl
      · have sign : rawIsNegative (store.read raw) = true := by
          simpa only [stored, CShape.Value.toBool] using correctSign.symm
        simp only [magnitudeArmStep, rawMagnitude, sign, ite_true]
        change (((store.applyOp (magnitudeComplementOp raw work)).applyOp
          (magnitudeIncrementOp work)).read
          (.storage (magnitudeIncrementOp work).outputRef.toCStorageRef)).toNat = _
        rw [Store.read_applyOp_output]
        change (Resource.WordUnaryOpcode.eval .increment width
          ((store.applyOp (magnitudeComplementOp raw work)).read
            (.storage (magnitudeComplementOp raw work).outputRef.toCStorageRef))).toNat = _
        rw [Store.read_applyOp_output]
        exact complementIncrement_toNat (store.read raw) (rawIsNegative_true_toNat_pos _ sign)

/-- Every actual arm preserves reads outside the magnitude cell, even when inputs alias it. -/
lemma selectMagnitude_callerFrame (raw : CInputRef ctx (.unsignedWord width))
    (negative : CInputRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : work.key ∉ other.storageKeys) :
    ((magnitudeStep (model := model) raw negative work store).1).read other = store.read other := by
  unfold magnitudeStep
  cases value : store.read negative with
  | bit flag =>
      cases flag
      · exact Store.read_applyOp_of_not_mem_storageKeys store _ other separate
      · change (((store.applyOp (magnitudeComplementOp raw work)).applyOp
          (magnitudeIncrementOp work)).read other) = _
        rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ separate,
          Store.read_applyOp_of_not_mem_storageKeys _ _ _ separate]

/-- Exact native operations performed by the selected magnitude arm. -/
def magnitudeTrace (width : Nat) (negative : Bool) :
    List (Resource.Event model) :=
  if negative then [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .complement width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width))]
  else [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width))]

/-- The actual path charges only the selected arm's one or two native instructions. -/
lemma selectMagnitude_events (raw : CInputRef ctx (.unsignedWord width))
    (negative : CInputRef ctx .bit) (work : CWriteRef ctx (.unsignedWord width))
    (path : (selectMagnitude (model := model) raw negative work).Path) :
    (selectMagnitude (model := model) raw negative work).eventTrace path = magnitudeTrace (model
      := model) width path.1.toBool := by
  rcases path with ⟨flag, armPath⟩
  cases flag with
  | bit flag =>
      cases flag
      · change (BitWord.instruction (execution := model) (magnitudeCopyOp raw work)).Path at armPath
        change (BitWord.instruction (execution := model)
          (magnitudeCopyOp raw work)).eventTrace armPath = _
        rw [BitWord.bitWord_instruction_eventTrace]
        rfl
      · change ((BitWord.instruction (execution := model) (magnitudeComplementOp raw work)).Path ×
          (BitWord.instruction (execution := model) (magnitudeIncrementOp work)).Path) at armPath
        change (BitWord.instruction (execution := model)
          (magnitudeComplementOp raw work)).eventTrace armPath.1 ++
          (BitWord.instruction (execution := model)
            (magnitudeIncrementOp work)).eventTrace armPath.2 = _
        simp only [BitWord.bitWord_instruction_eventTrace]
        rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord
