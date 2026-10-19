/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Encoding
import all QuantumAlg.Components.Classical.Modular.NativePower.Correctness
import all QuantumAlg.Components.Classical.Modular.NativePower.Preservation

/-!
# Actual stored-candidate modular-return validation

The existing native modular-power circuit consumes the real base and candidate
references. Three subsequent instructions compare the candidate against an
actual zero word, compare the produced residue against an actual one word,
and conjoin those two stored Boolean results. The returned path is the path
of those same actions, including every selected modular multiplication.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth candidateWidth : Nat}

/-- A real less-than instruction tests positivity of the stored candidate. -/
def candidatePositiveOp (zero candidate : CInputRef ctx (.unsignedWord candidateWidth))
    (positive : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord candidateWidth) (.unsignedWord candidateWidth))
      .bit ctx ctx :=
  .wordBinary .lessThan candidateWidth ctx (.product zero candidate) positive

/-- A real equality instruction compares the produced residue with the stored one word. -/
def candidateReturnOp (power one : CInputRef ctx (.unsignedWord modulusWidth))
    (valid : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord modulusWidth) (.unsignedWord modulusWidth))
      .bit ctx ctx :=
  .wordBinary .equal modulusWidth ctx (.product power one) valid

/-- The final actual conjunction reads both stored comparison results. -/
def candidateValidOp (positive valid : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (cellRead positive) (cellRead valid)) valid

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- All three post-power comparison instructions act on their actual references. -/
def validationChecks (zero candidate : CInputRef ctx (.unsignedWord candidateWidth))
    (power one : CInputRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (candidatePositiveOp zero candidate positive))
    (.seq (BitWord.instruction (execution := model) (candidateReturnOp power one valid))
      (BitWord.instruction (execution := model) (candidateValidOp positive valid)))

/-- The actual comparison store used by the following acceptance branch. -/
def validationChecksStore {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (zero candidate : CInputRef ctx (.unsignedWord candidateWidth))
    (power one : CInputRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) (store : Store ctx) : Store ctx :=
  ((store.applyOp (candidatePositiveOp zero candidate positive)).applyOp
    (candidateReturnOp power one valid)).applyOp (candidateValidOp positive valid)

/-- Actual returned values and caller store of the three comparison instructions. -/
def validationChecksStep (zero candidate : CInputRef ctx (.unsignedWord candidateWidth))
    (power one : CInputRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (validationChecks (model := model) zero candidate power one positive valid).Path :=
  let first := BitWord.instructionStep (execution := model)
    (candidatePositiveOp zero candidate positive) store
  let second := BitWord.instructionStep (execution := model)
    (candidateReturnOp power one valid) first.1
  let third := BitWord.instructionStep (execution := model)
    (candidateValidOp positive valid) second.1
  (third.1, (first.2, (second.2, third.2)))

/-- The complete candidate validation invokes native power and the three actual comparisons. -/
def validate (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (Modular.NativePower.into (model := model) spec base candidate power)
    (validationChecks (model := model) zero candidate (cellRead power) one positive valid)

/-- The actual power path and comparison writes determine the complete validation record. -/
def validateStep (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (validate (model := model) spec base candidate zero one power
      positive valid).Path :=
  let powered := Modular.NativePower.intoStep (model := model) spec base candidate power store
  let checked := validationChecksStep (model := model) zero candidate (cellRead power) one
    positive valid powered.1
  (checked.1, (powered.2, checked.2))

/-- The actual interpreter composes source-word power with its real stored comparisons. -/
lemma nativeValidation_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (validate (model := model) spec base candidate zero one power
      positive valid).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((validateStep (model := model) spec base candidate zero one power
          positive valid entry.1).1,
          (entry.2.1, (entry.2.2,
            (validateStep (model := model) spec base candidate zero one power
          positive valid entry.1).2)))) := by
  simp only [validate, validationChecks, Circuit.execute_seq,
    Modular.NativePower.nativePower_into_execute, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Validation preserves every actual borrowed classical value before any branch is chosen. -/
lemma nativeValidation_borrowed_values (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) (store : Store ctx) :
    (validateStep (model := model) spec base candidate zero one power
          positive valid store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [validateStep, validationChecksStep, BitWord.instructionStep,
    Store.readBorrowedClassical_applyOp,
    Modular.NativePower.nativePower_into_borrowed_values]

/-- The actual validation trace appends exactly the three real checks to native power. -/
lemma nativeValidation_eventTrace (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit)
    (path : (validate (model := model) spec base candidate zero one power
      positive valid).Path) :
    (validate (model := model) spec base candidate zero one power
      positive valid).eventTrace path =
      (Modular.NativePower.into (model := model) spec base candidate power).eventTrace path.1 ++
        [.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordBinary .lessThan candidateWidth)),
          .classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordBinary .equal modulusWidth)),
          .classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.bit .and))] := by
  simp only [validate, validationChecks, Circuit.eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The real checks add three dependent unit-time instructions to the actual power path. -/
lemma nativeValidation_unitDepth (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit)
    (path : (validate (model := model) spec base candidate zero one power
      positive valid).Path) :
    (validate (model := model) spec base candidate zero one power
      positive valid).depth (fun _ => 1) path =
      (Modular.NativePower.into (model := model) spec base candidate power).depth
        (fun _ => 1) path.1 + 3 := by
  rcases path with ⟨powerPath, positivePath, returnPath, validPath⟩
  simp only [validate, validationChecks, Circuit.depth_seq, BitWord.bitWord_instruction_depth]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
