/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation

/-!
# Full execution of the original preparation prefix

The actual component records compose on their real intermediate stores.
All quantum-reference matrix blocks and all chronological paths survive the
complete decoder, constant preparation, two scalings and final branch.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

omit [BitWord.Selected model] in
private lemma execute_preservingServiceSequence
    (first second : Circuit model ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      first.execute environment Reference state = state.mapClassical (fun entry =>
        let result := firstStep entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.execute environment Reference state = state.mapClassical (fun entry =>
        let result := secondStep entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq first second).execute
      environment Reference state = state.mapClassical (fun entry =>
      let head := firstStep entry.1
      let tail := secondStep head.1
      (tail.1, (entry.2.1, (entry.2.2, (head.2, tail.2))))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) first second
    (fun before => let result := firstStep before.1; ((result.1, before.2), result.2))
    (fun before => let result := secondStep before.1; ((result.1, before.2), result.2))
    ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (firstEquation reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact (secondEquation reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual decoding and splitting preserve the complete service/reference record. -/
lemma preparationDecode_execute
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preparationDecode (model := model) input refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := preparationDecodeStep (model := model) input refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (execute_preservingServiceSequence _ _ _ _
    (measuredDecodeInto_execute (model := model) input refs.decoded)
    (Word.Split.splitInto_execute (model := model) refs.split) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The modulus loader and single denominator seed retain all service/reference correlations. -/
lemma preparationConstants_execute (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preparationConstants (model := model) spec refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := preparationConstantsStep (model := model) spec refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (execute_preservingServiceSequence _ _ _ _
    (ConstantWord.constantWord_fold_execute (model := model) refs.modulusWide
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)))
    (scaleSeed_execute (model := model) refs.denominator) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Both actual scaling triples share their scratch and record all six native outputs. -/
lemma preparationScale_execute (refs : PreparationRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preparationScale (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := preparationScaleStep (model := model) refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  scalePairBody_execute (model := model) (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator)
    refs.product refs.division refs.left refs.right Reference state

/-- The actual narrowed modulus and equality result determine the real final native branch. -/
lemma preparationFinalize_execute (refs : PreparationRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preparationFinalize (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := preparationFinalizeStep (model := model) refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (execute_preservingServiceSequence _ _ _ _
    (fun _ {_} _ initial => BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model) refs.narrowOp initial)
    (negateBody_execute (model := model) (scaleRead refs.modulus) (scaleRead refs.right)
      (scaleRead refs.zero) refs.negationFlag refs.negatedRight) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete original prefix retains all shared state and actual chronological paths. -/
lemma preparationBody_execute (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preparationBody (model := model) spec input refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := preparationStep (model := model) spec input refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (execute_preservingServiceSequence
    (preparationDecodeSeed (model := model) spec input refs)
    (preparationScaleFinalize (model := model) refs)
    (fun before =>
      let decoded := preparationDecodeStep (model := model) input refs before
      let seeded := preparationConstantsStep (model := model) spec refs decoded.1
      (seeded.1, (decoded.2, seeded.2)))
    (fun before =>
      let scaled := preparationScaleStep (model := model) refs before
      let finalized := preparationFinalizeStep (model := model) refs scaled.1
      (finalized.1, (scaled.2, finalized.2)))
    ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (execute_preservingServiceSequence
      (preparationDecode (model := model) input refs)
      (preparationConstants (model := model) spec refs)
      (preparationDecodeStep (model := model) input refs)
      (preparationConstantsStep (model := model) spec refs)
      (preparationDecode_execute (model := model) input refs)
      (preparationConstants_execute (model := model) spec refs) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact (execute_preservingServiceSequence
      (preparationScale (model := model) refs) (preparationFinalize (model := model) refs)
      (preparationScaleStep (model := model) refs) (preparationFinalizeStep (model := model) refs)
      (preparationScale_execute (model := model) refs)
      (preparationFinalize_execute (model := model) refs) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
