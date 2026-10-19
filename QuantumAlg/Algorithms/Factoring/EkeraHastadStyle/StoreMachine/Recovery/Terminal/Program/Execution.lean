/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program

/-!
# Actual terminal decoder execution equations

The native bit fold, copied working word and native high/low split compose
on chronological stores. Two-sample decoding preserves both actual paths and
the complete quantum-reference blocks of the original incoming state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual native bit fold materializes the full word and retains every original state block. -/
lemma fullDecodeInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (fullDecodeInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := fullDecodeStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (TerminalDecode.terminalDecode_fold_execute refs.full
    (List.ofFn (fun index => decoderInputs refs (TerminalDecode.sourceIndex .littleEndian index)))
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The original scratch word is split by the complete actual native interpreter. -/
lemma splitFullInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (splitFullInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := splitFullStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Word.Split.splitInto_execute (splitRefs refs) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Copying the actual full word feeds its actual split without altering reference correlations. -/
lemma copySplitInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (copySplitInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := copySplitStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (BitWord.instruction (execution := model) (copyOp refs)) (splitFullInto refs)
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (copyOp refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := splitFullStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute
      (environment := environment) _ current)
    (fun reference _history _ current => splitFullInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- One actual terminal result feeds the actual native full-word and pair extraction. -/
lemma decodeInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decodeInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := decodeStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (fullDecodeInto refs) (copySplitInto refs)
    (fun before =>
      let actual := fullDecodeStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := copySplitStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => fullDecodeInto_execute refs reference current)
    (fun reference _history _ current => copySplitInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Two actual terminal results are decoded sequentially in the original full state. -/
lemma decodePairInto_execute (refs : PairRefs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decodePairInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := decodePairStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (decodeInto refs.first) (decodeInto refs.second)
    (fun before =>
      let actual := decodeStep refs.first before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := decodeStep refs.second before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => decodeInto_execute refs.first reference current)
    (fun reference _history _ current => decodeInto_execute refs.second reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine
