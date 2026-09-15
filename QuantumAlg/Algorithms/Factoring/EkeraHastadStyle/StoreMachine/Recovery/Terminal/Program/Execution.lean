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

/-- The actual native bit fold materializes the full word and retains every original state block. -/
theorem fullDecodeInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (fullDecodeInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((fullDecodeStep refs entry.1).1, (entry.2, (fullDecodeStep refs entry.1).2))) := by
  refine (TerminalDecode.terminalDecode_fold_execute refs.full
    (List.ofFn (fun index => decoderInputs refs (TerminalDecode.sourceIndex .littleEndian index)))
    Reference state).trans ?_
  congr 1

/-- The original scratch word is split by the complete actual native interpreter. -/
theorem splitFullInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (splitFullInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((splitFullStep refs entry.1).1, (entry.2, (splitFullStep refs entry.1).2))) := by
  refine (Word.Split.splitInto_execute (splitRefs refs) Reference state).trans ?_
  congr 1

/-- Copying the actual full word feeds its actual split without altering reference correlations. -/
theorem copySplitInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (copySplitInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((copySplitStep refs entry.1).1, (entry.2, (copySplitStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (copyOp refs)) (splitFullInto refs)
    (fun store => (store.applyOp (copyOp refs), ())) (splitFullStep refs) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (copyOp refs) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (splitFullInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- One actual terminal result feeds the actual native full-word and pair extraction. -/
theorem decodeInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (decodeInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((decodeStep refs entry.1).1, (entry.2, (decodeStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (fullDecodeInto refs) (copySplitInto refs)
    (fullDecodeStep refs) (copySplitStep refs) (fullDecodeInto_execute refs)
    (copySplitInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Two actual terminal results are decoded sequentially in the original full state. -/
theorem decodePairInto_execute (refs : PairRefs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (decodePairInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((decodePairStep refs entry.1).1, (entry.2, (decodePairStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (decodeInto refs.first) (decodeInto refs.second)
    (decodeStep refs.first) (decodeStep refs.second) (decodeInto_execute refs.first)
    (decodeInto_execute refs.second) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine
