/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Layout
import all QuantumAlg.Core.Execution.Retained.Record

/-!
# Actual native first batch followed by complete classical recovery

The source constructor runs once. Its final store is extended by a real
retained output, then the classical allocator initializes and releases all
recovery workspaces. The complete output lists every surviving live entry.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

open Execution ShortDLP.CompiledMAU

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Keep the already constructed source bank abstract while checking retained-state equality.
attribute [local irreducible] NativeBatch.context NativeBatch.code
  LatticeFixedBatchRecoveryMachine.into LatticeFixedBatchRecoveryMachine.step

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Complete classical recovery writes the retained optional factor before releasing scratch. -/
def body (input : Input N) :
    Circuit RuntimeRound.model (context base noQuantum N) (context base noQuantum N) :=
  LatticeFixedBatchRecoveryMachine.into (model := RuntimeRound.model)
    (context base noQuantum N) input
    (sourceParameter base noQuantum N) (terminals base noQuantum N) (resultRef base noQuantum N)

private def bodyStep (input : Input N)
    (before : Store (context base noQuantum N) × RuntimeRound.model.HiddenState) :
    (Store (context base noQuantum N) × RuntimeRound.model.HiddenState) ×
      (body base noQuantum input).Path :=
  let actual := LatticeFixedBatchRecoveryMachine.step (model := RuntimeRound.model)
    input (sourceParameter base noQuantum N) (terminals base noQuantum N)
      (resultRef base noQuantum N) before.1
  ((actual.1, before.2), actual.2)

private lemma body_execute (input : Input N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      (RuntimeRound.model.HiddenState × History)) :
    (body base noQuantum input).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := bodyStep base noQuantum input (entry.1, entry.2.1)
        (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))) := by
  unfold body bodyStep
  refine (LatticeFixedBatchRecoveryMachine.into_execute (model := RuntimeRound.model) input
    (sourceParameter base noQuantum N) (terminals base noQuantum N)
    (resultRef base noQuantum N) Reference state).trans ?_
  congr 1

-- Composition uses the body's proved record without unfolding its finite recovery path.
attribute [local irreducible] body bodyStep

/-- Actual output allocation precedes the actual classical recovery execution. -/
def tail (input : Input N) :
    Circuit RuntimeRound.model (NativeBatch.context base noQuantum N) (context base noQuantum N) :=
  .seq (.retain (model := RuntimeRound.model) (NativeBatch.context base noQuantum N)
    (resultKey base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh) (body base noQuantum input)

/-- The actual deterministic record contains the real retained allocation and body path. -/
def step (input : Input N)
    (before : Store (NativeBatch.context base noQuantum N) × RuntimeRound.model.HiddenState) :
    (Store (context base noQuantum N) × RuntimeRound.model.HiddenState) ×
      (tail base noQuantum input).Path :=
  let record := bodyStep base noQuantum input
    (before.1.pushRetained (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh, before.2)
  (record.1, ((), record.2))

/-- One original source execution, with its single bank, feeds the complete recovery tail. -/
def code (input : Input N) : Circuit RuntimeRound.model base (context base noQuantum N) :=
  .seq (NativeBatch.code base noQuantum N) (tail base noQuantum input)

/-- The optional factor is read from actual storage while every live entry remains manifested. -/
def run (input : Input N) :
    AlgorithmRun RuntimeRound.model base (context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  code := code base noQuantum input
  output := Output.all (context base noQuantum N)
    (.read (.storage (resultRef base noQuantum N).toCStorageRef))

/-- Actual allocation and recovery preserve complete quantum-reference blocks on every history. -/
lemma tail_execute (input : Input N) :
    Circuit.RetainedRecord (environment := environment)
      (tail base noQuantum input) (step base noQuantum input) := by
  intro Reference History historyFinite state
  have equation := Circuit.execute_retain_seq_mapClassical (environment := environment)
    (model := RuntimeRound.model)
    (NativeBatch.context base noQuantum N)
    (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh (body base noQuantum input)
    (bodyStep base noQuantum input) (body_execute base noQuantum input) Reference state
  unfold tail step
  refine equation.trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The complete run maps the original source execution, retaining its original path and bank. -/
lemma code_execute (input : Input N) :
    Circuit.RetainedTailRecord (environment := environment) (NativeBatch.code base noQuantum N)
      (tail base noQuantum input) (step base noQuantum input) :=
  Circuit.RetainedRecord.after (environment := environment)
    (NativeBatch.code base noQuantum N) (tail base noQuantum input)
    (step base noQuantum input) (tail_execute base noQuantum input)

/-- The complete output includes the same source bank, all source cells and the retained factor. -/
lemma output_listing (input : Input N) :
    (run base noQuantum input).output.listing = (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
