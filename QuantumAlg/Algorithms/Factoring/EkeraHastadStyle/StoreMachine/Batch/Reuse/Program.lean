/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Layout
import all QuantumAlg.Core.Execution.Retained.Record

/-!
# Actual later native batch followed by complete classical recovery

The source sampler runs on the already allocated bank. Its final store is extended by a real
retained output, then the classical allocator initializes and releases all
recovery workspaces. The complete output lists every surviving live entry.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

open Execution ShortDLP.CompiledMAU

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Keep the already constructed source bank abstract while checking retained-state equality.
attribute [local irreducible] NativeBatchReuse.context NativeBatchReuse.code
  LatticeFixedBatchRecoveryMachine.into LatticeFixedBatchRecoveryMachine.step

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (ShortDLP.CompiledMAU.runtimeLayout
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- Complete classical recovery writes the retained optional factor before releasing scratch. -/
def body (input : Input N) :
    Circuit RuntimeRound.model (context base N) (context base N) :=
  LatticeFixedBatchRecoveryMachine.into (model := RuntimeRound.model)
    (context base N) input
    (sourceParameter base N) (terminals base N) (resultRef base N)

private def bodyStep (input : Input N)
    (before : Store (context base N) × RuntimeRound.model.HiddenState) :
    (Store (context base N) × RuntimeRound.model.HiddenState) ×
      (body base input).Path :=
  let actual := LatticeFixedBatchRecoveryMachine.step (model := RuntimeRound.model)
    input (sourceParameter base N) (terminals base N)
      (resultRef base N) before.1
  ((actual.1, before.2), actual.2)

private theorem body_execute (input : Input N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context base N) Reference (RuntimeRound.model.HiddenState × History)) :
    (body base input).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := bodyStep base input (entry.1, entry.2.1)
        (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))) := by
  unfold body bodyStep
  refine (LatticeFixedBatchRecoveryMachine.into_execute (model := RuntimeRound.model) input
    (sourceParameter base N) (terminals base N)
    (resultRef base N) Reference state).trans ?_
  congr 1

-- Composition uses the body's proved record without unfolding its finite recovery path.
attribute [local irreducible] body bodyStep

/-- Actual output allocation precedes the actual classical recovery execution. -/
def tail (input : Input N) :
    Circuit RuntimeRound.model (NativeBatchReuse.context base N) (context base N) :=
  .seq (.retain (model := RuntimeRound.model) (NativeBatchReuse.context base N) (resultKey base N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh) (body base input)

/-- The actual deterministic record contains the real retained allocation and body path. -/
def step (input : Input N)
    (before : Store (NativeBatchReuse.context base N) × RuntimeRound.model.HiddenState) :
    (Store (context base N) × RuntimeRound.model.HiddenState) ×
      (tail base input).Path :=
  let record := bodyStep base input
    (before.1.pushRetained (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatchReuse.context base N).canonicalFreshKey_fresh, before.2)
  (record.1, ((), record.2))

/-- Fresh sampling on the same original bank feeds the complete recovery tail. -/
def code (input : Input N) : Circuit RuntimeRound.model base (context base N) :=
  .seq (NativeBatchReuse.code base N sameWires originalCells) (tail base input)

/-- The optional factor is read from actual storage while every live entry remains manifested. -/
def run (input : Input N) :
    AlgorithmRun RuntimeRound.model base (context base N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  code := code base sameWires originalCells input
  output := Output.all (context base N)
    (.read (.storage (resultRef base N).toCStorageRef))

/-- Actual allocation and recovery preserve complete quantum-reference blocks on every history. -/
theorem tail_execute (input : Input N) :
    Circuit.RetainedRecord (tail base input) (step base input) := by
  intro Reference History historyFinite state
  have equation := Circuit.execute_retain_seq_mapClassical (model := RuntimeRound.model)
    (NativeBatchReuse.context base N)
    (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh (body base input)
    (bodyStep base input) (body_execute base input) Reference state
  unfold tail step
  refine equation.trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The complete run maps the original source execution, retaining its original path and bank. -/
theorem code_execute (input : Input N) :
    Circuit.RetainedTailRecord (NativeBatchReuse.code base N sameWires originalCells)
      (tail base input) (step base input) :=
  Circuit.RetainedRecord.after (NativeBatchReuse.code base N sameWires originalCells)
    (tail base input) (step base input) (tail_execute base input)

/-- The complete output includes the same source bank, all source cells and the retained factor. -/
theorem output_listing (input : Input N) :
    (run base sameWires originalCells input).output.listing = (context base N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
