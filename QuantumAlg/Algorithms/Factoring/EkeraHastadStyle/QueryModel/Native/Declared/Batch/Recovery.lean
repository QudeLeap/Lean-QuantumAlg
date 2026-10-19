/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program

/-!
# Complete classical recovery after the declared EH batch

The existing complete sixteen-sample recovery reads the actual persistent
sample and parameter cells, allocates and releases its real workspaces, and
writes the preallocated optional factor result. Both the first attempt and a
later same-bank attempt retain every original classical cell and quantum wire.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

variable {environment : (model N).Environment}

/-- The original sampled parameter remains in its actual retained cell. -/
def parameter : CInputRef (Batch.context base noQuantum N) (ParameterShape N) :=
  .storage (Batch.parameterRef base noQuantum N).toCStorageRef

/-- The recovery reads all sixteen actual terminal cells in sampling order. -/
def terminals : LatticePairRecoveryBatch.Terminals (Batch.context base noQuantum N) N :=
  fun index => .storage (Batch.terminalRef base noQuantum N index).toCStorageRef

/-- Execute the existing complete recovery in the selected EH execution model. -/
def into : Circuit (model N) (Batch.context base noQuantum N)
    (Batch.context base noQuantum N) :=
  LatticeFixedBatchRecoveryMachine.into (model := model N)
    (Batch.context base noQuantum N) input
    (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N)

/-- The exact allocated recovery record retains the real path and final store. -/
def step (store : Store (Batch.context base noQuantum N)) :
    Store (Batch.context base noQuantum N) ×
      (into base noQuantum N input).Path :=
  LatticeFixedBatchRecoveryMachine.step (model := model N) input
    (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) store

/-- The actual recovery is deterministic even on correlated reference inputs. -/
lemma into_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference
      ((model N).HiddenState × History)) :
    (into base noQuantum N input).execute environment Reference state =
      state.mapClassical (fun entry =>
        (let actual := step base noQuantum N input entry.1
         (actual.1, (entry.2.1, (entry.2.2, actual.2))))) :=
  LatticeFixedBatchRecoveryMachine.into_execute (environment := environment) (model := model N)
    input
    (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) Reference state

/-- Every caller read outside the optional-factor destination survives. -/
lemma caller_frame (store : Store (Batch.context base noQuantum N)) :
    LatticeFixedBatchRecoveryMachine.CallerFrame (Batch.factorRef base noQuantum N)
      store (step base noQuantum N input store).1 :=
  LatticeFixedBatchRecoveryMachine.into_callerFrame (model := model N)
    input (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) store

/-- The actual factor cell receives the original complete batch recovery value. -/
lemma value (sample : Fin (2 ^ residueSamplingBits N))
    (store : Store (Batch.context base noQuantum N))
    (sampled : store.read (parameter base noQuantum N) =
      Canonical.parameterValue input sample) :
    (step base noQuantum N input store).1.read
      (.storage (Batch.factorRef base noQuantum N).toCStorageRef) =
        LatticeFixedBatchRecoveryMachine.batchValue sample
          (terminals base noQuantum N) store :=
  (LatticeFixedBatchRecoveryMachine.into_correct (model := model N)
    input sample (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) store ⟨sampled⟩).output

/-- One actual sample batch is followed by complete paid classical recovery. -/
def first : Circuit (model N) base (Batch.context base noQuantum N) :=
  .seq (Batch.code base noQuantum N) (into base noQuantum N input)

/-- A later batch redraws and recovers in the same complete live context. -/
def next : Circuit (model N) (Batch.context base noQuantum N)
    (Batch.context base noQuantum N) :=
  .seq (Batch.nextBatch base noQuantum N) (into base noQuantum N input)

/-- Read the real optional factor while retaining all live data and the bank. -/
def run : AlgorithmRun (model N) base (Batch.context base noQuantum N)
    (.option (.unsignedWord (modulusBits N))) where
  code := first base noQuantum N input
  output := Output.all (Batch.context base noQuantum N)
    (.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))

/-- The next attempt overwrites the same factor cell in the same context. -/
def nextRun : AlgorithmRun (model N) (Batch.context base noQuantum N)
    (Batch.context base noQuantum N) (.option (.unsignedWord (modulusBits N))) where
  code := next base noQuantum N input
  output := Output.all (Batch.context base noQuantum N)
    (.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))

/-- The first recovery exposes every surviving runtime key. -/
lemma output_listing :
    (run base noQuantum N input).output.listing =
      (Batch.context base noQuantum N).keys := rfl

/-- A later recovery exposes the same complete live manifest. -/
lemma next_output_listing :
    (nextRun base noQuantum N input).output.listing =
      (Batch.context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery
