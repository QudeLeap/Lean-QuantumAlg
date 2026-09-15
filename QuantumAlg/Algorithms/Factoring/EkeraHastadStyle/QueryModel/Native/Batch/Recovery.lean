/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program

/-!
# Actual classical recovery from the fixed original-width oracle batch

The existing full batch recovery consumes the sixteen actual persistent
sample cells and the current complete parameter. Its real workspace packages
are allocated and released by the same native program. The optional factor
is written into the batch's preallocated result cell. All other live storage,
the original quantum bank and arbitrary reference correlations remain present.

The first and subsequent attempts append this same recovery stage to their
actual sampling circuits. These constructors and deterministic recovery laws
do not assume a batch distribution or assert an oracle-only depth contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] LatticeFixedBatchRecoveryMachine.into
  LatticeFixedBatchRecoveryMachine.step

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Recovery reads the current actual parameter, including all early-factor fields. -/
def parameter : CInputRef (Batch.context base noQuantum N) (ParameterShape N) :=
  .storage (Batch.parameterRef base noQuantum N).toCStorageRef

/-- The original recovery sees the sixteen slots in their actual sampling order. -/
def terminals : LatticePairRecoveryBatch.Terminals (Batch.context base noQuantum N) N :=
  fun index => .storage (Batch.terminalRef base noQuantum N index).toCStorageRef

/-- Execute the original complete native recovery in the fixed caller context. -/
def into (input : Input N) :
    Circuit (Batch.context base noQuantum N) (Batch.context base noQuantum N) :=
  LatticeFixedBatchRecoveryMachine.into (Batch.context base noQuantum N) input
    (parameter base noQuantum N) (terminals base noQuantum N) (Batch.factorRef base noQuantum N)

/-- The actual existing recovery record includes every released scope and the real final store. -/
def step (input : Input N) (store : Store (Batch.context base noQuantum N)) :
    Store (Batch.context base noQuantum N) × (into base noQuantum N input).Path :=
  LatticeFixedBatchRecoveryMachine.step input (parameter base noQuantum N)
    (terminals base noQuantum N) (Batch.factorRef base noQuantum N) store

/-- Complete execution follows the original native record on arbitrary history and reference. -/
theorem nativeOracle_batchRecovery_execute (input : Input N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference History) :
    (into base noQuantum N input).execute Reference state =
      state.mapClassical (fun entry => ((step base noQuantum N input entry.1).1,
        (entry.2, (step base noQuantum N input entry.1).2))) :=
  LatticeFixedBatchRecoveryMachine.into_execute input (parameter base noQuantum N)
    (terminals base noQuantum N) (Batch.factorRef base noQuantum N) Reference state

/-- Every actual caller read outside the factor destination keeps its complete value. -/
theorem nativeOracle_batchRecovery_frame (input : Input N)
    (store : Store (Batch.context base noQuantum N)) :
    LatticeFixedBatchRecoveryMachine.CallerFrame (Batch.factorRef base noQuantum N)
      store (step base noQuantum N input store).1 :=
  LatticeFixedBatchRecoveryMachine.into_callerFrame input (parameter base noQuantum N)
    (terminals base noQuantum N) (Batch.factorRef base noQuantum N) store

/-- The original sampled parameter identifies the recovery value of the real terminal cells. -/
theorem nativeOracle_batchRecovery_value (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (store : Store (Batch.context base noQuantum N))
    (sampled : store.read (parameter base noQuantum N) = Canonical.parameterValue input sample) :
    (step base noQuantum N input store).1.read
      (.storage (Batch.factorRef base noQuantum N).toCStorageRef) =
        LatticeFixedBatchRecoveryMachine.batchValue sample (terminals base noQuantum N) store :=
  (LatticeFixedBatchRecoveryMachine.into_correct input sample (parameter base noQuantum N)
    (terminals base noQuantum N) (Batch.factorRef base noQuantum N) store ⟨sampled⟩).output

/-- Original actual preparation and sixteen real samples feed the complete classical recovery. -/
def first (input : Input N) : Circuit base (Batch.context base noQuantum N) :=
  .seq (Batch.code base noQuantum N input) (into base noQuantum N input)

/-- Redraw, sixteen paid bank reuses and complete recovery all execute in the same fixed context. -/
def next (input : Input N) :
    Circuit (Batch.context base noQuantum N) (Batch.context base noQuantum N) :=
  .seq (Batch.nextBatch base noQuantum N input) (into base noQuantum N input)

/-- Read the actual optional factor while exposing every surviving cell and the whole bank. -/
def run (input : Input N) :
    AlgorithmRun base (Batch.context base noQuantum N)
      (.option (.unsignedWord (modulusBits N))) where
  code := first base noQuantum N input
  output := Output.all (Batch.context base noQuantum N)
    (.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))

/-- A later attempt uses the same result cell and the same complete live context. -/
def nextRun (input : Input N) :
    AlgorithmRun (Batch.context base noQuantum N) (Batch.context base noQuantum N)
      (.option (.unsignedWord (modulusBits N))) where
  code := next base noQuantum N input
  output := Output.all (Batch.context base noQuantum N)
    (.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))

/-- The first actual recovery output does not hide any surviving runtime entry. -/
theorem nativeOracle_batchRecovery_output_listing (input : Input N) :
    (run base noQuantum N input).output.listing = (Batch.context base noQuantum N).keys := rfl

/-- The continuation exposes the same complete context after its original workspace release. -/
theorem nativeOracle_batchRecovery_next_output_listing (input : Input N) :
    (nextRun base noQuantum N input).output.listing = (Batch.context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery
