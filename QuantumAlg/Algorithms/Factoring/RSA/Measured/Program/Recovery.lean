/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Context
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Complete reference observations through the actual RSA batch recovery

The fixed-batch recovery executes its original lexical allocator, all pair
recoveries and release. Its proved actual record transports arbitrary weights
on complete caller stores and preserves the physical basis seed. Both external
reference coordinates remain present; no independence or parameter correctness
premise is required for these execution laws.
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

variable {environment : MeasuredRSAModel.Environment}

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  {N : Nat} (input : Input N) (count : Nat) (batch : Fin count)

/-- The caller store returned by the complete actual recovery record. -/
def recoveryStore (before : Store (readyContext base noQuantum N count)) :
    Store (readyContext base noQuantum N count) :=
  (LatticeFixedBatchRecoveryMachine.step
    (model := MeasuredRSAModel) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)) before).1

variable {Reference : Register} {History : Type} [Fintype History]

/-- Actual recovery keeps every complete store-reference block at the incoming local seed. -/
lemma rsaMeasuredParent_recover_seeded
    (seed : (readyContext base noQuantum N count).register.Index)
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed
      ((recover base noQuantum N input count batch).execute environment Reference state) := by
  have actual := LatticeFixedBatchRecoveryMachine.into_execute (environment := environment)
    (model := MeasuredRSAModel)
    (ctx := readyContext base noQuantum N count) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)) Reference state
  rw [show (recover base noQuantum N input count batch).execute
    environment Reference state = _ from actual]
  exact BasisSeeded.mapStore seed state seeded
    (recoveryStore base noQuantum input count batch)
    (fun entry =>
      (entry.2.1, (entry.2.2,
        (LatticeFixedBatchRecoveryMachine.step
          (model := MeasuredRSAModel) input
          (FirstAccepted.cellRead (bankWrite base noQuantum N count
            (Recycling.ClassicalFrame.parameterRef base N count batch)))
          (terminals base noQuantum N count batch)
          (bankWrite base noQuantum N count
            (Recycling.ClassicalFrame.factorRef base N count batch)) entry.1).2)))

/-- Full recovery transports a complete-store weight through its actual returned caller store. -/
lemma rsaMeasuredParent_recover_referenceFiberSum
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((recover base noQuantum N input count batch).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (recoveryStore base noQuantum input count batch entry.1))
        left right := by
  have actual := LatticeFixedBatchRecoveryMachine.into_execute (environment := environment)
    (model := MeasuredRSAModel)
    (ctx := readyContext base noQuantum N count) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)) Reference state
  rw [show (recover base noQuantum N input count batch).execute
    environment Reference state = _ from actual]
  exact ExecutionState.referenceFiberSum_mapClassical state _ _ left right

end

end QuantumAlg.Factoring.RSA.Measured.Program
