/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual Z writes followed by a closed classical instruction

The finite measurement sequence supplies its real outcomes and writes them
into actual storage. A selected deterministic native instruction then reads
that storage and writes its declared result. Every observation of the
resulting store retains the complete reference matrix entry of that fiber,
including correlations with the persistent service state.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A declared deterministic native instruction after Z writes has its exact
store-reference fiber, including the untouched persistent service state. -/
lemma measurementSequence_classical_reference_entry
    {allowAllocation : Bool} {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {ctx : RuntimeCtx .quantum} (readouts : List (ZReadout ctx))
    (application : operations.Application ctx)
    (compute : (operations.inputShape application.token).Value →
      (operations.outputShape application.token).Value)
    (declared : ∀ input,
      operations.evaluate application.token input = PMF.pure (compute input))
    {Reference : Register} {History Observed : Type} [Fintype History] [Fintype Observed]
    (state : State ctx Reference (services.HiddenState × History))
    (observe : Store ctx → Observed) (value : Observed)
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      DensityOperator.matrix
        ((ExecutionState.mapClassical
          ((Circuit.seq (measurementSequence (allowAllocation := allowAllocation)
            (gates := gates) (oracles := oracles) (operations := operations)
            (classicalOracles := services) readouts)
            (.classical (allowAllocation := allowAllocation) application)).execute environment
              Reference state)
          (fun entry => observe entry.1)).block value) (basis, left) (basis, right)) =
      ExecutionState.referenceFiberSum state (fun original basis =>
        if observe ((writeMeasurementPath (allowAllocation := allowAllocation)
          (gates := gates) (oracles := oracles) (operations := operations)
          (classicalOracles := services) readouts original.1
          (measurementBasisPath (allowAllocation := allowAllocation) (gates := gates)
            (oracles := oracles) (operations := operations)
            (classicalOracles := services) readouts basis)).write
              application.output
              (compute ((writeMeasurementPath (allowAllocation := allowAllocation)
                (gates := gates) (oracles := oracles) (operations := operations)
                (classicalOracles := services) readouts original.1
                (measurementBasisPath (allowAllocation := allowAllocation)
                  (gates := gates) (oracles := oracles)
                  (operations := operations) (classicalOracles := services)
                  readouts basis)).read application.input))) = value then 1 else 0)
        left right := by
  rw [ExecutionState.mapClassical_block_referenceFiberSum, execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  rw [execute_classical_mapClassical (environment := environment) (allowAllocation :=
    allowAllocation)
    (model := .quantum gates oracles operations services) application compute declared]
  simp only [ExecutionState.referenceFiberSum_mapClassical]
  exact measurementSequence_referenceFiberSum (environment := environment) (allowAllocation :=
    allowAllocation) readouts state
    (fun entry _ =>
      if observe (entry.1.write application.output
        (compute (entry.1.read application.input))) = value then 1 else 0) left right

end

end QuantumAlg.Circuit
