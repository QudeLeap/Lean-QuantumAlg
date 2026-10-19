/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Measurement.Cells.Store.Observation
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Reference.Weighted

/-!
# Actual initialized Store weights and their original reference fibers

The actual zero allocation, retained result cells and literal seed loader
transport every complete-Store weight through their real initialized Store
push. Both reference coordinates remain unchanged. This allows later outcome
formulas to use the original classical frame without equating different
quantum banks or supplying an external initialization certificate.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.PreparationObservation

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

/-- Only the actual owned presence marker and real initialized finite cells are adjoined. -/
def preparedStore (original : Store base) : Store (context base noQuantum m ell width) :=
  MeasurementCells.pushStore 2 (resultBits m ell)
    (original.pushOwnedLayout base.canonicalFreshKey (Arithmetic.layout width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width))

/-- The old operand is only lifted under the actual new storage, without an extra instruction. -/
def preparedInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base noQuantum m ell width) shape :=
  MeasurementCells.liftInput 2
    (input.underOwnedLayout base.canonicalFreshKey (Arithmetic.layout width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width))
    (resultBits m ell)

/-- Every earlier structural operand reads the same original frame value. -/
lemma preparedStore_read_input {shape : CShape}
    (original : Store base) (input : CInputRef base shape) :
    (preparedStore base noQuantum m ell width original).read
        (preparedInput base noQuantum m ell width input) = original.read input := by
  have cells := MeasurementCells.read_pushStore_liftInput 2 (resultBits m ell)
    (original.pushOwnedLayout base.canonicalFreshKey (Arithmetic.layout width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width))
    (input.underOwnedLayout base.canonicalFreshKey (Arithmetic.layout width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width))
  have bank := Store.read_pushOwnedLayout_underOwnedLayout original base.canonicalFreshKey
    (Arithmetic.layout width).toQuantum base.runtimeCtx_canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum width) input
  exact cells.trans bank

/-- The real preparation preserves every complete-Store-weighted reference matrix entry. -/
lemma prepare_referenceFiberSum_store (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History))
    (weight : Store (context base noQuantum m ell width) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((prepare base noQuantum m ell width N).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (preparedStore base noQuantum m ell width entry.1)) left right := by
  let allocated : Circuit model base (bankContext base noQuantum width) :=
    Circuit.prepareZero base base.canonicalFreshKey (Arithmetic.layout width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width)
  let retained : Circuit model (bankContext base noQuantum width)
      (context base noQuantum m ell width) :=
    MeasurementCells.allocate (model := model)
      (bankContext base noQuantum width) 2 (resultBits m ell)
  let loaded : Circuit model (context base noQuantum m ell width)
      (context base noQuantum m ell width) :=
    .unitary (load base noQuantum m ell width N)
  have first := Circuit.referenceFiberSum_execute_seq (environment := environment) allocated
    (retained.seq loaded)
    state weight left right
  have second := Circuit.referenceFiberSum_execute_seq (environment := environment) retained loaded
    (allocated.execute environment Reference state) weight left right
  have last := Circuit.unitary_weighted_reference (environment := environment)
    (allowAllocation := true)
    (operations := BitWord.model) (classicalOracles := .empty)
    (ctx := context base noQuantum m ell width)
    (load base noQuantum m ell width N)
    (retained.execute environment Reference (allocated.execute environment Reference state))
      weight left right
  have cells := MeasurementCells.allocate_referenceFiberSum_store (environment := environment)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := .empty)
    (bankContext base noQuantum width) 2 (resultBits m ell)
    (allocated.execute environment Reference state) weight left right
  have bank := Circuit.referenceFiberSum_execute_prepareZero (environment := environment)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := .empty)
    (ctx := base)
    base.canonicalFreshKey (Arithmetic.layout width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width) state
    (fun stored => weight (MeasurementCells.pushStore 2 (resultBits m ell) stored)) left right
  exact first.trans (second.trans (last.trans (cells.trans bank)))

/-- Actual parameter observations keep their full incoming reference correlations. -/
lemma prepare_referenceFiberSum_input (N : Nat) {shape : CShape}
    (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History))
    (weight : shape.Value → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((prepare base noQuantum m ell width N).execute environment Reference state)
        (fun entry _ => weight (entry.1.read
          (preparedInput base noQuantum m ell width input))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read input)) left right := by
  have actual := prepare_referenceFiberSum_store (environment := environment) base noQuantum
    m ell width N state
    (fun stored => weight (stored.read (preparedInput base noQuantum m ell width input)))
    left right
  have weights : (fun entry : Store base × (model.HiddenState × History) =>
      fun _ : base.register.Index => weight
        ((preparedStore base noQuantum m ell width entry.1).read
          (preparedInput base noQuantum m ell width input))) =
      (fun entry => fun _ => weight (entry.1.read input)) := by
    funext entry _basis
    exact congrArg weight (preparedStore_read_input base noQuantum m ell width entry.1 input)
  exact actual.trans (congrArg (fun observed =>
    ExecutionState.referenceFiberSum state observed left right) weights)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.PreparationObservation
