/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Probability
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialization
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation

/-!
# Complete original-input weights of one declared Shor observation

The actual retained-output allocation, selected member, measurements and pack
have their conditional source law jointly with any structural earlier read.
The bank seed is established by the real prepare and sampler prefixes.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (N : Nat) (input : Input N)

/-- The original conditional source probability of the actual stored base. -/
abbrev sourceWeight (value : (ParameterShape (modulusBits N)).Value)
    (outcome : Fin (phaseBits N) → Bool) : ℂ :=
  ((DeclaredSource.outcomePMF (sourceBounds input) (phaseBits N)
    (selectedBase value) outcome).toReal : ℂ)

/-- Real result-cell allocation preserves every earlier structural reference weight. -/
theorem allocate_reference_input {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (weight : shape.Value → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocate base N input).execute Reference state)
      (fun entry _ => weight (entry.1.read (Storage.liftInput base N observed)))
      leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read observed)) leftRef rightRef := by
  let retention := Circuit.retain (model := executionModel input) base
    base.canonicalFreshKey (.bits (phaseBits N)) base.canonicalFreshKey_fresh
  let cells := MeasurementCells.allocate (model := executionModel input)
    (Storage.resultContext base N) 2 (phaseBits N)
  have sequence := Circuit.referenceFiberSum_execute_seq retention cells state
    (fun store => weight (store.read (Storage.liftInput base N observed))) leftRef rightRef
  have allocated := MeasurementCells.allocate_referenceFiberSum_input
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (observed.underRetained base.canonicalFreshKey (.bits (phaseBits N))
      base.canonicalFreshKey_fresh) 2 (phaseBits N)
    (retention.execute Reference state) weight leftRef rightRef
  have retained := Circuit.referenceFiberSum_execute_retain_input
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    observed base.canonicalFreshKey (.bits (phaseBits N)) base.canonicalFreshKey_fresh
    state weight leftRef rightRef
  exact sequence.trans (allocated.trans retained)

private theorem observation_liftInput_product {left right : CShape}
    (first : CInputRef base left) (second : CInputRef base right) :
    Storage.liftInput base N (.product first second) =
      .product (Storage.liftInput base N first) (Storage.liftInput base N second) := by
  unfold Storage.liftInput
  exact MeasurementCells.liftInput_product 2 _ _ _

variable (sameWires : base.quantumWires = (layout N).wires)

/-- Actual allocation and observation retain original stored data jointly with the Born outcome. -/
theorem code_outcome_weighted_reference
    (parameter : CInputRef base (ParameterShape (modulusBits N)))
    {shape : CShape} (observed : CInputRef base shape) (weight : shape.Value → ℂ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds base.quantumLayout.zeroLabel state)
    (outcome : Fin (phaseBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base N input sameWires parameter).execute Reference state)
      (fun entry _ => weight (entry.1.read (Storage.liftInput base N observed)) *
        (if entry.1.read (.storage (Storage.resultRef base N).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read observed) *
          sourceWeight N input (entry.1.read parameter) outcome) leftRef rightRef := by
  let initialized := (allocate base N input).execute Reference state
  let readWeight := fun store : Store (Storage.context base N) =>
    weight (store.read (Storage.liftInput base N observed))
  have initialSeed := allocate_seeded (N := N) (input := input) base state seeded
  have sequence := Circuit.referenceFiberSum_execute_seq (allocate base N input)
    (body base N input sameWires parameter) state
    (fun store => readWeight store *
      (if store.read (.storage (Storage.resultRef base N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0)) leftRef rightRef
  have born := body_outcome_weighted_reference base N input sameWires parameter readWeight
    (by
      intro store basis
      exact congrArg weight
        (measured_packed_liftInput base N input sameWires observed store basis))
    initialized initialSeed outcome leftRef rightRef
  have regrouped := BasisSeeded.referenceFiberSum_seed _ initialized initialSeed
    (fun store => readWeight store *
      sourceWeight N input (store.read (Storage.liftInput base N parameter)) outcome)
    leftRef rightRef
  have allocated := allocate_reference_input base N input (.product observed parameter) state
    (fun value => weight value.first * sourceWeight N input value.second outcome)
    leftRef rightRef
  rw [observation_liftInput_product] at allocated
  exact sequence.trans (born.trans (regrouped.symm.trans allocated))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
