/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Initial
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Probability
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation

/-!
# Prepared declared EH observation on the original input

The actual zero preparation and result allocations supply the selected
member's seed. The conditional Born law is then transported back through
those real allocations to the original stored parameter and reference.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The original short-DLP source Born weight for one stored parameter value. -/
abbrev sourceWeight (value : (ParameterShape N).Value)
    (outcome : Fin (measurementBits N) → Bool) : ℂ :=
  (((ShortDLP.measurement (Native.parameters N)).outcomePMF
    (ShortDLP.BornProbability.evolvedState (Native.encoding input)
      (parameterUnit value) (parameterTarget value)) outcome).toReal : ℂ)

/-- The actual prepared code has the source Born law in each complete
initialized store-reference block. -/
lemma initialized_outcome_reference (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    let initialized := (allocate base noQuantum N).execute (sourceEnvironment input) Reference
      ((prepare base noQuantum N).execute (sourceEnvironment input) Reference state)
    ExecutionState.referenceFiberSum
      ((code base noQuantum N parameter).execute (sourceEnvironment input) Reference state)
      (fun entry _ => if entry.1.read
        (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ∑ original : Store (Native.context base noQuantum N),
        sourceWeight N input
          (original.read (Native.liftInput base noQuantum N parameter)) outcome *
          (initialized.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((Native.context base noQuantum N).quantumLayout.zeroLabel, leftRef)
            ((Native.context base noQuantum N).quantumLayout.zeroLabel, rightRef) := by
  let observed := fun store : Store (Native.context base noQuantum N) =>
    if store.read (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits outcome then (1 : ℂ) else 0
  exact (Circuit.referenceFiberSum_execute_seq (environment := (sourceEnvironment input))
    (prepare base noQuantum N)
    ((allocate base noQuantum N).seq (body base noQuantum N parameter))
    state observed leftRef rightRef).trans
      ((Circuit.referenceFiberSum_execute_seq (environment := (sourceEnvironment input))
        (allocate base noQuantum N)
        (body base noQuantum N parameter)
        ((prepare base noQuantum N).execute (sourceEnvironment input) Reference state)
        observed leftRef rightRef).trans
        (body_outcome_reference base noQuantum N input parameter _
          (initial_seeded base noQuantum N (environment := sourceEnvironment input) state)
            outcome leftRef rightRef))

/-- The actual allocations preserve the original parameter's weighted
reference observation, including all hidden-service state correlations. -/
lemma initialized_reference_input
    {environment : (model N).Environment} (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (weight : (ParameterShape N).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((allocate base noQuantum N).execute environment Reference
        ((prepare base noQuantum N).execute environment Reference state))
      (fun entry _ => weight
        (entry.1.read (Native.liftInput base noQuantum N parameter)))
      leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read parameter)) leftRef rightRef := by
  let prepared := (prepare base noQuantum N).execute environment Reference state
  let prior := MeasurementCells.liftInput 2
    (Native.bankInput base noQuantum N parameter) (measurementBits N)
  let retention := Circuit.retain (model := model N)
    (Native.cellsContext base noQuantum N)
    (Native.cellsContext base noQuantum N).canonicalFreshKey
    (.bits (measurementBits N))
    (Native.cellsContext base noQuantum N).canonicalFreshKey_fresh
  have split := Circuit.referenceFiberSum_execute_seq (environment := environment)
    (MeasurementCells.allocate (model := model N)
      (Native.bankContext base noQuantum N) 2 (measurementBits N))
    retention prepared
    (fun store => weight
      (store.read (Native.liftInput base noQuantum N parameter)))
    leftRef rightRef
  have retained := Circuit.referenceFiberSum_execute_retain_input (environment := environment)
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    prior
    (Native.cellsContext base noQuantum N).canonicalFreshKey
    (.bits (measurementBits N))
    (Native.cellsContext base noQuantum N).canonicalFreshKey_fresh
    ((MeasurementCells.allocate (model := model N)
      (Native.bankContext base noQuantum N) 2 (measurementBits N)).execute environment
        Reference prepared) weight leftRef rightRef
  have cellsPreserved := MeasurementCells.allocate_referenceFiberSum_input (environment :=
    environment)
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    (Native.bankInput base noQuantum N parameter) 2 (measurementBits N)
    prepared weight leftRef rightRef
  have preparationPreserved := Circuit.referenceFiberSum_execute_prepareZero_input (environment
    := environment)
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    parameter base.canonicalFreshKey (Native.layout N) base.canonicalFreshKey_fresh
    (Native.allocationDisjoint base noQuantum N) state weight leftRef rightRef
  exact split.trans (retained.trans (cellsPreserved.trans preparationPreserved))

/-- The complete actual observation has the source conditional Born law
weighted by the original stored parameter and entire external reference. -/
lemma code_outcome_reference (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum N parameter).execute (sourceEnvironment input) Reference state)
      (fun entry _ => if entry.1.read
        (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => sourceWeight N input (entry.1.read parameter) outcome)
        leftRef rightRef := by
  let initialized := (allocate base noQuantum N).execute (sourceEnvironment input) Reference
    ((prepare base noQuantum N).execute (sourceEnvironment input) Reference state)
  let weight := fun value : (ParameterShape N).Value => sourceWeight N input value outcome
  exact (initialized_outcome_reference base noQuantum N input parameter state
    outcome leftRef rightRef).trans
    ((BasisSeeded.referenceFiberSum_seed _ initialized
      (initial_seeded base noQuantum N (environment := sourceEnvironment input) state)
      (fun store => weight
        (store.read (Native.liftInput base noQuantum N parameter)))
      leftRef rightRef).symm.trans
        (initialized_reference_input base noQuantum N (environment := sourceEnvironment input)
          parameter
          state weight leftRef rightRef))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
