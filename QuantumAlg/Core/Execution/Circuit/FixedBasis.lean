/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.Support
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Classical.BasisSupport
import all QuantumAlg.Core.Base.Gate.Effect.FixedInput

/-!
# Uniform actual observations from a fixed local basis

A uniform pure-reference observation bound at every actual caller Store
and persistent-service input
extends to every classical-quantum state supported on that local basis.
The original conditional reference matrices keep their own masses. The proof
uses the same interpreter, its history naturality and its certified pulled
observable; no independent sampling or normalized posterior is introduced.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma mapClassical_single {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (sourceDecision : DecidableEq C) (outputDecision : DecidableEq D)
    (value : C) (density : DensityOperator R) (update : C → D) :
    (@ExecutionState.ofValue C _ R sourceDecision value density).mapClassical update =
      @ExecutionState.ofValue D _ R outputDecision (update value) density := by
  apply ExecutionState.ext
  intro output
  apply DensityOperator.ext
  ext row column
  simp only [ExecutionState.mapClassical_block_matrix, ExecutionState.ofValue_block,
    apply_ite DensityOperator.matrix, DensityOperator.zero_matrix]
  have select (current : C) :
      (if update current = output then if current = value then density.matrix else 0 else 0) =
        if current = value then (if update value = output then density.matrix else 0) else 0 := by
    by_cases same : current = value <;> simp [same]
  simp only [select, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases same : update value = output
  · rw [if_pos same, if_pos same.symm]
  · rw [if_neg same, if_neg (Ne.symm same)]

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  (environment : (ExecutionModel.quantum gates oracles operations services).Environment)

private lemma execute_single_history {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles operations services) pre post) (Reference : Register)
    {H : Type} [Fintype H]
    (store : Store pre) (hidden : services.HiddenState) (history : H)
    (density : DensityOperator (pre.register.prod Reference)) :
    (code.execute environment Reference (ExecutionState.ofValue (store, (hidden, history))
      density)).quantumMarginal =
      (code.execute environment Reference (ExecutionState.ofValue (store, (hidden, ()))
        density)).quantumMarginal := by
  have same :
      State.mapHistory (ctx := pre) (ExecutionState.ofValue (store, (hidden, ())) density)
          (fun entry : services.HiddenState × Unit => (entry.1, history)) =
        ExecutionState.ofValue (store, (hidden, history)) density := by
    unfold State.mapHistory
    refine (State.mapClassical_decision _
      (Classical.decEq (Store pre × (services.HiddenState × H))) _ _).trans ?_
    convert mapClassical_single (Classical.decEq (Store pre × (services.HiddenState × Unit)))
      (Classical.decEq (Store pre × (services.HiddenState × H))) (store, (hidden, ())) density
      (fun record => (record.1, (record.2.1, history))) using 1 <;> congr 2 <;>
      exact Subsingleton.elim _ _
  rw [← same]
  erw [execute_mapHistory code environment Reference
    (ExecutionState.ofValue (store, (hidden, ())) density) (fun _ : Unit => history),
    State.mapHistory_quantumMarginal]

/-- A fixed local basis extends uniform actual pure-input bounds to every original mixed block. -/
lemma observedWeight_lower_of_fixedBasis {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles operations services) pre post) (Reference : Register)
    (observed : Effect (post.register.prod Reference)) (label : pre.register.Index)
    (input : NormalizedVector Reference → NormalizedVector (pre.register.prod Reference))
    (represented : ∀ reference localBasis external,
      input reference (localBasis, external) =
        NormalizedVector.ket (R := pre.register) label localBasis * reference external)
    (lower : ℝ)
    (bound : ∀ (store : Store pre) (hidden : services.HiddenState)
      (reference : NormalizedVector Reference),
      lower ≤ observed.weight
        ((code.execute environment Reference (ExecutionState.ofValue (store, (hidden, ()))
          (DensityOperator.ofPure (input reference)))).quantumMarginal))
    {H : Type} [Fintype H] (state : State pre Reference (services.HiddenState × H))
    (support : ∀ basis : (pre.register.prod Reference).Index, basis.1 ≠ label →
      state.quantumMarginal.matrix basis basis = 0) :
    state.mass * lower ≤ observed.weight (code.execute
          environment Reference state).quantumMarginal := by
  have actual := code.effectWeight_execute environment Reference state (fun _ => observed)
  rw [ExecutionState.effectWeight_constant] at actual
  rw [actual]
  unfold ExecutionState.mass ExecutionState.effectWeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro record _
  let pulled := code.effectPullback environment Reference (fun _ => observed) record
  apply Effect.mass_mul_le_weight_of_basis_factor pulled (state.block record) label lower
  · intro left right refLeft refRight
    by_cases sameLeft : left = label
    · subst left
      by_cases sameRight : right = label
      · subst right
        simp [NormalizedVector.ket_apply]
      · have zero := ExecutionState.block_diagonal_zero state (right, refRight)
          (support (right, refRight) sameRight) record
        rw [DensityOperator.column_zero_of_diagonal_zero (state.block record)
          (right, refRight) zero (label, refLeft)]
        simp [NormalizedVector.ket_apply, sameRight]
    · have zero := ExecutionState.block_diagonal_zero state (left, refLeft)
        (support (left, refLeft) sameLeft) record
      rw [DensityOperator.row_zero_of_diagonal_zero (state.block record)
        (left, refLeft) zero (right, refRight)]
      simp [NormalizedVector.ket_apply, sameLeft]
  · intro reference
    rw [Effect.basisSliceEffect_weight_of_pure pulled label reference (input reference)
      (represented reference)]
    have actualPure := code.effectWeight_execute environment Reference
      (ExecutionState.ofValue record (DensityOperator.ofPure (input reference))) (fun _ => observed)
    rw [ExecutionState.effectWeight_constant, ExecutionState.effectWeight_ofValue_decision]
      at actualPure
    change lower ≤ (code.effectPullback environment Reference (fun _ => observed) record).weight _
    rw [← actualPure]
    erw [execute_single_history environment code Reference record.1 record.2.1 record.2.2
      (DensityOperator.ofPure (input reference))]
    exact bound record.1 record.2.1 reference

end

end QuantumAlg.Circuit
