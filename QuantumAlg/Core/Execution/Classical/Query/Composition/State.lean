/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Query.Composition
public import QuantumAlg.Core.Execution.Random.Kernel.Map
import all QuantumAlg.Core.Execution.Classical.Query.Composition
import all QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Actual service queries through persistent-state frames

A sum-granted query is exactly its original query executed with the other
service state held in mathematical history. The actual caller store is read
and written once, and all quantum/reference blocks are retained. Neither
service is initialized or reset by this reorganization.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma kernelChoice_mapOutcome {C A B : Type}
    [Fintype C] [Fintype A] [Fintype B] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF A) (update : C → A → B) :
    kernelChoice state (fun value => (transition value).map (update value)) =
      (kernelChoice state transition).mapClassical
        (fun entry => (entry.1, update entry.1 entry.2)) := by
  apply ExecutionState.ext
  rintro ⟨value, result⟩
  apply DensityOperator.ext
  rw [kernelChoice_block_matrix, ExecutionState.mapClassical_block_matrix,
    Fintype.sum_prod_type, Finset.sum_eq_single value]
  · rw [PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun outcome _ => by
      split_ifs <;> simp only [PMF.apply_ne_top, ne_eq, ENNReal.zero_ne_top, not_false_eq_true])]
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro outcome _
    by_cases same : result = update value outcome
    · simp only [same, if_true, kernelChoice_block_matrix]
    · simp only [same, if_false, ENNReal.toReal_zero, zero_smul,
        Prod.mk.injEq, true_and, Ne.symm same]
  · intro other _ different
    simp only [Prod.mk.injEq, different, false_and, if_false, Finset.sum_const_zero]
  · intro absent
    exact (absent (Finset.mem_univ value)).elim

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History : Type} [Fintype History] (left right : ClassicalOracleModel)

open scoped Classical in
/-- Expose the left persistent state while retaining the right state in history. -/
@[expose] public def serviceFrameLeft
    (state : State ctx Reference ((left.HiddenState × right.HiddenState) × History)) :
    State ctx Reference (left.HiddenState × (right.HiddenState × History)) :=
  state.mapClassical fun record =>
    (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))

open scoped Classical in
/-- Expose the right persistent state while retaining the left state in history. -/
@[expose] public def serviceFrameRight
    (state : State ctx Reference ((left.HiddenState × right.HiddenState) × History)) :
    State ctx Reference (right.HiddenState × (left.HiddenState × History)) :=
  state.mapClassical fun record =>
    (record.1, (record.2.1.2, (record.2.1.1, record.2.2)))

open scoped Classical in
/-- Rejoin a left query's next state and result with the preserved right state. -/
@[expose] public def serviceJoinLeftResult {Result : Type} [Fintype Result]
    (state : State ctx Reference (left.HiddenState × ((right.HiddenState × History) × Result))) :
    State ctx Reference ((left.HiddenState × right.HiddenState) × (History × Result)) :=
  state.mapClassical fun record =>
    (record.1, ((record.2.1, record.2.2.1.1), (record.2.2.1.2, record.2.2.2)))

open scoped Classical in
/-- Rejoin a right query's next state and result with the preserved left state. -/
@[expose] public def serviceJoinRightResult {Result : Type} [Fintype Result]
    (state : State ctx Reference (right.HiddenState × ((left.HiddenState × History) × Result))) :
    State ctx Reference ((left.HiddenState × right.HiddenState) × (History × Result)) :=
  state.mapClassical fun record =>
    (record.1, ((record.2.2.1.1, record.2.1), (record.2.2.1.2, record.2.2.2)))

/-- A left sum query preserves the other service as part of its untouched history. -/
public lemma queryStep_service_sum_left
    (environment : (ClassicalOracleModel.sum left right).Interpretation)
    (application : left.Application ctx)
    (state : State ctx Reference ((left.HiddenState × right.HiddenState) × History)) :
    queryStep environment
        ((ClassicalOracleModel.ServiceJoin.sum left right).applicationLeft application) state =
      serviceJoinLeftResult left right
        (queryStep environment.1 application (serviceFrameLeft left right state)) := by
  dsimp only [ClassicalOracleModel.ServiceJoin.applicationLeft, queryStep,
    serviceFrameLeft, serviceJoinLeftResult]
  rw [kernelChoice_mapClassical (afterMap := inferInstance)]
  dsimp only [Function.comp_def, ClassicalOracleModel.transition]
  rw [kernelChoice_mapOutcome]
  simp only [ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance), Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- A right sum query preserves the other service as part of its untouched history. -/
public lemma queryStep_service_sum_right
    (environment : (ClassicalOracleModel.sum left right).Interpretation)
    (application : right.Application ctx)
    (state : State ctx Reference ((left.HiddenState × right.HiddenState) × History)) :
    queryStep environment
        ((ClassicalOracleModel.ServiceJoin.sum left right).applicationRight application) state =
      serviceJoinRightResult left right
        (queryStep environment.2 application (serviceFrameRight left right state)) := by
  dsimp only [ClassicalOracleModel.ServiceJoin.applicationRight, queryStep,
    serviceFrameRight, serviceJoinRightResult]
  rw [kernelChoice_mapClassical (afterMap := inferInstance)]
  dsimp only [Function.comp_def, ClassicalOracleModel.transition]
  rw [kernelChoice_mapOutcome]
  simp only [ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance), Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Execution
