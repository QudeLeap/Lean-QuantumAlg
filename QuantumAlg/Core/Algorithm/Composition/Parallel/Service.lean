/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Exact service projections of an original child execution

Selecting an active service sums the inaccessible service coordinate without
conditioning. Its current state is still preserved by the actual surrounding
execution. These proof observations do not initialize or replace a service.
-/

namespace QuantumAlg.Execution

noncomputable section

attribute [local instance] Classical.decEq

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H Path : Type} [Fintype H] [Fintype Path]

/-- Observe the existing left service together with every original history label. -/
def selectServiceLeft (state : State ctx Reference (parent.HiddenState × H)) :
    State ctx Reference (left.HiddenState × H) :=
  state.mapHistory (fun record => ((join.hidden record.1).1, record.2))

/-- Observe the existing right service together with every original history label. -/
def selectServiceRight (state : State ctx Reference (parent.HiddenState × H)) :
    State ctx Reference (right.HiddenState × H) :=
  state.mapHistory (fun record => ((join.hidden record.1).2, record.2))

/-- The actual left input conversion only changes history coordinates. -/
lemma serviceInputLeft_eq_mapHistory
    (state : State ctx Reference (parent.HiddenState × H)) :
    serviceInputLeft join state = state.mapHistory (serviceHistoryLeft join H) :=
  ExecutionState.executionState_mapClassical_congr state rfl

/-- The actual right input conversion only changes history coordinates. -/
lemma serviceInputRight_eq_mapHistory
    (state : State ctx Reference (parent.HiddenState × H)) :
    serviceInputRight join state = state.mapHistory (serviceHistoryRight join H) :=
  ExecutionState.executionState_mapClassical_congr state rfl

/-- The actual left result conversion retains both current service components. -/
lemma serviceOutputLeft_eq_mapHistory
    (state : State ctx Reference (left.HiddenState × ((right.HiddenState × H) × Path))) :
    serviceOutputLeft join state = state.mapHistory (serviceResultLeft join H Path).symm :=
  ExecutionState.executionState_mapClassical_congr state rfl

/-- The actual right result conversion retains both current service components. -/
lemma serviceOutputRight_eq_mapHistory
    (state : State ctx Reference (right.HiddenState × ((left.HiddenState × H) × Path))) :
    serviceOutputRight join state = state.mapHistory (serviceResultRight join H Path).symm :=
  ExecutionState.executionState_mapClassical_congr state rfl

/-- Forgetting the inactive input coordinate gives the original left joint input. -/
lemma serviceInputLeft_forget_inactive
    (state : State ctx Reference (parent.HiddenState × H)) :
    (serviceInputLeft join state).mapHistory (fun record => (record.1, record.2.2)) =
      selectServiceLeft join state := by
  rw [serviceInputLeft_eq_mapHistory, State.mapHistory_comp]
  unfold selectServiceLeft State.mapHistory
  exact ExecutionState.executionState_mapClassical_congr state rfl

/-- Forgetting the inactive input coordinate gives the original right joint input. -/
lemma serviceInputRight_forget_inactive
    (state : State ctx Reference (parent.HiddenState × H)) :
    (serviceInputRight join state).mapHistory (fun record => (record.1, record.2.2)) =
      selectServiceRight join state := by
  rw [serviceInputRight_eq_mapHistory, State.mapHistory_comp]
  unfold selectServiceRight State.mapHistory
  exact ExecutionState.executionState_mapClassical_congr state rfl

/-- Left output projection keeps the changed active state and its actual newly produced path. -/
lemma serviceOutputLeft_select_active
    (state : State ctx Reference (left.HiddenState × ((right.HiddenState × H) × Path))) :
    selectServiceLeft join (serviceOutputLeft join state) =
      state.mapHistory (fun record => (record.1, (record.2.1.2, record.2.2))) := by
  rw [selectServiceLeft, serviceOutputLeft_eq_mapHistory, State.mapHistory_comp]
  unfold State.mapHistory
  apply ExecutionState.executionState_mapClassical_congr
  funext record
  change (record.1, ((join.hidden (join.hidden.symm
    (record.2.1, record.2.2.1.1))).1, (record.2.2.1.2, record.2.2.2))) = _
  rw [join.hidden.apply_symm_apply]

/-- Right output projection keeps the changed active state and its actual newly produced path. -/
lemma serviceOutputRight_select_active
    (state : State ctx Reference (right.HiddenState × ((left.HiddenState × H) × Path))) :
    selectServiceRight join (serviceOutputRight join state) =
      state.mapHistory (fun record => (record.1, (record.2.1.2, record.2.2))) := by
  rw [selectServiceRight, serviceOutputRight_eq_mapHistory, State.mapHistory_comp]
  unfold State.mapHistory
  apply ExecutionState.executionState_mapClassical_congr
  funext record
  change (record.1, ((join.hidden (join.hidden.symm
    (record.2.2.1.1, record.2.1))).2, (record.2.2.1.2, record.2.2.2))) = _
  rw [join.hidden.apply_symm_apply]

/-- A left child's actual execution on the projected input is its active output marginal. -/
lemma serviceLeft_execute_select_active
    {model : ExecutionModel} {other parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin model.classicalOracles other parent)
    {ctx : RuntimeCtx model.kind} (code : Circuit model ctx ctx false)
    (environment : model.Environment)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State ctx Reference (parent.HiddenState × H)) :
    selectServiceLeft join
        (serviceOutputLeft join
          (code.execute environment Reference (serviceInputLeft join state))) =
      code.execute environment Reference (selectServiceLeft join state) := by
  rw [serviceOutputLeft_select_active]
  exact (code.execute_mapHistory environment Reference
    (serviceInputLeft join state) Prod.snd).symm.trans
    (congrArg (code.execute environment Reference) (serviceInputLeft_forget_inactive join state))

/-- A right child's actual execution on the projected input is its active output marginal. -/
lemma serviceRight_execute_select_active
    {model : ExecutionModel} {other parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin other model.classicalOracles parent)
    {ctx : RuntimeCtx model.kind} (code : Circuit model ctx ctx false)
    (environment : model.Environment)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State ctx Reference (parent.HiddenState × H)) :
    selectServiceRight join
        (serviceOutputRight join
          (code.execute environment Reference (serviceInputRight join state))) =
      code.execute environment Reference (selectServiceRight join state) := by
  rw [serviceOutputRight_select_active]
  exact (code.execute_mapHistory environment Reference
    (serviceInputRight join state) Prod.snd).symm.trans
    (congrArg (code.execute environment Reference) (serviceInputRight_forget_inactive join state))

end

end QuantumAlg.Execution
