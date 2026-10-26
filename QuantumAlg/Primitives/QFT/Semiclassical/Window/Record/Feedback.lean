/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Matrix
import all QuantumAlg.Core.Execution.Instrument.Execution

/-!
# Full records of the actual causal earlier-window feedback leaf

The stored value read by the executed branch is retained in its real Path.
Other streams and future positions execute the existing identity branch.
Every original Store, hidden state, history and external reference entry
remains present, without a condition on initial classical cell values.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

private lemma conditional_values {Value : Type} {proposition : Prop}
    (first second : Decidable proposition) (yes no : Value) :
    @ite Value proposition first yes no = @ite Value proposition second yes no := by
  cases first with
  | isTrue chosen =>
      cases second with
      | isTrue _ => rfl
      | isFalse absent => exact False.elim (absent chosen)
  | isFalse absent =>
      cases second with
      | isTrue chosen => exact False.elim (absent chosen)
      | isFalse _ => rfl

/-- A static guard selects the actual component record using the same explicit decision. -/
private def guardedStoreRecord (proposition : Prop) (decision : Decidable proposition)
    (first second : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx false)
    (firstRecord : Store ctx → Unit → Store ctx × first.Path)
    (secondRecord : Store ctx → Unit → Store ctx × second.Path) :
    Store ctx → Unit → Store ctx ×
      (@ite (Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false)
        proposition decision first second).Path :=
  match decision with
  | .isTrue _ => firstRecord
  | .isFalse _ => secondRecord

private lemma guardedStoreRecord_store (proposition : Prop) (decision : Decidable proposition)
    (first second : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx false)
    (firstRecord : Store ctx → Unit → Store ctx × first.Path)
    (secondRecord : Store ctx → Unit → Store ctx × second.Path)
    (firstStore : ∀ store outcome, (firstRecord store outcome).1 = store)
    (secondStore : ∀ store outcome, (secondRecord store outcome).1 = store)
    (store : Store ctx) (outcome : Unit) :
    (guardedStoreRecord proposition decision first second firstRecord secondRecord
      store outcome).1 = store := by
  cases decision with
  | isTrue _ => exact firstStore store outcome
  | isFalse _ => exact secondStore store outcome

/-- Component interpreter equations transport through an identical static syntax guard. -/
private lemma guarded_record_matrix (proposition : Prop) (decision : Decidable proposition)
    (first second : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx false)
    (firstRecord : Store ctx → Unit → Store ctx × first.Path)
    (secondRecord : Store ctx → Unit → Store ctx × second.Path)
    (operator : (Reference : Register) → Store ctx → HilbertOperator (ctx.register.prod Reference))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment)
    (firstEquation : proposition → ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)) result,
      ((first.execute environment Reference state).block result).matrix =
        ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Unit,
          if Execution.Instrument.retainedRecord firstRecord original outcome = result then
            operator Reference original.1 * (state.block original).matrix *
              (operator Reference original.1).conjTranspose else 0)
    (secondEquation : ¬proposition → ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)) result,
      ((second.execute environment Reference state).block result).matrix =
        ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Unit,
          if Execution.Instrument.retainedRecord secondRecord original outcome = result then
            operator Reference original.1 * (state.block original).matrix *
              (operator Reference original.1).conjTranspose else 0)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (@ite (Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false)
        proposition decision first second).Path))) :
    (((@ite (Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false)
      proposition decision first second).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Unit,
        if Execution.Instrument.retainedRecord
            (guardedStoreRecord proposition decision first second firstRecord secondRecord)
              original outcome = result then
          operator Reference original.1 * (state.block original).matrix *
            (operator Reference original.1).conjTranspose else 0 := by
  cases decision with
  | isTrue chosen => exact firstEquation chosen Reference state result
  | isFalse absent => exact secondEquation absent Reference state result

private def selectedStoreRecord (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (store : Store ctx) (_outcome : Unit) :
    Store ctx × (selected (oracles := .empty) (operations := operations)
      (services := services) ports previous current).Path :=
  (store, ⟨store.read (.storage (ports.results previous).toCStorageRef), ()⟩)

/-- The real guarded branch keeps exactly the stored value it actually reads. -/
def oneStoreRecord (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (store : Store ctx) (_outcome : Unit) :
    Store ctx × (one (oracles := .empty) (operations := operations)
      (services := services) ports previous current).Path :=
  guardedStoreRecord (ports.past previous) (Classical.propDecidable (ports.past previous))
    (selected (oracles := .empty) (operations := operations) (services := services)
      ports previous current)
    (Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx)
    (selectedStoreRecord (operations := operations) (services := services) ports previous current)
    (fun stored (_ : Unit) => (stored, ())) store _outcome

lemma oneStoreRecord_store (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active) (store : Store ctx)
    (outcome : Unit) :
    (oneStoreRecord (operations := operations) (services := services) ports previous current
      store outcome).1 = store :=
  guardedStoreRecord_store _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) store outcome

private lemma selected_record_matrix (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (selected (oracles := .empty) (operations := operations) (services := services)
        ports previous current).Path))) :
    (((selected ports previous current).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Unit,
        if Execution.Instrument.retainedRecord
            (selectedStoreRecord (operations := operations) (services := services)
              ports previous current) original outcome = result then
          (UnitaryOperator.prodTensor ((phaseProgram ports previous current
              (original.1.read (.storage (ports.results previous).toCStorageRef))).matrix
                environment.quantum) (1 : UnitaryOperator Reference) :
                  HilbertOperator (ctx.register.prod Reference)) * (state.block original).matrix *
            (UnitaryOperator.prodTensor ((phaseProgram ports previous current
              (original.1.read (.storage (ports.results previous).toCStorageRef))).matrix
                environment.quantum) (1 : UnitaryOperator Reference) :
                  HilbertOperator (ctx.register.prod Reference)).conjTranspose
        else 0 := by
  dsimp only [selected, Circuit.Path] at result
  unfold selected
  rw [Circuit.selectedUnitary_execute, ExecutionState.mapClassical_block_matrix]
  simp only [Fintype.sum_unique, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix]
  apply Finset.sum_congr rfl
  intro original _
  simp only [Execution.Instrument.retainedRecord, selectedStoreRecord]
  exact conditional_values _ _ _ _

private lemma identity_record_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × Unit))) :
    (((Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ _outcome : Unit,
        if (original.1, (original.2.1, (original.2.2, ()))) = result then
          (1 : HilbertOperator (ctx.register.prod Reference)) * (state.block original).matrix *
            (1 : HilbertOperator (ctx.register.prod Reference)).conjTranspose
        else 0 := by
  simp only [Fintype.sum_unique, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rcases result with ⟨store, hidden, history, emptyPath⟩
  cases emptyPath
  rw [Circuit.execute_id_block]
  symm
  rw [Finset.sum_eq_single (store, (hidden, history))]
  · simp
  · intro original _ different
    have excluded : (original.1, (original.2.1, (original.2.2, ()))) ≠
        (store, (hidden, (history, ()))) := by
      intro same
      exact different (Prod.ext (congrArg (fun entry => entry.1) same)
        (Prod.ext (congrArg (fun entry => entry.2.1) same)
          (congrArg (fun entry => entry.2.2.1) same)))
    exact if_neg excluded
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

/-- Each complete actual feedback record has precisely its native selected full-layout operator. -/
lemma one_record_matrix (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (one (oracles := .empty) (operations := operations) (services := services)
        ports previous current).Path))) :
    (((one ports previous current).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Unit,
        if Execution.Instrument.retainedRecord
            (oneStoreRecord (operations := operations) (services := services)
              ports previous current) original outcome = result then
          oneOperator ports previous current environment.quantum Reference original.1 *
            (state.block original).matrix *
              (oneOperator ports previous current environment.quantum Reference
                original.1).conjTranspose
        else 0 := by
  exact guarded_record_matrix (ports.past previous)
    (Classical.propDecidable (ports.past previous))
    (selected (oracles := .empty) (operations := operations) (services := services)
      ports previous current)
    (Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx)
    (selectedStoreRecord (operations := operations) (services := services) ports previous current)
    (fun store (_ : Unit) => (store, ()))
    (fun reference store => oneOperator ports previous current environment.quantum reference store)
    environment
    (by
      intro prior reference history _ input selectedResult
      refine (selected_record_matrix ports previous current environment reference input
        selectedResult).trans ?_
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      simp only [oneOperator, if_pos prior])
    (by
      intro prior reference history _ input selectedResult
      refine (identity_record_matrix environment reference input selectedResult).trans ?_
      simp only [Fintype.sum_unique, oneOperator, if_neg prior,
        Execution.Instrument.retainedRecord,
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      apply Finset.sum_congr rfl
      intro original _
      exact conditional_values _ _ _ _)
    Reference state result

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
