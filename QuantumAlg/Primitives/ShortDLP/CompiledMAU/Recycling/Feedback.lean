/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Construction
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual previous-output feedback with its complete finite record

Every selected operator below comes from
the actual feedback gate list and actual previous-cell read. The equations
retain the whole caller store, hidden state, arbitrary prior history and
arbitrary external reference. No execution equation or instrument certificate
is required by an executable/public problem. The generic sequence helper is
used only to compose the proved native instruction equations.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

private lemma tensor_one (R S : Register) :
    UnitaryOperator.prodTensor (1 : UnitaryOperator R) (1 : UnitaryOperator S) = 1 := by
  apply Subtype.ext
  ext left right
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  change (if left.1 = right.1 then (1 : ℂ) else 0) *
      (if left.2 = right.2 then (1 : ℂ) else 0) =
    if left = right then 1 else 0
  have pair : left = right ↔ left.1 = right.1 ∧ left.2 = right.2 :=
    ⟨fun same => ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩,
      fun same => Prod.ext same.1 same.2⟩
  by_cases first : left.1 = right.1 <;> by_cases second : left.2 = right.2 <;>
    simp [pair, first, second]

private lemma applyUnitary_one {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) :
    state.applyUnitary (fun _ => 1) = state := by
  apply ExecutionState.ext
  intro entry
  exact DensityOperator.applyUnitary_one (state.block entry)

/-- The empty branch is an actual zero-event identity, with the same unique path as id. -/
lemma emptyUnitary_execute
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true)
      (UnitaryCircuit.identity AlgorithmGate.model .empty
        (Context base noQuantum m ell width).quantumLayout)).execute environment Reference state =
    (Circuit.id (model := model) (allowAllocation := true)
      (Context base noQuantum m ell width)).execute environment Reference state := by
  rw [Circuit.execute_unitary (quantumEnvironment := environment), UnitaryCircuit.identity_matrix,
    tensor_one,
    applyUnitary_one, Circuit.execute_id_mapClassical (environment := environment) (model := model)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The selected physical phase and its actual previous-bit branch are kept together. -/
lemma feedbackBit_execute (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    (feedbackBit base noQuantum m ell width inverse separation previous).execute environment
      Reference state =
    (state.applyUnitary fun entry => UnitaryOperator.prodTensor
      ((feedbackProgram base noQuantum m ell width inverse separation
        (entry.1.read (.storage previous.toCStorageRef))).matrix environment.quantum)
      (1 : UnitaryOperator Reference)).mapClassical
        (fun entry => (entry.1, (entry.2.1,
          (entry.2.2, ⟨entry.1.read (.storage previous.toCStorageRef), ()⟩)))) :=
  Circuit.selectedUnitary_execute (environment := environment) (allowAllocation := true)
    (.storage previous.toCStorageRef)
    (feedbackProgram base noQuantum m ell width inverse separation) state

/-- Internal composition of native store-preserving unitary equations.
The actual circuit paths remain in their true sequential product. -/
private lemma sequence_execute {ctx : RuntimeCtx .quantum}
    (first second : Circuit model ctx ctx)
    (Reference : Register)
    (leftAction rightAction : Store ctx → UnitaryOperator (ctx.register.prod Reference))
    (leftPath : Store ctx → first.Path) (rightPath : Store ctx → second.Path)
    (leftEquation : ∀ {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      first.execute environment Reference state =
        (state.applyUnitary fun entry => leftAction entry.1).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, leftPath entry.1)))))
    (rightEquation : ∀ {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.execute environment Reference state =
        (state.applyUnitary fun entry => rightAction entry.1).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, rightPath entry.1)))))
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (first.seq second).execute environment Reference state =
      (state.applyUnitary fun entry => rightAction entry.1 * leftAction entry.1).mapClassical
        (fun entry => (entry.1, (entry.2.1,
          (entry.2.2, (leftPath entry.1, rightPath entry.1))))) := by
  rw [Circuit.execute_seq (environment := environment), leftEquation, rightEquation,
    ExecutionState.applyUnitary_mapClassical]
  have combined :
      (state.applyUnitary fun entry => leftAction entry.1).applyUnitary
          (fun entry => rightAction entry.1) =
        state.applyUnitary (fun entry => rightAction entry.1 * leftAction entry.1) := by
    apply ExecutionState.ext
    intro entry
    exact (DensityOperator.applyUnitary_mul _ _ (state.block entry)).symm
  rw [combined]
  dsimp only [State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- These are the literal branch paths selected by the current complete store. -/
def feedbackPath (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → (bounded : count ≤ position.val) →
      Store (Context base noQuantum m ell width) →
        (feedbackPrefix base noQuantum m ell width inverse outputs position count bounded).Path
  | 0, _, _ => ()
  | count + 1, bounded, store => by
      refine ⟨feedbackPath inverse outputs position count (Nat.le_of_succ_le bounded) store, ?_⟩
      change (value : CShape.Value (.finite 2)) × Unit
      exact ⟨store.read (.storage
        ((outputs ⟨count, by have bound := position.isLt; omega⟩).toCStorageRef)), ()⟩

/-- The operator is the product of the real previous-bit-controlled native phase gates. -/
def feedbackAction (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (Reference : Register) :
    (count : Nat) → count ≤ position.val → Store (Context base noQuantum m ell width) →
      UnitaryOperator ((Context base noQuantum m ell width).register.prod Reference)
  | 0, _, _ => 1
  | count + 1, bounded, store =>
      UnitaryOperator.prodTensor
        ((feedbackProgram base noQuantum m ell width inverse (position.val - count - 1)
          (store.read (.storage
            (outputs ⟨count, by have bound := position.isLt; omega⟩).toCStorageRef))).matrix
              environment.quantum)
        (1 : UnitaryOperator Reference) *
      feedbackAction inverse outputs position Reference count
        (Nat.le_of_succ_le bounded) store

/-- Complete actual feedback, including coherent and mixed/reference correlations and history. -/
lemma feedbackPrefix_execute (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    (feedbackPrefix base noQuantum m ell width inverse outputs position count bounded).execute
      environment
        Reference state =
      (state.applyUnitary fun entry =>
        feedbackAction (environment := environment) base noQuantum m ell width inverse outputs
          position Reference
          count bounded entry.1).mapClassical
        (fun entry => (entry.1, (entry.2.1,
          (entry.2.2,
            feedbackPath base noQuantum m ell width inverse outputs position count bounded
              entry.1)))) := by
  induction count generalizing History with
  | zero =>
      simp only [feedbackPrefix, feedbackAction, feedbackPath,
        applyUnitary_one]
      exact (Circuit.execute_id_mapClassical (environment := environment) (model := model)
        Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | succ count ih =>
      let previous := outputs ⟨count, by have bound := position.isLt; omega⟩
      refine (sequence_execute (environment := environment) (ctx := Context base noQuantum m ell
        width)
        (feedbackPrefix base noQuantum m ell width inverse outputs position count
          (Nat.le_of_succ_le bounded))
        (feedbackBit base noQuantum m ell width inverse (position.val - count - 1) previous)
        Reference
        (feedbackAction (environment := environment) base noQuantum m ell width inverse outputs
          position Reference count
          (Nat.le_of_succ_le bounded))
        (fun store => UnitaryOperator.prodTensor
          ((feedbackProgram base noQuantum m ell width inverse (position.val - count - 1)
            (store.read (.storage previous.toCStorageRef))).matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        (feedbackPath base noQuantum m ell width inverse outputs position count
          (Nat.le_of_succ_le bounded))
        (fun store => ⟨store.read (.storage previous.toCStorageRef), ()⟩)
        (fun earlier => ih (Nat.le_of_succ_le bounded) earlier)
        (fun earlier => feedbackBit_execute base noQuantum m ell width inverse
          (position.val - count - 1) previous earlier) state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
