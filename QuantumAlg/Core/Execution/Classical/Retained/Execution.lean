/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Retained.Cells
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Classical.Retained.Cells
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete execution of heterogeneous retained-cell allocation

Each real retain instruction initializes its matching store cell. The
interpreter preserves the entire hidden service state, mathematical history,
quantum register, and external reference while recording the unique path.
-/

namespace QuantumAlg.Execution.RetainedCells

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The sole path through the actual sequence of retained allocations. -/
@[implicit_reducible]
public def allocatePath {model : ExecutionModel} (ctx : RuntimeCtx model.kind) :
    (shapes : List CShape) → (allocate (model := model) ctx shapes).Path
  | [] => ()
  | _ :: tail => (allocatePath (model := model) ctx tail, ())

/-- Retained classical storage leaves the complete quantum register unchanged. -/
public lemma context_register {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) :
    (context ctx shapes).register = ctx.register := by
  induction shapes with
  | nil => rfl
  | cons shape tail ih =>
      rw [context, RuntimeCtx.runtimeCtx_register_addRetained, ih]

private lemma mapClassical_register_transport
    {C D : Type} [Fintype C] [Fintype D]
    {Reference R S : Register} {first second : DecidableEq D}
    (h : R = S) (state : ExecutionState C (Register.prod R Reference))
    (update : C → D) :
    @ExecutionState.mapClassical C D _ _ (Register.prod S Reference) second
      (Eq.mp
        (congrArg
          (fun register : Register => ExecutionState C (Register.prod register Reference)) h)
        state) update =
      Eq.mp
        (congrArg
          (fun register : Register => ExecutionState D (Register.prod register Reference)) h)
        (@ExecutionState.mapClassical C D _ _ (Register.prod R Reference) first state
          update) := by
  cases h
  exact ExecutionState.executionState_mapClassical_congr state rfl

private lemma register_transport_refl
    {C : Type} [Fintype C] {Reference R : Register}
    (h : R = R) (state : ExecutionState C (Register.prod R Reference)) :
    Eq.mp
      (congrArg
        (fun register : Register => ExecutionState C (Register.prod register Reference)) h)
      state = state := by
  cases h
  rfl

/-- Every actual retain initializes the corresponding store cell and preserves the full
hidden, quantum, reference, and prior-history record. -/
public lemma allocate_execute {model : ExecutionModel}
    (environment : model.Environment) (ctx : RuntimeCtx model.kind)
    (shapes : List CShape) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (allocate (model := model) ctx shapes).execute environment Reference state =
      Eq.mp
        (congrArg
          (fun register : Register =>
            ExecutionState
              (Store (context ctx shapes) ×
                (model.HiddenState × (History × (allocate (model := model) ctx shapes).Path)))
              (Register.prod register Reference))
          (context_register ctx shapes).symm)
        (@ExecutionState.mapClassical _ _ _ _ _ (Classical.decEq _) state (fun entry =>
          (pushStore ctx shapes entry.1,
            (entry.2.1, (entry.2.2, allocatePath (model := model) ctx shapes))))) := by
  induction shapes with
  | nil =>
      rw [register_transport_refl
        (h := (context_register ctx ([] : List CShape)).symm)]
      simp only [allocate, pushStore, allocatePath]
      rw [Circuit.execute_id]
      exact ExecutionState.executionState_mapClassical_congr state rfl
  | cons shape tail ih =>
      let prior := context ctx tail
      let key := prior.canonicalFreshKey
      let fresh := prior.canonicalFreshKey_fresh
      change (Circuit.seq (allocate (model := model) ctx tail)
          (Circuit.retain (model := model) prior key shape fresh)).execute
            environment Reference state = _
      rw [Circuit.execute_seq, Circuit.execute_retain, ih]
      simp only [State.mapHistory,
        ExecutionState.executionState_mapClassical_comp_instances, Function.comp_def]
      rw [mapClassical_register_transport
        (R := ctx.register) (S := (context ctx tail).register)
        (Reference := Reference)
        (h := (context_register ctx tail).symm)
        (first := Classical.decEq _)]
      simp only [ExecutionState.executionState_mapClassical_comp_instances,
        Function.comp_def]
      have sameCarrier :
          (context_register ctx (shape :: tail)).symm =
            (context_register ctx tail).symm := Subsingleton.elim _ _
      rw [sameCarrier]
      congr 1
      exact ExecutionState.executionState_mapClassical_congr state rfl

end

end QuantumAlg.Execution.RetainedCells
