/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Measure.Instrument
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Execution.Random.Kernel
import all QuantumAlg.Core.Execution.Control
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density

/-!
# Exact equations for the single circuit interpreter

These equations retain caller storage, persistent classical service state,
mathematical paths and the full quantum/reference block. Native operations and
queries use only their model-owned transitions. A query changes its service
state explicitly; other instructions preserve that state.

Unitary execution conjugates each complete block beside the reference identity
[dW19, qcnotes.tex:5405]. Z measurement preserves the full projected block,
writes the observed result, and records that same outcome [dW19, qcnotes.tex:5409].
Classical branches select bodies by actual stored values.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Decidable equality implementations do not change finite block pushforwards.
private theorem mapClassical_instance_eq {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (first second : DecidableEq D) (state : ExecutionState C R) (f : C → D) :
    @ExecutionState.mapClassical C D _ _ R first state f =
      @ExecutionState.mapClassical C D _ _ R second state f := by
  cases Subsingleton.elim first second
  rfl

private theorem mapClassical_function_eq {C D : Type} [Fintype C] [Fintype D]
    {R : Register} {first second : DecidableEq D} (state : ExecutionState C R)
    {f g : C → D} (agree : f = g) :
    @ExecutionState.mapClassical C D _ _ R first state f =
      @ExecutionState.mapClassical C D _ _ R second state g := by
  cases Subsingleton.elim first second
  cases agree
  rfl

private theorem mapClassical_comp_any {C D E : Type} [Fintype C] [Fintype D] [Fintype E]
    {R : Register} {middle : DecidableEq D} {last result : DecidableEq E}
    (state : ExecutionState C R) (first : C → D) (second : D → E) :
    @ExecutionState.mapClassical D E _ _ R last
      (@ExecutionState.mapClassical C D _ _ R middle state first) second =
        @ExecutionState.mapClassical C E _ _ R result state (second ∘ first) := by
  exact (@ExecutionState.executionState_mapClassical_comp C D _ _ R E _ middle last
    state first second).trans (mapClassical_instance_eq last result state _)

private theorem record_key {C S H : Type} (entry : C × (S × H))
    (store : C) (hidden : S) (history : H) :
    (entry.1, (entry.2.1, (entry.2.2, ()))) = (store, (hidden, (history, ()))) ↔
      entry = (store, (hidden, history)) := by
  constructor
  · intro equality
    exact Prod.ext (congrArg (fun value : C × (S × (H × Unit)) => value.1) equality)
      (Prod.ext (congrArg (fun value : C × (S × (H × Unit)) => value.2.1) equality)
        (congrArg (fun value : C × (S × (H × Unit)) => value.2.2.1) equality))
  · intro equality
    cases equality
    rfl

private theorem record_block {C S H : Type} [Fintype C] [Fintype S] [Fintype H]
    {R : Register} (state : ExecutionState (C × (S × H)) R)
    (store : C) (hidden : S) (history : H) :
    (state.mapClassical fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))).block
      (store, (hidden, (history, ()))) = state.block (store, (hidden, history)) := by
  apply DensityOperator.ext
  change (∑ entry : C × (S × H),
    if (entry.1, (entry.2.1, (entry.2.2, ()))) = (store, (hidden, (history, ()))) then
      (state.block entry).matrix else 0) = (state.block (store, (hidden, history))).matrix
  simp only [record_key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {Reference : Register}
  {H : Type} [Fintype H]

/-- Identity records its unique path and preserves the same persistent state. -/
theorem execute_id (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.id (model := model) ctx).execute Reference state =
      state.mapClassical (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  dsimp only [execute, interpret, preserveService, State.skip, State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance)]
  exact mapClassical_function_eq _ rfl

/-- The identity instruction preserves each complete service/quantum/reference block. -/
theorem execute_id_block (state : State ctx Reference (model.HiddenState × H))
    (store : Store ctx) (hidden : model.HiddenState) (history : H) :
    ((Circuit.id (model := model) ctx).execute Reference state).block
      (store, (hidden, (history, ()))) = state.block (store, (hidden, history)) := by
  rw [execute_id]
  exact record_block state store hidden history

/-- Public identity execution keeps the entire joint state block. -/
public theorem circuit_execute_id_block (state : State ctx Reference (model.HiddenState × H))
    (store : Store ctx) (hidden : model.HiddenState) (history : H) :
    ((Circuit.id (model := model) ctx).execute Reference state).block
      (store, (hidden, (history, ()))) = state.block (store, (hidden, history)) :=
  execute_id_block state store hidden history

/-- A native instruction samples its declaration and writes that actual result. -/
theorem execute_classical (state : State ctx Reference (model.HiddenState × H))
    (application : model.classicalOperations.Application ctx) :
    (Circuit.classical (model := model) application).execute Reference state =
      (kernelChoice state fun entry => model.classicalOperations.evaluate application.token
        (entry.1.read application.input)).mapClassical (fun entry =>
          (entry.1.1.write application.output entry.2,
            (entry.1.2.1, (entry.1.2.2, entry.2)))) := by
  dsimp only [execute, interpret, preserveService, nativeStep, State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance)]
  exact mapClassical_function_eq _ rfl

/-- Native output blocks sum the actual declaration probabilities without losing correlations. -/
theorem execute_classical_block_matrix (state : State ctx Reference (model.HiddenState × H))
    (application : model.classicalOperations.Application ctx)
    (result : Store ctx × (model.HiddenState ×
      (H × (model.classicalOperations.outputShape application.token).Value))) :
    (((Circuit.classical (model := model) application).execute Reference state).block
      result).matrix =
      ∑ entry : Store ctx × (model.HiddenState × H), ∑ outcome,
        if (entry.1.write application.output outcome,
            (entry.2.1, (entry.2.2, outcome))) = result then
          (model.classicalOperations.evaluate application.token
            (entry.1.read application.input) outcome).toReal •
              (state.block entry).matrix else 0 := by
  rw [execute_classical]
  change (∑ entry : (Store ctx × (model.HiddenState × H)) ×
      (model.classicalOperations.outputShape application.token).Value,
    if (entry.1.1.write application.output entry.2,
        (entry.1.2.1, (entry.1.2.2, entry.2))) = result then
      ((kernelChoice state fun value => model.classicalOperations.evaluate application.token
        (value.1.read application.input)).block entry).matrix else 0) = _
  rw [Fintype.sum_prod_type]
  simp only [kernelChoice_block_matrix]

open scoped Classical in
/-- Public native execution uses only the granted token's actual probability law. -/
public theorem circuit_execute_classical_block_matrix
    (state : State ctx Reference (model.HiddenState × H))
    (application : model.classicalOperations.Application ctx)
    (result : Store ctx × (model.HiddenState ×
      (H × (model.classicalOperations.outputShape application.token).Value))) :
    (((Circuit.classical (model := model) application).execute Reference state).block
      result).matrix =
      ∑ entry : Store ctx × (model.HiddenState × H), ∑ outcome,
        if (entry.1.write application.output outcome,
            (entry.2.1, (entry.2.2, outcome))) = result then
          (model.classicalOperations.evaluate application.token
            (entry.1.read application.input) outcome).toReal • (state.block entry).matrix else 0 :=
  execute_classical_block_matrix state application result

/-- A granted query uses the current shared state and returns its actual next state. -/
theorem execute_classicalQuery (state : State ctx Reference (model.HiddenState × H))
    (application : model.classicalOracles.Application ctx) :
    (Circuit.classicalQuery (model := model) application).execute Reference state =
      queryStep application state := rfl

open scoped Classical in
/-- A granted query retains its joint next-state/result distribution in public observations. -/
public theorem circuit_execute_classicalQuery_block_matrix
    (state : State ctx Reference (model.HiddenState × H))
    (application : model.classicalOracles.Application ctx)
    (result : Store ctx × (model.HiddenState ×
      (H × (model.classicalOracles.outputShape application.query).Value))) :
    (((Circuit.classicalQuery (model := model) application).execute Reference state).block
      result).matrix =
      ∑ entry : Store ctx × (model.HiddenState × H),
        ∑ outcome : model.HiddenState ×
            (model.classicalOracles.outputShape application.query).Value,
          if (entry.1.write application.output outcome.2,
              (outcome.1, (entry.2.2, outcome.2))) = result then
            (model.classicalOracles.transition application.query entry.2.1
              (entry.1.read application.input) outcome).toReal • (state.block entry).matrix
          else 0 := by
  rw [execute_classicalQuery]
  exact queryStep_block_matrix application state result

/-- Branches execute only the corresponding actual read fibers, preserving service state. -/
theorem execute_branch_block_matrix {post : RuntimeCtx model.kind} {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit model ctx post)
    (state : State ctx Reference (model.HiddenState × H))
    (result : Store post × (model.HiddenState × (H × (Circuit.branch input body).Path))) :
    (((Circuit.branch input body).execute Reference state).block result).matrix =
      ∑ value : shape.Value,
        ((((body value).execute Reference
          (state.selectClassical (fun entry => entry.1.read input) value)).mapHistory
            (fun history => (history.1, (history.2.1, ⟨value, history.2.2⟩)))).block
              result).matrix := rfl

/-- Retaining a result initializes its real cell and preserves the existing service state. -/
theorem execute_retain (state : State ctx Reference (model.HiddenState × H))
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (Circuit.retain (model := model) ctx key shape fresh).execute Reference state =
      state.mapClassical (fun entry =>
        (entry.1.pushRetained key shape fresh, (entry.2.1, (entry.2.2, ())))) := by
  dsimp only [execute, interpret, preserveService, State.retain, State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance)]
  exact mapClassical_function_eq _ rfl

/-- Sequential execution passes the same service state between actual bodies. -/
theorem execute_seq {middle post : RuntimeCtx model.kind}
    (first : Circuit model ctx middle) (second : Circuit model middle post)
    (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.seq first second).execute Reference state =
      (second.execute Reference (first.execute Reference state)).mapHistory
        (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) := rfl

section Quantum

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- The granted unitary acts on each block beside the external reference identity. -/
theorem execute_unitary (state : State ctx Reference (services.HiddenState × H))
    (program : UnitaryCircuit gates oracles ctx.quantumLayout) :
    (Circuit.unitary (operations := operations) (classicalOracles := services)
      program).execute Reference state =
      (state.applyUnitary fun _ =>
        UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  dsimp only [execute, interpret, preserveService, State.unitary, State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance)]
  exact mapClassical_function_eq _ rfl

/-- A unitary preserves hidden-state correlations as well as the external reference. -/
theorem execute_unitary_block (state : State ctx Reference (services.HiddenState × H))
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (store : Store ctx) (hidden : services.HiddenState) (history : H) :
    ((Circuit.unitary (operations := operations) (classicalOracles := services)
      program).execute Reference state).block (store, (hidden, (history, ()))) =
        DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
          (state.block (store, (hidden, history))) := by
  rw [execute_unitary]
  exact record_block (state.applyUnitary fun _ =>
    UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) store hidden history

/-- Complete unitary block evolution, including mixed and reference-correlated inputs. -/
theorem execute_unitary_block_matrix (state : State ctx Reference (services.HiddenState × H))
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (store : Store ctx) (hidden : services.HiddenState) (history : H) :
    (((Circuit.unitary (operations := operations) (classicalOracles := services)
      program).execute Reference state).block (store, (hidden, (history, ())))).matrix =
        let operator := UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)
        (operator : HilbertOperator (ctx.register.prod Reference)) *
          (state.block (store, (hidden, history))).matrix *
            (operator : HilbertOperator (ctx.register.prod Reference)).conjTranspose := by
  rw [execute_unitary_block]
  exact DensityOperator.applyUnitary_matrix _ _

/-- Public exact unitary evolution keeps the complete service/quantum/reference block. -/
public theorem circuit_execute_unitary_block_matrix
    (state : State ctx Reference (services.HiddenState × H))
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (store : Store ctx) (hidden : services.HiddenState) (history : H) :
    (((Circuit.unitary (operations := operations) (classicalOracles := services)
      program).execute Reference state).block (store, (hidden, (history, ())))).matrix =
        let operator := UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)
        (operator : HilbertOperator (ctx.register.prod Reference)) *
          (state.block (store, (hidden, history))).matrix *
            (operator : HilbertOperator (ctx.register.prod Reference)).conjTranspose :=
  execute_unitary_block_matrix state program store hidden history

/-- Z execution writes and records the same observed result without resetting service state. -/
theorem execute_measureZ (state : State ctx Reference (services.HiddenState × H))
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    (Circuit.measureZ (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := services) wire output).execute Reference state =
      (ExecutionState.measureZ state fun basis => basis.1 wire).mapClassical (fun entry =>
        (entry.1.1.write output (.finite entry.2), (entry.1.2.1, (entry.1.2.2, entry.2)))) := by
  dsimp only [execute, interpret, preserveService, State.measureZ, State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance)]
  exact mapClassical_function_eq _ rfl

/-- Measurement projects the physical wire while retaining every classical and reference block. -/
theorem execute_measureZ_block_matrix (state : State ctx Reference (services.HiddenState × H))
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (result : Store ctx × (services.HiddenState ×
      (H × Fin (ctx.quantumLayout.wire wire).dimension))) :
    (((Circuit.measureZ (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := services) wire output).execute Reference state).block result).matrix =
      ∑ entry : (Store ctx × (services.HiddenState × H)) ×
          Fin (ctx.quantumLayout.wire wire).dimension,
        if (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, entry.2))) = result then
          (ZMeasurement.branch (R := ctx.register.prod Reference)
            (fun basis => basis.1 wire) entry.2 (state.block entry.1)).matrix else 0 := by
  rw [execute_measureZ]
  rfl

open scoped Classical in
/-- Public Z execution retains its complete projected blocks and the actual stored readout. -/
public theorem circuit_execute_measureZ_block_matrix
    (state : State ctx Reference (services.HiddenState × H))
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (result : Store ctx × (services.HiddenState ×
      (H × Fin (ctx.quantumLayout.wire wire).dimension))) :
    (((Circuit.measureZ (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := services) wire output).execute Reference state).block result).matrix =
      ∑ entry : (Store ctx × (services.HiddenState × H)) ×
          Fin (ctx.quantumLayout.wire wire).dimension,
        if (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, entry.2))) = result then
          (ZMeasurement.branch (R := ctx.register.prod Reference)
            (fun basis => basis.1 wire) entry.2 (state.block entry.1)).matrix else 0 :=
  execute_measureZ_block_matrix state wire output result

end Quantum

end

end QuantumAlg.Circuit
