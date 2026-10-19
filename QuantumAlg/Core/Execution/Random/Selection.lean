/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Random.Kernel.Selection
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Control
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density

/-!
# Sampling followed by an actual granted quantum subprogram

The selected native declaration owns its probability distribution. Its actual
output is written to the supplied storage reference, and a classical branch
reads that same storage to choose a unitary circuit over the already-granted
gate and quantum oracle models. Neither a free unitary nor detached accounting
is admitted at this boundary.

The complete state equality keeps the actual store, persistent service state,
mathematical history, sampled and selected paths, and arbitrary quantum reference.
Every matrix block carries the declaration's actual weight, including zero
probabilities and nonuniform distributions.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Decidable equality implementations do not change finite block pushforwards.
private lemma mapClassical_instance_eq {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (first second : DecidableEq D) (state : ExecutionState C R) (f : C → D) :
    @ExecutionState.mapClassical C D _ _ R first state f =
      @ExecutionState.mapClassical C D _ _ R second state f := by
  cases Subsingleton.elim first second
  rfl

private lemma mapClassical_function_eq {C D : Type} [Fintype C] [Fintype D]
    {R : Register} {first second : DecidableEq D} (state : ExecutionState C R)
    {f g : C → D} (agree : f = g) :
    @ExecutionState.mapClassical C D _ _ R first state f =
      @ExecutionState.mapClassical C D _ _ R second state g := by
  cases Subsingleton.elim first second
  cases agree
  rfl

private lemma mapClassical_comp_any {C D E : Type} [Fintype C] [Fintype D] [Fintype E]
    {R : Register} {middle : DecidableEq D} {last result : DecidableEq E}
    (state : ExecutionState C R) (first : C → D) (second : D → E) :
    @ExecutionState.mapClassical D E _ _ R last
      (@ExecutionState.mapClassical C D _ _ R middle state first) second =
        @ExecutionState.mapClassical C E _ _ R result state (second ∘ first) := by
  exact (@ExecutionState.executionState_mapClassical_comp C D _ _ R E _ middle last
    state first second).trans (mapClassical_instance_eq last result state _)

-- Summing selected branches is the same complete state as the actual read's
-- conditional unitary, with the selected value retained in every output record.
private lemma selected_unitary {C D Value : Type} [Fintype C] [Fintype D] [Fintype Value]
    [DecidableEq D] [DecidableEq Value]
    {R : Register} (state : ExecutionState C R) (read : C → Value)
    (operator : Value → UnitaryOperator R) (record : C → Value → D) :
    runSelected state read
        (fun value part => (part.applyUnitary fun _ => operator value).mapClassical
          fun entry => record entry value)
        (fun _ part => (ExecutionState.mapClassical_mass _ _).trans
          (ExecutionState.applyUnitary_mass part _)) =
      (state.applyUnitary fun entry => operator (read entry)).mapClassical
        (fun entry => record entry (read entry)) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [runSelected_block_matrix]
  simp only [ExecutionState.mapClassical, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix, ExecutionState.selectClassical_block,
    apply_ite DensityOperator.matrix, DensityOperator.zero_matrix]
  change (∑ value, ∑ entry,
    if record entry value = result then
      (operator value : HilbertOperator R) *
        (if read entry = value then (state.block entry).matrix else 0) *
          (operator value : HilbertOperator R).conjTranspose else 0) =
    ∑ entry, if record entry (read entry) = result then
      (operator (read entry) : HilbertOperator R) * (state.block entry).matrix *
        (operator (read entry) : HilbertOperator R).conjTranspose else 0
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entry _
  rw [Finset.sum_eq_single (read entry)]
  · simp only [if_true]
  · intro other _ different
    simp only [Ne.symm different, if_false, Matrix.mul_zero, Matrix.zero_mul, ite_self]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum} {Reference : Register} {H : Type} [Fintype H]
  (environment : (ExecutionModel.quantum gates oracles operations services).Environment)

private lemma execute_unitary (word : UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : State ctx Reference (services.HiddenState × H)) :
    (Circuit.unitary (allowAllocation := true) (operations := operations)
      (classicalOracles := services) word).execute
        environment Reference state =
      (state.applyUnitary fun _ =>
        UnitaryOperator.prodTensor (word.matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  dsimp only [Circuit.execute, interpret, preserveService, State.unitary, State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance)]
  exact mapClassical_function_eq _ rfl

-- The actual classical branch reads storage and applies the chosen granted word.
private lemma execute_selected {shape : CShape} (input : CInputRef ctx shape)
    (words : shape.Value → UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : State ctx Reference (services.HiddenState × H)) :
    (Circuit.branch input (fun value =>
      Circuit.unitary (allowAllocation := true) (operations := operations)
        (classicalOracles := services)
        (words value))).execute environment Reference state =
      (state.applyUnitary fun entry =>
        UnitaryOperator.prodTensor ((words (entry.1.read input)).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
            (entry.1, (entry.2.1, (entry.2.2,
              (⟨entry.1.read input, ()⟩ : (_ : shape.Value) × Unit))))) := by
  have body_eq (value : shape.Value)
      (part : State ctx Reference (services.HiddenState × H)) :
      ((Circuit.unitary (allowAllocation := true) (operations := operations)
        (classicalOracles := services)
        (words value)).execute environment Reference part).mapHistory
          (fun history => (history.1, (history.2.1,
            (⟨value, history.2.2⟩ : (_ : shape.Value) × Unit)))) =
        (part.applyUnitary fun _ =>
          UnitaryOperator.prodTensor ((words value).matrix environment.quantum)
            (1 : UnitaryOperator Reference)).mapClassical
            (fun entry => (entry.1, (entry.2.1, (entry.2.2,
              (⟨value, ()⟩ : (_ : shape.Value) × Unit))))) := by
    rw [execute_unitary]
    dsimp only [State.mapHistory]
    rw [mapClassical_comp_any (result := inferInstance)]
    exact mapClassical_function_eq _ rfl
  change runSelected state (fun entry => entry.1.read input)
    (fun value part =>
      ((Circuit.unitary (allowAllocation := true) (operations := operations)
        (classicalOracles := services)
        (words value)).execute environment Reference part).mapHistory
          (fun history => (history.1, (history.2.1,
            (⟨value, history.2.2⟩ : (_ : shape.Value) × Unit)))))
      (fun value part =>
        (State.mapHistory_mass
          ((Circuit.unitary (allowAllocation := true) (operations := operations)
            (classicalOracles := services)
            (words value)).execute environment Reference part)
          (fun history => (history.1, (history.2.1,
            (⟨value, history.2.2⟩ : (_ : shape.Value) × Unit))))).trans
          (Circuit.execute_mass
            (Circuit.unitary (allowAllocation := true) (operations := operations)
              (classicalOracles := services)
              (words value)) environment Reference part)) = _
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [runSelected_block_matrix]
  simp_rw [body_eq]
  exact congrArg (fun final => (final.block result).matrix)
    (selected_unitary state (fun entry => entry.1.read input)
      (fun value => UnitaryOperator.prodTensor ((words value).matrix environment.quantum)
        (1 : UnitaryOperator Reference))
      (fun entry value => (entry.1, (entry.2.1, (entry.2.2,
        (⟨value, ()⟩ : (_ : shape.Value) × Unit))))))

private lemma execute_native (application : operations.Application ctx)
    (state : State ctx Reference (services.HiddenState × H)) :
    (Circuit.classical (allowAllocation := true)
      (model := .quantum gates oracles operations services) application).execute
        environment Reference state =
      (kernelChoice state fun entry => operations.evaluate application.token
        (entry.1.read application.input)).mapClassical (fun entry =>
          (entry.1.1.write application.output entry.2,
            (entry.1.2.1, (entry.1.2.2, entry.2)))) := by
  dsimp only [Circuit.execute, interpret, preserveService, nativeStep, State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance)]
  exact mapClassical_function_eq _ rfl

/-- Sample a declared native result and execute the granted word selected by its stored value. -/
@[expose, implicit_reducible]
public def sampleUnitary (application : operations.Application ctx)
    (words : (operations.outputShape application.token).Value →
      UnitaryCircuit gates oracles ctx.quantumLayout) :
    Circuit (.quantum gates oracles operations services) ctx ctx :=
  .seq (.classical application)
    (.branch (.storage application.output.toCStorageRef) fun value => .unitary (words value))

open scoped Classical in
/-- Exact complete state of the actual sampler, store read, selected word and path. -/
public lemma sampleUnitary_execute (application : operations.Application ctx)
    (words : (operations.outputShape application.token).Value →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : State ctx Reference (services.HiddenState × H)) :
    (sampleUnitary (services := services) application words).execute environment Reference state =
      ((kernelChoice state fun entry => operations.evaluate application.token
        (entry.1.read application.input)).applyUnitary fun entry =>
          UnitaryOperator.prodTensor ((words entry.2).matrix environment.quantum)
            (1 : UnitaryOperator Reference)).mapClassical
            (fun entry => (entry.1.1.write application.output entry.2,
              (entry.1.2.1, (entry.1.2.2,
                (entry.2, (⟨entry.2, ()⟩ :
                  (_ : (operations.outputShape application.token).Value) × Unit)))))) := by
  change (((Circuit.branch (.storage application.output.toCStorageRef) fun value =>
      Circuit.unitary (allowAllocation := true) (operations := operations)
        (classicalOracles := services)
        (words value)).execute
        environment Reference ((Circuit.classical (allowAllocation := true)
          (model := .quantum gates oracles operations services)
          application).execute environment Reference state)).mapHistory fun history =>
            (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) = _
  rw [execute_selected, execute_native]
  rw [ExecutionState.applyUnitary_mapClassical]
  dsimp only [State.mapHistory]
  rw [mapClassical_comp_any (result := inferInstance),
    mapClassical_comp_any (result := inferInstance)]
  simp only [Function.comp_def, Store.read_write_same]
  exact mapClassical_function_eq _ rfl

private lemma sampleUnitary_eventTrace_eq (application : operations.Application ctx)
    (words : (operations.outputShape application.token).Value →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (sample selected : (operations.outputShape application.token).Value) :
    (sampleUnitary (services := services) application words).eventTrace (sample, ⟨selected, ()⟩) =
      [.classicalOperation (operations.coordinate application.token)] ++
        (words selected).eventTrace operations services := rfl

/-- Sampling contributes its native event before the selected word's actual events. -/
public lemma sampleUnitary_eventTrace (application : operations.Application ctx)
    (words : (operations.outputShape application.token).Value →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (sample selected : (operations.outputShape application.token).Value) :
    (sampleUnitary (services := services) application words).eventTrace (sample, ⟨selected, ()⟩) =
      [.classicalOperation (operations.coordinate application.token)] ++
        (words selected).eventTrace operations services :=
  sampleUnitary_eventTrace_eq application words sample selected

open scoped Classical in
/-- Each actual final record contains precisely the corresponding weighted input blocks. -/
public lemma sampleUnitary_block_matrix (application : operations.Application ctx)
    (words : (operations.outputShape application.token).Value →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : State ctx Reference (services.HiddenState × H))
    (result : Store ctx × (services.HiddenState ×
      (H × ((operations.outputShape application.token).Value ×
        (_ : (operations.outputShape application.token).Value) × Unit)))) :
    (((sampleUnitary (services := services) application words).execute
      environment Reference state).block
      result).matrix =
      ∑ entry : Store ctx × (services.HiddenState × H),
        ∑ outcome : (operations.outputShape application.token).Value,
          if (entry.1.write application.output outcome,
              (entry.2.1, (entry.2.2, (outcome, ⟨outcome, ()⟩)))) = result then
            (operations.evaluate application.token
              (entry.1.read application.input) outcome).toReal •
              (let operator := UnitaryOperator.prodTensor
                ((words outcome).matrix environment.quantum)
                (1 : UnitaryOperator Reference)
               (operator : HilbertOperator (ctx.register.prod Reference)) *
                 (state.block entry).matrix *
                   (operator : HilbertOperator (ctx.register.prod Reference)).conjTranspose)
          else 0 := by
  rw [sampleUnitary_execute]
  simp only [ExecutionState.mapClassical]
  rw [Fintype.sum_prod_type]
  simp only [kernelChoice_selected_block_matrix]

private lemma mapClassical_marginal {C D : Type} [Fintype C] [Fintype D]
    {R : Register} {decision : DecidableEq D} (state : ExecutionState C R) (f : C → D) :
    (@ExecutionState.mapClassical C D _ _ R decision state f).quantumMarginal =
      state.quantumMarginal :=
  @ExecutionState.mapClassical_quantumMarginal C D _ _ R decision state f

/-- The quantum/reference marginal is the complete weighted mixture of the executed words. -/
public lemma sampleUnitary_quantumMarginal_matrix (application : operations.Application ctx)
    (words : (operations.outputShape application.token).Value →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : State ctx Reference (services.HiddenState × H)) :
    ((sampleUnitary (services := services) application words).execute
      environment Reference state).quantumMarginal.matrix =
      ∑ entry : Store ctx × (services.HiddenState × H),
        ∑ outcome : (operations.outputShape application.token).Value,
          (operations.evaluate application.token
              (entry.1.read application.input) outcome).toReal •
            (let operator := UnitaryOperator.prodTensor ((words outcome).matrix environment.quantum)
              (1 : UnitaryOperator Reference)
             (operator : HilbertOperator (ctx.register.prod Reference)) *
               (state.block entry).matrix *
                 (operator : HilbertOperator (ctx.register.prod Reference)).conjTranspose) := by
  rw [sampleUnitary_execute, mapClassical_marginal,
    kernelChoice_selected_mixture_matrix]

end

end QuantumAlg.Execution
