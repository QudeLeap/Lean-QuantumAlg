/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Primitives.ZReset.Resources
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Primitives.ZReset.Semantics
import all QuantumAlg.Primitives.ZReset.Reference
import all QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Complete reset of one supplied owned qudit

The endpoint allocates an actual finite classical result cell, measures the
owned system, and selects the declared cyclic correction from that cell.
Its complete Output retains both the quantum system and the classical result.
The quantum state requirement observes the actual final quantum marginal
and requires the pure zero basis state, independently of the measured value.

Local projective measurement [dW19, qcnotes.tex:5409,5420] and the selected
unitary [dW19, qcnotes.tex:5405] act on every external-reference extension of
every local input. A dimension-one system and its zero-bit finite result cell
remain actual live entries; dimension three counts one qutrit and no qubits.
-/

namespace QuantumAlg.ZReset.Owned

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def layout (dimension : ℕ+) : QuantumLayout 1 :=
  QuantumLayout.uniform 1 dimension Fin.val Fin.val_injective

/-- One supplied owned system of the stated dimension at physical identity zero. -/
@[reducible] public def inputContext (dimension : ℕ+) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ (layout dimension) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

public lemma resultFresh (dimension : ℕ+) :
    (⟨1⟩ : StorageKey) ∉ (inputContext dimension).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The quantum system and the actual finite measurement-result cell remain live. -/
@[reducible] public def outputContext (dimension : ℕ+) : RuntimeCtx .quantum :=
  (inputContext dimension).addRetained ⟨1⟩ (.finite dimension) (resultFresh dimension)

/-- The physical system retained at index zero after result-cell allocation. -/
public def wire (dimension : ℕ+) : Fin (outputContext dimension).systemCount :=
  ⟨0, by change 0 < 1; decide⟩

/-- The retained finite result cell written by the physical measurement. -/
public def resultWrite (dimension : ℕ+) :
    CWriteRef (outputContext dimension) (.finite dimension) :=
  CWriteRef.retainedHead (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension)

private def resultRead (dimension : ℕ+) :
    CInputRef (outputContext dimension) (.finite dimension) :=
  .storage (resultWrite dimension).toCStorageRef

/-- The exact cell allocation followed by the measured and corrected reset. -/
public def code {gates : GateModel} {oracles : OracleModel} (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension)) :
    Circuit (.quantum gates oracles) (inputContext dimension) (outputContext dimension) :=
  .seq (.retain (model := .quantum gates oracles)
    (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension))
    (ZReset.circuit (wire dimension) (resultWrite dimension) realizations)

/-- The same measured reset on the already retained live context. -/
public def retainedCode {gates : GateModel} {oracles : OracleModel} (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension)) :
    Circuit (.quantum gates oracles) (outputContext dimension) (outputContext dimension) :=
  ZReset.circuit (wire dimension) (resultWrite dimension) realizations

private def zeroSelected (dimension : ℕ+) :
    (outputContext dimension).quantumLayout.SelectedBasis Finset.univ :=
  (outputContext dimension).quantumLayout.restrictSelectedBasis Finset.univ
    (outputContext dimension).quantumLayout.zeroLabel

private def zeroTarget (dimension : ℕ+) : NormalizedVector
    ((outputContext dimension).quantumLayout.selectedRegister Finset.univ) :=
  NormalizedVector.ket (zeroSelected dimension)

private def stateRequirement (dimension : ℕ+) :
    StateRequirement (inputContext dimension) (outputContext dimension) :=
  .marginal Finset.univ .unit (fun _ _ => .pure (zeroTarget dimension))

private def retainedStateRequirement (dimension : ℕ+) :
    StateRequirement (outputContext dimension) (outputContext dimension) :=
  .marginal Finset.univ .unit (fun _ _ => .pure (zeroTarget dimension))

private def inputSpace (dimension : ℕ+) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems query => if dimension = query then 1 else 0

private def spaceBudget (dimension : ℕ+) : SpacePool .quantum
  | .classicalBits => CShape.bitWidth (.finite dimension)
  | .quantumSystems query => if dimension = query then 1 else 0

/-- Independently specified reset of a supplied owned finite-dimensional system.

**Input.** One owned system of any positive dimension, in any normalized local
state, allowing all classical mixtures and external-reference extensions.
**Output.** The same quantum system in its pure zero basis state and the actual
finite measurement result read from its retained classical cell. Both live
keys occur in the complete Output.
**Resource budget.** One dimension-indexed Z event and an independently supplied
budget that bounds every selected correction realization. Each actual path uses
one correction, including zero. Resident and auxiliary limits each contain
one system at exactly the stated dimension and `Nat.clog 2 dimension`
classical bits. Unit-event depth is at most one plus the supplied correction
depth bound. The supplied owned system contributes to auxiliary space; no new
quantum system is prepared.
**Success.** The actual result lies in its declared finite outcome domain with
probability one. The nonempty state requirement asserts the pure zero quantum
marginal after summing all actual outcomes. The full external reference is
restored as part of the mandatory empty borrowed-interface observation.
**Source.** Projective measurement and local-system projectors are
[dW19, qcnotes.tex:5409,5420]; unitary correction uses
[dW19, qcnotes.tex:5405], with the pure-state outer product at
[dW19, qcnotes.tex:5381]. The native resource limits follow this declared circuit.
-/
public def problem {gates : GateModel} {oracles : OracleModel} (dimension : ℕ+)
    (correctionBudget : ResourcePool (.quantum gates oracles))
    (correctionDepth : Nat) :
    Problem (.quantum gates oracles) (inputContext dimension)
      (outputContext dimension) (.finite dimension) where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ result => result.toFin.val < dimension
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [stateRequirement dimension]
  resources :=
    { events := ZReset.eventEnvelope dimension correctionBudget
      resident := spaceBudget dimension
      auxiliary := spaceBudget dimension }
  quantumTimeLimit := 1 + correctionDepth

/-- Allocate the result cell, execute the actual reset, and expose both live entries. -/
public def algorithm {gates : GateModel} {oracles : OracleModel} (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension)) :
    Algorithm (.quantum gates oracles) (inputContext dimension)
      (outputContext dimension) (.finite dimension) where
  run :=
    { code := code dimension realizations
      output := Output.all (outputContext dimension) (.read (resultRead dimension)) }

/-- Independently specified reset using an already retained result cell.

**Input.** One owned system of any positive dimension and its retained finite
result cell, with arbitrary joint input and external-reference correlations.
**Output.** The same system in the pure zero basis state and its newly measured
finite result, with both original live entries retained.
**Resource budget.** One Z measurement plus the independently supplied correction
event and depth bounds; one system and the existing finite classical cell.
**Success.** The result is in its declared domain with probability one and the
nonempty state requirement asserts actual pure-zero output.
**Source.** Projective measurement [dW19, qcnotes.tex:5409,5420] and unitary
correction [dW19, qcnotes.tex:5405].
-/
public def retainedProblem {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+) (correctionBudget : ResourcePool (.quantum gates oracles))
    (correctionDepth : Nat) :
    Problem (.quantum gates oracles) (outputContext dimension)
      (outputContext dimension) (.finite dimension) where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ result => result.toFin.val < dimension
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [retainedStateRequirement dimension]
  resources :=
    { events := ZReset.eventEnvelope dimension correctionBudget
      resident := spaceBudget dimension
      auxiliary := spaceBudget dimension }
  quantumTimeLimit := 1 + correctionDepth

/-- Reset and overwrite the actual previously allocated result cell. -/
public def retainedAlgorithm {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension)) :
    Algorithm (.quantum gates oracles) (outputContext dimension)
      (outputContext dimension) (.finite dimension) where
  run :=
    { code := retainedCode dimension realizations
      output := Output.all (outputContext dimension) (.read (resultRead dimension)) }

private lemma input_resident (dimension : ℕ+) :
    (inputContext dimension).residentSpace = inputSpace dimension := by
  simp only [inputContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems query =>
      exact QuantumLayout.dimensionCount_uniform 1 dimension query Fin.val Fin.val_injective

private lemma input_auxiliary (dimension : ℕ+) :
    (inputContext dimension).auxiliarySpace = inputSpace dimension := by
  simp only [inputContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems query =>
      exact QuantumLayout.dimensionCount_uniform 1 dimension query Fin.val Fin.val_injective

private lemma output_resident (dimension : ℕ+) :
    (outputContext dimension).residentSpace = spaceBudget dimension := by
  rw [outputContext, RuntimeCtx.residentSpace_addRetained, input_resident]
  funext axis
  cases axis <;> simp [SpacePool.ofShape, inputSpace, spaceBudget]

private lemma output_auxiliary (dimension : ℕ+) :
    (outputContext dimension).auxiliarySpace = spaceBudget dimension := by
  rw [outputContext, RuntimeCtx.auxiliarySpace_addRetained, input_auxiliary]
  funext axis
  cases axis <;> simp [SpacePool.ofShape, inputSpace, spaceBudget]

private lemma actual_visitedContexts {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (path : (code dimension realizations).Path) :
    (code dimension realizations).visitedContexts path =
      [inputContext dimension, outputContext dimension, outputContext dimension,
        outputContext dimension] := by
  exact congrArg
    (fun contexts : List (RuntimeCtx .quantum) =>
      [inputContext dimension, outputContext dimension] ++ contexts)
    (ZReset.zReset_visitedContexts (wire dimension) (resultWrite dimension)
      realizations path.2)

private lemma actual_events {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (correctionBudget : ResourcePool (.quantum gates oracles))
    (bounded : ∀ amount,
      ResourcePool.ofList (realizations amount).circuit.eventTrace ≤ correctionBudget)
    (path : (code dimension realizations).Path) :
    (code dimension realizations).resourcePool path ≤
      ZReset.eventEnvelope dimension correctionBudget :=
  ZReset.zReset_resourcePool_le_envelope (wire dimension) (resultWrite dimension)
    realizations correctionBudget bounded path.2

private lemma actual_resident {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (path : (code dimension realizations).Path) :
    (code dimension realizations).peakResidentSpace path ≤ spaceBudget dimension := by
  unfold Circuit.peakResidentSpace
  rw [actual_visitedContexts dimension realizations]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, output_resident,
    SpacePool.max_zero, SpacePool.max_self, input_resident]
  apply SpacePool.max_le
  · intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems => exact le_rfl
  · exact le_rfl

private lemma actual_auxiliary {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (path : (code dimension realizations).Path) :
    (code dimension realizations).peakAuxiliarySpace path ≤ spaceBudget dimension := by
  unfold Circuit.peakAuxiliarySpace
  rw [actual_visitedContexts dimension realizations]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, output_auxiliary,
    SpacePool.max_zero, SpacePool.max_self, input_auxiliary]
  apply SpacePool.max_le
  · intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems => exact le_rfl
  · exact le_rfl

private lemma actual_depth {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (correctionDepth : Nat)
    (bounded : ∀ amount,
      (realizations amount).circuit.evaluatedEventDepth (fun _ => 1) ≤
        correctionDepth)
    (path : (code dimension realizations).Path) :
    (code dimension realizations).depth (fun _ => 1) path ≤ 1 + correctionDepth := by
  have resetBound := ZReset.zReset_depth_le_envelope (wire dimension)
    (resultWrite dimension) realizations (fun _ => 1) correctionDepth bounded path.2
  change 0 + (ZReset.circuit (wire dimension) (resultWrite dimension)
    realizations).depth (fun _ => 1) path.2 ≤ 1 + correctionDepth
  simpa only [Nat.zero_add, ZReset.depthEnvelope] using resetBound

private def retainedState {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+) (Reference : Register)
    (input : Execution.OracleInput
      (ExecutionModel.quantum gates oracles).classicalOracles
      (inputContext dimension) Reference) :
    Execution.State (outputContext dimension) Reference
      ((ExecutionModel.quantum gates oracles).HiddenState ×
        (Execution.Store (inputContext dimension) × Unit)) :=
  (Circuit.retain (model := .quantum gates oracles)
    (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension)).execute environment
    Reference (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))

private lemma final_quantumMarginal {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (Reference : Register)
    (input : Execution.OracleInput
      (ExecutionModel.quantum gates oracles).classicalOracles
      (inputContext dimension) Reference) :
    ((algorithm dimension realizations).run.finalState
      environment Reference input.state).quantumMarginal =
      ((ZReset.circuit (wire dimension) (resultWrite dimension) realizations).execute
        environment Reference
        (retainedState
          (environment := environment) dimension Reference input)).quantumMarginal := by
  let finished := (ZReset.circuit (wire dimension) (resultWrite dimension)
    realizations).execute environment Reference
    (retainedState (environment := environment) dimension Reference input)
  calc
    ((algorithm dimension realizations).run.finalState
      environment Reference input.state).quantumMarginal =
        ((algorithm dimension realizations).run.execute
          environment Reference input.state).quantumMarginal :=
      ExecutionState.mapClassical_quantumMarginal
        ((algorithm dimension realizations).run.execute environment Reference input.state) Prod.fst
    _ = (finished.mapHistory
        (fun history =>
          (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))).quantumMarginal :=
      congrArg ExecutionState.quantumMarginal
        (Circuit.execute_seq (environment := environment)
          (.retain (model := .quantum gates oracles)
            (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension))
          (ZReset.circuit (wire dimension) (resultWrite dimension) realizations)
          (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    _ = finished.quantumMarginal := Execution.State.mapHistory_quantumMarginal finished _

private lemma selected_row_ne_zero (dimension : ℕ+)
    (row : (outputContext dimension).quantumLayout.SelectedBasis Finset.univ)
    (different : row ≠ zeroSelected dimension) :
    row ⟨wire dimension, Finset.mem_univ _⟩ ≠
      (outputContext dimension).quantumLayout.zeroLabel (wire dimension) := by
  intro atZero
  apply different
  funext index
  have sameWire : index.val = wire dimension := by
    apply Fin.ext
    have bounded := index.val.isLt
    change index.val.val < 1 at bounded
    change index.val.val = 0
    omega
  have sameIndex : index = ⟨wire dimension, Finset.mem_univ _⟩ := Subtype.ext sameWire
  subst index
  exact atZero

private lemma observed_row_zero {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (Reference : Register)
    (input : Execution.OracleInput
      (ExecutionModel.quantum gates oracles).classicalOracles
      (inputContext dimension) Reference)
    (row column : (outputContext dimension).quantumLayout.SelectedBasis Finset.univ)
    (different : row ≠ zeroSelected dimension) :
    (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ Reference
      ((algorithm dimension realizations).run.finalState environment Reference
        input.state).quantumMarginal).matrix
        row column = 0 := by
  rw [DensityOperator.observeSelection_entry]
  apply Finset.sum_eq_zero
  intro reference _
  apply Finset.sum_eq_zero
  intro complement _
  rw [final_quantumMarginal dimension realizations]
  apply ZReset.zReset_execute_selected_zero (realizations := realizations)
  change (outputContext dimension).quantumLayout.joinSelectedBasis Finset.univ row complement
    (⟨wire dimension, Finset.mem_univ _⟩ :
      QuantumLayout.SelectedPosition (Finset.univ : Finset (Fin
        (outputContext dimension).systemCount))).val ≠ _
  rw [QuantumLayout.joinSelectedBasis_selected_value]
  exact selected_row_ne_zero dimension row different

private lemma actual_state {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    {Reference : Register}
    (input : Execution.OracleInput
      (ExecutionModel.quantum gates oracles).classicalOracles
      (inputContext dimension) Reference) :
    (stateRequirement dimension).Holds input.caller
      ((algorithm dimension realizations).run.finalState environment Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.pure (zeroTarget dimension)).Holds
        (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ
          Reference ((((algorithm dimension realizations).run.finalState environment Reference
            input.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block]
      apply StatePromise.statePromise_pureKet_of_row_support
      intro row different column
      exact observed_row_zero dimension realizations Reference input row column different

private lemma runRestoresBorrowed_of_history
    {model : ExecutionModel} {environment : model.Environment}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model pre post shape) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (restored : run.code.BorrowedRestored Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      (run.execute environment Reference input.state)) :
    run.RestoresBorrowed environment input := by
  unfold Circuit.BorrowedRestored at restored
  unfold AlgorithmRun.RestoresBorrowed Circuit.BorrowedRestored
  apply restored.trans
  convert Execution.observeBorrowed_mapClassical input.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl) using 1
  exact congrArg (Execution.observeBorrowed Reference)
    (ExecutionState.executionState_mapClassical_congr_decision
      input.state _ _ (fun _ => rfl) _ _)

private lemma restores_borrowed {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    {Reference : Register}
    (input : Execution.OracleInput
      (ExecutionModel.quantum gates oracles).classicalOracles
      (inputContext dimension) Reference) :
    (algorithm dimension realizations).run.RestoresBorrowed environment input := by
  apply runRestoresBorrowed_of_history (algorithm dimension realizations).run input
  dsimp only [AlgorithmRun.execute, algorithm]
  unfold code
  apply Circuit.borrowedRestored_seq
    (first := .retain (model := .quantum gates oracles)
      (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension))
    (second := ZReset.circuit (wire dimension) (resultWrite dimension) realizations)
    (state := input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
  · exact Circuit.borrowedRestored_retain environment ⟨1⟩ (.finite dimension)
      (resultFresh dimension) _
  · exact ZReset.zReset_borrowedRestored_noBorrowed rfl rfl
      (wire dimension) (resultWrite dimension) realizations _

/-- The actual reset restores the borrowed interface for every input state,
including inputs outside any separately stated problem predicate. -/
public lemma code_borrowedRestored {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State (inputContext dimension) Reference
      ((ExecutionModel.quantum gates oracles).HiddenState × H)) :
    (code dimension realizations).BorrowedRestored Reference state
      ((code dimension realizations).execute environment Reference state) := by
  unfold code
  apply Circuit.borrowedRestored_seq
    (first := .retain (model := .quantum gates oracles)
      (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension))
    (second := ZReset.circuit (wire dimension) (resultWrite dimension) realizations)
    (state := state)
  · exact Circuit.borrowedRestored_retain environment ⟨1⟩ (.finite dimension)
      (resultFresh dimension) _
  · exact ZReset.zReset_borrowedRestored_noBorrowed rfl rfl
      (wire dimension) (resultWrite dimension) realizations _

/-- The stated reset algorithm itself solves the independent finite-outcome,
pure-zero, and resource contract. -/
public lemma algorithm_solves {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (correctionBudget : ResourcePool (.quantum gates oracles))
    (boundedEvents : ∀ amount,
      ResourcePool.ofList (realizations amount).circuit.eventTrace ≤ correctionBudget)
    (correctionDepth : Nat)
    (boundedDepth : ∀ amount,
      (realizations amount).circuit.evaluatedEventDepth (fun _ => 1) ≤ correctionDepth) :
    Algorithm.Solves (algorithm dimension realizations)
      (problem dimension correctionBudget correctionDepth) := by
  constructor
  · intro environment _witness Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro pair _supported
    exact pair.2.toFin.isLt
  · intro environment _witness Reference input _valid _initialized requirement present
    have same : requirement = stateRequirement dimension := List.mem_singleton.mp present
    subst requirement
    exact actual_state dimension realizations input
  · intro environment _witness Reference input _valid _initialized
    exact restores_borrowed dimension realizations input
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_events dimension realizations correctionBudget boundedEvents path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_resident dimension realizations path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_auxiliary dimension realizations path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact actual_depth dimension realizations correctionDepth boundedDepth path

/-- The actual owned reset solves its independent finite-outcome, pure-zero,
and resource contract. -/
public theorem main {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (correctionBudget : ResourcePool (.quantum gates oracles))
    (boundedEvents : ∀ amount,
      ResourcePool.ofList (realizations amount).circuit.eventTrace ≤ correctionBudget)
    (correctionDepth : Nat)
    (boundedDepth : ∀ amount,
      (realizations amount).circuit.evaluatedEventDepth (fun _ => 1) ≤ correctionDepth) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate
      (problem dimension correctionBudget correctionDepth) :=
  ⟨algorithm dimension realizations,
    algorithm_solves dimension realizations correctionBudget boundedEvents
      correctionDepth boundedDepth⟩

private lemma output_borrowedSelection_empty (dimension : ℕ+) :
    (outputContext dimension).borrowedSelection = ∅ := by
  ext index
  constructor
  · intro present
    have borrowed := ((outputContext dimension).mem_borrowedSelection index).mp present
    have none : (outputContext dimension).borrowedQuantumWires = [] := rfl
    simp only [none, List.not_mem_nil] at borrowed
  · intro absent
    simp at absent

private lemma code_block_selected_zero {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State (inputContext dimension) Reference
      ((ExecutionModel.quantum gates oracles).HiddenState × H))
    (result : Execution.Store (outputContext dimension) ×
      ((ExecutionModel.quantum gates oracles).HiddenState ×
        (H × (code dimension realizations).Path)))
    (left right : (outputContext dimension).quantumLayout.Basis)
    (leftRef rightRef : Reference.Index)
    (nonzero : left (wire dimension) ≠
      (outputContext dimension).quantumLayout.zeroLabel (wire dimension)) :
    (((code dimension realizations).execute environment Reference state).block result).matrix
      (left, leftRef) (right, rightRef) = 0 := by
  unfold code at result ⊢
  rw [Circuit.execute_seq]
  simp only [Execution.State.mapHistory, ExecutionState.mapClassical_block_matrix,
    Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro record _
  split_ifs
  · exact ZReset.zReset_execute_block_selected_zero (wire dimension)
      (resultWrite dimension) realizations _ record left right leftRef rightRef nonzero
  · rfl

private lemma code_block_observed_row_zero {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State (inputContext dimension) Reference
      ((ExecutionModel.quantum gates oracles).HiddenState × H))
    (result : Execution.Store (outputContext dimension) ×
      ((ExecutionModel.quantum gates oracles).HiddenState ×
        (H × (code dimension realizations).Path)))
    (row column : (outputContext dimension).quantumLayout.SelectedBasis Finset.univ)
    (different : row ≠ zeroSelected dimension) :
    (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ
      Reference (((code dimension realizations).execute
        environment Reference state).block result)).matrix
        row column = 0 := by
  rw [DensityOperator.observeSelection_entry]
  apply Finset.sum_eq_zero
  intro reference _
  apply Finset.sum_eq_zero
  intro complement _
  apply code_block_selected_zero dimension realizations Reference state result
  change (outputContext dimension).quantumLayout.joinSelectedBasis Finset.univ row complement
    (⟨wire dimension, Finset.mem_univ _⟩ :
      QuantumLayout.SelectedPosition (Finset.univ : Finset (Fin
        (outputContext dimension).systemCount))).val ≠ _
  rw [QuantumLayout.joinSelectedBasis_selected_value]
  exact selected_row_ne_zero dimension row different

private lemma reset_observed_zero {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State (outputContext dimension) Reference
      ((ExecutionModel.quantum gates oracles).HiddenState × H)) :
    (StatePromise.pure (zeroTarget dimension)).Holds
      (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ
        Reference
        ((retainedCode dimension realizations).execute
          environment Reference state).quantumMarginal) := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.observeSelection_entry]
  apply Finset.sum_eq_zero
  intro reference _
  apply Finset.sum_eq_zero
  intro complement _
  apply ZReset.zReset_execute_selected_zero (realizations := realizations)
  change (outputContext dimension).quantumLayout.joinSelectedBasis Finset.univ row complement
    (⟨wire dimension, Finset.mem_univ _⟩ :
      QuantumLayout.SelectedPosition (Finset.univ : Finset (Fin
        (outputContext dimension).systemCount))).val ≠ _
  rw [QuantumLayout.joinSelectedBasis_selected_value]
  exact selected_row_ne_zero dimension row different

private lemma retained_actual_state {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    {Reference : Register}
    (input : Execution.OracleInput
      (ExecutionModel.quantum gates oracles).classicalOracles
      (outputContext dimension) Reference) :
    (retainedStateRequirement dimension).Holds input.caller
      ((retainedAlgorithm dimension realizations).run.finalState
        environment Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.pure (zeroTarget dimension)).Holds
        (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ
          Reference ((((retainedAlgorithm dimension realizations).run.finalState
            environment Reference
            input.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block,
        AlgorithmRun.finalState_quantumMarginal]
      exact reset_observed_zero dimension realizations Reference _

private lemma retained_actual_resident {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (path : (retainedCode dimension realizations).Path) :
    (retainedCode dimension realizations).peakResidentSpace path ≤ spaceBudget dimension := by
  exact le_of_eq ((ZReset.zReset_peakResidentSpace (ctx := outputContext dimension)
    (wire dimension) (resultWrite dimension) realizations path).trans (output_resident dimension))

private lemma retained_actual_auxiliary {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (path : (retainedCode dimension realizations).Path) :
    (retainedCode dimension realizations).peakAuxiliarySpace path ≤ spaceBudget dimension := by
  exact le_of_eq ((ZReset.zReset_peakAuxiliarySpace (ctx := outputContext dimension)
    (wire dimension) (resultWrite dimension) realizations path).trans (output_auxiliary dimension))

/-- The retained reset solves its own independent problem on every admitted input. -/
public lemma retainedAlgorithm_solves {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (correctionBudget : ResourcePool (.quantum gates oracles))
    (boundedEvents : ∀ amount,
      ResourcePool.ofList (realizations amount).circuit.eventTrace ≤ correctionBudget)
    (correctionDepth : Nat)
    (boundedDepth : ∀ amount,
      (realizations amount).circuit.evaluatedEventDepth (fun _ => 1) ≤ correctionDepth) :
    Algorithm.Solves (retainedAlgorithm dimension realizations)
      (retainedProblem dimension correctionBudget correctionDepth) := by
  constructor
  · intro environment _witness Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro pair _supported
    exact pair.2.toFin.isLt
  · intro environment _witness Reference input _valid _initialized requirement present
    have same : requirement = retainedStateRequirement dimension := List.mem_singleton.mp present
    subst requirement
    exact retained_actual_state dimension realizations input
  · intro environment _witness Reference input _valid _initialized
    apply runRestoresBorrowed_of_history (retainedAlgorithm dimension realizations).run input
    exact ZReset.zReset_borrowedRestored_noBorrowed rfl rfl
      (wire dimension) (resultWrite dimension) realizations _
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact ZReset.zReset_resourcePool_le_envelope (wire dimension) (resultWrite dimension)
      realizations correctionBudget boundedEvents path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact retained_actual_resident dimension realizations path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact retained_actual_auxiliary dimension realizations path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact ZReset.zReset_depth_le_envelope (wire dimension) (resultWrite dimension)
      realizations (fun _ => 1) correctionDepth boundedDepth path

/-- Actual measurement and reinitialization provide physical cleanup.
The caller's independent cycle plan separately determines whether to cut here. -/
public lemma restartCleanup {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles).Environment}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension)) :
    Circuit.RestartCleanup (code dimension realizations) environment := by
  refine { measured := ?_
           restores := ?_
           reinitialized := ?_ }
  · intro path
    unfold code at path
    refine ⟨dimension, ?_⟩
    change Resource.Event.measurement (model := .quantum gates oracles) dimension ∈
      (Circuit.retain (model := .quantum gates oracles)
        (inputContext dimension) ⟨1⟩ (.finite dimension)
          (resultFresh dimension)).eventTrace path.1 ++
      (ZReset.circuit (wire dimension) (resultWrite dimension) realizations).eventTrace path.2
    apply List.mem_append.mpr
    right
    have actual := ZReset.zReset_eventTrace (ctx := outputContext dimension)
      (wire dimension) (resultWrite dimension) realizations path.2
    rw [actual]
    left
  · intro Reference H _ state
    exact code_borrowedRestored dimension realizations Reference state
  · refine ⟨(outputContext dimension).quantumLayout.restrictSelectedBasis
      (outputContext dimension).borrowedSelectionᶜ
      (outputContext dimension).quantumLayout.zeroLabel, ?_⟩
    intro Reference H _ state label
    have ownedAll : (outputContext dimension).borrowedSelectionᶜ = Finset.univ := by
      rw [output_borrowedSelection_empty]
      simp
    rw [ownedAll]
    apply StatePromise.statePromise_pureKet_of_row_support
    intro row different column
    exact code_block_observed_row_zero dimension realizations Reference state label
      row column different

/-- Independently specified final outcome and whole-run budget of two resets.

**Input.** One owned system of any positive dimension in an arbitrary joint state.
**Output.** The same pure-zero system and the second reset's retained finite result.
**Resource budget.** Two complete measurement-and-correction envelopes and their
summed dependency depths; the single system and result cell stay live throughout.
**Success.** The finite-domain result and final pure-zero state hold with certainty.
**Source.** Projective measurement [dW19, qcnotes.tex:5409,5420] and unitary
correction [dW19, qcnotes.tex:5405], applied twice in chronological order.
-/
public def repeatedProblem {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+) (correctionBudget : ResourcePool (.quantum gates oracles))
    (correctionDepth : Nat) :
    Problem (.quantum gates oracles) (inputContext dimension)
      (outputContext dimension) (.finite dimension) :=
  { problem dimension correctionBudget correctionDepth with
    resources :=
      { events := ZReset.eventEnvelope dimension correctionBudget +
          ZReset.eventEnvelope dimension correctionBudget
        resident := spaceBudget dimension
        auxiliary := spaceBudget dimension }
    quantumTimeLimit := (1 + correctionDepth) + (1 + correctionDepth) }

/-- Execute both complete resets and read the actual final result cell. -/
public def repeatedAlgorithm {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension)) :
    Algorithm (.quantum gates oracles) (inputContext dimension)
      (outputContext dimension) (.finite dimension) where
  run :=
    { code := .seq (code dimension realizations) (retainedCode dimension realizations)
      output := Output.all (outputContext dimension) (.read (resultRead dimension)) }

/-- The repeated actual execution solves the independently stated whole-run problem. -/
public lemma repeatedAlgorithm_solves {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (realizations : QuditShift.Realizations gates oracles
      (outputContext dimension).quantumLayout (wire dimension))
    (correctionBudget : ResourcePool (.quantum gates oracles))
    (boundedEvents : ∀ amount,
      ResourcePool.ofList (realizations amount).circuit.eventTrace ≤ correctionBudget)
    (correctionDepth : Nat)
    (boundedDepth : ∀ amount,
      (realizations amount).circuit.evaluatedEventDepth (fun _ => 1) ≤ correctionDepth) :
    Algorithm.Solves (repeatedAlgorithm dimension realizations)
      (repeatedProblem dimension correctionBudget correctionDepth) := by
  constructor
  · intro environment _witness Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro pair _supported
    exact pair.2.toFin.isLt
  · intro environment _witness Reference input _valid _initialized requirement present
    have same : requirement = stateRequirement dimension := List.mem_singleton.mp present
    subst requirement
    intro value
    cases value with
    | unit =>
        change (StatePromise.pure (zeroTarget dimension)).Holds
          (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ
            Reference ((((repeatedAlgorithm dimension realizations).run.finalState
              environment Reference
              input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
        rw [ExecutionState.executionState_mapClassical_const_block,
          AlgorithmRun.finalState_quantumMarginal]
        change (StatePromise.pure (zeroTarget dimension)).Holds
          (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ
            Reference ((Circuit.seq (code dimension realizations)
              (retainedCode dimension realizations)).execute environment Reference
                (input.state.mapClassical
                  (fun value => (value.1, (value.2, value.1))))).quantumMarginal)
        rw [Circuit.execute_seq, Execution.State.mapHistory_quantumMarginal]
        exact reset_observed_zero dimension realizations Reference _
  · intro environment _witness Reference input _valid _initialized
    apply runRestoresBorrowed_of_history (repeatedAlgorithm dimension realizations).run input
    dsimp only [AlgorithmRun.execute, repeatedAlgorithm]
    apply Circuit.borrowedRestored_seq
      (first := code dimension realizations) (second := retainedCode dimension realizations)
    · exact code_borrowedRestored dimension realizations Reference _
    · exact ZReset.zReset_borrowedRestored_noBorrowed rfl rfl
        (wire dimension) (resultWrite dimension) realizations _
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    change ResourcePool.ofList
      ((code dimension realizations).eventTrace path.1 ++
        (retainedCode dimension realizations).eventTrace path.2) ≤
      ZReset.eventEnvelope dimension correctionBudget +
        ZReset.eventEnvelope dimension correctionBudget
    rw [ResourcePool.ofList_append]
    exact add_le_add (actual_events dimension realizations correctionBudget boundedEvents path.1)
      (ZReset.zReset_resourcePool_le_envelope (wire dimension) (resultWrite dimension)
        realizations correctionBudget boundedEvents path.2)
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    change (Circuit.seq (code dimension realizations)
      (retainedCode dimension realizations)).peakResidentSpace path ≤ spaceBudget dimension
    exact (Circuit.peakResidentSpace_seq (code dimension realizations)
      (retainedCode dimension realizations) path).trans_le
        (SpacePool.max_le (actual_resident dimension realizations path.1)
          (retained_actual_resident dimension realizations path.2))
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    change (Circuit.seq (code dimension realizations)
      (retainedCode dimension realizations)).peakAuxiliarySpace path ≤ spaceBudget dimension
    exact (Circuit.peakAuxiliarySpace_seq (code dimension realizations)
      (retainedCode dimension realizations) path).trans_le
        (SpacePool.max_le (actual_auxiliary dimension realizations path.1)
          (retained_actual_auxiliary dimension realizations path.2))
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    change (code dimension realizations).depth (fun _ => 1) path.1 +
      (retainedCode dimension realizations).depth (fun _ => 1) path.2 ≤
      (1 + correctionDepth) + (1 + correctionDepth)
    exact Nat.add_le_add (actual_depth dimension realizations correctionDepth boundedDepth path.1)
      (ZReset.zReset_depth_le_envelope (wire dimension) (resultWrite dimension)
        realizations (fun _ => 1) correctionDepth boundedDepth path.2)

end

end QuantumAlg.ZReset.Owned
