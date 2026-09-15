/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Primitives.ZReset.Semantics
import all QuantumAlg.Primitives.ZReset.Reference
import all QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ExecutionState
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

private theorem resultFresh (dimension : ℕ+) :
    (⟨1⟩ : StorageKey) ∉ (inputContext dimension).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The quantum system and the actual finite measurement-result cell remain live. -/
@[reducible] public def outputContext (dimension : ℕ+) : RuntimeCtx .quantum :=
  (inputContext dimension).addRetained ⟨1⟩ (.finite dimension) (resultFresh dimension)

private def wire (dimension : ℕ+) : Fin (outputContext dimension).systemCount :=
  ⟨0, by change 0 < 1; decide⟩

private def resultWrite (dimension : ℕ+) :
    CWriteRef (outputContext dimension) (.finite dimension) :=
  CWriteRef.retainedHead (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension)

private def resultRead (dimension : ℕ+) :
    CInputRef (outputContext dimension) (.finite dimension) :=
  .storage (resultWrite dimension).toCStorageRef

private def code (dimension : ℕ+) :
    Circuit (inputContext dimension) (outputContext dimension) :=
  .seq (.retain (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension))
    (ZReset.circuit (wire dimension) (resultWrite dimension))

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
**Resource budget.** One dimension-indexed Z event and an envelope containing
one of each possible declared correction coordinate. Each actual path uses
one correction, including zero. Resident and auxiliary limits each contain
one system at exactly the stated dimension and `Nat.clog 2 dimension`
classical bits. Unit-event depth is two. The supplied owned system contributes
to auxiliary space; no new quantum system is prepared.
**Success.** The actual result lies in its declared finite outcome domain with
probability one. The nonempty state requirement asserts the pure zero quantum
marginal after summing all actual outcomes. The full external reference is
restored as part of the mandatory empty borrowed-interface observation.
**Source.** Projective measurement and local-system projectors are
[dW19, qcnotes.tex:5409,5420]; unitary correction uses
[dW19, qcnotes.tex:5405], with the pure-state outer product at
[dW19, qcnotes.tex:5381]. The native resource limits follow this declared circuit.
-/
public def problem (dimension : ℕ+) :
    Problem .quantum (inputContext dimension) (outputContext dimension) (.finite dimension) where
  valid := fun _ => True
  accepts := fun _ result => result.toFin.val < dimension
  successLB := ⟨1, le_rfl⟩
  states := [stateRequirement dimension]
  resources :=
    { events := ZReset.eventEnvelope dimension
      resident := spaceBudget dimension
      auxiliary := spaceBudget dimension }
  depth := .quantum (fun _ => 1) 2

/-- Allocate the result cell, execute the actual reset, and expose both live entries. -/
public def algorithm (dimension : ℕ+) :
    Algorithm .quantum (inputContext dimension) (outputContext dimension) (.finite dimension) where
  run :=
    { code := code dimension
      output := Output.all (outputContext dimension) (.read (resultRead dimension)) }

private theorem input_resident (dimension : ℕ+) :
    (inputContext dimension).residentSpace = inputSpace dimension := by
  simp only [inputContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems query =>
      exact QuantumLayout.dimensionCount_uniform 1 dimension query Fin.val Fin.val_injective

private theorem input_auxiliary (dimension : ℕ+) :
    (inputContext dimension).auxiliarySpace = inputSpace dimension := by
  simp only [inputContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems query =>
      exact QuantumLayout.dimensionCount_uniform 1 dimension query Fin.val Fin.val_injective

private theorem output_resident (dimension : ℕ+) :
    (outputContext dimension).residentSpace = spaceBudget dimension := by
  rw [outputContext, RuntimeCtx.residentSpace_addRetained, input_resident]
  funext axis
  cases axis <;> simp [SpacePool.ofShape, inputSpace, spaceBudget]

private theorem output_auxiliary (dimension : ℕ+) :
    (outputContext dimension).auxiliarySpace = spaceBudget dimension := by
  rw [outputContext, RuntimeCtx.auxiliarySpace_addRetained, input_auxiliary]
  funext axis
  cases axis <;> simp [SpacePool.ofShape, inputSpace, spaceBudget]

private theorem actual_visitedContexts (dimension : ℕ+) (path : (code dimension).Path) :
    (code dimension).visitedContexts path =
      [inputContext dimension, outputContext dimension, outputContext dimension,
        outputContext dimension] := by
  exact congrArg
    (fun contexts : List (RuntimeCtx .quantum) =>
      [inputContext dimension, outputContext dimension] ++ contexts)
    (ZReset.zReset_visitedContexts (wire dimension) (resultWrite dimension) path.2)

private theorem actual_events (dimension : ℕ+) (path : (code dimension).Path) :
    (code dimension).resourcePool path ≤ ZReset.eventEnvelope dimension :=
  ZReset.zReset_resourcePool_le_envelope (wire dimension) (resultWrite dimension) path.2

private theorem actual_resident (dimension : ℕ+) (path : (code dimension).Path) :
    (code dimension).peakResidentSpace path ≤ spaceBudget dimension := by
  unfold Circuit.peakResidentSpace
  rw [actual_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, output_resident,
    SpacePool.max_zero, SpacePool.max_self, input_resident]
  apply SpacePool.max_le
  · intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems => exact le_rfl
  · exact le_rfl

private theorem actual_auxiliary (dimension : ℕ+) (path : (code dimension).Path) :
    (code dimension).peakAuxiliarySpace path ≤ spaceBudget dimension := by
  unfold Circuit.peakAuxiliarySpace
  rw [actual_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, output_auxiliary,
    SpacePool.max_zero, SpacePool.max_self, input_auxiliary]
  apply SpacePool.max_le
  · intro axis
    cases axis with
    | classicalBits => exact Nat.zero_le _
    | quantumSystems => exact le_rfl
  · exact le_rfl

private theorem actual_depth (dimension : ℕ+) (path : (code dimension).Path) :
    (code dimension).depth (fun _ => 1) path ≤ 2 := by
  exact le_of_eq ((Nat.zero_add _).trans
    (ZReset.zReset_unitDepth (wire dimension) (resultWrite dimension) path.2))

private def retainedState (dimension : ℕ+) (Reference : Register)
    (input : Execution.Input (inputContext dimension) Reference) :
    Execution.State (outputContext dimension) Reference
      (Execution.Store (inputContext dimension) × Unit) :=
  (Circuit.retain (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension)).execute
    Reference (input.state.mapClassical (fun store => (store, store)))

private theorem final_quantumMarginal (dimension : ℕ+) (Reference : Register)
    (input : Execution.Input (inputContext dimension) Reference) :
    ((algorithm dimension).run.finalState Reference input.state).quantumMarginal =
      ((ZReset.circuit (wire dimension) (resultWrite dimension)).execute Reference
        (retainedState dimension Reference input)).quantumMarginal := by
  let finished := (ZReset.circuit (wire dimension) (resultWrite dimension)).execute Reference
    (retainedState dimension Reference input)
  calc
    ((algorithm dimension).run.finalState Reference input.state).quantumMarginal =
        ((algorithm dimension).run.execute Reference input.state).quantumMarginal :=
      ExecutionState.mapClassical_quantumMarginal
        ((algorithm dimension).run.execute Reference input.state) Prod.fst
    _ = (finished.mapHistory
        (fun history => (history.1.1, (history.1.2, history.2)))).quantumMarginal :=
      congrArg ExecutionState.quantumMarginal
        (Circuit.execute_seq
          (.retain (inputContext dimension) ⟨1⟩ (.finite dimension) (resultFresh dimension))
          (ZReset.circuit (wire dimension) (resultWrite dimension))
          (input.state.mapClassical (fun store => (store, store))))
    _ = finished.quantumMarginal := Execution.State.mapHistory_quantumMarginal finished _

private theorem selected_row_ne_zero (dimension : ℕ+)
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

private theorem observed_row_zero (dimension : ℕ+) (Reference : Register)
    (input : Execution.Input (inputContext dimension) Reference)
    (row column : (outputContext dimension).quantumLayout.SelectedBasis Finset.univ)
    (different : row ≠ zeroSelected dimension) :
    (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ Reference
      ((algorithm dimension).run.finalState Reference input.state).quantumMarginal).matrix
        row column = 0 := by
  rw [DensityOperator.observeSelection_entry]
  apply Finset.sum_eq_zero
  intro reference _
  apply Finset.sum_eq_zero
  intro complement _
  rw [final_quantumMarginal]
  apply ZReset.zReset_execute_selected_zero
  change (outputContext dimension).quantumLayout.joinSelectedBasis Finset.univ row complement
    (⟨wire dimension, Finset.mem_univ _⟩ :
      QuantumLayout.SelectedPosition (Finset.univ : Finset (Fin
        (outputContext dimension).systemCount))).val ≠ _
  rw [QuantumLayout.joinSelectedBasis_selected_value]
  exact selected_row_ne_zero dimension row different

private theorem actual_state (dimension : ℕ+) {Reference : Register}
    (input : Execution.Input (inputContext dimension) Reference) :
    (stateRequirement dimension).Holds input
      ((algorithm dimension).run.finalState Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.pure (zeroTarget dimension)).Holds
        (DensityOperator.observeSelection (outputContext dimension).quantumLayout Finset.univ
          Reference ((((algorithm dimension).run.finalState Reference input.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block]
      apply StatePromise.statePromise_pureKet_of_row_support
      intro row different column
      exact observed_row_zero dimension Reference input row column different

private theorem restores_borrowed (dimension : ℕ+) {Reference : Register}
    (input : Execution.Input (inputContext dimension) Reference) :
    (algorithm dimension).run.RestoresBorrowed input := by
  change (code dimension).BorrowedRestored Reference
    (input.state.mapClassical (fun store => (store, store)))
    ((code dimension).execute Reference (input.state.mapClassical (fun store => (store, store))))
  unfold code
  refine Circuit.borrowedRestored_seq _ _ _ ?_ ?_
  · exact Circuit.borrowedRestored_retain ⟨1⟩ (.finite dimension) (resultFresh dimension) _
  · exact ZReset.zReset_borrowedRestored_noBorrowed rfl rfl
      (wire dimension) (resultWrite dimension) _

/-- The actual owned reset solves its independent finite-outcome, pure-zero,
and resource contract. -/
public theorem main (dimension : ℕ+) :
    ∃ candidate, Algorithm.Solves candidate (problem dimension) := by
  refine ⟨algorithm dimension, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro pair _supported
    exact pair.2.toFin.isLt
  · intro Reference input _valid requirement present
    have same : requirement = stateRequirement dimension := List.mem_singleton.mp present
    subst requirement
    exact actual_state dimension input
  · intro Reference input _valid
    exact restores_borrowed dimension input
  · intro _Reference _input _valid path _supported
    exact actual_events dimension path
  · intro _Reference _input _valid path _supported
    exact actual_resident dimension path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary dimension path
  · intro _Reference _input _valid path _supported
    exact actual_depth dimension path

end

end QuantumAlg.ZReset.Owned
