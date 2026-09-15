/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Correctness

/-!
# Actual fixed-fuel LLL initialization

The original initialization order refreshes all six Gram entries, then clears
both phase latches with native XOR instructions. No prior latch or Gram value
is assumed. The represented full-rank basis and original capacity establish
the original initial invariant of the actual fixed-fuel driver.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Native XOR reads a latch twice and overwrites it with false. -/
def clearOp (output : CWriteRef ctx .bit) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (.storage output.toCStorageRef) (.storage output.toCStorageRef)) output

private theorem clear_frame (output : CWriteRef ctx .bit) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : output.key ∉ other.storageKeys) :
    (store.applyOp (clearOp output)).read other = store.read other :=
  Store.read_applyOp_of_not_mem_storageKeys store (clearOp output) other avoids

private theorem clear_read (output : CWriteRef ctx .bit) (store : Store ctx) :
    ((store.applyOp (clearOp output)).read (.storage output.toCStorageRef)).toBool = false := by
  simp only [Store.applyOp, clearOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval]
  change (Resource.BitOpcode.eval .xor (.product (store.read (.storage output.toCStorageRef))
    (store.read (.storage output.toCStorageRef)))).toBool = false
  cases store.read (.storage output.toCStorageRef) with
  | bit value => exact Bool.xor_self value

/-- Clear the original second-phase latch, then the original terminal latch. -/
def resetFirstInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (clearOp refs.machine.secondPhase)) (.classical (clearOp refs.machine.done))

/-- The actual chronological result of the two original XOR writes. -/
def resetFirstStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  (store.applyOp (clearOp refs.machine.secondPhase)).applyOp (clearOp refs.machine.done)

/-- The original two actual latch writes preserve all full-state histories and correlations. -/
theorem resetFirstInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (resetFirstInto refs).execute Reference state = state.mapClassical (fun entry =>
      (resetFirstStore refs entry.1, (entry.2, ((), ())))) := by
  simp only [resetFirstInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Every actual read outside the two original latch writes is retained exactly. -/
theorem resetFirstInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (secondPhase : refs.machine.secondPhase.key ∉ other.storageKeys)
    (done : refs.machine.done.key ∉ other.storageKeys) :
    (resetFirstStore refs store).read other = store.read other := by
  unfold resetFirstStore
  rw [clear_frame _ _ other done, clear_frame _ _ other secondPhase]

/-- Both actual latches encode the first phase after reset, regardless of their initial values. -/
theorem resetFirstInto_phase (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) : refs.machine.PhaseRepresents (resetFirstStore refs store) .first := by
  have different : refs.machine.done.key ≠ refs.machine.secondPhase.key := by
    intro equal
    have impossible : LatticeState.MachineCell.done = .secondPhase := separation.machine equal
    cases impossible
  constructor
  · change (((store.applyOp (clearOp refs.machine.secondPhase)).applyOp
      (clearOp refs.machine.done)).read (.storage refs.machine.secondPhase.toCStorageRef)).toBool
      = false
    rw [clear_frame _ _ _ (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
      different)]
    exact clear_read refs.machine.secondPhase store
  · exact clear_read refs.machine.done _

/-- Original machine separation retains the whole represented basis across the actual reset. -/
theorem resetFirstInto_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis) :
    LatticeMetricMachine.BasisRawRepresents (resetFirstStore refs store) refs.machine.basis basis :=
  basis_of_frames refs basis (fun cell => resetFirstInto_callerFrame refs store _
    (phase_avoids_basis refs separation .secondFail cell)
    (phase_avoids_basis refs separation .secondPass cell)) rep

private theorem latch_avoids_metric (refs : Refs ctx width) (latch : CWriteRef ctx .bit)
    (separate : ∀ cell, LatticeMetricMachine.metricCellKey refs.metric cell ∉
      (phaseInput latch).storageKeys) (cell : LatticeMetricMachine.MetricCell) :
    latch.key ∉ (.storage (LatticeMetricMachine.metricCellRef refs.metric cell).toCStorageRef :
      CInputRef ctx _).storageKeys := by
  have different : (LatticeMetricMachine.metricCellRef refs.metric cell).key ≠ latch.key := by
    simpa only [LatticeMetricMachine.metricCellKey, phaseInput, CInputRef.storageKeys,
      List.mem_singleton] using separate cell
  simpa only [CInputRef.storageKeys, List.mem_singleton] using different.symm

/-- The actual reset retains every original Gram output under the original phase frames. -/
theorem resetFirstInto_gram (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.GramRawRepresents store refs.metric basis) :
    LatticeMetricMachine.GramRawRepresents (resetFirstStore refs store) refs.metric basis := by
  intro entry
  rw [resetFirstInto_callerFrame refs store _
    (latch_avoids_metric refs refs.machine.secondPhase separation.secondPhaseMetric _)
    (latch_avoids_metric refs refs.machine.done separation.doneMetric _)]
  exact rep entry

/-- Original initialization order: refresh the actual Gram snapshot, then reset both latches. -/
def refreshResetInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeMetricMachine.refreshInto refs.machine.basis refs.metric) (resetFirstInto refs)

/-- Actual initialization store and its complete thirty-two-instruction path. -/
def refreshResetStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refreshResetInto refs).Path :=
  (resetFirstStore refs (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric store),
    (LatticeMetricMachine.refreshPath refs.machine.basis refs.metric, ((), ())))

/-- The exact original initial mathematical LLL state of a represented basis. -/
def initialState (basis : NumberTheory.IntegerBasis3) : NumberTheory.LLLState3 :=
  { basis := basis, phase := .first, steps := [] }

/-- Actual Gram refresh and reset compose on their chronological full execution states. -/
theorem refreshResetInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (refreshResetInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((refreshResetStep refs entry.1).1, (entry.2, (refreshResetStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeMetricMachine.refreshInto refs.machine.basis refs.metric) (resetFirstInto refs)
    (fun store => (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric store,
      LatticeMetricMachine.refreshPath refs.machine.basis refs.metric))
    (fun store => (resetFirstStore refs store, ((), ())))
    (LatticeMetricMachine.refreshInto_execute refs.machine.basis refs.metric)
    (by
      intro Reference History _ state
      refine (resetFirstInto_execute refs Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual initialization establishes the full invariant without prior Gram or bit values. -/
theorem refreshResetInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis)
    (fullRank : basis.FullRank)
    (capacity : Nat.size (256 * (NumberTheory.lllStateEnvelope3 basis + 1) ^ 8) + 1 ≤ width) :
    StoreInvariant refs basis (refreshResetStep refs store).1 (initialState basis) := by
  have refreshed := LatticeMetricMachine.refreshInto_correct refs.machine.basis refs.metric
    separation.metric store basis rep
  have bounded := NumberTheory.LLLState3.boundedFrom_initial basis fullRank
  refine ⟨resetFirstInto_basis refs separation _ basis refreshed.2,
    resetFirstInto_phase refs separation _, resetFirstInto_gram refs separation _ basis refreshed.1,
    bounded, capacity, LatticeStepBounds.stepFits_of_boundedFrom bounded capacity⟩

/-- Actual initialization retains the complete original fixed-fuel caller frame. -/
theorem refreshResetInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (refreshResetStep refs store).1.read other = store.read other := by
  change (resetFirstStore refs
    (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric store)).read other = _
  rw [resetFirstInto_callerFrame refs _ other separate.secondPhase separate.done]
  exact LatticeMetricMachine.refreshInto_callerFrame _ _ _ other
    (caller_avoids_metric refs other separate)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
