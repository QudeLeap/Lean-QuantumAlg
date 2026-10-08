/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Coordinates
import all QuantumAlg.Core.Execution.Circuit.Reference
import all QuantumAlg.Core.Execution.Circuit.Reference.History
import all QuantumAlg.Core.Execution.Input.Oracle.Empty
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Recorded

/-!
# Actual output probabilities with the prescribed public inputs

The output is the original vector of measured finite cells, read through
its actual structural reference in the complete final context. Exact frame
coordinates retain every final block and every external-reference matrix.
Summing the other recorded values therefore leaves this output probability
unchanged; it does not assert equality for arbitrary frame-dependent events.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] storeFintype Nat.size orderWidth

private theorem splitState_read_mass {ctx framed : RuntimeCtx .quantum}
    (separate : RuntimeCtx.StorageDisjoint ctx framed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion framed separate) Reference History)
    {shape : CShape} (input : CInputRef ctx shape) (value : shape.Value) :
    (((splitState ctx framed separate state).mapClassical
      (fun record => record.1.read input)).block value).mass =
    ((state.mapClassical (fun record => record.1.read (inputLeft separate input))).block
      value).mass := by
  unfold splitState
  rw [ExecutionState.coordinate_reindex_mapClassical, ExecutionState.reindex_block_mass,
    ExecutionState.executionState_mapClassical_comp]
  have reads :
      (fun record : Store ctx × (Store framed × History) => record.1.read input) ∘
        recordEquiv ctx framed separate History =
      (fun record : Store (ctx.disjointUnion framed separate) × History =>
        record.1.read (inputLeft separate input)) := by
    funext record
    change (split separate record.1).1.read input = record.1.read (inputLeft separate input)
    have original := contextUnion_read_join_left separate
      (split separate record.1).1 (split separate record.1).2 input
    rw [join_split_store] at original
    exact original.symm
  rw [reads]

private theorem splitServiceState_read_mass {ctx framed : RuntimeCtx .quantum}
    (separate : RuntimeCtx.StorageDisjoint ctx framed)
    {Reference : Register} {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State (ctx.disjointUnion framed separate) Reference (Hidden × History))
    {shape : CShape} (input : CInputRef ctx shape) (value : shape.Value) :
    (((splitServiceState ctx framed separate state).mapClassical
      (fun record => record.1.read input)).block value).mass =
    ((state.mapClassical (fun record => record.1.read (inputLeft separate input))).block
      value).mass := by
  unfold splitServiceState State.mapHistory
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact splitState_read_mass separate state input value

private theorem splitServiceState_attach_empty {ctx framed : RuntimeCtx .quantum}
    (separate : RuntimeCtx.StorageDisjoint ctx framed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion framed separate) Reference History) :
    splitServiceState ctx framed separate (state.mapHistory (fun history => ((), history))) =
      (splitState ctx framed separate state).mapHistory (fun history => ((), history)) := by
  unfold splitServiceState
  rw [contextUnion_splitState_mapHistory, State.mapHistory_comp]
  rfl

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Original output-cell probabilities are unchanged by the exact complete frame coordinates. -/
theorem exponentRun_outputProbability_split (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} (input : Input (before E (orderWidth problem)) Reference)
    (value : (CShape.fixedVector (2 * orderWidth problem) (.finite 2)).Value) :
    (exponentRun E fieldTail odd problem points).outputDistribution
      (OracleInput.withEmptyService input) value =
      ENNReal.ofReal
        ((((splitServiceState (exponentMeasurementContext p (orderWidth problem))
          (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
          ((exponentRun E fieldTail odd problem points).execute Reference
            (OracleInput.withEmptyService input).state)).mapClassical
            (fun record => record.1.read
              (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))))).block
                value).mass) := by
  let run := exponentRun E fieldTail odd problem points
  let supplied := OracleInput.withEmptyService input
  have actual := congrArg (fun distribution => distribution value)
    (ExecutionState.toPMF_mapClassical (run.execute Reference supplied.state)
      (run.execute_normalized supplied) run.result).symm
  change run.outputDistribution supplied value = _
  exact actual.trans (congrArg ENNReal.ofReal
    (splitServiceState_read_mass (terminal_disjoint E (orderWidth problem))
      (run.execute Reference supplied.state)
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))) value).symm)

attribute [local irreducible] ExecutionState.mapClassical ExecutionState.reindex
attribute [local irreducible] AlgorithmRun.execute Circuit.execute splitServiceState
attribute [local implicit_reducible] before terminal

/-- The actual code retains the prescribed public inputs and the entire incoming record. -/
private theorem exponentRun_code_execute_recorded_initialState (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * orderWidth problem)))
      (Register.prod (Allocation.before p.size (2 * orderWidth problem)).register Reference)) :
    splitServiceState (exponentMeasurementContext p (orderWidth problem))
      (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
      ((exponentRun E fieldTail odd problem points).code.execute Reference
        (State.mapHistory (ctx := before E (orderWidth problem))
          ((initialState E (orderWidth problem) problem original).mapClassical
            (fun stored => (stored, stored))) (fun history => ((), history)))) =
      (State.mapHistory (ctx := exponentMeasurementContext p (orderWidth problem))
        ((Measured.exponentRun E fieldTail odd problem points).code.execute Reference
          (State.mapHistory (ctx := Allocation.before p.size (2 * orderWidth problem))
            (original.mapClassical (fun stored => (stored, stored)))
            (fun history => ((), history))))
        (fun history => (history.1, (store E (orderWidth problem) problem,
          (initialStore E (orderWidth problem) problem history.2.1,
            exponentRunCodePathEquiv E fieldTail odd problem points history.2.2))))).reindex
          (S := Register.prod (exponentMeasurementContext p (orderWidth problem)).register
            (Register.prod (frame E (orderWidth problem)).register Reference))
          ((Equiv.refl (exponentMeasurementContext p (orderWidth problem)).register.Index).prodCongr
            (referenceEquiv E (orderWidth problem) Reference)) := by
  let width := orderWidth problem
  have labels :
      State.mapHistory (ctx := Allocation.before p.size (2 * width))
        (original.mapClassical (fun value =>
          (value, (store E width problem, initialStore E width problem value))))
        (fun history => ((), history)) =
      State.mapHistory (ctx := Allocation.before p.size (2 * width))
        (State.mapHistory (ctx := Allocation.before p.size (2 * width))
          (original.mapClassical (fun stored => (stored, stored)))
          (fun history => ((), history)))
        (fun history => (history.1, (store E width problem,
          initialStore E width problem history.2))) := by
    simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
      Function.comp_def]
  rw [exponentRun_code_execute, splitServiceState_attach_empty,
    initialState_split E width problem original, State.reference_history, labels,
    Circuit.execute_referenceReindex]
  have transported := Circuit.execute_mapHistory_reference
    (model := .quantum AlgorithmGate.model .empty)
    (pre := Allocation.before p.size (2 * width))
    (post := exponentMeasurementContext p width)
    (H := Store (Allocation.before p.size (2 * width)))
    (K := Store (frame E width) × Store (before E width))
    (L := Unit × (Store (frame E width) ×
      (Store (before E width) × (exponentRun E fieldTail odd problem points).code.Path)))
    (Measured.exponentRun E fieldTail odd problem points).code Reference
    (Register.prod (frame E width).register Reference)
    (State.mapHistory (ctx := Allocation.before p.size (2 * width))
      (original.mapClassical (fun stored => (stored, stored))) (fun history => ((), history)))
    (fun history : Store (Allocation.before p.size (2 * width)) =>
      (store E width problem, initialStore E width problem history))
    (fun record : Unit × ((Store (frame E width) × Store (before E width)) ×
        (Measured.exponentRun E fieldTail odd problem points).code.Path) =>
      (record.1, (record.2.1.1, (record.2.1.2,
      exponentRunCodePathEquiv E fieldTail odd problem points record.2.2))))
    (referenceEquiv E width Reference)
  exact transported


/-- Execution on the prescribed input retains the full original state in exact coordinates. -/
theorem exponentRun_execute_initialState (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * orderWidth problem)))
      (Register.prod (Allocation.before p.size (2 * orderWidth problem)).register Reference)) :
    splitServiceState (exponentMeasurementContext p (orderWidth problem))
      (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
      ((exponentRun E fieldTail odd problem points).execute Reference
        ((initialState E (orderWidth problem) problem original).mapClassical
          (fun stored => (stored, ())))) =
      (State.mapHistory (ctx := exponentMeasurementContext p (orderWidth problem))
        ((Measured.exponentRun E fieldTail odd problem points).execute Reference
          (original.mapClassical (fun stored => (stored, ()))))
        (fun history => (history.1, (store E (orderWidth problem) problem,
          (initialStore E (orderWidth problem) problem history.2.1,
            exponentRunCodePathEquiv E fieldTail odd problem points history.2.2))))).reindex
          (S := Register.prod (exponentMeasurementContext p (orderWidth problem)).register
            (Register.prod (frame E (orderWidth problem)).register Reference))
          ((Equiv.refl (exponentMeasurementContext p (orderWidth problem)).register.Index).prodCongr
            (referenceEquiv E (orderWidth problem) Reference)) := by
  let width := orderWidth problem
  have actualRecord := AlgorithmRun.emptyService_recorded_execute
    (inputDecision := @instDecidableEqProd (Store (before E (orderWidth problem)))
      (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState
      (Classical.decEq _) (Classical.decEq _))
    (exponentRun E fieldTail odd problem points) Reference
    (initialState E (orderWidth problem) problem original)
  have originalRecord := AlgorithmRun.emptyService_recorded_execute
    (inputDecision := @instDecidableEqProd
      (Store (Allocation.before p.size (2 * orderWidth problem)))
      (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState
      (Classical.decEq _) (Classical.decEq _))
    (Measured.exponentRun E fieldTail odd problem points) Reference original
  have actualSplit := congrArg
    (fun final : State (terminal E width) Reference
        (Unit × (Store (before E width) ×
          (exponentRun E fieldTail odd problem points).code.Path)) =>
      splitServiceState (exponentMeasurementContext p width) (frame E width)
        (terminal_disjoint E width) (Reference := Reference) (Hidden := Unit)
        (H := Store (before E width) × (exponentRun E fieldTail odd problem points).code.Path)
        final) actualRecord
  have originalCoordinates := congrArg
    (fun final : State (exponentMeasurementContext p width) Reference
        (Unit × (Store (Allocation.before p.size (2 * width)) ×
          (Measured.exponentRun E fieldTail odd problem points).code.Path)) =>
      (State.mapHistory (ctx := exponentMeasurementContext p width) final
        (fun history => (history.1, (store E width problem,
          (initialStore E width problem history.2.1,
            exponentRunCodePathEquiv E fieldTail odd problem points history.2.2))))).reindex
          (S := Register.prod (exponentMeasurementContext p width).register
            (Register.prod (frame E width).register Reference))
          ((Equiv.refl (exponentMeasurementContext p width).register.Index).prodCongr
            (referenceEquiv E width Reference))) originalRecord
  refine actualSplit.trans (Eq.trans ?_ originalCoordinates.symm)
  exact exponentRun_code_execute_recorded_initialState E fieldTail odd problem points original

/-- Supplying the original public inputs preserves the actual complete exponent output PMF. -/
theorem exponentRun_outputDistribution (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    (exponentRun E fieldTail odd problem points).outputDistribution
      (OracleInput.withEmptyService (initialInput E (orderWidth problem) problem original)) =
        (Measured.exponentRun E fieldTail odd problem points).outputDistribution
        (OracleInput.withEmptyService original) := by
  apply PMF.ext
  intro value
  refine (exponentRun_outputProbability_split E fieldTail odd problem points
    (initialInput E (orderWidth problem) problem original) value).trans ?_
  dsimp only [OracleInput.withEmptyService, initialInput]
  have supplied :
      (OracleInput.withEmptyService
        (initialInput E (orderWidth problem) problem original)).state =
      @ExecutionState.mapClassical _
        (Store (before E (orderWidth problem)) ×
          (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState) _ _ _
        (@instDecidableEqProd (Store (before E (orderWidth problem)))
          (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState
          (Classical.decEq _) (Classical.decEq _))
        (initialState E (orderWidth problem) problem original.state)
        (fun stored => (stored, ())) := by
    dsimp only [OracleInput.withEmptyService, initialInput]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  have suppliedObservation := congrArg
    (fun incoming : State (before E (orderWidth problem)) Reference
        (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState =>
      ENNReal.ofReal
        (((splitServiceState (exponentMeasurementContext p (orderWidth problem))
          (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
          (Reference := Reference) (Hidden := Unit)
          (H := Store (before E (orderWidth problem)) ×
            (exponentRun E fieldTail odd problem points).code.Path)
          ((exponentRun E fieldTail odd problem points).execute Reference incoming)).mapClassical
          (fun record => record.1.read
            (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))))).block
              value).mass) supplied
  have complete := exponentRun_execute_initialState E fieldTail odd problem points original.state
  have observed := congrArg
    (fun final : State (exponentMeasurementContext p (orderWidth problem))
        (Register.prod (frame E (orderWidth problem)).register Reference)
        (Unit × (Store (frame E (orderWidth problem)) ×
          (Store (before E (orderWidth problem)) ×
            (exponentRun E fieldTail odd problem points).code.Path))) =>
      ((final.mapClassical (fun record => record.1.read
        (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))))).block value).mass)
    complete
  refine suppliedObservation.trans ((congrArg ENNReal.ofReal observed).trans ?_)
  rw [ExecutionState.coordinate_reindex_mapClassical, ExecutionState.reindex_block_mass]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  let run := Measured.exponentRun E fieldTail odd problem points
  let supplied := OracleInput.withEmptyService original
  have originalSupplied :
      @ExecutionState.mapClassical _
        (Store (Allocation.before p.size (2 * orderWidth problem)) ×
          (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState) _ _ _
        (@instDecidableEqProd (Store (Allocation.before p.size (2 * orderWidth problem)))
          (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState
          (Classical.decEq _) (Classical.decEq _))
        original.state (fun stored => (stored, ())) = supplied.state := by
    dsimp only [supplied, OracleInput.withEmptyService]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  have originalObservation := congrArg
    (fun incoming : State (Allocation.before p.size (2 * orderWidth problem)) Reference
        (ExecutionModel.quantum AlgorithmGate.model .empty).HiddenState =>
      ENNReal.ofReal (((run.execute Reference incoming).mapClassical
        (fun record => record.1.read
          (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))))).block
            value).mass) originalSupplied
  have mapped := congrArg (fun distribution => distribution value)
    (ExecutionState.toPMF_mapClassical (run.execute Reference supplied.state)
      (run.execute_normalized supplied) run.result)
  rw [ExecutionState.toPMF_apply] at mapped
  exact originalObservation.trans (mapped.trans rfl)

/-- Every event on the actual measured exponent vector has its original probability. -/
theorem exponentRun_eventProbability (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    ((exponentRun E fieldTail odd problem points).outputDistribution
      (OracleInput.withEmptyService (initialInput E (orderWidth problem) problem original))).map
        (fun value => event (QubitReadouts.mask value)) true =
      ((Measured.exponentRun E fieldTail odd problem points).outputDistribution
        (OracleInput.withEmptyService original)).map
        (fun value => event (QubitReadouts.mask value)) true := by
  rw [exponentRun_outputDistribution]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
