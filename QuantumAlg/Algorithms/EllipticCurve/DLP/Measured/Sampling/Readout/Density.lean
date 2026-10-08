/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout
import all QuantumAlg.Core.Execution.Local.Cells.State
import all QuantumAlg.Core.Execution.Local.Cells.Observation
import all QuantumAlg.Core.Execution.Measurement.Readout.Effect
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Actual sampling events with arbitrary old result cells

The final event reads only the original cells overwritten by the actual
terminal measurements. Both public inputs and every old result-cell value
remain part of the complete state throughout the local sampling prefix.
Exact frame coordinates preserve all quantum-reference correlations; they
do not assert equality for arbitrary events on older classical values.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem splitState_eventWeight {ctx framed : RuntimeCtx .quantum}
    (separate : RuntimeCtx.StorageDisjoint ctx framed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion framed separate) Reference History)
    {shape : CShape} (input : CInputRef ctx shape) (event : shape.Value → Bool) :
    state.effectWeight (fun record =>
      if event (record.1.read (inputLeft separate input)) = true then
        Effect.one (Register.prod (ctx.disjointUnion framed separate).register Reference)
      else Effect.zero (Register.prod (ctx.disjointUnion framed separate).register Reference)) =
      (splitState ctx framed separate state).effectWeight (fun record =>
        if event (record.1.read input) = true then
          Effect.one (Register.prod ctx.register (Register.prod framed.register Reference))
        else Effect.zero
          (Register.prod ctx.register (Register.prod framed.register Reference))) := by
  let : DecidableEq Bool := Classical.decEq Bool
  have sameDecision : instDecidableEqBool = Classical.decEq Bool := Subsingleton.elim _ _
  rw [sameDecision]
  rw [ExecutionState.effectWeight_observed_mass, ExecutionState.effectWeight_observed_mass]
  unfold splitState
  rw [ExecutionState.coordinate_reindex_mapClassical, ExecutionState.reindex_block_mass,
    ExecutionState.executionState_mapClassical_comp]
  have reads :
      (fun record : Store ctx × (Store framed × History) => event (record.1.read input)) ∘
        recordEquiv ctx framed separate History =
      (fun record : Store (ctx.disjointUnion framed separate) × History =>
        event (record.1.read (inputLeft separate input))) := by
    funext record
    apply congrArg event
    change (split separate record.1).1.read input = record.1.read (inputLeft separate input)
    have original := contextUnion_read_join_left separate
      (split separate record.1).1 (split separate record.1).2 input
    rw [join_split_store] at original
    exact original.symm
  rw [reads]

private theorem splitServiceState_eventWeight {ctx framed : RuntimeCtx .quantum}
    (separate : RuntimeCtx.StorageDisjoint ctx framed)
    {Reference : Register} {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State (ctx.disjointUnion framed separate) Reference (Hidden × History))
    {shape : CShape} (input : CInputRef ctx shape) (event : shape.Value → Bool) :
    state.effectWeight (fun record =>
      if event (record.1.read (inputLeft separate input)) = true then
        Effect.one (Register.prod (ctx.disjointUnion framed separate).register Reference)
      else Effect.zero (Register.prod (ctx.disjointUnion framed separate).register Reference)) =
      (splitServiceState ctx framed separate state).effectWeight (fun record =>
        if event (record.1.read input) = true then
          Effect.one (Register.prod ctx.register (Register.prod framed.register Reference))
        else Effect.zero
          (Register.prod ctx.register (Register.prod framed.register Reference))) := by
  rw [splitServiceState, State.effectWeight_mapHistory]
  exact splitState_eventWeight separate state input event

private theorem framedReadout_eventWeight {ctx framed : RuntimeCtx .quantum} {width : Nat}
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (separate : RuntimeCtx.StorageDisjoint ctx framed)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion framed separate) Reference
      (services.HiddenState × History))
    (event : (Fin width → Bool) → Bool) :
    ((frameLocal (Circuit.measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (QubitReadouts.readouts wires qubits cells))
      (Circuit.measurementSequence_isLocal _) framed separate).execute Reference state).effectWeight
        (fun record => if event (QubitReadouts.mask
          (record.1.read (inputLeft separate (QubitReadouts.input cells)))) = true then
            Effect.one (Register.prod (ctx.disjointUnion framed separate).register Reference)
          else Effect.zero (Register.prod (ctx.disjointUnion framed separate).register Reference)) =
      (QubitReadouts.eventEffect wires event (Register.prod framed.register Reference)).weight
        (splitServiceState ctx framed separate state).quantumMarginal := by
  rw [splitServiceState_eventWeight separate _ (QubitReadouts.input cells)
    (fun value => event (QubitReadouts.mask value))]
  erw [frameLocal_execute]
  erw [State.effectWeight_mapHistory]
  exact QubitReadouts.measurement_eventEffectWeight wires qubits cells distinct _ event

private theorem framedPrefixReadout_eventWeight {ctx framed : RuntimeCtx .quantum} {width : Nat}
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (separate : RuntimeCtx.StorageDisjoint ctx framed)
    (prior : Circuit (.quantum gates oracles operations services) ctx ctx)
    (supported : prior.IsLocal)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion framed separate) Reference
      (services.HiddenState × History))
    (event : (Fin width → Bool) → Bool) :
    (((frameLocal prior supported framed separate).seq
      (frameLocal (Circuit.measurementSequence (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (QubitReadouts.readouts wires qubits cells))
        (Circuit.measurementSequence_isLocal _) framed separate)).execute
          Reference state).effectWeight
        (fun record => if event (QubitReadouts.mask
          (record.1.read (inputLeft separate (QubitReadouts.input cells)))) = true then
            Effect.one (Register.prod (ctx.disjointUnion framed separate).register Reference)
          else Effect.zero (Register.prod (ctx.disjointUnion framed separate).register Reference)) =
      (QubitReadouts.eventEffect wires event (Register.prod framed.register Reference)).weight
        (prior.execute (Register.prod framed.register Reference)
          (splitServiceState ctx framed separate state)).quantumMarginal := by
  rw [Circuit.execute_seq]
  erw [State.effectWeight_mapHistory]
  rw [framedReadout_eventWeight separate wires qubits cells distinct]
  erw [frameLocal_execute, State.mapHistory_quantumMarginal]

private theorem cellPrefixReadout_eventWeight {ctx : RuntimeCtx .quantum}
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (prior : Circuit (.quantum gates oracles operations services) ctx ctx)
    (supported : prior.IsLocal) (count : Nat)
    {width : Nat} (wires : Fin width → Fin ctx.systemCount)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasurementCells.context ctx 2 count) Reference
      (services.HiddenState × History))
    (event : (Fin width → Bool) → Bool) :
    (QubitReadouts.eventEffect
      (fun index ↦ MeasurementCells.wireEquiv ctx 2 count (wires index)) event Reference).weight
        (((Circuit.underMeasurementCells prior supported 2 count).execute
          Reference state).quantumMarginal) =
      (QubitReadouts.eventEffect wires event
        (Circuit.measurementCellsReference ctx 2 count Reference)).weight
          (prior.execute (Circuit.measurementCellsReference ctx 2 count Reference)
            (Circuit.underMeasurementCellsSplitState ctx 2 count state)).quantumMarginal := by
  rw [Circuit.underMeasurementCells_eventEffectWeight]
  have commute := Circuit.underMeasurementCells_execute
    (model := .quantum gates oracles operations services) ctx 2 prior supported count state
  rw [commute, State.mapHistory_quantumMarginal]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Actual terminal readout overwrites the old result cells before evaluating the event. -/
theorem samplingReadout_eventWeight (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    ((samplingReadout E fieldTail odd problem points).execute Reference state).effectWeight
      (fun record => if event (QubitReadouts.mask (record.1.read
        (inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
          (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))))) = true then
            Effect.one (Register.prod (PublicInput.terminal E (orderWidth problem)).register
              Reference)
          else Effect.zero (Register.prod (PublicInput.terminal E (orderWidth problem)).register
            Reference)) =
      (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem)) event
        (Register.prod (PublicInput.frame E (orderWidth problem)).register Reference)).weight
          ((Circuit.underMeasurementCells (samplingPrefix E fieldTail odd problem points)
            (samplingPrefix_isLocal E fieldTail odd problem points) 2
            (2 * orderWidth problem)).execute
              (Register.prod (PublicInput.frame E (orderWidth problem)).register Reference)
              (splitServiceState (exponentMeasurementContext p (orderWidth problem))
                (PublicInput.frame E (orderWidth problem))
                (PublicInput.terminal_disjoint E (orderWidth problem)) state)).quantumMarginal :=
  framedPrefixReadout_eventWeight
    (PublicInput.terminal_disjoint E (orderWidth problem))
    (Circuit.underMeasurementCells (samplingPrefix E fieldTail odd problem points)
      (samplingPrefix_isLocal E fieldTail odd problem points) 2 (2 * orderWidth problem))
    (Circuit.underMeasurementCells_isLocal (samplingPrefix E fieldTail odd problem points)
      (samplingPrefix_isLocal E fieldTail odd problem points) 2 (2 * orderWidth problem))
    (exponentMeasurementWires p (orderWidth problem))
    (exponentMeasurementWires_qubits p (orderWidth problem))
    (exponentMeasurementCells p (orderWidth problem))
    (exponentMeasurementCells_distinct p (orderWidth problem)) state event

/-- Exact coordinates retain all old cells and public stores beside the original scalar state. -/
def samplingReadoutSplitState (exponentWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E exponentWidth) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    State (Allocation.after p.size (2 * exponentWidth))
      (Circuit.measurementCellsReference (Allocation.after p.size (2 * exponentWidth)) 2
        (2 * exponentWidth) (Register.prod (PublicInput.frame E exponentWidth).register Reference))
      (ClassicalOracleModel.empty.HiddenState ×
        (Circuit.measurementCellsHistory (Allocation.after p.size (2 * exponentWidth)) 2
          (2 * exponentWidth) × (Store (PublicInput.frame E exponentWidth) × History))) :=
  Circuit.underMeasurementCellsSplitState (Allocation.after p.size (2 * exponentWidth)) 2
    (2 * exponentWidth)
    (splitServiceState (exponentMeasurementContext p exponentWidth)
      (PublicInput.frame E exponentWidth)
      (PublicInput.terminal_disjoint E exponentWidth) state)

/-- Actual result events are the original-wire event of the complete scalar execution. -/
theorem samplingReadout_eventWeight_split (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    ((samplingReadout E fieldTail odd problem points).execute Reference state).effectWeight
      (fun record => if event (QubitReadouts.mask (record.1.read
        (inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
          (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))))) = true then
            Effect.one (Register.prod (PublicInput.terminal E (orderWidth problem)).register
              Reference)
          else Effect.zero (Register.prod (PublicInput.terminal E (orderWidth problem)).register
            Reference)) =
      (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem)) event
        (Circuit.measurementCellsReference (Allocation.after p.size (2 * orderWidth problem)) 2
          (2 * orderWidth problem)
          (Register.prod (PublicInput.frame E (orderWidth problem)).register Reference))).weight
        ((samplingPrefix E fieldTail odd problem points).execute _
          (samplingReadoutSplitState E (orderWidth problem) state)).quantumMarginal := by
  rw [samplingReadout_eventWeight]
  exact cellPrefixReadout_eventWeight (samplingPrefix E fieldTail odd problem points)
    (samplingPrefix_isLocal E fieldTail odd problem points) (2 * orderWidth problem)
    (afterExponentWires p (orderWidth problem))
    (splitServiceState (exponentMeasurementContext p (orderWidth problem))
      (PublicInput.frame E (orderWidth problem))
      (PublicInput.terminal_disjoint E (orderWidth problem)) state) event

/-- Original good density determines actual events with arbitrary old classical values. -/
theorem samplingReadout_eventWeight_of_initialized (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (input : DensityOperator
      (Register.prod (Allocation.before p.size (2 * orderWidth problem)).register
        (Circuit.measurementCellsReference (Allocation.after p.size (2 * orderWidth problem)) 2
          (2 * orderWidth problem)
          (Register.prod (PublicInput.frame E (orderWidth problem)).register Reference))))
    (same : (samplingReadoutSplitState E (orderWidth problem) state).quantumMarginal =
      Allocation.initializedDensity p (2 * orderWidth problem) _ input)
    (support : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem _ input).matrix basis basis = 0)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    ((samplingReadout E fieldTail odd problem points).execute Reference state).effectWeight
      (fun record => if event (QubitReadouts.mask (record.1.read
        (inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
          (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))))) = true then
            Effect.one (Register.prod (PublicInput.terminal E (orderWidth problem)).register
              Reference)
          else Effect.zero (Register.prod (PublicInput.terminal E (orderWidth problem)).register
            Reference)) =
      (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem)) event
        (Circuit.measurementCellsReference (Allocation.after p.size (2 * orderWidth problem)) 2
          (2 * orderWidth problem)
          (Register.prod (PublicInput.frame E (orderWidth problem)).register Reference))).weight
        (preMeasurementDensity E fieldTail odd problem points _ input) := by
  rw [samplingReadout_eventWeight_split]
  exact congrArg (fun density =>
    (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem)) event
      (Circuit.measurementCellsReference (Allocation.after p.size (2 * orderWidth problem)) 2
        (2 * orderWidth problem)
        (Register.prod (PublicInput.frame E (orderWidth problem)).register Reference))).weight
          density)
    (samplingPrefix_density_of_initialized E fieldTail sameWidth fits odd problem points seed
      (samplingReadoutSplitState E (orderWidth problem) state) input same support)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
