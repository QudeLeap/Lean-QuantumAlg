/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Coordinates
import all QuantumAlg.Core.Execution.Circuit.Reference

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

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Original output-cell probabilities are unchanged by the exact complete frame coordinates. -/
theorem exponentRun_outputProbability_split (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} (input : Input (before E (orderWidth problem)) Reference)
    (value : (CShape.fixedVector (2 * orderWidth problem) (.finite 2)).Value) :
    (exponentRun E fieldTail odd problem points).outputDistribution input value =
      ENNReal.ofReal
        ((((splitState (exponentMeasurementContext p (orderWidth problem))
          (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
          ((exponentRun E fieldTail odd problem points).execute Reference input.state)).mapClassical
            (fun record => record.1.read
              (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))))).block
                value).mass) := by
  let run := exponentRun E fieldTail odd problem points
  have actual := congrArg (fun distribution => distribution value)
    (ExecutionState.toPMF_mapClassical (run.execute Reference input.state)
      (run.execute_normalized input) run.result).symm
  change run.outputDistribution input value = _
  exact actual.trans (congrArg ENNReal.ofReal
    (splitState_read_mass (terminal_disjoint E (orderWidth problem))
      (run.execute Reference input.state)
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))) value).symm)

/-- Execution on the prescribed input retains the full original state in exact coordinates. -/
theorem exponentRun_execute_initialState (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * orderWidth problem)))
      (Register.prod (Allocation.before p.size (2 * orderWidth problem)).register Reference)) :
    splitState (exponentMeasurementContext p (orderWidth problem))
      (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
      ((exponentRun E fieldTail odd problem points).execute Reference
        (initialState E (orderWidth problem) problem original)) =
      (State.mapHistory (ctx := exponentMeasurementContext p (orderWidth problem))
        ((Measured.exponentRun E fieldTail odd problem points).execute Reference original)
        (fun history => (store E (orderWidth problem) problem,
          (initialStore E (orderWidth problem) problem history.1,
            exponentRunCodePathEquiv E fieldTail odd problem points history.2)))).reindex
          (S := Register.prod (exponentMeasurementContext p (orderWidth problem)).register
            (Register.prod (frame E (orderWidth problem)).register Reference))
          ((Equiv.refl (exponentMeasurementContext p (orderWidth problem)).register.Index).prodCongr
            (referenceEquiv E (orderWidth problem) Reference)) := by
  let width := orderWidth problem
  have labels :
      original.mapClassical (fun value =>
        (value, (store E width problem, initialStore E width problem value))) =
      State.mapHistory (ctx := Allocation.before p.size (2 * orderWidth problem))
        (original.mapClassical (fun value => (value, value)))
        (fun value => (store E width problem, initialStore E width problem value)) := by
    simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
      Function.comp_def]
    exact State.mapClassical_decision _ _ _ _
  unfold AlgorithmRun.execute
  rw [exponentRun_code_execute]
  erw [initialState_split E (orderWidth problem) problem original]
  rw [labels, Circuit.execute_referenceReindex, Circuit.execute_mapHistory]
  rw [State.reference_history, State.mapHistory_comp]
  rfl

/-- Supplying the original public inputs preserves the actual complete exponent output PMF. -/
theorem exponentRun_outputDistribution (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    (exponentRun E fieldTail odd problem points).outputDistribution
      (initialInput E (orderWidth problem) problem original) =
        (Measured.exponentRun E fieldTail odd problem points).outputDistribution original := by
  apply PMF.ext
  intro value
  rw [exponentRun_outputProbability_split]
  change ENNReal.ofReal
    ((((splitState (exponentMeasurementContext p (orderWidth problem))
      (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
      ((exponentRun E fieldTail odd problem points).execute Reference
        (initialState E (orderWidth problem) problem original.state))).mapClassical
      (fun record => record.1.read
        (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))))).block value).mass)
    = _
  rw [exponentRun_execute_initialState,
    ExecutionState.coordinate_reindex_mapClassical, ExecutionState.reindex_block_mass]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  let run := Measured.exponentRun E fieldTail odd problem points
  exact (congrArg (fun distribution => distribution value)
    (ExecutionState.toPMF_mapClassical (run.execute Reference original.state)
      (run.execute_normalized original) run.result)).trans rfl

/-- Every event on the actual measured exponent vector has its original probability. -/
theorem exponentRun_eventProbability (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    ((exponentRun E fieldTail odd problem points).outputDistribution
      (initialInput E (orderWidth problem) problem original)).map
        (fun value => event (QubitReadouts.mask value)) true =
      ((Measured.exponentRun E fieldTail odd problem points).outputDistribution original).map
        (fun value => event (QubitReadouts.mask value)) true := by
  rw [exponentRun_outputDistribution]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
