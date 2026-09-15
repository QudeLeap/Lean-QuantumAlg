/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Measurement
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Readout

/-!
# Actual measured exponent output

The original exponent preparation, initialized measured scalar cascade,
original inverse QFT, real finite result-cell allocation, and sequential Z
measurements form one actual execution. Its complete output manifest reads
the actual finite-two result vector in the original exponent order. Classical
recovery is a subsequent operation and is not part of this exponent output.

The event theorem applies to arbitrary subnormalized mixed input, including
zero mass. Its mathematical domain is the original active-step exceptional
condition after the original exponent preparation. The normalized probability
statement follows from the same actual event weight without changing input
amplitudes or conditioning the run on an intermediate measurement outcome.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP ConcreteCircuitAccess

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The complete actual exponent run returns its own retained finite measurement cells. -/
def exponentRun (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    AlgorithmRun (before p.size (2 * orderWidth problem))
      (exponentMeasurementContext p (orderWidth problem))
      (.fixedVector (2 * orderWidth problem) (.finite 2)) :=
  AlgorithmRun.qubitReadout
    ((preMeasurement E fieldTail odd problem points).seq
      (exponentMeasurementAllocate p (orderWidth problem)))
    (exponentMeasurementWires p (orderWidth problem))
    (exponentMeasurementWires_qubits p (orderWidth problem))
    (exponentMeasurementCells p (orderWidth problem))

/-- The prescribed pre-readout density uses only the original operators and actual cell basis. -/
def exponentRunDensity (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (Reference : Register)
    (input : DensityOperator (Register.prod
      (before p.size (2 * orderWidth problem)).register Reference)) :
    DensityOperator (Register.prod
      (exponentMeasurementContext p (orderWidth problem)).register Reference) :=
  (preMeasurementDensity E fieldTail odd problem points Reference input).reindex
    (MeasurementCells.jointBasisEquiv (after p.size (2 * orderWidth problem)) 2
      (2 * orderWidth problem) Reference)

/-- Actual exponent events have the prescribed full-density weight on the original good domain. -/
theorem exponentRun_eventWeight (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register}
    (input : ExecutionState (Store (before p.size (2 * orderWidth problem)))
      (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (support : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem Reference input.quantumMarginal).matrix basis basis = 0)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    ((exponentRun E fieldTail odd problem points).execute Reference input).effectWeight
        (fun record => if event (QubitReadouts.mask (record.1.read
          (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))))) = true then
            Effect.one (Register.prod
              (exponentMeasurementContext p (orderWidth problem)).register Reference)
          else Effect.zero (Register.prod
            (exponentMeasurementContext p (orderWidth problem)).register Reference)) =
      (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem))
        event Reference).weight
          (exponentRunDensity E fieldTail odd problem points Reference input.quantumMarginal) := by
  have domain : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem Reference
          (input.mapClassical (fun store => (store, store))).quantumMarginal).matrix
            basis basis = 0 := by
    rw [ExecutionState.mapClassical_quantumMarginal]
    exact support
  have computed := preMeasurement_density E fieldTail sameWidth fits odd problem points seed
    (input.mapClassical (fun store => (store, store))) domain
  rw [ExecutionState.mapClassical_quantumMarginal] at computed
  have allocated := exponentMeasurementAllocate_density p (orderWidth problem)
    ((preMeasurement E fieldTail odd problem points).execute Reference
      (input.mapClassical (fun store => (store, store))))
  have density :
      (((preMeasurement E fieldTail odd problem points).seq
        (exponentMeasurementAllocate p (orderWidth problem))).execute Reference
          (input.mapClassical (fun store => (store, store)))).quantumMarginal =
        exponentRunDensity E fieldTail odd problem points Reference input.quantumMarginal := by
    rw [Circuit.execute_seq, State.mapHistory_quantumMarginal]
    exact allocated.trans (congrArg
      (fun state => state.reindex
        (MeasurementCells.jointBasisEquiv (after p.size (2 * orderWidth problem)) 2
          (2 * orderWidth problem) Reference)) computed)
  have observed := AlgorithmRun.qubitReadout_effectWeight
    ((preMeasurement E fieldTail odd problem points).seq
      (exponentMeasurementAllocate p (orderWidth problem)))
    (exponentMeasurementWires p (orderWidth problem))
    (exponentMeasurementWires_qubits p (orderWidth problem))
    (exponentMeasurementCells p (orderWidth problem))
    (exponentMeasurementCells_distinct p (orderWidth problem)) input event
  exact observed.trans (congrArg
    (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem))
      event Reference).weight density)

/-- The normalized output PMF is the same actual full-density trace pairing. -/
theorem exponentRun_eventProbability (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register}
    (input : Execution.Input (before p.size (2 * orderWidth problem)) Reference)
    (support : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem Reference input.state.quantumMarginal).matrix
          basis basis = 0)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    ((exponentRun E fieldTail odd problem points).outputDistribution input).map
        (fun value => event (QubitReadouts.mask value)) true =
      ENNReal.ofReal ((QubitReadouts.eventEffect
        (exponentMeasurementWires p (orderWidth problem)) event Reference).weight
          (exponentRunDensity E fieldTail odd problem points Reference
            input.state.quantumMarginal)) := by
  rw [AlgorithmRun.outputDistribution_event_eq_effectWeight]
  exact congrArg ENNReal.ofReal (exponentRun_eventWeight E fieldTail sameWidth fits odd problem
    points seed input.state support event)

/-- Actual complete execution charges preparation, scalar work, inverse QFT and every final Z. -/
theorem exponentRun_budget (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.resourcePool path ≤
      (exponentPreparationCircuit problem).eventCost +
        Encoding.convertedEventBudget p (2 * orderWidth problem) (2 * orderWidth problem) +
          (exponentReadoutCircuit problem).eventCost +
            (2 * orderWidth problem) • ResourcePool.singleton (Circuit.zEvent 2) := by
  change ((preMeasurement E fieldTail odd problem points).Path ×
    (MeasurementCells.allocate (after p.size (2 * orderWidth problem)) 2
      (2 * orderWidth problem)).Path) × (exponentMeasurements p (orderWidth problem)).Path at path
  change ResourcePool.ofList
    (((preMeasurement E fieldTail odd problem points).eventTrace path.1.1 ++
      (MeasurementCells.allocate _ 2 (2 * orderWidth problem)).eventTrace path.1.2) ++
      (exponentMeasurements p (orderWidth problem)).eventTrace path.2) ≤ _
  rw [MeasurementCells.allocate_eventTrace, List.append_nil, ResourcePool.ofList_append]
  exact ResourcePool.add_mono (preMeasurement_budget E fieldTail odd problem points path.1.1)
    (QubitReadouts.measurement_resources _ _ _ path.2).le

/-- Actual serial depth includes both original exponent programs and each terminal measurement. -/
theorem exponentRun_depth (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.depth (fun _ => 1) path ≤
      (exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
        (2 + (4 * MAU.Multiplication.Gidney.eventBound p.size +
          (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size)) +
        (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) +
          2 * orderWidth problem := by
  change ((preMeasurement E fieldTail odd problem points).Path ×
    (MeasurementCells.allocate (after p.size (2 * orderWidth problem)) 2
      (2 * orderWidth problem)).Path) × (exponentMeasurements p (orderWidth problem)).Path at path
  change ((preMeasurement E fieldTail odd problem points).depth (fun _ => 1) path.1.1 +
    (MeasurementCells.allocate _ 2 (2 * orderWidth problem)).depth (fun _ => 1) path.1.2) +
      (exponentMeasurements p (orderWidth problem)).depth (fun _ => 1) path.2 ≤ _
  rw [MeasurementCells.allocate_depth, Nat.add_zero]
  have measured : (exponentMeasurements p (orderWidth problem)).depth (fun _ => 1) path.2 =
      2 * orderWidth problem :=
    (Circuit.measurementSequence_unitDepth _ path.2).trans List.length_ofFn
  rw [measured]
  exact Nat.add_le_add_right (preMeasurement_depth E fieldTail odd problem points path.1.1) _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
