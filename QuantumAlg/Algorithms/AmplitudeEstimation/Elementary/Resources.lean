/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Queries
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Reflection
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Independent native resources of elementary amplitude estimation

The source grants ordinary preparation, inverse preparation and controlled
good-reflection queries. The known controlled zero reflection contributes
only its actual elementary X, H, Z, CNOT and Toffoli occurrences. Every
formula below depends on widths alone; the one actual stored sequence
supplies the equal event multiplicities and critical-path depths.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

open AmplitudeAmplificationSource

/-- The three source-query coordinates and the independent elementary S0 budget. -/
def stepEventPool (n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton ((goodReflectionEvent n).controlForDimension 2) +
    ResourcePool.singleton (inversePreparationEvent n) +
    ZeroReflection.controlledElementaryEventPool n + ResourcePool.singleton (preparationEvent n)

/-- Native inverse-QFT multiplicities on the original phase register. -/
def readoutEventPool (t : Nat) : ResourcePool .quantum :=
  t • ResourcePool.singleton (.gate (.builtin "hadamard")) +
    t.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
    (t / 2) • ResourcePool.singleton (.gate (.builtin "swap"))

/-- Independent full unitary budget including the initial ordinary preparation query. -/
def unitaryEventPool (t n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (preparationEvent n) +
    (ResourcePool.singleton (.gate (.builtin "hadamard")) t +
      ((2 ^ t - 1) • stepEventPool n + readoutEventPool t))

/-- Independent duration of one actual source iterate, with sequential elementary S0. -/
def stepDepth (n : Nat) : Nat := 3 + ZeroReflection.controlledElementaryGateCount n

/-- Unit-duration budget retains parallel phase Hadamards and the literal source/readout order. -/
def unitaryDepth (t n : Nat) : Nat :=
  1 + ((if t = 0 then 0 else 1) +
    ((2 ^ t - 1) * stepDepth n + (t + t * (t - 1) / 2 + t / 2)))

/-- Independent elementary count excludes the three separately counted source-query families. -/
def unitaryGateCount (t n : Nat) : Nat :=
  2 * t + (2 ^ t - 1) * ZeroReflection.controlledElementaryGateCount n + t.choose 2 + t / 2

theorem step_eventCost {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (step U good stage).eventCost = stepEventPool n := by
  simp only [step, UnitaryCircuit.seq_eventCost, controlledGoodReflection_eventCost,
    inversePreparation_eventCost, reflection_eventCost, preparation_eventCost, stepEventPool]

theorem step_unitDepth {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (step U good stage).evaluatedEventDepth (fun _ => 1) = stepDepth n := by
  simp only [step, UnitaryCircuit.evaluatedEventDepth_seq, controlledGoodReflection_unitDepth,
    inversePreparation_unitDepth, reflection_unitDepth, preparation_unitDepth, stepDepth]
  omega

theorem ladder_eventCost {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (ladder t U good).eventCost = (2 ^ t - 1) • stepEventPool n := by
  rw [ladder, UnitaryCircuit.indexedProductNamed_eventCost,
    UnitaryCircuit.identity_eventCost, zero_add]
  simp only [powerStage, UnitaryCircuit.iterate_eventCost, step_eventCost]
  rw [Finset.sum_nsmul_assoc]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  exact qpe_sum_two_pow_range t

theorem ladder_unitDepth {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (ladder t U good).evaluatedEventDepth (fun _ => 1) = (2 ^ t - 1) * stepDepth n := by
  rw [ladder, UnitaryCircuit.evaluatedEventDepth_indexedProductNamed]
  change 0 + ∑ stage : Fin t, (powerStage U good stage).evaluatedEventDepth (fun _ => 1) = _
  simp only [zero_add, powerStage, UnitaryCircuit.evaluatedEventDepth_iterate, step_unitDepth]
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range, qpe_sum_two_pow_range]

private theorem phaseHadamards_eventCost (t n : Nat) :
    (phaseHadamards t n).eventCost = ResourcePool.singleton (.gate (.builtin "hadamard")) t := by
  simpa only [phaseHadamards, UnitaryCircuit.reindex_eventCost, qpePreparationCircuit,
    UnitaryCircuit.tensorQubits_eventCost, UnitaryCircuit.identity_eventCost, add_zero,
    WalshHadamard.hadamardEvent] using WalshHadamard.hadamardLayer_eventCost t

private theorem phaseReadout_eventCost (t n : Nat) :
    (phaseReadout t n).eventCost = readoutEventPool t := by
  rw [phaseReadout, UnitaryCircuit.reindex_eventCost, qpeReadoutFullCircuit,
    UnitaryCircuit.tensorQubits_eventCost, UnitaryCircuit.identity_eventCost, add_zero,
    qpeReadoutCircuit_eventCost, QFTCircuit_eventCost_eq]
  rfl

private theorem phaseHadamards_unitDepth (t n : Nat) :
    (phaseHadamards t n).evaluatedEventDepth (fun _ => 1) = if t = 0 then 0 else 1 := by
  change (qpePreparationCircuit t (helperWidth t n + n)).evaluatedEventDepth (fun _ => 1) = _
  rw [qpePreparationCircuit, UnitaryCircuit.evaluatedEventDepth_tensorQubits]
  change max (DepthExpr.depthEval (fun _ => 1)
    (WalshHadamard.hadamardLayer t).eventDepth) 0 = _
  rw [Nat.max_zero, WalshHadamard.hadamardLayer_eventDepth,
    WalshHadamard.parallelHadamardEventDepth_unit_depth]

private theorem phaseReadout_unitDepth (t n : Nat) :
    (phaseReadout t n).evaluatedEventDepth (fun _ => 1) =
      t + t * (t - 1) / 2 + t / 2 := by
  change (qpeReadoutFullCircuit t (helperWidth t n + n)).evaluatedEventDepth (fun _ => 1) = _
  rw [qpeReadoutFullCircuit, UnitaryCircuit.evaluatedEventDepth_tensorQubits]
  change max ((qpeReadoutCircuit t).evaluatedEventDepth (fun _ => 1)) 0 = _
  rw [Nat.max_zero, qpeReadoutCircuit_evaluatedEventDepth, QFTCircuit_evaluatedEventDepth_of_one]

/-- Every count is an equality on the single actual unitary sequence. -/
theorem program_eventCost {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (program t U good).eventCost = unitaryEventPool t n := by
  simp only [program, UnitaryCircuit.seq_eventCost, preparation_eventCost,
    phaseHadamards_eventCost, ladder_eventCost, phaseReadout_eventCost, unitaryEventPool]

/-- Exact critical-path depth includes the original phase readout and every source occurrence. -/
theorem program_unitDepth {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (program t U good).evaluatedEventDepth (fun _ => 1) = unitaryDepth t n := by
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq, preparation_unitDepth,
    phaseHadamards_unitDepth, ladder_unitDepth, phaseReadout_unitDepth, unitaryDepth]

end

end QuantumAlg.AmplitudeEstimation.Elementary
