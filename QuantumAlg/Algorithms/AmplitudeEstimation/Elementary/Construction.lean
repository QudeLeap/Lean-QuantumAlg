/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Queries
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Reflection
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction

/-!
# The elementary source-query ladder of amplitude estimation

Each actual binary-power occurrence runs the source-granted controlled good
reflection, ordinary inverse preparation, elementary positive zero reflection
and ordinary preparation. The optional exceptional work position remains
outside the original phase Hadamards and inverse QFT. Power multiplicities
are the original 2^s, even when the physical register contains that position.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

private def phaseRegroupEquiv (t n : Nat) :
    Fin (2 ^ (t + (helperWidth t n + n))) ≃ Fin (2 ^ totalQubits t n) :=
  finCongr (congrArg (fun width : Nat => 2 ^ width) (Nat.add_assoc t (helperWidth t n) n).symm)

/-- Actual Hadamards on only the original t phase positions. -/
def phaseHadamards (t n : Nat) : UnitaryCircuit (Qubits (totalQubits t n)) :=
  UnitaryCircuit.reindex (phaseRegroupEquiv t n)
    (qpePreparationCircuit t (helperWidth t n + n))

/-- Actual inverse QFT on only the original t phase positions. -/
def phaseReadout (t n : Nat) : UnitaryCircuit (Qubits (totalQubits t n)) :=
  UnitaryCircuit.reindex (phaseRegroupEquiv t n)
    (qpeReadoutFullCircuit t (helperWidth t n + n))

theorem phaseHadamards_physical_idx (t n : Nat) :
    (phaseHadamards t n).physical_idx = List.range (totalQubits t n) :=
  (qpePreparationCircuit_physical_idx t (helperWidth t n + n)).trans
    (congrArg List.range (Nat.add_assoc t (helperWidth t n) n).symm)

theorem phaseReadout_physical_idx (t n : Nat) :
    (phaseReadout t n).physical_idx = List.range (totalQubits t n) :=
  (qpeReadoutFullCircuit_physical_idx t (helperWidth t n + n)).trans
    (congrArg List.range (Nat.add_assoc t (helperWidth t n) n).symm)

/-- The exact four-step source sequence contains the actual elementary S0 occurrence. -/
def step {n t : Nat} (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n))
    (stage : Fin t) : UnitaryCircuit (Qubits (totalQubits t n)) :=
  (((controlledGoodReflection good stage).seq (inversePreparation t U)).seq
    (reflection n stage)).seq (preparation t U)

theorem step_physical_idx {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (step U good stage).physical_idx = List.range (totalQubits t n) := by
  have goodContained : (controlledGoodReflection good stage).physical_idx ⊆
      List.range (totalQubits t n) := by
    rw [controlledGoodReflection_full_physical_idx]
    exact List.Subset.refl _
  have inverseContained : (inversePreparation t U).physical_idx ⊆
      List.range (totalQubits t n) := by
    rw [inversePreparation_physical_idx]
    exact List.Subset.refl _
  have before : (((controlledGoodReflection good stage).seq (inversePreparation t U)).seq
      (reflection n stage)).physical_idx ⊆ List.range (totalQubits t n) :=
    UnitaryCircuit.seq_physical_idx_subset _ _
      (UnitaryCircuit.seq_physical_idx_subset _ _ goodContained inverseContained)
      (reflection_physical_idx_subset_range n stage)
  change UnitaryCircuit.unionPhysicalIdx _ (preparation t U).physical_idx = _
  rw [preparation_physical_idx]
  exact UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _ before

/-- The actual stage retains the original binary power, independent of any work-position index. -/
def powerStage {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    UnitaryCircuit (Qubits (totalQubits t n)) :=
  UnitaryCircuit.iterate (2 ^ stage.val) (step U good stage)

/-- The original finite t-stage ladder, with no stage at zero phase width. -/
def ladder {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) : UnitaryCircuit (Qubits (totalQubits t n)) :=
  UnitaryCircuit.indexedProductNamed "amplitude-estimation-elementary-source-ladder" t
    (UnitaryCircuit.identity (Qubits (totalQubits t n))
      (List.range (totalQubits t n)) List.nodup_range)
    (powerStage U good)

theorem ladder_physical_idx {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (ladder t U good).physical_idx = List.range (totalQubits t n) := by
  rw [ladder, UnitaryCircuit.indexedProductNamed]
  apply foldl_unionPhysicalIdx_eq_self
  intro layout present
  obtain ⟨stage, rfl⟩ := List.mem_ofFn.mp present
  exact step_physical_idx U good stage

/-- Initial source preparation, original phase preparation, actual elementary ladder and readout. -/
def program {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) : UnitaryCircuit (Qubits (totalQubits t n)) :=
  (preparation t U).seq
    ((phaseHadamards t n).seq ((ladder t U good).seq (phaseReadout t n)))

/-- Every original and explicitly selected work system remains on the complete interface. -/
theorem program_physical_idx {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (program t U good).physical_idx = List.range (totalQubits t n) := by
  change UnitaryCircuit.unionPhysicalIdx (preparation t U).physical_idx
    (UnitaryCircuit.unionPhysicalIdx (phaseHadamards t n).physical_idx
      (UnitaryCircuit.unionPhysicalIdx (ladder t U good).physical_idx
        (phaseReadout t n).physical_idx)) = _
  rw [preparation_physical_idx, phaseHadamards_physical_idx, ladder_physical_idx,
    phaseReadout_physical_idx]
  simp only [UnitaryCircuit.unionPhysicalIdx_self]

end

end QuantumAlg.AmplitudeEstimation.Elementary
