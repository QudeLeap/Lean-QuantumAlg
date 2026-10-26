/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Prefix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Resources.Numeric
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Resources of the complete paid P-256 run

The counted program includes the actual bank and retained-cell allocation,
signed point preparation, three checked full-range attempts and terminal
physical cleanup. Native quantum coordinates, measurements, duration and
modeled classical operations are independent projections of that same code.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalRoutines.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable {services : ClassicalOracleModel}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

/-- The complete prefix contributes zero modeled quantum duration, including physical allocation. -/
lemma paidPrefix_quantumTime_zero
    (path : (paidPrefix (services := services) base noQuantum I basePoint targetPoint).Path) :
    (paidPrefix (services := services) base noQuantum I basePoint targetPoint).quantumTime path =
      0 := by
  let code := paidPrefix (services := services) base noQuantum I basePoint targetPoint
  have work : ResourcePool.weightedCount Resource.Event.quantumDuration
      (code.resourcePool path) = 0 := by
    apply ResourcePool.weightedCount_eq_zero_of_mem
    intro event present
    cases event with
    | classicalOperation coordinate => rfl
    | classicalQuery coordinate => rfl
    | preparation dimension => rfl
    | measurement dimension => rfl
    | gate coordinate =>
        have missing := paidPrefix_count_zero base noQuantum I basePoint targetPoint
          (.gate coordinate) (fun _ impossible => by cases impossible)
          (fun _ impossible => by cases impossible) path
        exact False.elim ((Multiset.count_eq_zero.mp missing) present)
    | oracle coordinate =>
        have missing := paidPrefix_count_zero base noQuantum I basePoint targetPoint
          (.oracle coordinate) (fun _ impossible => by cases impossible)
          (fun _ impossible => by cases impossible) path
        exact False.elim ((Multiset.count_eq_zero.mp missing) present)
  exact Nat.eq_zero_of_le_zero
    ((code.depth_le_weightedCount_of_pool_le Resource.Event.quantumDuration
      (code.resourcePool path) path le_rfl).trans_eq work)

/-- Every native gate bound includes the complete paid prefix and final whole-bank reset. -/
lemma paidRun_native_le (coordinate : AlgorithmGate.Coordinate)
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate)
      ((paidRun (services := services) base noQuantum I basePoint targetPoint).code.resourcePool
        path) ≤ Sampling.Storage.Inputs.runFinalizedNativeLimit coordinate := by
  have prefixZero := paidPrefix_count_zero base noQuantum I basePoint targetPoint
    (.gate coordinate) (fun _ impossible => by cases impossible)
    (fun _ impossible => by cases impossible) path.1
  have continuation :=
    (retainedInputs base noQuantum I basePoint targetPoint).runFinalized_native_numeric_le
      (services := services) coordinate path.2
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.gate coordinate)
    ((paidPrefix (services := services) base noQuantum I basePoint targetPoint).resourcePool
      path.1 +
      ((retainedInputs base noQuantum I basePoint targetPoint).runFinalized
        (services := services)).code.resourcePool path.2) ≤ _
  rw [ResourcePool.count_add, prefixZero, Nat.zero_add]
  exact continuation

/-- All 215432 measurements belong to the same paid program, including terminal cleanup. -/
lemma paidRun_measurement_count
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((paidRun (services := services) base noQuantum I basePoint targetPoint).code.resourcePool
        path) = 215432 := by
  have prefixZero := paidPrefix_count_zero base noQuantum I basePoint targetPoint
    (.measurement (2 : ℕ+)) (fun _ impossible => by cases impossible)
    (fun _ impossible => by cases impossible) path.1
  have continuation :=
    (retainedInputs base noQuantum I basePoint targetPoint).runFinalized_measurement_count
      (services := services) path.2
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+))
    ((paidPrefix (services := services) base noQuantum I basePoint targetPoint).resourcePool
      path.1 +
      ((retainedInputs base noQuantum I basePoint targetPoint).runFinalized
        (services := services)).code.resourcePool path.2) = _
  rw [ResourcePool.count_add, prefixZero, Nat.zero_add]
  exact continuation

/-- Real prefix preparation and actual finalized attempts give the same quantum-time ceiling. -/
lemma paidRun_quantumTime_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.quantumTime path ≤
      171185448791 := by
  have prefixZero := paidPrefix_quantumTime_zero base noQuantum I basePoint targetPoint path.1
  have continuation :=
    (retainedInputs base noQuantum I basePoint targetPoint).runFinalized_quantumTime_le
      (services := services) path.2
  change (paidPrefix (services := services) base noQuantum I basePoint targetPoint).quantumTime
    path.1 +
    ((retainedInputs base noQuantum I basePoint targetPoint).runFinalized
      (services := services)).code.quantumTime path.2 ≤ _
  rw [prefixZero, Nat.zero_add]
  exact continuation

/-- Modeled classical work includes the previously separate paid signed-row prefix. -/
lemma paidRun_classical_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((paidRun (services := services) base noQuantum I basePoint targetPoint).code.resourcePool
        path) ≤ 20292181815 := by
  have prefixBound := paidPrefix_classical_le base noQuantum I basePoint targetPoint path.1
  have continuation :=
    (retainedInputs base noQuantum I basePoint targetPoint).runFinalized_classical_le
      (services := services) path.2
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((paidPrefix (services := services) base noQuantum I basePoint targetPoint).resourcePool
      path.1 +
      ((retainedInputs base noQuantum I basePoint targetPoint).runFinalized
        (services := services)).code.resourcePool path.2) ≤ _
  rw [ResourcePool.weightedCount_add]
  exact (Nat.add_le_add prefixBound continuation).trans_eq (by norm_num)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
