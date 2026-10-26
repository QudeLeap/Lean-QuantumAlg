/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Run
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Resources
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Classical.Retained.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Events and native work of the actual P-256 paid prefix

The one real bank allocation prepares all 854 physical systems. Retaining
520 result cells and ten table cells emits no gate or measurement event.
The following signed-row code pays its actual classical work. These facts
refer to the literal prefix of paidRun, including its original Paths.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalRoutines.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable {services : ClassicalOracleModel}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- All actual allocation events belong to the one original owned physical bank. -/
lemma prepareWithTables_eventTrace
    (path : (prepareWithTables (services := services) base noQuantum).Path) :
    (prepareWithTables (services := services) base noQuantum).eventTrace path =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (QubitLayout.canonical encoding.width).toQuantum BitWord.model services := by
  have results := MeasurementCells.allocate_eventTrace
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (bankContext base noQuantum) 2 520 path.1.2
  have tables := RetainedCells.allocate_eventTrace
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (resultContext base noQuantum) (WindowTables.Outer.sharedShapes 256) path.2
  exact (congrArg₂ List.append
    ((congrArg (fun events =>
      ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (QubitLayout.canonical encoding.width).toQuantum BitWord.model services ++ events)
      results).trans (List.append_nil _)) tables).trans (List.append_nil _)

/-- The original physical bank is charged as 854 actual preparation occurrences. -/
lemma prepareWithTables_preparation_count
    (path : (prepareWithTables (services := services) base noQuantum).Path) :
    ((prepareWithTables (services := services) base noQuantum).eventTrace path).length = 854 := by
  rw [prepareWithTables_eventTrace]
  simp only [ZeroPreparation.eventTrace, List.length_ofFn]
  exact encoding_width

/-- Allocating the real bank emits no quantum gate or measurement coordinate. -/
lemma prepareWithTables_count_zero
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (notPreparation : ∀ dimension, focus ≠ .preparation dimension)
    (path : (prepareWithTables (services := services) base noQuantum).Path) :
    ResourcePool.count focus
      ((prepareWithTables (services := services) base noQuantum).resourcePool path) = 0 := by
  classical
  rw [Circuit.resourcePool, prepareWithTables_eventTrace]
  apply Multiset.count_eq_zero.mpr
  intro present
  change focus ∈ ZeroPreparation.eventTrace AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum BitWord.model services at present
  obtain ⟨wire, same⟩ := List.mem_ofFn.mp present
  exact notPreparation _ same.symm

/-- Physical allocation has zero modeled classical-operation weight. -/
lemma prepareWithTables_classical_zero
    (path : (prepareWithTables (services := services) base noQuantum).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((prepareWithTables (services := services) base noQuantum).resourcePool path) = 0 := by
  rw [Circuit.resourcePool, prepareWithTables_eventTrace, ResourcePool.weightedCount_ofList]
  simp [ZeroPreparation.eventTrace, Resource.Event.classicalOperationWeight]

variable (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

/-- The full paid prefix contributes no native quantum gate or measurement. -/
lemma paidPrefix_count_zero
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (notPreparation : ∀ dimension, focus ≠ .preparation dimension)
    (notClassical : ∀ coordinate, focus ≠ .classicalOperation coordinate)
    (path : (paidPrefix (services := services) base noQuantum I basePoint targetPoint).Path) :
    ResourcePool.count focus
      ((paidPrefix (services := services) base noQuantum I basePoint targetPoint).resourcePool
        path) = 0 := by
  unfold paidPrefix at path ⊢
  rw [Circuit.resourcePool_count_seq]
  rw [prepareWithTables_count_zero base noQuantum focus notPreparation,
    WindowTables.Outer.Preparation.Signed.prepare_count_zero _ _ _ _ _ focus notClassical,
    Nat.zero_add]

/-- The closed prefix bound includes both original point unpacks and signed target construction. -/
lemma paidPrefix_classical_le
    (path : (paidPrefix (services := services) base noQuantum I basePoint targetPoint).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((paidPrefix (services := services) base noQuantum I basePoint targetPoint).resourcePool
        path) ≤ 3999251 := by
  have allocated := prepareWithTables_classical_zero base noQuantum path.1
  have prepared := WindowTables.Outer.Preparation.Signed.prepare_classical_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (tableFrame base noQuantum)
    (actualCurveSpec I).field (actualCurveSpec I).curve.a.val
    (originalInputAfterTables base noQuantum basePoint)
    (originalInputAfterTables base noQuantum targetPoint) path.2
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((prepareWithTables (services := services) base noQuantum).resourcePool path.1 +
      (WindowTables.Outer.Preparation.Signed.prepare
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (tableFrame base noQuantum) (actualCurveSpec I).field (actualCurveSpec I).curve.a.val
        (originalInputAfterTables base noQuantum basePoint)
        (originalInputAfterTables base noQuantum targetPoint)).resourcePool path.2) ≤ _
  rw [ResourcePool.weightedCount_add, allocated, Nat.zero_add]
  convert prepared using 1
  norm_num [WindowTables.Outer.Preparation.Signed.classicalLimit]

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
