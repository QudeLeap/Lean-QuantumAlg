/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Prefix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Resources.Events
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Resources.Events
import all QuantumAlg.Core.Execution.Preparation.Resources

/-!
# Independent complete native-event budget of the actual paid P-256 factory

The allowance is composed from public arithmetic specifications and fixed
physical sizes. It includes fresh preparation, signed table preparation,
all three complete sampling and paid recovery attempts, terminal cleanup
and the final native option pack. No execution or recorded path is used to
define the budget.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalRoutines.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

/-- Independent complete finite allowance for physical preparation and both signed row families. -/
def prefixEventEnvelope (services : ClassicalOracleModel)
    (I : DomainParameters.PublicKeyInstance) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  854 • ResourcePool.singleton
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.preparation (2 : ℕ+)) +
      WindowTables.Outer.Preparation.Signed.envelope
        (.quantum AlgorithmGate.model .empty BitWord.model services) (actualCurveSpec I).field

/-- Independent complete native allowance for the original paid factory, including all cleanup. -/
def eventEnvelope (services : ClassicalOracleModel) (I : DomainParameters.PublicKeyInstance) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  prefixEventEnvelope services I + Sampling.Storage.Inputs.finalizedEventEnvelope services
    (actualCurveSpec I).field (actualCurveSpec I) (orderSpec I)

variable {services : ClassicalOracleModel}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

private lemma prepareWithTables_pool
    (path : (prepareWithTables (services := services) base noQuantum).Path) :
    (prepareWithTables (services := services) base noQuantum).resourcePool path =
      854 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.preparation (2 : ℕ+)) := by
  rw [Circuit.resourcePool, prepareWithTables_eventTrace]
  exact (ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum 2 (by intro index; rfl)
    BitWord.model services).trans (by rw [encoding_width])

variable (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

attribute [local irreducible] Circuit.resourcePool

/-- The full actual prefix pays every preparation and literal signed-preparation event. -/
lemma paidPrefix_pool_le
    (path : (paidPrefix (services := services) base noQuantum I basePoint targetPoint).Path) :
    (paidPrefix (services := services) base noQuantum I basePoint targetPoint).resourcePool path ≤
      prefixEventEnvelope services I := by
  unfold paidPrefix at path ⊢
  have allocated := prepareWithTables_pool base noQuantum path.1
  have signed := WindowTables.Outer.Preparation.Signed.prepare_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (tableFrame base noQuantum) (actualCurveSpec I).field (actualCurveSpec I).curve.a.val
    (originalInputAfterTables base noQuantum basePoint)
    (originalInputAfterTables base noQuantum targetPoint) path.2
  unfold prefixEventEnvelope
  exact WindowTables.Accounting.seq_pool_le _ _ _ _ path allocated.le signed

/-- Every actual complete path fits the independent budget in every native event coordinate. -/
lemma paidRun_pool_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.resourcePool path ≤
      eventEnvelope services I := by
  unfold paidRun at path ⊢
  have prefixBound := paidPrefix_pool_le base noQuantum I basePoint targetPoint path.1
  have continuation := (retainedInputs base noQuantum I basePoint targetPoint).runFinalized_pool_le
    (services := services) path.2
  unfold eventEnvelope
  exact WindowTables.Accounting.seq_pool_le _ _ _ _ path prefixBound continuation

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
