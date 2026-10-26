/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Run
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Space
import all QuantumAlg.Components.GateModel.Algorithm.Resources.Hybrid
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent complete resource contract of the paid P-256 factory

The finite nongate allowance retains every literal preparation, measurement
and native classical-operation label. Its independently established native
gate limits remain sharp. The separate sharp modeled classical-work and
quantum-time bounds are not inferred from the conservative nongate allowance.
The storage budget charges the caller plus 854 physical qubits and every
retained or scratch classical cell; mathematical source labels add no hardware.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open ClassicalRoutines.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

/-- Complete independent native pool with the established three sharp native gate limits. -/
def nativeEventBudget (services : ClassicalOracleModel) (I : DomainParameters.PublicKeyInstance) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  AlgorithmGate.gateEnvelope BitWord.model services 25700867624 81134896044 99272733288 +
    AlgorithmGate.nonGateEnvelope (eventEnvelope services I)

/-- Explicit additional storage, including all actual retained cells and physical qubits. -/
def additionalSpaceBudget : SpacePool .quantum
  | .classicalBits => 85101142
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then 854 else 0

/-- Complete independent limits retain the original caller's resident and auxiliary roles. -/
def resourceBudget (services : ClassicalOracleModel) (base : RuntimeCtx .quantum)
    (I : DomainParameters.PublicKeyInstance) :
    ResourceBudget (.quantum AlgorithmGate.model .empty BitWord.model services) where
  events := nativeEventBudget services I
  resident := additionalSpaceBudget + base.residentSpace
  auxiliary := additionalSpaceBudget + base.auxiliarySpace

/-- Independent complete-run quantum computation time, including all actual terminal cleanup. -/
def quantumTimeBudget : Nat := 171185448791

variable {services : ClassicalOracleModel}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

attribute [local irreducible] Circuit.resourcePool

/-- The literal complete run meets every native coordinate in the independently supplied pool. -/
lemma paidRun_events_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.resourcePool path ≤
      (resourceBudget services base I).events := by
  apply AlgorithmGate.complete_pool_le
  · intro coordinate
    cases coordinate <;>
      exact paidRun_native_le base noQuantum I basePoint targetPoint _ path
  · exact AlgorithmGate.nonGateEnvelope_mono
      (paidRun_pool_le base noQuantum I basePoint targetPoint path)

/-- The independent resident allowance covers every actual path and every physical dimension. -/
lemma paidRun_resident_budget
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakResidentSpace
      path ≤ (resourceBudget services base I).resident := by
  intro axis
  cases axis with
  | classicalBits =>
      exact paidRun_resident_classical_le base noQuantum I basePoint targetPoint path
  | quantumSystems dimension =>
      exact paidRun_resident_quantumSystems_le base noQuantum I basePoint targetPoint dimension path

/-- Actual auxiliary roles obey the independent allowance, including every caller cell. -/
lemma paidRun_auxiliary_budget
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakAuxiliarySpace
      path ≤ (resourceBudget services base I).auxiliary := by
  intro axis
  cases axis with
  | classicalBits =>
      exact paidRun_auxiliary_classical_le base noQuantum I basePoint targetPoint path
  | quantumSystems dimension =>
      exact paidRun_auxiliary_quantumSystems_le base noQuantum I basePoint targetPoint
        dimension path

/-- The complete actual dependency depth retains the separate sharp independent time limit. -/
lemma paidRun_time_budget
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.quantumTime path ≤
      quantumTimeBudget :=
  paidRun_quantumTime_le base noQuantum I basePoint targetPoint path

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
