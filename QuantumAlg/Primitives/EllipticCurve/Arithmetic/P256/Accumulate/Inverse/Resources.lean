/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Time
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-! # Complete original native ledger and actual duration of the MAC adjoint -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse

noncomputable section

open QuantumAlg.EncodedBit Horner

private lemma dagger_cost {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout) :
    (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost = body.eventCost := by
  apply UnitaryCircuit.dagger_eventCost body (AlgorithmGate.oracleFreeAdjoints .empty)
    (AddMonoidHom.id _)
  · intro count layout application
    change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate (AlgorithmGate.adjointApplication application).coordinate) =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate application.coordinate)
    rw [AlgorithmGate.algorithmGate_adjointApplication_coordinate]
  · intro count layout application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

private lemma dagger_time {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout) :
    (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
        Resource.Event.quantumDuration =
      body.evaluatedEventDepth Resource.Event.quantumDuration := by
  have inverseTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)) .empty .empty
  have forwardTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth body .empty .empty
  exact inverseTime.trans
    ((AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth .empty body).trans forwardTime.symm)

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

/-- No forward instruction is discarded by complete native adjoint construction. -/
lemma eventCost :
    (program saved multiplier outer outerMultiplier).eventCost =
      (Accumulate.program saved multiplier outer outerMultiplier).eventCost :=
  dagger_cost (Accumulate.program saved multiplier outer outerMultiplier)

lemma program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program saved multiplier outer outerMultiplier).eventCost = 22717258 :=
  (congrArg (ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli))
    (eventCost saved multiplier outer outerMultiplier)).trans
      (Accumulate.program_toffoli_count saved multiplier outer outerMultiplier)

lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program saved multiplier outer outerMultiplier).eventCost = 1241338 :=
  (congrArg (ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot))
    (eventCost saved multiplier outer outerMultiplier)).trans
      (Accumulate.program_cnot_count saved multiplier outer outerMultiplier)

lemma program_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program saved multiplier outer outerMultiplier).eventCost = 259080 :=
  (congrArg (ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit))
    (eventCost saved multiplier outer outerMultiplier)).trans
      (Accumulate.program_x_count saved multiplier outer outerMultiplier)

/-- The actual native adjoint has the complete original quantum duration. -/
lemma program_quantumTime :
    (program saved multiplier outer outerMultiplier).evaluatedEventDepth
      Resource.Event.quantumDuration = 24217676 :=
  (dagger_time (Accumulate.program saved multiplier outer outerMultiplier)).trans
    (Accumulate.program_quantumTime saved multiplier outer outerMultiplier)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse
