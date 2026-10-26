/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Reverse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-! # Actual native adjoint resources of the descending arithmetic stream -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned

noncomputable section

/-- The generated inverse retains every actual source native event occurrence. -/
lemma reverseProgram_eventCost (width : Nat) (kind : ArithmeticTop.Kind) :
    (reverseProgram width kind).eventCost = (forwardProgram width kind).eventCost := by
  apply UnitaryCircuit.dagger_eventCost (forwardProgram width kind)
    (AlgorithmGate.oracleFreeAdjoints .empty) (AddMonoidHom.id _)
  · intro count layout application
    change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate (AlgorithmGate.adjointApplication application).coordinate) =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate application.coordinate)
    rw [AlgorithmGate.algorithmGate_adjointApplication_coordinate]
  · intro count layout application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

/-- Reversing the actual dependency construction retains its default quantum duration. -/
lemma reverseProgram_quantumTime (width : Nat) (kind : ArithmeticTop.Kind) :
    (reverseProgram width kind).evaluatedEventDepth Resource.Event.quantumDuration =
      (forwardProgram width kind).evaluatedEventDepth Resource.Event.quantumDuration := by
  have inverseTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (reverseProgram width kind) .empty .empty
  have forwardTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (forwardProgram width kind) .empty .empty
  change (reverseProgram width kind).evaluatedEventDepth Resource.Event.quantumDuration =
    (reverseProgram width kind).evaluatedEventDepth (fun _ => 1) at inverseTime
  change (forwardProgram width kind).evaluatedEventDepth Resource.Event.quantumDuration =
    (forwardProgram width kind).evaluatedEventDepth (fun _ => 1) at forwardTime
  exact inverseTime.trans
    ((AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth .empty
      (forwardProgram width kind)).trans forwardTime.symm)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned
