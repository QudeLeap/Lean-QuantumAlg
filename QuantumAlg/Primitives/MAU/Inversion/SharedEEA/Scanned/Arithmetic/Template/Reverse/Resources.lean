/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Reverse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-! # Actual native adjoint resources of the descending arithmetic stream -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

/-- The generated inverse retains every actual source native event occurrence. -/
lemma reverseProgram_eventCost (width : Nat) (stage : Stage) :
    (reverseProgram width stage).eventCost = (forwardProgram width stage).eventCost := by
  apply UnitaryCircuit.dagger_eventCost (forwardProgram width stage)
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
lemma reverseProgram_quantumTime (width : Nat) (stage : Stage) :
    (reverseProgram width stage).evaluatedEventDepth Resource.Event.quantumDuration =
      (forwardProgram width stage).evaluatedEventDepth Resource.Event.quantumDuration := by
  have inverseTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (reverseProgram width stage) .empty .empty
  have forwardTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (forwardProgram width stage) .empty .empty
  change (reverseProgram width stage).evaluatedEventDepth Resource.Event.quantumDuration =
    (reverseProgram width stage).evaluatedEventDepth (fun _ => 1) at inverseTime
  change (forwardProgram width stage).evaluatedEventDepth Resource.Event.quantumDuration =
    (forwardProgram width stage).evaluatedEventDepth (fun _ => 1) at forwardTime
  exact inverseTime.trans
    ((AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth .empty
      (forwardProgram width stage)).trans forwardTime.symm)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
