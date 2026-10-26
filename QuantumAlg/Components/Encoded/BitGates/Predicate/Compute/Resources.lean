/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-! # Actual resource identities of native compute/select/uncompute -/

namespace QuantumAlg.EncodedBit.PredicateCompute

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
variable (prepare select : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical encoding.width).toQuantum)

private lemma inverse_eventCost :
    (prepare.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost =
      prepare.eventCost := by
  apply UnitaryCircuit.dagger_eventCost prepare (AlgorithmGate.oracleFreeAdjoints .empty)
    (AddMonoidHom.id _)
  · intro count layout application
    change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate (AlgorithmGate.adjointApplication application).coordinate) =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate application.coordinate)
    rw [AlgorithmGate.algorithmGate_adjointApplication_coordinate]
  · intro count layout application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

/-- The emitted native adjoint pays one inverse for every real preparation instruction. -/
lemma program_eventCost :
    (program prepare select).eventCost = 2 • prepare.eventCost + select.eventCost := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost, inverse_eventCost]
  abel

private lemma inverse_quantumTime :
    (prepare.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
        Resource.Event.quantumDuration =
      prepare.evaluatedEventDepth Resource.Event.quantumDuration := by
  have inverse := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (prepare.dagger (AlgorithmGate.oracleFreeAdjoints .empty)) .empty .empty
  have forward := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth prepare .empty .empty
  exact inverse.trans
    ((AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth .empty prepare).trans
      forward.symm)

/-- Both actual preparation dependency schedules and the real middle selection are counted. -/
lemma program_quantumTime :
    (program prepare select).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * prepare.evaluatedEventDepth Resource.Event.quantumDuration +
        select.evaluatedEventDepth Resource.Event.quantumDuration := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, inverse_quantumTime]
  omega

end

end QuantumAlg.EncodedBit.PredicateCompute
