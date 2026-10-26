/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Inverse
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Actual resources of the complete scanned compute/copy/native-adjoint

Every forward gate and every native inverse gate is charged. The
actual arbitrary-target copy adds its own original-width CNOT word.
These symbolic equalities do not import a planned final point budget.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInverse

noncomputable section

private lemma inverseForward_eventCost (modulus : Nat) (nontrivial : 1 < modulus) :
    ((forwardProgram modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost =
        (forwardProgram modulus nontrivial).eventCost := by
  apply UnitaryCircuit.dagger_eventCost (forwardProgram modulus nontrivial)
    (AlgorithmGate.oracleFreeAdjoints .empty) (AddMonoidHom.id _)
  · intro count layout application
    change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate (AlgorithmGate.adjointApplication application).coordinate) =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate application.coordinate)
    rw [AlgorithmGate.algorithmGate_adjointApplication_coordinate]
  · intro count layout application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

private lemma inverseForward_quantumTime (modulus : Nat) (nontrivial : 1 < modulus) :
    ((forwardProgram modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
          Resource.Event.quantumDuration =
      (forwardProgram modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration := by
  have inverseTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    ((forwardProgram modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
    .empty .empty
  have forwardTime := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (forwardProgram modulus nontrivial) .empty .empty
  change ((forwardProgram modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
        Resource.Event.quantumDuration =
    ((forwardProgram modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth (fun _ => 1) at inverseTime
  change (forwardProgram modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
    (forwardProgram modulus nontrivial).evaluatedEventDepth (fun _ => 1) at forwardTime
  exact inverseTime.trans
    ((AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth .empty
      (forwardProgram modulus nontrivial)).trans forwardTime.symm)

/-- The full actual inverse charges both complete forward event pools and the output copy. -/
lemma program_eventCost (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost =
      2 • (CorrectedSchedule.program modulus nontrivial).eventCost +
        (OutputCopy.program modulus.size).eventCost := by
  have forwardCost : (forwardProgram modulus nontrivial).eventCost =
      (CorrectedSchedule.program modulus nontrivial).eventCost :=
    UnitaryCircuit.prodLeft_eventCost (n := modulus.size)
      (CorrectedSchedule.program modulus nontrivial)
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    inverseForward_eventCost, forwardCost]
  abel

private lemma copy_quantumTime (width : Nat) :
    (OutputCopy.program width).evaluatedEventDepth Resource.Event.quantumDuration = width := by
  rw [OutputCopy.program, EncodedBit.GateSpec.programList_quantumTime, OutputCopy.gates_length]

/-- Native inversion retains the actual forward dependencies twice and the actual copy duration. -/
lemma program_quantumTime (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * (CorrectedSchedule.program modulus nontrivial).evaluatedEventDepth
        Resource.Event.quantumDuration + modulus.size := by
  have forwardTime :
      (forwardProgram modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
        (CorrectedSchedule.program modulus nontrivial).evaluatedEventDepth
          Resource.Event.quantumDuration :=
    UnitaryCircuit.prodLeft_evaluatedEventDepth Resource.Event.quantumDuration
      (n := modulus.size) (CorrectedSchedule.program modulus nontrivial)
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    inverseForward_quantumTime, copy_quantumTime, forwardTime]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInverse
