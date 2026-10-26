/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Body
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Boundary

/-! # Four complete actual bodies and the unchanged terminal boundary in every fixed cycle -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

def cycleProgram (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  (bodyProgram width enough).seq ((bodyProgram width enough).seq
    ((bodyProgram width enough).seq
      ((bodyProgram width enough).seq (ControlledBoundary.program width enough))))

lemma cycleProgram_quantumTime (width : Nat) (enough : 2 ≤ width.size) :
    (cycleProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration =
      4 * (bodyProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration +
        (ControlledBoundary.program width enough).evaluatedEventDepth
          Resource.Event.quantumDuration := by
  simp only [cycleProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  omega

lemma iterate_cycle_quantumTime (width count : Nat) (enough : 2 ≤ width.size) :
    (UnitaryCircuit.iterate count (cycleProgram width enough)).evaluatedEventDepth
        Resource.Event.quantumDuration =
      count * (4 * (bodyProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration +
        (ControlledBoundary.program width enough).evaluatedEventDepth
          Resource.Event.quantumDuration) := by
  rw [UnitaryCircuit.evaluatedEventDepth, UnitaryCircuit.iterate_eventDepth,
    DepthExpr.depthEval_iterate]
  change count * (cycleProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration = _
  rw [cycleProgram_quantumTime]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
