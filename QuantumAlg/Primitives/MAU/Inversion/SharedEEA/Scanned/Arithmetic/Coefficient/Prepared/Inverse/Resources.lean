/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Prepared.Inverse
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources.Empty

/-! # Exact resources of the entire actual native prepared-arithmetic inverse -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress

noncomputable section

/-- The entire actual prepared arithmetic body is inverted, including both paid preparations. -/
lemma inverseProgram_eventCost (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    (inverseProgram width positive signed).eventCost =
      (program width positive signed).eventCost :=
  AlgorithmGate.algorithmGate_emptyAdjoints_eventCost (program width positive signed)

/-- Actual inversion retains the original physical dependency schedule in default quantum time. -/
lemma inverseProgram_quantumTime (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    (inverseProgram width positive signed).evaluatedEventDepth Resource.Event.quantumDuration =
      (program width positive signed).evaluatedEventDepth Resource.Event.quantumDuration :=
  AlgorithmGate.algorithmGate_emptyAdjoints_quantumTime (program width positive signed)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress
