/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Cycle
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Initialization
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Completion

/-! # Actual complete paired EEA forward and original physical ports -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding modulus.size).width).toQuantum :=
  (ControlledInitialization.loadProgram modulus).seq
    ((((ControlledInitialization.program modulus).seq
      (UnitaryCircuit.iterate (2 * modulus.size - 1)
        (cycleProgram modulus.size (PredicateLayout.modulus_length_width modulus nontrivial)))).seq
          (ControlledCompletion.program modulus)).seq
            (ControlledCompletion.unloadProgram modulus))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
