/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Arithmetic
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Action
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SignQuotient
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Phase
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Body

/-! # Actual complete seven-block EEA body -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

def bodyProgram (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  (ControlledShiftBlock.program width false).seq
    ((arithmeticProgram width (NativeMicrostep.positive_of_enough width enough) false).seq
      ((ControlledSignQuotient.program width).seq
        ((arithmeticProgram width (NativeMicrostep.positive_of_enough width enough) true).seq
          ((ControlledShiftBlock.program width true).seq
            ((ControlledPhaseUpdates.program width enough false).seq
              (ControlledPhaseUpdates.program width enough true))))))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
