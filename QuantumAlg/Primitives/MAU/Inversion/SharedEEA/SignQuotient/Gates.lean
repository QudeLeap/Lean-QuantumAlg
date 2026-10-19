/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.SignQuotient

/-!
# Literal Sign-location selection followed by the complete quotient update

The full selector retains its corrected original offset. The actual quotient
word then executes on the same frame, with both borrowed words restored.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SignQuotient

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit GateSpec

/-- Every original location selector followed by the complete phase-selected quotient list. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  SelectionSchedule.gates width ++ PhaseQuotient.gates width

/-- The emitted word has the complete original action for every incoming label and Ctrl. -/
lemma signQuotient_gates_step (width : Nat) (state : Registers width) :
    stepList (gates width) state = step width state := by
  rw [gates, stepList_append, SelectionSchedule.gates_step, PhaseQuotient.phaseQuotient_gates_step]
  rfl

/-- All amplitudes, phases and arbitrary borrowed-word contents follow the same native action. -/
lemma signQuotient_gates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (gates width)) environment (step width) :=
  realizesList_congrStep layout .empty _ (signQuotient_gates_step width) environment

/-- Full selector and quotient words retain exactly the original native event sequence. -/
lemma signQuotient_gates_trace (width : Nat) :
    (gates width).map (event .empty) = (program width).eventTrace := by
  simp only [gates, List.map_append, program, UnitaryCircuit.seq_eventTrace,
    SelectionSchedule.program, PhaseQuotient.nativeProgram, programList_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.SignQuotient
