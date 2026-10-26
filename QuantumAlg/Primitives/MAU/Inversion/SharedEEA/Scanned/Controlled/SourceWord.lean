/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Frame

/-!
# Literal original source words beside the complete scanned pool and external coordinates

All native placements retain the actual original source-prefix wires.
The full pool is outside every original gate. Optional external lowering
uses only the real supplied C/W coordinates, without assuming either
original source work or pool is zero or independent of a Reference.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSourceWord

noncomputable section

open EncodedBit

def sourceGates (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    List (GateSpec (Scanned.encoding width)) :=
  body.map (GateSpec.prodLeft (poolEncoding width))

def selectedGates (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    List (GateSpec (ControlledFrame.encoding width)) :=
  ExternalWord.gates (Scanned.encoding width) (sourceGates width body)

def liftedGates (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    List (GateSpec (ControlledFrame.encoding width)) :=
  (sourceGates width body).map (GateSpec.prodLeft ExternalWord.flags)

private lemma sourceGates_step (width : Nat) (body : List (GateSpec (SharedEEA.encoding width)))
    (state : Scanned.Data width) : GateSpec.stepList (sourceGates width body) state =
      (GateSpec.stepList body state.1, state.2) :=
  GateSpec.stepList_prodLeft (poolEncoding width) body state

/-- Every original source gate retains the complete old pool and both actual external wires. -/
lemma liftedGates_step (width : Nat) (body : List (GateSpec (SharedEEA.encoding width)))
    (state : ControlledFrame.Data width) :
    GateSpec.stepList (liftedGates width body) state =
      ((GateSpec.stepList body state.1.1, state.1.2), state.2) := by
  exact (GateSpec.stepList_prodLeft ExternalWord.flags (sourceGates width body) state).trans
    (congrArg (fun source => (source, state.2)) (sourceGates_step width body state.1))

/-- External control selects the full source action and restores arbitrary external work. -/
lemma selectedGates_step (width : Nat) (body : List (GateSpec (SharedEEA.encoding width)))
    (state : ControlledFrame.Data width) :
    GateSpec.stepList (selectedGates width body) state =
      ((if state.2.1 then GateSpec.stepList body state.1.1 else state.1.1, state.1.2),
        state.2) := by
  have actual := ExternalWord.gates_step (Scanned.encoding width) (sourceGates width body) state
  rw [ExternalWord.step, sourceGates_step] at actual
  exact actual.trans (by cases state.2.1 <;> rfl)

def program (width : Nat) (body : List (GateSpec (SharedEEA.encoding width))) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (selectedGates width body)

/-- Exact native all-label semantics do not require a source-value or initialized-work premise. -/
lemma program_realizes (width : Nat) (body : List (GateSpec (SharedEEA.encoding width)))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding width) (program width body) environment
      (fun state =>
        ((if state.2.1 then GateSpec.stepList body state.1.1 else state.1.1, state.1.2),
          state.2)) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (selectedGates_step width body) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSourceWord
