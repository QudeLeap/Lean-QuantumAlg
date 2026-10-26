/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.WorkWordExchange
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Fredkin
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-! # Complete original-word boundary exchange with one Toffoli per pair -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.BoundaryExchange

noncomputable section

open EncodedBit

/-- All original word positions, including the terminal clock padding, are actually exchanged. -/
def sourceGates (width : Nat) : List (GateSpec (SharedEEA.encoding width)) :=
  Word.fredkinGates (SharedEEA.controlBit width) (WorkWordExchange.leftWord width)
    (WorkWordExchange.rightWord width) (WorkWordExchange.control_left width)
    (WorkWordExchange.control_right width) (fun index => WorkWordExchange.left_right width index
      index)

/-- Exact complete original-register action for arbitrary Ctrl and arbitrary words. -/
lemma sourceGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (sourceGates width) state = WorkWordExchange.step state := by
  have actual := Word.fredkinGates_step (SharedEEA.controlBit width)
    (WorkWordExchange.leftWord width) (WorkWordExchange.rightWord width)
    (WorkWordExchange.control_left width) (WorkWordExchange.control_right width)
    (fun index => WorkWordExchange.left_right width index index) state
  exact actual.trans (WorkWordExchange.gates_step width state)

private def sourceProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (SharedEEA.encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (sourceGates width)

private lemma sourceProgram_realizes (width : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (SharedEEA.encoding width) (sourceProgram width) environment
      WorkWordExchange.step :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty (sourceGates width)
    (sourceGates_step width) environment

/-- Native gates act on the actual original prefix while the entire existing pool stays resident. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (sourceProgram width)

/-- Full native ket action includes every original field and every arbitrary incoming pool value. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment
      (fun state => (WorkWordExchange.step state.1, state.2)) :=
  (sourceProgram_realizes width environment).onBinaryPrefix

/-- Exact actual gate coordinates replace three-Toffoli exchanges without adding systems. -/
lemma sourceGates_counts (width : Nat) :
    ((sourceGates width).map (GateSpec.event .empty)).count (.gate .toffoli) = width + 3 ∧
      ((sourceGates width).map (GateSpec.event .empty)).count (.gate .cnot) = 2 * (width + 3) ∧
      (sourceGates width).length = 3 * (width + 3) :=
  Word.fredkinGates_counts (SharedEEA.controlBit width) (WorkWordExchange.leftWord width)
    (WorkWordExchange.rightWord width) (WorkWordExchange.control_left width)
    (WorkWordExchange.control_right width) (fun index => WorkWordExchange.left_right width index
      index)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.BoundaryExchange
