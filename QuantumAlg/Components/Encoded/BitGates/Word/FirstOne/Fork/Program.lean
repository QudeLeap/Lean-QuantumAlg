/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Fork
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-! # Actual predicate fork: two supplied native tests, two CNOTs, and both real child programs -/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Every predicate computation and its full cleanup execute as the actual supplied native body. -/
def forkProgram (enable next : EncodedBit encoding) (different : enable.wire ≠ next.wire)
    (toggle lower higher : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  let copy := (GateSpec.cnot enable next different).program (QubitLayout.canonical _) .empty
  toggle.seq (lower.seq (copy.seq (higher.seq (toggle.seq copy))))

/-- Exact source-order composition retains both native tests and both actual child actions. -/
lemma forkProgram_realizes (enable next : EncodedBit encoding)
    (different : enable.wire ≠ next.wire) (predicate : Data → Bool)
    (toggle lower higher : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum)
    (lowerStep higherStep : Bool → Data → Data)
    (environment : OracleModel.empty.Interpretation)
    (toggleActual : UnitaryCircuit.Realizes encoding toggle environment
      (predicateFlip next (fun state => enable.get state && predicate state)))
    (lowerActual : UnitaryCircuit.Realizes encoding lower environment
      (fun state => lowerStep (next.get state) state))
    (higherActual : UnitaryCircuit.Realizes encoding higher environment
      (fun state => higherStep (next.get state) state)) :
    UnitaryCircuit.Realizes encoding (forkProgram enable next different toggle lower higher)
      environment (forkStep enable next predicate lowerStep higherStep) := by
  have copyActual := GateSpec.realizes (QubitLayout.canonical _) .empty
    (.cnot enable next different) environment
  have cleanup := UnitaryCircuit.Realizes.seq toggleActual copyActual
  have higherTail := UnitaryCircuit.Realizes.seq higherActual cleanup
  have alternate := UnitaryCircuit.Realizes.seq copyActual higherTail
  have lowerTail := UnitaryCircuit.Realizes.seq lowerActual alternate
  have complete := UnitaryCircuit.Realizes.seq toggleActual lowerTail
  exact complete

/-- The full native event ledger includes both predicate tests, child words and copied prefixes. -/
lemma forkProgram_eventTrace (enable next : EncodedBit encoding)
    (different : enable.wire ≠ next.wire)
    (toggle lower higher : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum) :
    (forkProgram enable next different toggle lower higher).eventTrace =
      toggle.eventTrace ++ (lower.eventTrace ++
        ([.gate .cnot] ++ (higher.eventTrace ++ (toggle.eventTrace ++ [.gate .cnot])))) := by
  simp only [forkProgram, UnitaryCircuit.seq_eventTrace, GateSpec.program_eventTrace]
  rfl

end

end QuantumAlg.EncodedBit.FirstOne
