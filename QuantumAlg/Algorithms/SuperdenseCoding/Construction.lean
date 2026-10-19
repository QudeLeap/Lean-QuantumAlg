/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Geometry
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel.Matrix
import all QuantumAlg.Algorithms.SuperdenseCoding.Geometry
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Execution.Output

/-!
# Actual parallel superdense-coding execution

The branch reads the original classical input. On each disjoint Bell pair,
Alice applies its selected X and Z gates, then Bob executes CNOT and H.
Every physical qubit is subsequently measured into a distinct retained cell.
The output is a structural read of those actual cells
[dW19, qcnotes.tex:879-890].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution Gate

/-- Native one-qubit gates, CNOT and actual Z measurement, without services or oracles. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- One real CNOT uses the declaration's canonical two-wire placement. -/
def cnot : UnitaryCircuit AlgorithmGate.model .empty blockLayout :=
  .native (GateModel.Application.canonical AlgorithmGate.model .cnot)

def selectedGate (selected : Bool) (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model .empty blockLayout :=
  if selected then Gate.singleQubitAt blockLayout .empty operator (0 : Fin 2) rfl
  else .identity AlgorithmGate.model .empty blockLayout

/-- Alice's actual native X-then-Z encoding on her half of the supplied Bell pair. -/
def encodingWord (first second : Bool) : UnitaryCircuit AlgorithmGate.model .empty blockLayout :=
  (selectedGate first XOp).seq (selectedGate second ZOp)

/-- Bob's actual CNOT-then-H decoder, retaining both original physical systems. -/
def decodingWord : UnitaryCircuit AlgorithmGate.model .empty blockLayout :=
  cnot.seq (Gate.singleQubitAt blockLayout .empty HOp (0 : Fin 2) rfl)

/-- A selected block contains exactly the source's encoding and decoding instructions. -/
def blockWord (first second : Bool) : UnitaryCircuit AlgorithmGate.model .empty blockLayout :=
  (encodingWord first second).seq decodingWord

/-- Parallel words retain the actual disjoint consecutive Bell pairs. -/
public def word : (count : Nat) → SuperdenseMessage count →
    UnitaryCircuit AlgorithmGate.model .empty (layout count)
  | 0, _ => .identity AlgorithmGate.model .empty (layout 0)
  | count + 1, bits =>
      (word count (fun index => bits index.castSucc)).parallelBinary
        (blockWord (bits (Fin.last count)).1 (bits (Fin.last count)).2)

/-- The finite stored message, read without arithmetic or an invented decoded value. -/
def storedBits {count : Nat} (value : CShape.Value (messageShape count)) :
    SuperdenseMessage count := fun index =>
  (decide ((value.get index).first.toFin.val = 1),
    decide ((value.get index).second.toFin.val = 1))

/-- Place the same actual parallel word onto all original live context wires. -/
public def placedWord (count : Nat) (bits : SuperdenseMessage count) :
    UnitaryCircuit AlgorithmGate.model .empty (context count).quantumLayout :=
  unitaryOfEqualWires _ _ (context_wires count) (word count bits)

/-- Every selected operation comes from the actual classical input cell. -/
public def selectedWord (count : Nat) (value : CShape.Value (messageShape count)) :
    UnitaryCircuit AlgorithmGate.model .empty (context count).quantumLayout :=
  placedWord count (storedBits value)

/-- The actual fixed-context branch and readout sequence. -/
public def code (count : Nat) : Circuit model (context count) (context count) false :=
  .seq (.branch (messageInput count) (fun value => .unitary (selectedWord count value)))
    (Circuit.measurementSequence (readouts count))

/-- Complete output retains every input, measured quantum system and real result cell. -/
public def algorithm (count : Nat) :
    Algorithm model (context count) (context count) (messageShape count) false where
  run := { code := code count, output := Output.all (context count) (.read (resultInput count)) }

end
end QuantumAlg.SuperdenseCoding.Execution
