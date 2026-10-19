/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Geometry
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Execution.Measurement.Sequence
public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Algorithms.Teleportation.Geometry
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Output

/-!
# Native measurement and feedback for one teleportation block

The code executes Alice's CNOT and Hadamard, writes both measured outcomes to
their actual cells, and uses those cells to choose Bob's X then Z correction
[dW19, qcnotes.tex:790,802,804]. No classical message is invented by a proof.
The current language does not model communication events or Alice/Bob locality;
the separately retained communication profile is not a transmission trace.
-/

namespace QuantumAlg.QuantumTeleportation.Block

noncomputable section

open Execution Gate

/-- Standard native one-qubit and CNOT grants, without an oracle or classical service. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- One canonical native CNOT on Alice's ordered two physical systems. -/
def aliceCnot : UnitaryCircuit AlgorithmGate.model .empty
    (QuantumSignature.qubits 2).canonicalPlacement.layout :=
  .native (GateModel.Application.canonical AlgorithmGate.model .cnot)

/-- Alice's native Bell measurement word before the actual Z readouts. -/
public def aliceWord : UnitaryCircuit AlgorithmGate.model .empty layout :=
  (UnitaryCircuit.onBinaryPrefix 1 aliceCnot).seq
    (Gate.singleQubitAt layout .empty HOp 0 rfl)

/-- The two selected corrections are emitted in the source's X-then-Z order. -/
public def correctionWord (first second : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty layout :=
  (if second then Gate.singleQubitAt layout .empty XOp 2 rfl
    else .identity AlgorithmGate.model .empty layout).seq
    (if first then Gate.singleQubitAt layout .empty ZOp 2 rfl
      else .identity AlgorithmGate.model .empty layout)

/-- Place a native word using equality of the complete physical wire list. -/
def onContext (word : UnitaryCircuit AlgorithmGate.model .empty layout) :
    UnitaryCircuit AlgorithmGate.model .empty context.quantumLayout :=
  unitaryOfEqualWires layout context.quantumLayout layout_wires_eq_context word

/-- Bob's feedback reads each actual finite value just written by Alice's measurement. -/
public def selectedCorrection (value : CShape.Value (.fixedVector 2 (.finite 2))) :
    UnitaryCircuit AlgorithmGate.model .empty context.quantumLayout :=
  onContext (correctionWord (QubitReadouts.mask value 0) (QubitReadouts.mask value 1))

/-- One actual fixed-context program: native gates, Z writes and classical branch selection. -/
public def code : Circuit model context context false :=
  .seq (.unitary (onContext aliceWord))
    (.seq (Circuit.measurementSequence readouts)
      (.branch resultInput (fun value => .unitary (selectedCorrection value))))

/-- Every system and stored result is retained; the classical output reads the measured cells. -/
public def algorithm : Algorithm model context context (.fixedVector 2 (.finite 2)) false where
  run := { code := code, output := Output.all context (.read resultInput) }

end

end QuantumAlg.QuantumTeleportation.Block
