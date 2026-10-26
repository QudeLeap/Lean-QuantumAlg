/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Ports
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback
import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Components.QuditShift.Qubit

/-!
# Native inverse-Fourier measurement and same-cell reset on an existing window

Each head executes H, one MZ, phases selected from that recorded outcome,
and its actual identity/X correction before the remaining bank is reused.
The classical operation/service models are parameters of the same syntax.
No full exponent bank or additional quantum system is constructed.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Original retained result positions, with the first stream preceding the second. -/
def previousPositions (totalBits : Nat) : List (BitPosition totalBits) :=
  (List.finRange 2).flatMap fun stream =>
    (List.finRange totalBits).map fun position => (stream, position)

/-- Only the real guarded phase reads execute for one current physical wire. -/
def feedbackAt (ports : Ports ctx totalBits active) (current : Fin active) :
    List (BitPosition totalBits) →
      Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false
  | [] => Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx
  | previous :: rest =>
      (Feedback.one ports previous current).seq (feedbackAt ports current rest)

/-- The complete literal prior-window phase word on every active wire. -/
def priorFeedback (ports : Ports ctx totalBits active) : List (Fin active) →
    Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false
  | [] => Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx
  | current :: rest =>
      (feedbackAt ports current (previousPositions totalBits)).seq (priorFeedback ports rest)

/-- The measured head controls the real tail phases and its paid negative shift. -/
def afterHead (ports : Ports ctx totalBits (active + 1))
    (value : CShape.Value (.finite (ctx.quantumLayout.wire (ports.wires 0)).dimension)) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  (selectedPhase true ports.tail.wires ports.tail.qubits value).seq
    (QuditShift.qubitShiftCircuit ctx.quantumLayout (ports.wires 0) (ports.qubits 0)
      .empty (-value.toFin))

/-- Exactly one Fourier measurement writes the original cell used by both phase and reset. -/
def stage (ports : Ports ctx totalBits (active + 1)) :
    Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false :=
  (Circuit.unitary (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp
    (ports.wires 0) (ports.qubits 0))).seq
      ((Circuit.measureZ (ports.wires 0) (ports.measuredOutput 0)).seq
        (.branch (.storage (ports.measuredOutput 0).toCStorageRef)
          (fun value => .unitary (afterHead ports value))))

/-- Structural inverse-Fourier recursion resets each selected head before continuing. -/
def readout : (count : Nat) → Ports ctx totalBits count →
    Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false
  | 0, _ => Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx
  | count + 1, ports => (stage (operations := operations) (services := services) ports).seq
      (readout count ports.tail)

/-- Actual earlier-window feedback precedes the measured, physically reset active-bank recursion. -/
def inverseCode (ports : Ports ctx totalBits active) :
    Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx false :=
  (priorFeedback ports (List.finRange active)).seq (readout active ports)

/-- Literal H preparation of the active bank on its same original physical injection. -/
def preparation : (count : Nat) → Ports ctx totalBits count →
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout
  | 0, _ => .identity AlgorithmGate.model .empty ctx.quantumLayout
  | count + 1, ports =>
      (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0)
        (ports.qubits 0)).seq (preparation count ports.tail)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
