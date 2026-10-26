/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Components.QuditShift.Qubit

/-!
# Actual measured arithmetic and semiclassical readout stages

Each original stage executes H, the complete measured modular multiplier,
all stored feedback phases, H and a physical measurement/reset. Both
exponents share the actual arithmetic bank and reused vent cells. Every
exponent output has separate retained storage [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The actual physical control is the original first port of the complete arithmetic frame. -/
def control : Fin (Context base noQuantum m ell width).systemCount :=
  EncodedBit.MeasuredUncompute.placedWire (Physical.layout width).control (Physical.qubits width)
    (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)

lemma control_qubit :
    ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension = 2 :=
  EncodedBit.MeasuredUncompute.placedWire_qubit (Physical.layout width).control
    (Physical.qubits width) (Context base noQuantum m ell width)
    (context_wires base noQuantum m ell width)

def single (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (Context base noQuantum m ell width).quantumLayout :=
  Gate.singleQubitAt _ .empty operator (control base noQuantum m ell width)
    (control_qubit base noQuantum m ell width)

def firstCell (position : Fin (ell + m)) :
    CWriteRef (Context base noQuantum m ell width) (.finite 2) :=
  resultCell base noQuantum m ell width (Fin.castAdd ell position)

def secondCell (position : Fin ell) :
    CWriteRef (Context base noQuantum m ell width) (.finite 2) :=
  resultCell base noQuantum m ell width (Fin.natAdd (ell + m) position)

/-- One real prior output cell selects its paid native feedback phase or literal identity. -/
def feedbackProgram (inverse : Bool) (separation : Nat) (value : CShape.Value (.finite 2)) :
    UnitaryCircuit AlgorithmGate.model .empty (Context base noQuantum m ell width).quantumLayout :=
  if value.toFin.val = 1 then
    single base noQuantum m ell width
      (phaseGateOp (if inverse then -(QuantumFourierTransform.Source.phaseAngle separation)
        else QuantumFourierTransform.Source.phaseAngle separation))
  else UnitaryCircuit.identity AlgorithmGate.model .empty _

def feedbackBit (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2)) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  .branch (.storage previous.toCStorageRef) fun value =>
    .unitary (feedbackProgram base noQuantum m ell width inverse separation value)

/-- Only the earlier retained outputs of this exponent control the real feedback prefix. -/
def feedbackPrefix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → count ≤ position.val →
      Circuit model (Context base noQuantum m ell width)
        (Context base noQuantum m ell width) false
  | 0, _ => .id _
  | count + 1, bounded =>
      (feedbackPrefix inverse outputs position count (by omega)).seq
        (feedbackBit base noQuantum m ell width inverse (position.val - count - 1)
          (outputs ⟨count, by have bound := position.isLt; omega⟩))

/-- MZ overwrites the retained exponent cell and reads it for the physical identity/X reset. -/
def measuredReset (result : CWriteRef (Context base noQuantum m ell width) (.finite 2)) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  ZReset.circuit (control base noQuantum m ell width)
    (MAU.Addition.Gidney.Measured.Instruction.finiteOutput
      (control_qubit base noQuantum m ell width) result)
    (QuditShift.qubitRealizations (Context base noQuantum m ell width).quantumLayout
      (control base noQuantum m ell width) (control_qubit base noQuantum m ell width) .empty)
    BitWord.model .empty false

/-- Literal H/measured-multiplication/feedback/H/MZ/reset order on the same original bank. -/
def stage (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  (Circuit.unitary (single base noQuantum m ell width Gate.HOp)).seq
    ((arithmetic base noQuantum m ell width wide modulus (unit ^ (2 ^ position.rev.val))).seq
      ((feedbackPrefix base noQuantum m ell width inverse outputs position position.val le_rfl).seq
        ((Circuit.unitary (single base noQuantum m ell width Gate.HOp)).seq
          (measuredReset base noQuantum m ell width (outputs position)))))

/-- The literal source exponent suffix executes one measured multiplication per original bit. -/
def exponentSuffix (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (unit : (ZMod modulus.toNat)ˣ) :
    (remaining position : Nat) → position + remaining ≤ bits →
      Circuit model (Context base noQuantum m ell width)
        (Context base noQuantum m ell width) false
  | 0, _, _ => .id _
  | remaining + 1, position, bounded =>
      (stage base noQuantum m ell width wide inverse outputs modulus unit
        ⟨position, by omega⟩).seq
      (exponentSuffix wide inverse outputs modulus unit remaining (position + 1) (by omega))

def exponentCode (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (unit : (ZMod modulus.toNat)ˣ) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit bits 0 (by omega)

/-- Both actual exponent streams reuse the same retained power, auxiliary, helpers and vent bank. -/
def member (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : (ZMod modulus.toNat)ˣ) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  (exponentCode base noQuantum m ell width wide true
    (firstCell base noQuantum m ell width) modulus generator).seq
      (exponentCode base noQuantum m ell width wide true
        (secondCell base noQuantum m ell width) modulus target⁻¹)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
