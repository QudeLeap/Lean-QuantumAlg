/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Components.QuditShift.Qubit

/-!
# Literal MSB-first arithmetic and semiclassical readout on one recycled control

Each stage actually executes H, the
existing selected modular multiplier, all already-stored feedback phases,
H, measurement, and stored-result-controlled X. No reset is represented by
a state assertion. The power and auxiliary words persist across all stages
and both exponents. This module assumes no untyped Fourier equivalence.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

open Execution

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

def single (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (Context base noQuantum m ell width).quantumLayout :=
  Gate.singleQubitAt _ .empty operator (control base noQuantum m ell width)
    (control_qubit base noQuantum m ell width)

/-- The total valid/fallback branch is internal, matching the existing selected-power compiler. -/
def sourceArithmetic (N : Nat) (coefficient : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (Arithmetic.layout width).toQuantum :=
  if _positive : 0 < N then
    if fitted : N ≤ 2 ^ width then
      Arithmetic.program ⟨N, Nat.lt_succ_of_le fitted⟩ coefficient
    else UnitaryCircuit.identity AlgorithmGate.model .empty (Arithmetic.layout width).toQuantum
  else UnitaryCircuit.identity AlgorithmGate.model .empty (Arithmetic.layout width).toQuantum

def arithmetic (N : Nat) (coefficient : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (Context base noQuantum m ell width).quantumLayout :=
  unitaryOfEqualWires (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) (sourceArithmetic width N coefficient)

/-- The zero branch is the actual empty gate list; the one branch has one phase gate. -/
def feedbackProgram (inverse : Bool) (separation : Nat)
    (value : CShape.Value (.finite 2)) :
    UnitaryCircuit AlgorithmGate.model .empty (Context base noQuantum m ell width).quantumLayout :=
  match value with
  | .finite bit => if bit.val = 1 then
      single base noQuantum m ell width
        (phaseGateOp (if inverse then -(QuantumFourierTransform.Source.phaseAngle separation)
          else QuantumFourierTransform.Source.phaseAngle separation))
    else UnitaryCircuit.identity AlgorithmGate.model .empty _

/-- Exactly the actual previous stored bit chooses one physical feedback phase gate. -/
def feedbackBit (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2)) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
  .branch (.storage previous.toCStorageRef) fun value =>
    .unitary (feedbackProgram base noQuantum m ell width inverse separation value)

/-- Feedback reads only earlier cells of this exponent, never the other exponent's outputs. -/
def feedbackPrefix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → count ≤ position.val →
      Circuit model (Context base noQuantum m ell width)
        (Context base noQuantum m ell width)
  | 0, _ => .id _
  | count + 1, bounded =>
      (feedbackPrefix inverse outputs position count
        (Nat.le_of_succ_le bounded)).seq
        (feedbackBit base noQuantum m ell width inverse (position.val - count - 1)
          (outputs ⟨count, by have bound := position.isLt; omega⟩))

/-- Transport the existing binary output cell only across the actual wire's dimension equality. -/
def dimensionedCell (result : CWriteRef (Context base noQuantum m ell width) (.finite 2)) :
    CWriteRef (Context base noQuantum m ell width)
      (.finite ((Context base noQuantum m ell width).quantumLayout.wire
        (control base noQuantum m ell width)).dimension) := by
  rw [control_qubit]
  exact result

/-- The existing exact reset measures once into this output cell, then reads it for identity/X. -/
def measuredReset (result : CWriteRef (Context base noQuantum m ell width) (.finite 2)) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
  ZReset.circuit (control base noQuantum m ell width)
    (dimensionedCell base noQuantum m ell width result)
    (QuditShift.qubitRealizations (Context base noQuantum m ell width).quantumLayout
      (control base noQuantum m ell width) (control_qubit base noQuantum m ell width) .empty)
    BitWord.model

/-- The real store-selected unitary prefix immediately before one measured reset. -/
def stagePreparation (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
  (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
    (single base noQuantum m ell width Gate.HOp)).seq
    ((Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (arithmetic base noQuantum m ell width N (unit ^ (2 ^ position.rev.val)))).seq
      ((feedbackPrefix base noQuantum m ell width inverse outputs position position.val le_rfl).seq
        (.unitary (single base noQuantum m ell width Gate.HOp))))

/-- Process one MSB-addressed power while the accumulator and arithmetic auxiliary stay live. -/
def stage (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
  (stagePreparation base noQuantum m ell width inverse outputs N unit position).seq
    (measuredReset base noQuantum m ell width (outputs position))

/-- The remaining chronological stages use the same single control and the same two words. -/
def exponentSuffix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) :
    (remaining position : Nat) → position + remaining ≤ bits →
      Circuit model (Context base noQuantum m ell width)
        (Context base noQuantum m ell width)
  | 0, _, _ => .id _
  | remaining + 1, position, bounded =>
      (stage base noQuantum m ell width inverse outputs N unit
        ⟨position, by omega⟩).seq
          (exponentSuffix inverse outputs N unit
            remaining (position + 1) (by omega))

def exponentCode (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
  exponentSuffix base noQuantum m ell width inverse outputs N unit bits 0 (by omega)

/-- Match the existing generator/target-inverse action and inverse Fourier convention.
The first stream finishes before the second; the accumulator is never reinitialized between them. -/
def member (N : Nat) (generator target : (ZMod N)ˣ) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
  (exponentCode base noQuantum m ell width true
    (firstCell base noQuantum m ell width) N generator).seq
      (exponentCode base noQuantum m ell width true
        (secondCell base noQuantum m ell width) N target⁻¹)

/-- Actual first-member initialization followed by the same-bank adaptive schedule. -/
def initializedMember (N : Nat) (generator target : (ZMod N)ˣ) :
    Circuit model base (Context base noQuantum m ell width) :=
  (prepare base noQuantum m ell width N).seq
    (member base noQuantum m ell width N generator target)

/-- The complete readout keeps every live entry and observes the actual retained bit vector. -/
def run (N : Nat) (generator target : (ZMod N)ˣ) :
    AlgorithmRun model base (Context base noQuantum m ell width)
      (.fixedVector (resultBits m ell) (.finite 2)) where
  code := initializedMember base noQuantum m ell width N generator target
  output := Output.all (Context base noQuantum m ell width)
    (resultRead base noQuantum m ell width)

lemma output_listing (N : Nat) (generator target : (ZMod N)ˣ) :
    (run base noQuantum m ell width N generator target).output.listing =
      (Context base noQuantum m ell width).keys := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
