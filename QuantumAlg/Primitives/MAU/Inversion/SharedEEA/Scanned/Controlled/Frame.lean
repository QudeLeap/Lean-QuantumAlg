/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers
import all QuantumAlg.Components.Encoded.BitGates.Controlled.ExternalWord

/-!
# Existing scanned source beside the supplied external control and restored work

The added coordinates are actual caller-owned systems. Point placement
will use C or N and the one extra W coordinate, retaining the numerator
and every other point/window coordinate. Original source Ctrl remains
an internal latch and is not identified with the external control.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledFrame

noncomputable section

open EncodedBit

abbrev Data (width : Nat) := ExternalWord.Registers (Scanned.Data width)

def encoding (width : Nat) : BinaryLabelEncoding (Data width) :=
  ExternalWord.encoding (Scanned.encoding width)

/-- An original source/pool bit retains its actual prefix position. -/
def sourceBit (width : Nat) (bit : EncodedBit (Scanned.encoding width)) :
    EncodedBit (encoding width) :=
  BinaryLabelEncoding.prodLeftBit (Scanned.encoding width) ExternalWord.flags bit

/-- The external supplied control is a distinct retained physical coordinate. -/
def controlBit (width : Nat) : EncodedBit (encoding width) :=
  ExternalWord.controlBit (Scanned.encoding width)

/-- One actual external work coordinate is restored by every native small-word lowering. -/
def workBit (width : Nat) : EncodedBit (encoding width) :=
  ExternalWord.workBit (Scanned.encoding width)

lemma sourceBit_get (width : Nat) (bit : EncodedBit (Scanned.encoding width))
    (state : Data width) : (sourceBit width bit).get state = bit.get state.1 := rfl

lemma sourceBit_flip (width : Nat) (bit : EncodedBit (Scanned.encoding width))
    (state : Data width) : (sourceBit width bit).flip state = (bit.flip state.1, state.2) := rfl

lemma controlBit_get (width : Nat) (state : Data width) :
    (controlBit width).get state = state.2.1 := rfl

lemma workBit_get (width : Nat) (state : Data width) :
    (workBit width).get state = state.2.2 := rfl

/-- Uncontrolled heavy source bodies execute on the same complete original source/pool prefix. -/
def liftProgram (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix ExternalWord.flags.width body

/-- Full source realizations retain both actual external coordinates and their correlations. -/
lemma liftProgram_realizes (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum)
    (action : Scanned.Data width → Scanned.Data width)
    (environment : OracleModel.empty.Interpretation)
    (actual : UnitaryCircuit.Realizes (Scanned.encoding width) body environment action) :
    UnitaryCircuit.Realizes (encoding width) (liftProgram width body) environment
      (fun state => (action state.1, state.2)) := actual.onBinaryPrefix

/-- Prefix lifting retains the same actual native ledger, with no fresh allocation. -/
lemma liftProgram_eventCost (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum) :
    (liftProgram width body).eventCost = body.eventCost := by
  have trace : (liftProgram width body).eventTrace = body.eventTrace :=
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace ExternalWord.flags.width body
  have ledger := congrArg
    (ResourcePool.ofList (model := .quantum AlgorithmGate.model .empty)) trace
  simpa only [UnitaryCircuit.ofList_eventTrace_eq_eventCost] using ledger

/-- The exact original source dependency schedule is retained under physical prefix lifting. -/
lemma liftProgram_quantumTime (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum) :
    (liftProgram width body).evaluatedEventDepth Resource.Event.quantumDuration =
      body.evaluatedEventDepth Resource.Event.quantumDuration :=
  UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth _ _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledFrame
