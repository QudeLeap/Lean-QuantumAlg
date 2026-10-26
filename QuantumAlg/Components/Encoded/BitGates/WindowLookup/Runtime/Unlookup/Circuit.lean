/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Frame
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Restoration

/-!
# Actual runtime-table measurement unlookup

The physically measured/reset result systems supply the existing low unary
word. Every high-address leaf reads actual table words and pays full-width
AND/XOR parity before its stored-mask native phase. The true native unary
inverse restores those same systems. No quantum child allocation is allowed.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}

/-- One real high leaf reads its supplied runtime table row before selecting physical feedback. -/
def halfCallback (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth)) (label : Fin (2 ^ highRemaining)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  RuntimeRow.rowCircuit physical sameWires measured parity temporary (table label)
    frame.lowWord frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
    (frame.highStack_lowWord _) lowWidth

/-- Every high leaf retains its actual table reads, paid parity and physical phase. -/
def halfCircuit (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  frame.high.circuit physical sameWires
    (halfCallback frame physical sameWires measured parity temporary table)
    (SelectorTrie.full highRemaining)

/-- Two real top-bit flips surround the two chronological actual runtime-table traversals. -/
def phaseCircuit (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  let flip := SelectorFrame.placedCircuit physical sameWires
    ((GateSpec.x (frame.high.stack ⟨0, by omega⟩)).program physical .empty)
  flip.seq ((halfCircuit frame physical sameWires measured parity temporary (table false)).seq
    (flip.seq (halfCircuit frame physical sameWires measured parity temporary (table true))))

/-- Actual paid feedback is bracketed by preparation and its native inverse on existing systems. -/
def restorationCircuit (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (SelectorFrame.placedCircuit physical sameWires (frame.low.program physical .empty)).seq
    ((phaseCircuit frame physical sameWires measured parity temporary table).seq
      (SelectorFrame.placedCircuit physical sameWires (frame.low.uncomputeProgram physical)))

/-- The same physical H/MZ/reset, actual paid feedback and exact native inverse form one program. -/
def circuit (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (measuredResetWordCircuit physical sameWires frame.result frame.resultDistinct output mask).seq
    (restorationCircuit frame physical sameWires (.storage mask.toCStorageRef)
      parity temporary table)

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
