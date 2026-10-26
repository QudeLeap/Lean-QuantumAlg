/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Frame
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Restoration

/-!
# Actual split-address measurement unlookup on supplied existing systems

The original result word executes parallel H, real MZ, paid mask packing and
physical reset. Binary-to-unary preparation then reuses its certified subset.
Both high-address half traversals execute every paid parity row and selected
native phase; the original top high bit is restored by its two actual X gates.
The final native inverse restores unary workspace. All children forbid allocation.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}

/-- Both actual high-address halves retain all native XOR rows and stored physical feedback. -/
def phaseCircuit (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  let flip := SelectorFrame.placedCircuit physical sameWires
    ((GateSpec.x (frame.high.stack ⟨0, by omega⟩)).program physical .empty)
  let half (top : Bool) := frame.high.circuit physical sameWires
    (fun label => MaskParity.rowCircuit physical sameWires measured parity (table top label)
      frame.lowWord frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
      (frame.highStack_lowWord _) lowWidth) (SelectorTrie.full highRemaining)
  flip.seq ((half false).seq (flip.seq (half true)))

/-- Complete actual measurement, reused unary preparation, paid feedback and native restoration. -/
def circuit (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (measuredResetWordCircuit physical sameWires frame.result frame.resultDistinct output mask).seq
    ((SelectorFrame.placedCircuit physical sameWires (frame.low.program physical .empty)).seq
      ((frame.phaseCircuit physical sameWires (.storage mask.toCStorageRef) parity table).seq
        (SelectorFrame.placedCircuit physical sameWires (frame.low.uncomputeProgram physical))))

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
