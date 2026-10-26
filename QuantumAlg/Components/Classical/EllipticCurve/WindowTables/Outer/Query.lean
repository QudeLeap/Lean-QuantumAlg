/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Parameters
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction

/-!
# Existing quantum query placement without a supplied table value

The source array is supplied by the actual enclosing table scope. Every
remaining field describes original physical systems, real classical
outcome/parity storage or a native tree height, with no semantic or cost
certificate replacing a circuit.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution EncodedBit EncodedBit.WindowLookup

variable {Data : Type} (encoding : BinaryLabelEncoding Data)

/-- Literal existing placement of one load/unlookup pair, independent of its table source. -/
structure QueryPlacement (ctx : RuntimeCtx .quantum)
    (wordWidth lowWidth highRemaining : Nat) where
  frame : UnlookupFrame encoding wordWidth lowWidth highRemaining
  lookup : SelectorFrame encoding (highRemaining + lowWidth)
  outsideAddress : ∀ bit label, (frame.result.bit bit).wire ≠ (lookup.address label).wire
  outsideStack : ∀ bit label, (frame.result.bit bit).wire ≠ (lookup.stack label).wire
  physical : QubitLayout encoding.width
  sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires
  output : Fin wordWidth → CWriteRef ctx (.finite 2)
  mask : CWriteRef ctx (.bits wordWidth)
  parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit
  temporary : CWriteRef ctx .bit
  height : Nat
  covered : wordWidth ≤ 2 ^ height

namespace QueryPlacement

variable {encoding} {ctx : RuntimeCtx .quantum}
  {wordWidth lowWidth highRemaining : Nat}
  (placement : QueryPlacement encoding ctx wordWidth lowWidth highRemaining)

/-- The actual enclosing table reference is the only source selected by the query. -/
def parameters (source : CInputRef ctx
    (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth))) :
    RuntimeTable.CycleParameters encoding ctx wordWidth lowWidth highRemaining where
  frame := placement.frame
  lookup := placement.lookup
  outsideAddress := placement.outsideAddress
  outsideStack := placement.outsideStack
  physical := placement.physical
  sameWires := placement.sameWires
  source := source
  output := placement.output
  mask := placement.mask
  parity := placement.parity
  temporary := placement.temporary
  height := placement.height
  covered := placement.covered

noncomputable section

variable {services : ClassicalOracleModel}

/-- Existing allocation-free physical code embedded identically into an enclosing lexical scope. -/
def circuit (source : CInputRef ctx
    (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth))) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx :=
  .embed (ContextEmbedding.identity ctx) ((placement.parameters source).circuit)

end

end QueryPlacement

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
