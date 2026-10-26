/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Comparison.Complete
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Restoration.Execution
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Restoration

/-!
# Exact observed-table matrix of the complete actual runtime restoration

Identical native unary preparation and inverse surround the proved exact
paid feedback matrix. The resulting equality holds before any clean-input
or lookup-graph promise, hence also after tensoring any external reference.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}

/-- All actual runtime feedback and native restoration have the observed-table matrix. -/
lemma restorationOperator_eq_observed
    (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (protection : RuntimeRow.Protection measured parity temporary
      (fun row : Bool × Fin (2 ^ highRemaining) => table row.1 row.2))
    (snapshot : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (environment : OracleModel.Interpretation .empty) (firstStore secondStore : Store ctx)
    (sameTable : ∀ top row, RuntimeRow.readTable (table top row) firstStore = snapshot top row)
    (sameMask : firstStore.read measured = secondStore.read measured) :
    restorationOperator frame (services := services) physical sameWires measured parity temporary
      table environment firstStore =
      frame.restorationOperator (services := services) physical sameWires measured parity snapshot
        environment secondStore := by
  exact congrArg (fun middle : UnitaryOperator ctx.register =>
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (frame.low.uncomputeProgram physical)).matrix environment * middle *
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (frame.low.program physical .empty)).matrix environment)
    (phaseOperator_eq_observed (services := services)
      frame physical sameWires measured parity temporary table
      protection snapshot environment firstStore secondStore sameTable sameMask)

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
