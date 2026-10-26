/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Store

/-!
# Original protected table data through both real arithmetic call records

The actual native prefix and stored-mask feedback introduce no classical
writes. Only the original measured destinations and paid mask packing can
change Store, so every separate original table survives every call path.
No arithmetic validity or clean-input premise is used in this record law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- Every original structural table read outside the actual measurement cells is retained. -/
lemma callRecord_read_input
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (output index).key ∉ observed.storageKeys)
    (maskFree : mask.key ∉ observed.storageKeys) (store : Store ctx)
    (outcome : Reset.Instrument.Outcome (services := services) .numerator sameWires output) :
    (record (services := services) sameWires output mask kind stream width bounded store
      outcome).1.read observed = store.read observed :=
  measuredWordFinalStore_read_other (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires
    (Window.resultWord .numerator) output mask observed outputFree maskFree store outcome

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
