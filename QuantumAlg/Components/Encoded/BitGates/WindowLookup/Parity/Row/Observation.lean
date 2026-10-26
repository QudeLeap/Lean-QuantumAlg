/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Semantics

/-!
# Original measured-mask observations through actual paid row feedback

The selected physical unitary writes no classical cell. The complete row
therefore retains every structural observation outside its supplied parity
cells, including the original actual measurement mask used by later rows.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- The actual paid row record preserves every caller observation outside its parity cells. -/
lemma rowCircuitRecord_read_other (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : ∀ index, (parity index).key ∉ observed.storageKeys) (store : Store ctx) :
    (rowCircuitRecord (oracles := oracles) (services := services)
      physical sameWires measured parity table target distinct selector outside height store).1.read
        observed = store.read observed :=
  rowRecord_read_other measured parity table (List.ofFn fun index : Fin columns => index)
    observed (fun index _ => separate index) store

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity
