/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Execution
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Operator
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Protection

/-!
# Actual stored feedback equals the original runtime-table phase

The equality follows from every real paid AND/XOR write and final parity
read. It does not add a free phase program: both sides describe the native
physical branch selected by the existing actual row execution.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat} {Rows : Type}

/-- Exact matrix equality for the actual stored parity branch on every original caller Store. -/
lemma actualOperator_eq_original (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Rows → Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (protection : Protection measured parity temporary table) (row : Rows)
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (environment : oracles.Interpretation) (store : Store ctx) :
    actualOperator (services := services) physical sameWires measured parity temporary (table row)
      target distinct selector outside height environment store =
      rowOperator physical sameWires measured (table row) target distinct selector outside height
        environment store := by
  unfold actualOperator rowOperator MaskParity.rowOperator
  rw [storedRowConstant_eq measured parity temporary protection.parityDistinct
    protection.temporaryDifferent protection.maskFree protection.temporaryMaskFree (table row)
    (fun index => protection.tableFree index row) (protection.temporaryTableFree row)]

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow
