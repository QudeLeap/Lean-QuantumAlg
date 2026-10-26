/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Semantics

/-!
# Stable actual Store observations through the complete hybrid traversal

Native selector gates preserve the real Store. Each callback receives the
preceding callback's actual next Store; a proved observation preserved by
every callback is therefore retained by the whole chronological traversal.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

/-- A callback-preserved real Store observation survives every actual chronological leaf. -/
lemma circuitAtRecord_observe {Value : Type} (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (record : ∀ label, Store ctx → Store ctx × (callback label).Path)
    (observe : Store ctx → Value)
    (preserved : ∀ label store, observe (record label store).1 = observe store)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (store : Store ctx) :
    observe (frame.circuitAtRecord physical sameWires callback record
      tree depth fits offset bounded store).1 = observe store := by
  induction tree generalizing depth offset store with
  | skip remaining => rfl
  | leaf => exact preserved _ store
  | @fork remaining left right leftIH rightIH =>
      exact (rightIH (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded)
        (frame.circuitAtRecord physical sameWires callback record left (depth + 1) (by omega)
          offset (left_bound bounded) store).1).trans
            (leftIH (depth + 1) (by omega) offset (left_bound bounded) store)

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
