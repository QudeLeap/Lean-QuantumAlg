/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Semantics
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Observation

/-!
# Exact comparison of retained selector operators through protected observations

The actual callback records may have different finite paths and overwrite
different work cells. If each preserves its stated original observation and
the callback matrices agree on equal observations, the complete retained
native selector products agree. Native forks, placement and order are the
same literal ones. This lemma adds no circuit constructor or runtime action.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

/-- Different real callback paths with equal protected observations give the same native matrix. -/
lemma circuitAtOperator_congr_observation {Value : Type} (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (firstCallback secondCallback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (firstRecord : ∀ label, Store ctx → Store ctx × (firstCallback label).Path)
    (secondRecord : ∀ label, Store ctx → Store ctx × (secondCallback label).Path)
    (firstOperator secondOperator : Fin (2 ^ width) → Store ctx → UnitaryOperator ctx.register)
    (firstObservation secondObservation : Store ctx → Value)
    (firstPreserved : ∀ label store,
      firstObservation (firstRecord label store).1 = firstObservation store)
    (secondPreserved : ∀ label store,
      secondObservation (secondRecord label store).1 = secondObservation store)
    (callbacks : ∀ label firstStore secondStore,
      firstObservation firstStore = secondObservation secondStore →
        firstOperator label firstStore = secondOperator label secondStore)
    (environment : oracles.Interpretation) {remaining : Nat} (tree : SelectorTrie remaining)
    (depth : Nat) (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (firstStore secondStore : Store ctx)
    (same : firstObservation firstStore = secondObservation secondStore) :
    frame.circuitAtOperator physical sameWires firstCallback firstRecord firstOperator environment
      tree depth fits offset bounded firstStore =
      frame.circuitAtOperator physical sameWires secondCallback secondRecord secondOperator
        environment tree depth fits offset bounded secondStore := by
  induction tree generalizing depth offset firstStore secondStore with
  | skip remaining => rfl
  | leaf => exact callbacks _ firstStore secondStore same
  | @fork remaining left right leftIH rightIH =>
      let firstLeft := frame.circuitAtRecord physical sameWires firstCallback firstRecord left
        (depth + 1) (by omega) offset (left_bound bounded) firstStore
      let secondLeft := frame.circuitAtRecord physical sameWires secondCallback secondRecord left
        (depth + 1) (by omega) offset (left_bound bounded) secondStore
      have firstSame := frame.circuitAtRecord_observe physical sameWires firstCallback firstRecord
        firstObservation firstPreserved left (depth + 1) (by omega) offset (left_bound bounded)
        firstStore
      have secondSame := frame.circuitAtRecord_observe physical sameWires secondCallback
        secondRecord secondObservation secondPreserved left (depth + 1) (by omega) offset
        (left_bound bounded) secondStore
      have rightSame : firstObservation firstLeft.1 = secondObservation secondLeft.1 :=
        firstSame.trans (same.trans secondSame.symm)
      have leftActual := leftIH (depth + 1) (by omega) offset (left_bound bounded)
        firstStore secondStore same
      have rightActual := rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (right_bound bounded) firstLeft.1 secondLeft.1 rightSame
      dsimp only [circuitAtOperator]
      rw [rightActual, leftActual]

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
