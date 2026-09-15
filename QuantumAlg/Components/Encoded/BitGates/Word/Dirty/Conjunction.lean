/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ZeroTest
import all QuantumAlg.Util.Bool.DirtyConjunction

/-!
# Exact conjunction-chain updates on arbitrary borrowed bits

The physical word-test layout already separates every source, work, and output
wire. Its literal Toffoli chain also has an exact recurrence on arbitrary
incoming work. Reversing an output-disjoint computation restores the entire
encoded state around a conditional output flip, without a cleanliness premise.

These are elementary construction facts for the all-zero predicate
[dW19, qcnotes.tex:1335-1337]. Arbitrary borrowed-bit restoration is checked on
the full encoded state, including its relative phases when realized as a circuit.
-/

namespace QuantumAlg.EncodedBit.Word.ZeroTestLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {tail : Nat}
variable (layout : ZeroTestLayout (encoding := encoding) tail)

private theorem prefix_succ_step (index : Fin tail) (state : Data) :
    andStagePrefixStep layout (index.val + 1) state =
      (andGateAt layout index).step (andStagePrefixStep layout index.val state) := by
  have bound : index.val < (andStageIndices (tail := tail)).length := by
    rw [andStageIndices_length]
    exact index.isLt
  have selected : (andStageIndices (tail := tail))[index.val]'bound = index := by
    apply Fin.ext
    exact andStageIndices_getElem_val (tail := tail) bound
  have splitPrefix : (andStageIndices (tail := tail)).take (index.val + 1) =
      (andStageIndices (tail := tail)).take index.val ++ [index] := by
    rw [← List.take_concat_get' (andStageIndices (tail := tail)) index.val bound, selected]
  unfold andStagePrefixStep
  rw [splitPrefix, List.foldl_append]
  rfl

/-- The actual next gate xors its conjunction into the original, unrestricted work bit. -/
theorem dirtyAndPrefix_work (index : Fin tail) (state : Data) :
    (layout.work.bit index).get (andStagePrefixStep layout (index.val + 1) state) =
      ((layout.work.bit index).get state ^^
        ((chainControlA layout index).get (andStagePrefixStep layout index.val state) &&
          (chainControlB layout index).get (andStagePrefixStep layout index.val state))) := by
  rw [prefix_succ_step, andGateAt_get_work, andStagePrefixStep_get_work_before]

/-- The complete chain retains the actual incoming value in each work-bit recurrence. -/
theorem dirtyAndChain_work (index : Fin tail) (state : Data) :
    (layout.work.bit index).get (andStageIndexStep layout state) =
      ((layout.work.bit index).get state ^^
        ((chainControlA layout index).get (andStageIndexStep layout state) &&
          (chainControlB layout index).get (andStageIndexStep layout state))) := by
  rw [andStageIndexStep_get_work_from_prefix, dirtyAndPrefix_work,
    chainControlA_get_prefix_eq_indexStep, chainControlB_get_prefix_eq_indexStep]

/-- A literal compute-flip-inverse list restores every encoded coordinate except its output. -/
theorem dirtyConjunction_sandwich (compute : List (GateSpec encoding))
    (disjoint : ∀ gate, gate ∈ compute → GateSpec.bitDisjoint layout.output gate)
    (state : Data) :
    GateSpec.stepList (compute ++ [finalGate layout] ++ compute.reverse) state =
      if finalControl layout (GateSpec.stepList compute state) then layout.output.flip state
      else state := by
  rw [GateSpec.stepList_append, GateSpec.stepList_append]
  change GateSpec.stepList compute.reverse
      ((finalGate layout).step (GateSpec.stepList compute state)) = _
  rw [finalGate_step_eq_if]
  split
  · rw [GateSpec.stepList_flip_comm_of_bitDisjoint compute.reverse layout.output
      (fun gate present => disjoint gate (List.mem_reverse.mp present))]
    exact congrArg layout.output.flip (GateSpec.stepList_reverse_stepList compute state)
  · exact GateSpec.stepList_reverse_stepList compute state

end

end QuantumAlg.EncodedBit.Word.ZeroTestLayout
