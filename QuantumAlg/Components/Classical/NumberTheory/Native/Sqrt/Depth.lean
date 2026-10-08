/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Construction
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Actual serial native depth of square-root refinement

Every emitted classical instruction lies on the literal dependency chain.
The independent bound includes the selected copy, each bit of the real
constant loader, and both outer copies. Arbitrary native durations are
retained; unit durations give the explicit bound `7 * width + 2`.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Duration allowance of the actual five-operation refinement chain. -/
def roundDuration (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .add
    width))) +
    (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.mulFull width
      width))) +
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
        .lessThan (width + width)))) +
        (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
          .copy width))) +
          duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordUnary .shiftRight width))))))

/-- Independent serial duration bound for the real initialization, rounds and final copy. -/
def nativeDepthLimit (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize width
    (width + width)))) +
    (width * (duration (ConstantWord.shiftEvent (model := model) width) +
        duration (ConstantWord.incrementEvent (model := model) width)) +
      (width * roundDuration width duration +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
          .copy width)))))

/-- The real selected branch has at most the duration of its one actual copy. -/
theorem nativeSqrt_select_depth_le (refs : RoundRefs ctx width)
    (duration : Resource.Event model → Nat) (path : (select (model := model) refs).Path) :
    (select (model := model) refs).depth duration path ≤
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
        .copy width))) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit flag =>
      cases flag
      · change (BitWord.instruction (execution := model) (copyOp refs)).Path at path
        change (BitWord.instruction (execution := model) (copyOp refs)).depth duration path ≤ _
        rw [BitWord.bitWord_instruction_depth]
        exact le_rfl
      · exact Nat.zero_le _

/-- The actual round includes all arithmetic dependencies before and after selection. -/
theorem nativeSqrt_round_depth_le
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (duration : Resource.Event model → Nat) (path : (round (model := model) input refs).Path) :
    (round (model := model) input refs).depth duration path ≤ roundDuration width duration := by
  change (BitWord.instruction (execution := model) (addOp refs)).depth duration path.1 +
    ((BitWord.instruction (execution := model) (squareOp refs)).depth duration path.2.1 +
      ((BitWord.instruction (execution := model) (compareOp input refs)).depth duration path.2.2.1 +
        ((select (model := model) refs).depth duration path.2.2.2.1 +
          (BitWord.instruction (execution := model) (shiftOp refs)).depth duration
            path.2.2.2.2))) ≤ _
  simp only [BitWord.bitWord_instruction_depth]
  change duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordBinary .add width))) +
    (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.mulFull width
      width))) +
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
        .lessThan (width + width)))) +
        ((select (model := model) refs).depth duration path.2.2.2.1 +
          duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordUnary .shiftRight width)))))) ≤ _
  exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add_right (nativeSqrt_select_depth_le refs duration path.2.2.2.1) _) _) _) _

/-- Repetition sums exactly the actual body depths at its finite stage indices. -/
theorem nativeSqrt_iteration_depth_le
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (count : Nat) (duration : Resource.Event model → Nat)
    (path : (Circuit.iterate count (round (model := model) input refs)).Path) :
    (Circuit.iterate count (round (model := model) input refs)).depth duration path ≤
      count * roundDuration width duration := by
  change 0 + ∑ index : Fin count, (round (model := model) input refs).depth duration (path index) ≤
    _
  rw [Nat.zero_add]
  calc
    _ ≤ ∑ _index : Fin count, roundDuration width duration :=
      Finset.sum_le_sum (fun index _ => nativeSqrt_round_depth_le input refs duration (path index))
    _ = count * roundDuration width duration := by simp

/-- The initialized body pays its literal loader and both outer operations in full. -/
theorem nativeSqrt_body_depth_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (body (model := model) input output).Path) :
    (body (model := model) input output).depth duration path ≤ nativeDepthLimit width duration := by
  change (BitWord.instruction (execution := model) (widenOp input)).depth duration path.1 +
    ((ConstantWord.circuit (model := model) (halfCell ctx width)
      (initialHalf width)).depth duration path.2.1 +
      ((rounds (model := model) ctx width).depth duration path.2.2.1 +
        (BitWord.instruction (execution := model) (finishOp output)).depth duration path.2.2.2)) ≤ _
  simp only [BitWord.bitWord_instruction_depth]
  change duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize width (width + width)))) +
    ((ConstantWord.circuit (model := model) (halfCell ctx width) (initialHalf width)).depth
      duration path.2.1 +
      ((rounds (model := model) ctx width).depth duration path.2.2.1 +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
          .copy width))))) ≤ _
  exact Nat.add_le_add_left (Nat.add_le_add
    (ConstantWord.constantWord_depth_le (halfCell ctx width) (initialHalf width) duration path.2.1)
    (Nat.add_le_add_right (nativeSqrt_iteration_depth_le
      (.storage (wideCell ctx width).toCStorageRef) (roundRefs ctx width) width
      duration path.2.2.1) _)) _

/-- The real lexical scopes add no arithmetic duration beyond their actual body. -/
theorem nativeSqrt_into_depth_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (into (model := model) input output).Path) :
    (into (model := model) input output).depth duration path ≤ nativeDepthLimit width duration :=
  nativeSqrt_body_depth_le input output duration path

/-- At unit native duration the actual complete serial depth is at most the linear event bound. -/
theorem nativeSqrt_into_unitDepth_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) input
      output).Path) :
    (into (model := model) input output).depth (fun _ => 1) path ≤ 7 * width + 2 := by
  have bounded := nativeSqrt_into_depth_le input output (fun _ => 1) path
  change (into (model := model) input output).depth (fun _ => 1) path ≤ 1 + (width * 2 + (width * 5
    + 1)) at bounded
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
