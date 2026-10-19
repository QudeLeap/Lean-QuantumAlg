/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Circuit
import all QuantumAlg.Core.Execution.Trace

/-!
# Literal native resources of saturating subtraction

Every actual path emits two native events: the comparison and one selected
word instruction. The independent coordinatewise envelope includes all three
possible labels, so its cardinality is three while the actual event count
and unit-duration serial depth are two. Width zero keeps those real instructions.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent support and multiplicities of every possible native instruction. -/
def nativeEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordBinary .lessThan width))) +
    (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width))) +
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .sub width))))

/-- The actual decision selects precisely one of the two native output coordinates. -/
lemma nativeSub_into_eventTrace (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) left right
      output).Path) :
    (into (model := model) left right output).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .lessThan
        width)),
        if path.2.1.toBool then .classicalOperation (BitWord.selectedCoordinate (execution :=
          model) (.wordBinary .bitXor width))
          else .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
            .sub width))] := by
  rcases path with ⟨head, value, tail⟩
  change (BitWord.instruction (execution := model) (compareOp left right)).Path at head
  cases value with
  | bit flag =>
      cases flag
      · change (BitWord.instruction (execution := model)
          (subtractOp left right output)).Path at tail
        change (BitWord.instruction (execution := model) (compareOp left right)).eventTrace head ++
          (BitWord.instruction (execution := model)
            (subtractOp left right output)).eventTrace tail = _
        simp only [BitWord.bitWord_instruction_eventTrace]
        rfl
      · change (BitWord.instruction (execution := model) (clearOp output)).Path at tail
        change (BitWord.instruction (execution := model) (compareOp left right)).eventTrace head ++
          (BitWord.instruction (execution := model) (clearOp output)).eventTrace tail = _
        simp only [BitWord.bitWord_instruction_eventTrace]
        rfl

/-- Every actual path fits the independent allowance in each native event coordinate. -/
lemma nativeSub_into_pool_le (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) left right
      output).Path) :
    (into (model := model) left right output).resourcePool path ≤ nativeEnvelope (model := model)
      width := by
  change ResourcePool.ofList ((into (model := model) left right output).eventTrace path) ≤ _
  rw [nativeSub_into_eventTrace]
  cases flag : path.2.1.toBool
  · exact add_le_add le_rfl (le_add_of_nonneg_left (zero_le : (0 : ResourcePool model) ≤
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .bitXor width)))))
  · exact add_le_add le_rfl (le_add_of_nonneg_right (zero_le : (0 : ResourcePool model) ≤
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .sub width)))))

/-- The independent envelope admits three native coordinates rather than claiming three events. -/
lemma nativeSub_nativeEnvelope_card (width : Nat) :
    (nativeEnvelope (model := model) width).card = 3 := by
  simp [nativeEnvelope, ResourcePool.singleton]

/-- Both actual branches execute exactly two native instructions, including at width zero. -/
lemma nativeSub_into_eventCount (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) left right
      output).Path) :
    ((into (model := model) left right output).resourcePool path).card = 2 := by
  change (ResourcePool.ofList ((into (model := model) left right output).eventTrace path)).card = _
  rw [nativeSub_into_eventTrace]
  rfl

/-- Independent duration allowance for the comparison and the more expensive actual branch. -/
def nativeDepthLimit (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
    .lessThan width))) +
    max (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width))))
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
        .sub width))))

/-- The actual dependency chain charges both the comparison and its selected instruction. -/
lemma nativeSub_into_depth_le (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (into (model := model) left right output).Path) :
    (into (model := model) left right output).depth duration path ≤ nativeDepthLimit width
      duration := by
  rcases path with ⟨head, value, tail⟩
  change (BitWord.instruction (execution := model) (compareOp left right)).Path at head
  cases value with
  | bit flag =>
      cases flag
      · change (BitWord.instruction (execution := model)
          (subtractOp left right output)).Path at tail
        change (BitWord.instruction (execution := model) (compareOp left right)).depth duration
          head +
          (BitWord.instruction (execution := model)
            (subtractOp left right output)).depth duration tail ≤ _
        simp only [BitWord.bitWord_instruction_depth]
        exact Nat.add_le_add_left (Nat.le_max_right _ _) _
      · change (BitWord.instruction (execution := model) (clearOp output)).Path at tail
        change (BitWord.instruction (execution := model) (compareOp left right)).depth duration
          head +
          (BitWord.instruction (execution := model) (clearOp output)).depth duration tail ≤ _
        simp only [BitWord.bitWord_instruction_depth]
        exact Nat.add_le_add_left (Nat.le_max_left _ _) _

/-- At unit native duration every actual selected path has serial depth exactly two. -/
lemma nativeSub_into_unitDepth (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) left right
      output).Path) :
    (into (model := model) left right output).depth (fun _ => 1) path = 2 := by
  rcases path with ⟨head, value, tail⟩
  cases value with
  | bit flag => cases flag <;> rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
