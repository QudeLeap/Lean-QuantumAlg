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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent support and multiplicities of every possible native instruction. -/
def nativeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordBinary .lessThan width)) +
    (ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor width)) +
      ResourcePool.singleton (.classicalOperation (.wordBinary .sub width)))

/-- The actual decision selects precisely one of the two native output coordinates. -/
theorem nativeSub_into_eventTrace (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into left right output).Path) :
    (into left right output).eventTrace path =
      [.classicalOperation (.wordBinary .lessThan width),
        if path.2.1.toBool then .classicalOperation (.wordBinary .bitXor width)
          else .classicalOperation (.wordBinary .sub width)] := by
  rcases path with ⟨head, value, tail⟩
  cases value with
  | bit flag => cases flag <;> rfl

/-- Every actual path fits the independent allowance in each native event coordinate. -/
theorem nativeSub_into_pool_le (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into left right output).Path) :
    (into left right output).resourcePool path ≤ nativeEnvelope kind width := by
  rcases path with ⟨head, value, tail⟩
  cases value with
  | bit flag =>
      cases flag
      · exact add_le_add le_rfl (le_add_of_nonneg_left
          (zero_le : (0 : ResourcePool kind) ≤
            ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor width))))
      · exact add_le_add le_rfl (le_add_of_nonneg_right
          (zero_le : (0 : ResourcePool kind) ≤
            ResourcePool.singleton (.classicalOperation (.wordBinary .sub width))))

/-- The independent envelope admits three native coordinates rather than claiming three events. -/
theorem nativeSub_nativeEnvelope_card (kind : ProblemKind) (width : Nat) :
    (nativeEnvelope kind width).card = 3 := by
  simp [nativeEnvelope, ResourcePool.singleton]

/-- Both actual branches execute exactly two native instructions, including at width zero. -/
theorem nativeSub_into_eventCount (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into left right output).Path) :
    ((into left right output).resourcePool path).card = 2 := by
  change (ResourcePool.ofList ((into left right output).eventTrace path)).card = _
  rw [nativeSub_into_eventTrace]
  rfl

/-- Independent duration allowance for the comparison and the more expensive actual branch. -/
def nativeDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.wordBinary .lessThan width)) +
    max (duration (.classicalOperation (.wordBinary .bitXor width)))
      (duration (.classicalOperation (.wordBinary .sub width)))

/-- The actual dependency chain charges both the comparison and its selected instruction. -/
theorem nativeSub_into_depth_le (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (into left right output).Path) :
    (into left right output).depth duration path ≤ nativeDepthLimit width duration := by
  rcases path with ⟨head, value, tail⟩
  cases value with
  | bit flag =>
      cases flag
      · exact Nat.add_le_add_left (Nat.le_max_right _ _) _
      · exact Nat.add_le_add_left (Nat.le_max_left _ _) _

/-- At unit native duration every actual selected path has serial depth exactly two. -/
theorem nativeSub_into_unitDepth (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into left right output).Path) :
    (into left right output).depth (fun _ => 1) path = 2 := by
  rcases path with ⟨head, value, tail⟩
  cases value with
  | bit flag => cases flag <;> rfl

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
