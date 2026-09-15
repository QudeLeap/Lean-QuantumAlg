/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Resources
import all QuantumAlg.Core.Base.Accounting.Support

/-!
# Finite native support for signed word arithmetic

The alphabet includes the original word width and the widened division width.
It is independent of placements, stored values, and actual execution paths.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {width : Nat}

/-- Independent native coordinates for signed arithmetic, comparison, and bit latches. -/
def nativeAlphabet (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList [
    .classicalOperation (.bit .copy),
    .classicalOperation (.bit .xor),
    .classicalOperation (.bit .not),
    .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .complement width),
    .classicalOperation (.wordUnary .increment width),
    .classicalOperation (.wordUnary .shiftLeft width),
    .classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .sub width),
    .classicalOperation (.wordBinary .add width),
    .classicalOperation (.wordBinary .lessThan width),
    .classicalOperation (.wordUnary .shiftLeft (width + 1)),
    .classicalOperation (.wordUnary .decrement (width + 1)),
    .classicalOperation (.wordBinary .add (width + 1)),
    .classicalOperation (.wordResize width (width + 1)),
    .classicalOperation (.wordResize (width + 1) width),
    .classicalOperation (.divRem (width + 1) (width + 1))]

/-- Every member of an instruction formula belongs to the independent native alphabet. -/
def NativeTraceSupported (width : Nat) (events : List (Resource.Event kind)) : Prop :=
  ∀ event ∈ events, event ∈ nativeAlphabet width

/-- Concatenation preserves finite support independently in its two components. -/
theorem nativeTraceSupported_append (left right : List (Resource.Event kind)) :
    NativeTraceSupported width (left ++ right) ↔
      NativeTraceSupported width left ∧ NativeTraceSupported width right := by
  simp only [NativeTraceSupported, List.mem_append, or_imp, forall_and]

/-- Repeating a fixed instruction formula introduces no new native coordinates. -/
theorem nativeTraceSupported_replicate (events : List (Resource.Event kind))
    (supported : NativeTraceSupported width events) (count : Nat) :
    NativeTraceSupported width (List.replicate count events).flatten := by
  intro event present
  obtain ⟨trace, member, present⟩ := List.mem_flatten.mp present
  have same := (List.mem_replicate.mp member).2
  subst trace
  exact supported event present

/-- Sign classification stays in the alphabet even for a zero-width word. -/
theorem signTrace_nativeSupported (width : Nat) :
    NativeTraceSupported width (signTrace (kind := kind) width) := by
  unfold signTrace
  split <;> simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

/-- Both magnitude arms have finite native support without a sign assumption. -/
theorem magnitudeTrace_nativeSupported (width : Nat) (negative : Bool) :
    NativeTraceSupported width (magnitudeTrace (kind := kind) width negative) := by
  cases negative <;> simp [magnitudeTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

/-- Every rounded-division formula uses only the independent original and widened coordinates. -/
theorem roundedDivBodyTrace_nativeSupported (width : Nat)
    (magnitudeNegative correctionNegative restoreNegative : Bool) :
    NativeTraceSupported width
      (RoundedDiv.bodyTrace (kind := kind) width magnitudeNegative correctionNegative
        restoreNegative) := by
  have correction : NativeTraceSupported (kind := kind) width
      (if correctionNegative then
        [.classicalOperation (.wordUnary .decrement (width + 1))] else []) := by
    cases correctionNegative <;>
      simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]
  have restore : NativeTraceSupported (kind := kind) width
      (if restoreNegative then [.classicalOperation (.wordUnary .complement width),
        .classicalOperation (.wordUnary .increment width)] else []) := by
    cases restoreNegative <;>
      simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]
  simp only [RoundedDiv.bodyTrace, nativeTraceSupported_append, and_assoc]
  refine ⟨signTrace_nativeSupported width, magnitudeTrace_nativeSupported width magnitudeNegative,
    ?_, correction, ?_, restore⟩
  all_goals simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord
