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

variable {model : ExecutionModel} [BitWord.Selected model] {width : Nat}

/-- Independent native coordinates for signed arithmetic, comparison, and bit latches. -/
def nativeAlphabet (width : Nat) : ResourcePool model :=
  ResourcePool.ofList [
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .copy)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .xor)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .complement width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .add width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .decrement (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem (width + 1) (width + 1)))]

/-- Every member of an instruction formula belongs to the independent native alphabet. -/
def NativeTraceSupported (width : Nat) (events : List (Resource.Event model)) : Prop :=
  ∀ event ∈ events, event ∈ nativeAlphabet width

/-- Concatenation preserves finite support independently in its two components. -/
lemma nativeTraceSupported_append (left right : List (Resource.Event model)) :
    NativeTraceSupported width (left ++ right) ↔
      NativeTraceSupported width left ∧ NativeTraceSupported width right := by
  simp only [NativeTraceSupported, List.mem_append, or_imp, forall_and]

/-- Repeating a fixed instruction formula introduces no new native coordinates. -/
lemma nativeTraceSupported_replicate (events : List (Resource.Event model))
    (supported : NativeTraceSupported width events) (count : Nat) :
    NativeTraceSupported width (List.replicate count events).flatten := by
  intro event present
  obtain ⟨trace, member, present⟩ := List.mem_flatten.mp present
  have same := (List.mem_replicate.mp member).2
  subst trace
  exact supported event present

/-- Sign classification stays in the alphabet even for a zero-width word. -/
lemma signTrace_nativeSupported (width : Nat) :
    NativeTraceSupported width (signTrace (model := model) width) := by
  unfold signTrace
  split <;> simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

/-- Both magnitude arms have finite native support without a sign assumption. -/
lemma magnitudeTrace_nativeSupported (width : Nat) (negative : Bool) :
    NativeTraceSupported width (magnitudeTrace (model := model) width negative) := by
  cases negative <;> simp [magnitudeTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

/-- Every rounded-division formula uses only the independent original and widened coordinates. -/
lemma roundedDivBodyTrace_nativeSupported (width : Nat)
    (magnitudeNegative correctionNegative restoreNegative : Bool) :
    NativeTraceSupported width
      (RoundedDiv.bodyTrace (model := model) width magnitudeNegative correctionNegative
        restoreNegative) := by
  cases correctionNegative <;> cases restoreNegative <;>
    simp only [RoundedDiv.bodyTrace, Bool.false_eq_true, if_false, if_true,
      List.append_nil, nativeTraceSupported_append,
      and_assoc]
  all_goals refine ⟨signTrace_nativeSupported width,
    magnitudeTrace_nativeSupported width magnitudeNegative, ?_⟩
  all_goals simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord
