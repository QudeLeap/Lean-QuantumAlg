/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Cardinality

/-!
# Original numerical ceiling for actual three-cell recovery

The real finite-bit decoder, original scaling preparation, checked inverse,
selected recovery and three chronological copies are counted explicitly.
No optional pack is executed here; the batch allocates and packs it later.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular NumberTheory.Checked.Native

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original coordinatewise final-negation allowance has at most five instructions. -/
theorem preparationFinalEnvelope_card_le (kind : ProblemKind) (width : Nat) :
    (preparationFinalEnvelope kind width).card ≤ 5 := by
  have branches := Multiset.card_le_card (Multiset.union_le_add
    (ResourcePool.ofList (negateEvents kind width true))
    (ResourcePool.ofList (negateEvents kind width false)))
  change (ResourcePool.max _ _).card ≤ 4 at branches
  unfold preparationFinalEnvelope
  rw [Multiset.card_add]
  change 1 + _ ≤ 5
  omega

/-- All original preparation phases fit a width-linear actual instruction allowance. -/
theorem preparationEnvelope_card_le (kind : ProblemKind) (spec : ModulusSpec width) :
    (preparationEnvelope kind spec).card ≤ 8 * width + 17 := by
  have loaded := ConstantWord.constantLoader_length_le kind (width + 1) spec.modulus
  have finalization := preparationFinalEnvelope_card_le kind width
  unfold preparationEnvelope
  simp only [Multiset.card_add, measuredDecodeEnvelope, TerminalDecode.envelope,
    TerminalDecode.bitEnvelope, ResourcePool.scale, ResourcePool.singleton,
    Multiset.card_nsmul, Multiset.card_replicate, ResourcePool.ofList,
    Multiset.coe_card, Word.Split.splitTrace, Word.Split.shiftTrace,
    preparationSeedEvents, Word.PowerOfTwo.shiftTrace, scaleBodyEvents,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

/-- The real selected recovery emits its eight operations and three original caller copies. -/
theorem selectedExposureEvents_length (kind : ProblemKind) (width : Nat) (selected : Bool) :
    (selectedExposureEvents kind width selected).length = if selected then 11 else 3 := by
  cases selected <;> rfl

/-- The actual complete raw-recovery allowance retains the original numerical ceiling. -/
theorem singleExposureEnvelope_card_le (kind : ProblemKind) (spec : ModulusSpec width) :
    (singleExposureEnvelope kind spec).card ≤ 42 * width + 103 := by
  have preparation := preparationEnvelope_card_le kind spec
  have checked := checkedInverseEnvelope_card_le kind spec
  unfold singleExposureEnvelope checkedExposureEnvelope
  simp only [Multiset.card_add, ResourcePool.ofList, Multiset.coe_card,
    selectedExposureEvents_length, if_true]
  omega

/-- Every actual three-cell recovery trace obeys that same original numerical ceiling. -/
theorem singleIntoCells_eventCount_le (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (path : (singleIntoCells spec input inverseSuccess candidate reconstruction).Path) :
    ((singleIntoCells spec input inverseSuccess candidate reconstruction).eventTrace path).length ≤
      42 * width + 103 :=
  (Multiset.card_le_card
    (singleIntoCells_pool_le spec input inverseSuccess candidate reconstruction path)).trans
      (singleExposureEnvelope_card_le kind spec)

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
