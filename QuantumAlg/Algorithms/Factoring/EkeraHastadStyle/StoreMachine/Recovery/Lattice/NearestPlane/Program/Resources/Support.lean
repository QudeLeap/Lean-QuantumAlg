/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program.Resources
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Support

/-!
# Independent native coordinate budget for nearest plane

The three chronological phase formulas share the signed-arithmetic alphabet.
Each conditional contribution is handled separately from the other decisions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree

open Execution ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma third_supported (width : Nat)
    (denominator numerator magnitude correction restore : Bool) :
    NativeTraceSupported width
      (LatticeNearestPlaneThird.phaseTrace (model := model) width denominator numerator magnitude
        correction restore) := by
  have numeratorSupport : NativeTraceSupported (model := model) width
      (if numerator then
        [.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordUnary .complement width)),
          .classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordUnary .increment width))]
        else []) := by
    cases numerator <;> simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]
  simp only [LatticeNearestPlaneThird.phaseTrace, LatticeNearestPlaneThird.normalizationTrace,
    nativeTraceSupported_append, and_assoc]
  refine ⟨?_, signTrace_nativeSupported width, magnitudeTrace_nativeSupported width denominator,
    numeratorSupport, roundedDivBodyTrace_nativeSupported width magnitude correction restore, ?_⟩
  all_goals simp [LatticeNearestPlaneThird.prefixTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

private lemma secondPrefix_supported (width : Nat) :
    NativeTraceSupported width
      (LatticeNearestPlaneSecond.prefixTrace (model := model) width) := by
  simp [LatticeNearestPlaneSecond.prefixTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

private lemma second_supported (width : Nat) (magnitude correction restore : Bool) :
    NativeTraceSupported width
      (LatticeNearestPlaneSecond.phaseTrace (model := model) width magnitude correction
        restore) := by
  simp only [LatticeNearestPlaneSecond.phaseTrace, nativeTraceSupported_append]
  refine ⟨secondPrefix_supported width, ?_,
    roundedDivBodyTrace_nativeSupported width magnitude correction restore, ?_⟩
  all_goals simp [LatticeNearestPlaneSecond.numeratorTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

private lemma first_supported (width : Nat) (magnitude correction restore : Bool) :
    NativeTraceSupported width
      (LatticeNearestPlaneFirst.phaseTrace (model := model) width magnitude correction
        restore) := by
  simp only [LatticeNearestPlaneFirst.phaseTrace, nativeTraceSupported_append, and_assoc]
  refine ⟨?_, roundedDivBodyTrace_nativeSupported width magnitude correction restore, ?_⟩
  all_goals simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

/-- Every three-phase formula has finite native support independently of its eleven decisions. -/
lemma phaseTrace_nativeSupported (width : Nat) (denominatorNegative numeratorNegative : Bool)
    (thirdMagnitude thirdCorrection thirdRestore : Bool)
    (secondMagnitude secondCorrection secondRestore : Bool)
    (firstMagnitude firstCorrection firstRestore : Bool) :
    NativeTraceSupported width
      (phaseTrace (model := model) width denominatorNegative numeratorNegative
        thirdMagnitude thirdCorrection thirdRestore secondMagnitude secondCorrection secondRestore
        firstMagnitude firstCorrection firstRestore) := by
  simp only [phaseTrace, nativeTraceSupported_append]
  exact ⟨third_supported width denominatorNegative numeratorNegative thirdMagnitude thirdCorrection
    thirdRestore, second_supported width secondMagnitude secondCorrection secondRestore,
    first_supported width firstMagnitude firstCorrection firstRestore⟩

/-- Independent native coordinate allowance for all three original nearest-plane stages. -/
def eventEnvelope (width : Nat) : ResourcePool model := 128 • nativeAlphabet width

-- The generic accounting application elaborates the full dependent three-stage path.
set_option maxRecDepth 4096 in
/-- Every actual nearest-plane path satisfies the independent native coordinate allowance. -/
lemma threeInto_pool_le (refs : Refs ctx width) (path : (threeInto refs).Path) :
    (threeInto refs).resourcePool path ≤ eventEnvelope width := by
  refine ResourcePool.le_scaled_of_support_card_le
    ((threeInto refs).resourcePool path) (nativeAlphabet width) 128 ?_ ?_
  · intro event present
    change event ∈ (threeInto refs).eventTrace path at present
    rw [threeInto_events] at present
    exact phaseTrace_nativeSupported width _ _ _ _ _ _ _ _ _ _ _ event present
  · exact threeInto_eventCount_le refs path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree
