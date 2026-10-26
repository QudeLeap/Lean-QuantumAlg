/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Forward

/-!
# The unchanged native source prefix behind a moving-flag traversal

The actual traversal is identified with the literal ordered source gates.
The original conjunction wire is restored, including when the source word
has an arbitrary dirty complement. This equation is the native boundary
used to compare the six stages against their arithmetic specification.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Exactly the original source instructions below the selected public boundary. -/
def prefixGates (width : Nat) (stage : Stage) (count : Nat) :
    List (GateSpec (encoding width)) :=
  (List.range count).flatMap (source width stage)

private lemma source_flag (width : Nat) (stage : Stage) (index : Nat) (state : Data width) :
    flagEquiv width (GateSpec.stepList (source width stage index) state) =
      (baseAction width stage index (flagEquiv width state).1,
        (flagEquiv width state).2) := by
  have actual := source_flagEquiv width stage index
    (flagEquiv width state).1 (flagEquiv width state).2
  simpa only [Prod.eta, Equiv.symm_apply_apply] using actual

/-- The finite source word acts on the full base and retains the same physical flag. -/
lemma prefixGates_flagEquiv (width : Nat) (stage : Stage) (count : Nat) (state : Data width) :
    flagEquiv width (GateSpec.stepList (prefixGates width stage count) state) =
      (ThresholdStream.word (baseAction width stage) count (flagEquiv width state).1,
        (flagEquiv width state).2) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prefixGates, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        GateSpec.stepList_append]
      rw [source_flag]
      change (baseAction width stage count
        (flagEquiv width (GateSpec.stepList (prefixGates width stage count) state)).1,
          (flagEquiv width (GateSpec.stepList (prefixGates width stage count) state)).2) = _
      rw [ih]
      simp only [ThresholdStream.word, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

/-- The real forward circuit executes the literal native prefix under the retained Ctrl. -/
lemma forwardProgram_apply_nativePrefix (width : Nat) (positive : 1 ≤ width) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (forwardProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          GateSpec.stepList (prefixGates width stage (state.2.1.toNat + 1)) state
          else state))) := by
  have actual := forwardProgram_apply_prefix width positive stage environment state
    clean zero within
  have output : (flagEquiv width).symm
      (if state.1.control then
        ThresholdStream.word (baseAction width stage) (state.2.1.toNat + 1)
          (flagEquiv width state).1 else (flagEquiv width state).1, false) =
      (if state.1.control then
        GateSpec.stepList (prefixGates width stage (state.2.1.toNat + 1)) state else state) := by
    apply (flagEquiv width).injective
    rw [Equiv.apply_symm_apply]
    split
    · rw [prefixGates_flagEquiv]
      exact Prod.ext rfl zero.symm
    · exact Prod.ext rfl zero.symm
  rw [output] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
