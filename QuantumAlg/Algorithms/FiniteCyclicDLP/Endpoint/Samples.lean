/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Distribution

/-!
# Reversible mathematical observation of the original raw sample cells

Each retained two-valued cell has exactly one original Boolean value. The
inverse below only relates value carriers; it introduces no runtime packing,
copying, storage or classical event. Ordered vectors preserve every sample.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open GateLevelAttempt.Native (sampleWidth)

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The original bit string determines every two-valued cell of the same raw sample. -/
def rawSample (P : KnownOrderProblem G) (outcome : Fin (sampleWidth P) → Bool) :
    (CShape.fixedVector (sampleWidth P) (.finite 2)).Value :=
  .fixedVector fun index => .finite (if outcome index then 1 else 0)

/-- Reading the inverse value recovers exactly the original ordered bit string. -/
theorem observed_rawSample (P : KnownOrderProblem G) (outcome : Fin (sampleWidth P) → Bool) :
    GateLevelAttempt.Native.observedOutcome P (rawSample P outcome) = outcome := by
  funext index
  cases value : outcome index <;>
    simp only [GateLevelAttempt.Native.observedOutcome, rawSample, CShape.Value.get,
      CShape.Value.toFin, value, Bool.false_eq_true, if_false, if_true]
  all_goals rfl

/-- Every actual finite sample is recovered, including both possible values in every cell. -/
theorem rawSample_observed (P : KnownOrderProblem G)
    (value : (CShape.fixedVector (sampleWidth P) (.finite 2)).Value) :
    rawSample P (GateLevelAttempt.Native.observedOutcome P value) = value := by
  cases value with
  | fixedVector values =>
      dsimp only [rawSample]
      congr 1
      funext index
      cases observed : values index with
      | finite number =>
          fin_cases number <;>
            simp only [GateLevelAttempt.Native.observedOutcome, CShape.Value.get,
              CShape.Value.toFin, observed]
          all_goals rfl

/-- The ordered original vector determines precisely the entire retained finite sample value. -/
def rawSamples (P : KnownOrderProblem G) (count : Nat)
    (outcomes : List.Vector (Fin (sampleWidth P) → Bool) count) :
    (CShape.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))).Value :=
  .fixedVector fun index => rawSample P (outcomes.get index)

/-- The complete mathematical observation preserves the original vector and its ordering. -/
theorem observed_rawSamples (P : KnownOrderProblem G) (count : Nat)
    (outcomes : List.Vector (Fin (sampleWidth P) → Bool) count) :
    GateLevelAttempt.Native.Batch.observedVector P count (rawSamples P count outcomes) =
      outcomes := by
  apply List.Vector.ext
  intro index
  simp only [GateLevelAttempt.Native.Batch.observedVector, List.Vector.get_ofFn,
    rawSamples, CShape.Value.get, observed_rawSample]

/-- The inverse observation retains all finite cells, with no discarded or added sample. -/
theorem rawSamples_observed (P : KnownOrderProblem G) (count : Nat)
    (value : (CShape.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))).Value) :
    rawSamples P count (GateLevelAttempt.Native.Batch.observedVector P count value) = value := by
  cases value with
  | fixedVector values =>
      dsimp only [rawSamples]
      congr 1
      funext index
      simpa only [GateLevelAttempt.Native.Batch.observedVector, List.Vector.get_ofFn,
        CShape.Value.get] using rawSample_observed P (values index)

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
