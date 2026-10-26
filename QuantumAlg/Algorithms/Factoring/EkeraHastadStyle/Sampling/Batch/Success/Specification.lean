/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import Mathlib.Data.Set.Defs

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Util.BinomialTail

/-!
# Original conditional batch-success event and sampler-adjusted floor

Success means returning one of the two declared factors of the existing
proof-side RSA key. The raw fixed-source and uniformly sampled batch laws
already check every nonempty result; their support therefore satisfies this
declared event. The analytic floor retains the original sampler loss and
sixteen-sample feasible-pair floor.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess

noncomputable section

/-- The original same-source sixteen-measurement batch floor is at most one. -/
lemma sixteenSampleBatchFloor_le_one :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ) ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  norm_num [BinomialTail.sixteenSampleBatchFloor, BinomialTail.atLeastTwoOfSixteenAtOneEighth]

/-- The original one-batch floor includes the fixed-width sampler's exceptional mass. -/
def successFloor (bitWidth : Nat) : ENNReal :=
  (1 - ENNReal.ofReal (RSA.FixedWidthSampling.samplerFailureBound bitWidth)) *
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : ℝ)

/-- The sampler-adjusted conditional floor is a valid probability bound at every width. -/
lemma successFloor_le_one (bitWidth : Nat) : successFloor bitWidth ≤ 1 := by
  exact (mul_le_mul' (tsub_le_self :
    1 - ENNReal.ofReal (RSA.FixedWidthSampling.samplerFailureBound bitWidth) ≤ 1)
    sixteenSampleBatchFloor_le_one).trans_eq (one_mul 1)

/-- Successful raw batch outputs are exactly populated declared-factor values. -/
public def accepts {N : Nat} (model : GoodKeyModel N) : Set (Option Nat) :=
  {output | ∃ factor, output = some factor ∧
    (factor = model.semiprime.leftFactor ∨ factor = model.semiprime.rightFactor)}

/-- The empty optional value cannot satisfy the declared-factor event. -/
lemma not_accepts_none {N : Nat} (model : GoodKeyModel N) : none ∉ accepts model := by
  simp [accepts]

/-- A populated output is accepted exactly when its factor is one of the declared pair. -/
lemma accepts_some {N factor : Nat} (model : GoodKeyModel N) :
    some factor ∈ accepts model ↔
      factor = model.semiprime.leftFactor ∨ factor = model.semiprime.rightFactor := by
  simp [accepts]

/-- Every populated full recovery value is a declared factor of the original key model. -/
lemma batchValue_some_declared {N factor sampleCount : Nat} (model : GoodKeyModel N)
    {inputs : List.Vector (PreparedBatchSample N) sampleCount}
    (result : BatchRecovery.batchValue N (registerParameters N).m
      (registerParameters N).ell inputs = some factor) :
    factor = model.semiprime.leftFactor ∨ factor = model.semiprime.rightFactor := by
  have sound := BatchRecovery.batchValue_some_sound result
  exact model.semiprime.nontrivial_factor_eq_declared sound.1 sound.2.1 sound.2.2

/-- A supported populated fixed-source result is one of the two original declared factors. -/
lemma fixed_some_declared {N factor : Nat} (model : GoodKeyModel N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (supported : some factor ∈ (fixedBatchOutputPMF model.input sample).support) :
    factor = model.semiprime.leftFactor ∨ factor = model.semiprime.rightFactor := by
  have sound := fixedBatchOutputPMF_some_sound model.input sample supported
  exact model.semiprime.nontrivial_factor_eq_declared sound.1 sound.2.1 sound.2.2

/-- A supported populated uniformly sampled result is one of the original declared factors. -/
lemma sampled_some_declared {N factor : Nat} (model : GoodKeyModel N)
    (supported : some factor ∈ (sampledBatchOutputPMF model.input).support) :
    factor = model.semiprime.leftFactor ∨ factor = model.semiprime.rightFactor := by
  have sound := sampledBatchOutputPMF_some_sound model.input supported
  exact model.semiprime.nontrivial_factor_eq_declared sound.1 sound.2.1 sound.2.2

/-- On the original sampled law's support, success is exactly a populated output. -/
lemma sampled_accepts_iff_ne_none {N : Nat} (model : GoodKeyModel N)
    (output : Option Nat) (supported : output ∈ (sampledBatchOutputPMF model.input).support) :
    output ∈ accepts model ↔ output ≠ none := by
  cases output with
  | none => simp only [not_accepts_none, ne_eq, not_true_eq_false]
  | some factor =>
      exact iff_of_true ((accepts_some model).mpr (sampled_some_declared model supported))
        (Option.some_ne_none factor)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchSuccess
