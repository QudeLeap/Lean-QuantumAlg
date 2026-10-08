/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights
import all QuantumAlg.Util.PMF.FiniteWeights
import all QuantumAlg.Util.PMF.VectorMass
import all QuantumAlg.Util.PMF.MapIndicator

/-!
# The finite Shor source weights are the original repeated PMF

The source outcomes are precisely the finite pairs of sampled bits and Born
results. Existing finite PMF map, bind and vector laws identify their scalar
weights with the original source distribution and its original independent
replication. This is a probability identity, not an execution premise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.SourceWeights

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def outcomeEquiv (N : Nat) :
    (Fin (2 ^ residueSamplingBits N) ×
      TerminalZMeasure.Outcome (phaseBits N)) ≃ SourceOutcome N where
  toFun pair := ⟨pair.1, pair.2⟩
  invFun outcome := (outcome.sample, outcome.measurement)
  left_inv _ := rfl
  right_inv outcome := by cases outcome; rfl

local instance {N : Nat} : Fintype (SourceOutcome N) :=
  Fintype.ofEquiv (Fin (2 ^ residueSamplingBits N) × TerminalZMeasure.Outcome (phaseBits N))
    (outcomeEquiv N)

private theorem one_eq {N : Nat} (source : Input N) (weight : SourceOutcome N → ℂ) :
    one source weight =
      ∑ outcome : SourceOutcome N,
        ((sourceOutcomePMF source outcome).toReal : ℂ) * weight outcome := by
  symm
  refine (PMF.sum_bind_toReal_mul
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N)))
    (fun sample => (sourceSampleOutcomePMF source sample).map
      (fun outcome => (⟨sample, outcome⟩ : SourceOutcome N))) weight).trans ?_
  change _ = ∑ sample : Fin (2 ^ residueSamplingBits N),
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
      ∑ outcome : TerminalZMeasure.Outcome (phaseBits N),
        weight ⟨sample, outcome⟩ * ((sourceSampleOutcomePMF source sample outcome).toReal : ℂ)
  apply Finset.sum_congr rfl
  intro sample _
  rw [PMF.sum_map_toReal_mul]
  have uniform :
      ((PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N)) sample).toReal : ℂ) =
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) := by
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Complex.ofReal_inv]
  rw [uniform]
  apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
  apply Finset.sum_congr rfl
  intro outcome _
  exact mul_comm _ _

private theorem batch_eq {N : Nat} (source : Input N) (count : Nat)
    (weight : (Fin count → SourceOutcome N) → ℂ) :
    batch source count weight =
      ∑ outcomes : List.Vector (SourceOutcome N) count,
        ((PMF.independentReplicateVector (sourceOutcomePMF source) count outcomes).toReal : ℂ) *
          weight outcomes.get := by
  induction count with
  | zero =>
      symm
      change (∑ outcomes : List.Vector (SourceOutcome N) 0,
        (((PMF.pure List.Vector.nil) outcomes).toReal : ℂ) * weight outcomes.get) =
          weight Fin.elim0
      rw [Finset.sum_eq_single List.Vector.nil]
      · simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, Complex.ofReal_one, one_mul]
        apply congrArg weight
        funext index
        exact Fin.elim0 index
      · intro outcomes _ different
        exact (different (Subsingleton.elim _ _)).elim
      · intro absent
        exact (absent (Finset.mem_univ _)).elim
  | succ count induction =>
      change one source (fun first => batch source count
        (fun rest => weight (Fin.cons first rest))) = _
      rw [one_eq]
      refine Eq.trans ?_
        (PMF.independentReplicateVector_weighted_cons (sourceOutcomePMF source) count
          (fun outcomes => weight outcomes.get)).symm
      apply Finset.sum_congr rfl
      intro first _
      apply congrArg (fun value : ℂ => ((sourceOutcomePMF source first).toReal : ℂ) * value)
      refine (induction (fun rest => weight (Fin.cons first rest))).trans ?_
      apply Finset.sum_congr rfl
      intro rest _
      apply congrArg (fun value : ℂ =>
        ((PMF.independentReplicateVector (sourceOutcomePMF source) count rest).toReal : ℂ) * value)
      apply congrArg weight
      funext index
      exact Fin.cases (List.Vector.get_cons_zero first rest).symm
        (fun index => (List.Vector.get_cons_succ first rest index).symm) index

/-- Characteristic source weights give the exact point mass of the original repeated-source map. -/
theorem batch_indicator {N : Nat} (source : Input N) (count : Nat)
    {Result : Type} [DecidableEq Result]
    (read : (Fin count → SourceOutcome N) → Result) (selected : Result) :
    batch source count (fun outcomes => if read outcomes = selected then 1 else 0) =
      (((PMF.independentReplicateVector (sourceOutcomePMF source) count).map
        (fun outcomes => read outcomes.get) selected).toReal : ℂ) := by
  refine (batch_eq source count
    (fun outcomes => if read outcomes = selected then 1 else 0)).trans ?_
  exact PMF.sum_toReal_map_indicator
    (PMF.independentReplicateVector (sourceOutcomePMF source) count)
    (fun outcomes => read outcomes.get) selected

end

end QuantumAlg.Factoring.ShorStyle.Canonical.SourceWeights
