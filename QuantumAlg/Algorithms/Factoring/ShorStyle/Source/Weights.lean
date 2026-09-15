/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Distribution

/-!
# Finite reference weights of the original Shor source law

The coefficients below are the original uniform source draw and its selected
Born probabilities. Finite repetition integrates a weight against those fixed
source laws in order. This is source mathematics: no execution, resource
witness or caller-supplied distribution occurs in its definitions.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.SourceWeights

noncomputable section

/-- A scalar weight integrated against the original uniform draw and conditional Born law. -/
def one {N : Nat} (source : Input N) (weight : SourceOutcome N → ℂ) : ℂ :=
  ∑ sample : Fin (2 ^ residueSamplingBits N),
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
      ∑ outcome : OrderFinding.Outcome (phaseBits N),
        weight ⟨sample, outcome⟩ * ((sourceSampleOutcomePMF source sample outcome).toReal : ℂ)

/-- The ordered finite product of exactly the same original source law. -/
def batch {N : Nat} (source : Input N) :
    (count : Nat) → ((Fin count → SourceOutcome N) → ℂ) → ℂ
  | 0, weight => weight Fin.elim0
  | count + 1, weight => one source
      (fun first => batch source count (fun rest => weight (Fin.cons first rest)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.SourceWeights
