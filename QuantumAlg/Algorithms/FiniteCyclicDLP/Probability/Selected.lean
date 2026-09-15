/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
import Mathlib.Data.ZMod.Basic

/-!
# Selected finite-cyclic Fourier outcomes

The original unit-indexed family and its positive numerical floor depend
only on the known-order group and the mathematical secret witness. The
circuit-specific Born lower bound is proved separately.
-/

namespace QuantumAlg

open scoped BigOperators

noncomputable section

namespace FiniteCyclicDLP.Canonical.Probability

universe u

variable {G : Type u} [Group G]

/-- Distinguished zero residue of the known-order group. -/
def zeroResidue (P : KnownOrderProblem G) : Fin P.order :=
  ⟨0, P.order_pos⟩


/-- Uniform numerical floor contributed by each group-element tail to a
selected raw terminal outcome. -/
def selectedTailPointwiseLowerBound
    (P : KnownOrderProblem G) : ENNReal :=
  ENNReal.ofReal (1 / (4 * (fourierModulus P : ℝ) ^ 2))

/-- Uniform numerical floor for each selected raw terminal outcome, obtained
by summing the `r` distinct group-element tails. -/
def selectedRawOutcomePointwiseLowerBound
    (P : KnownOrderProblem G) : ENNReal :=
  P.order • selectedTailPointwiseLowerBound P

/-- Finite family of raw outcomes selected by invertible residues. -/
def selectedRawOutcomeFamily (P : KnownOrderProblem G)
    (input : SecretInput P) : Finset (BornBridge.Outcome P) :=
  letI : NeZero P.order := ⟨P.order_ne_zero⟩
  Finset.univ.image (selectedRawOutcome P input)

theorem selectedRawOutcomeFamily_card (P : KnownOrderProblem G)
    (input : SecretInput P) :
    (selectedRawOutcomeFamily P input).card = Nat.totient P.order := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  rw [selectedRawOutcomeFamily,
    Finset.card_image_of_injective _ (selectedRawOutcome_injective P input),
    Finset.card_univ, ZMod.card_units_eq_totient]

/-- Explicit one-attempt floor obtained by summing the pointwise bound over
all invertible raw Fourier residues. -/
def selectedRawOutcomeFamilyLowerBound (P : KnownOrderProblem G) : ENNReal :=
  letI : NeZero P.order := ⟨P.order_ne_zero⟩
  Fintype.card (ZMod P.order)ˣ • selectedRawOutcomePointwiseLowerBound P

/-- The selected-family floor is positive for every positive known order. -/
theorem selectedRawOutcomeFamilyLowerBound_pos (P : KnownOrderProblem G) :
    0 < selectedRawOutcomeFamilyLowerBound P := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  unfold selectedRawOutcomeFamilyLowerBound
    selectedRawOutcomePointwiseLowerBound selectedTailPointwiseLowerBound
  have hcard : 0 < Fintype.card (ZMod P.order)ˣ := Fintype.card_pos
  have hmodulus : (0 : ℝ) < fourierModulus P := by
    unfold fourierModulus
    positivity
  exact nsmul_pos
    (nsmul_pos
      (ENNReal.ofReal_pos.2 (by positivity)) P.order_ne_zero)
    (Nat.ne_of_gt hcard)

end FiniteCyclicDLP.Canonical.Probability

end

end QuantumAlg
