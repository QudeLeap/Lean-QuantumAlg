/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Born
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Geometry.Transport

/-!
# Full-range floor for branch-dependent addition schedules

Any actual effect agreeing with the certified complete cyclic Fourier experiment
on its coherent admissible component inherits its strict-window floor. The exceptional
mass uses the supplied branch-dependent selected addends on every physical
branch. A window implementation must supply its own agreement certificate,
including the zero address; no old bitwise good-seed certificate is reused.
-/

namespace QuantumAlg.EllipticCurve.FullRange

noncomputable section

open QuantumAlg.Execution
open PrimeFieldShortWeierstrass FiniteCyclicDLP ECDLP.Measured
open FiniteCyclicDLP.Canonical.Probability (SecretInput)

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The full-q floor transfers through equality on the original coherent good
vector, without requiring an entrywise comparison of the two effects. -/
lemma fullRange_effect_lower_of_good_weight (problem : KnownOrderProblem E.GroupPoint)
    [NeZero problem.order] (seed : AffinePoint E) (input : SecretInput problem)
    (oversampling : 16 * problem.order ≤ 2 ^ orderWidth problem)
    (steps : Nat) (selected : Branch (orderWidth problem) → Fin steps → Bool)
    (addend : Branch (orderWidth problem) → Fin steps → E.GroupPoint)
    {Reference : Register} (reference : NormalizedVector Reference)
    (actual : Effect ((idealBranchRegister problem).prod Reference))
    (agrees :
      actual.weight (DensityOperator.ofSubnormalizedVector
        (Geometry.goodVector (orderWidth problem) steps selected addend
          seed.toGroupPoint reference)
        (Geometry.goodVector_norm_le_one (orderWidth problem) steps selected addend
          seed.toGroupPoint reference)) =
      (idealBranchEffect problem seed (recoverableExponentEvent problem input) Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (Geometry.goodVector (orderWidth problem) steps selected addend
            seed.toGroupPoint reference)
          (Geometry.goodVector_norm_le_one (orderWidth problem) steps selected addend
            seed.toGroupPoint reference))) :
    (55 : ℝ) / 64 - 1 / problem.order -
        4 * Real.sqrt
          (exceptionalMass (orderWidth problem) steps selected addend seed.toGroupPoint) ≤
      actual.weight
        (DensityOperator.ofPure (Geometry.sourceState (orderWidth problem) reference)) := by
  let ideal := idealBranchEffect problem seed (recoverableExponentEvent problem input) Reference
  have comparison := Geometry.effect_weight_le_add_four_sqrt (orderWidth problem) steps selected
    addend seed.toGroupPoint reference actual ideal agrees
  have lower := (idealRecoverableMass_ge (orderWidth problem) (0 : ZMod problem.order)
    input.secret oversampling).trans
    (idealBranchEffect_recoverable_lower problem seed input reference)
  exact sub_le_iff_le_add.mpr (lower.trans comparison)

/-- The coherent good-weight floor transports through an explicit width equality,
keeping every branch family and source register at that same width. -/
lemma fullRange_effect_lower_of_good_weight_at_width
    (problem : KnownOrderProblem E.GroupPoint) [NeZero problem.order]
    (width : Nat) (same : width = orderWidth problem)
    (seed : AffinePoint E) (input : SecretInput problem)
    (oversampling : 16 * problem.order ≤ 2 ^ orderWidth problem)
    (steps : Nat) (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → E.GroupPoint)
    {Reference : Register} (reference : NormalizedVector Reference)
    (actual : Effect ((Geometry.branchRegister width).prod Reference))
    (agrees : actual.weight (DensityOperator.ofSubnormalizedVector
        (Geometry.goodVector width steps selected addend
          seed.toGroupPoint reference)
        (Geometry.goodVector_norm_le_one width steps selected addend
          seed.toGroupPoint reference)) =
      (Geometry.widthEffect same
        (idealBranchEffect problem seed
          (recoverableExponentEvent problem input) Reference)).weight
        (DensityOperator.ofSubnormalizedVector
          (Geometry.goodVector width steps selected addend
            seed.toGroupPoint reference)
          (Geometry.goodVector_norm_le_one width steps selected addend
            seed.toGroupPoint reference))) :
    (55 : ℝ) / 64 - 1 / problem.order -
        4 * Real.sqrt
          (exceptionalMass width steps selected addend seed.toGroupPoint) ≤
      actual.weight
        (DensityOperator.ofPure
          (Geometry.sourceState width reference)) := by
  cases same
  exact fullRange_effect_lower_of_good_weight problem seed input
    oversampling steps selected addend reference actual agrees

/-- Exact full-q source amplitudes transfer the ideal strict-window floor to
any certified actual effect for the supplied branch-dependent addition schedule. -/
lemma fullRange_effect_lower (problem : KnownOrderProblem E.GroupPoint)
    [NeZero problem.order] (seed : AffinePoint E) (input : SecretInput problem)
    (oversampling : 16 * problem.order ≤ 2 ^ orderWidth problem)
    (steps : Nat) (selected : Branch (orderWidth problem) → Fin steps → Bool)
    (addend : Branch (orderWidth problem) → Fin steps → E.GroupPoint)
    {Reference : Register} (reference : NormalizedVector Reference)
    (actual : Effect ((idealBranchRegister problem).prod Reference))
    (agrees : ∀ left right : ((idealBranchRegister problem).prod Reference).Index,
      left.1 ∈ admissibleBranches (orderWidth problem) steps selected addend seed.toGroupPoint →
      right.1 ∈ admissibleBranches (orderWidth problem) steps selected addend seed.toGroupPoint →
      actual.matrix left right =
        (idealBranchEffect problem seed (recoverableExponentEvent problem input) Reference).matrix
          left right) :
    (55 : ℝ) / 64 - 1 / problem.order -
        4 * Real.sqrt
          (exceptionalMass (orderWidth problem) steps selected addend seed.toGroupPoint) ≤
      actual.weight
        (DensityOperator.ofPure (Geometry.sourceState (orderWidth problem) reference)) := by
  let ideal := idealBranchEffect problem seed (recoverableExponentEvent problem input) Reference
  have good := Geometry.goodVector_weight_eq_of_matrix (orderWidth problem) steps selected addend
    seed.toGroupPoint reference actual ideal agrees
  exact fullRange_effect_lower_of_good_weight problem seed input oversampling steps selected
    addend reference actual good

end

end QuantumAlg.EllipticCurve.FullRange
