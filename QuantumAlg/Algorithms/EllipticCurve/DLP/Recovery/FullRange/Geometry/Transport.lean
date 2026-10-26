/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Geometry

/-!
# Equal-width transport of full-range source effects

The original positive contractive effect retains its complete coherent quadratic form.
The transport uses only equality of widths and preserves arbitrary raw Reference vectors.
-/

namespace QuantumAlg.EllipticCurve.FullRange.Geometry

noncomputable section

open scoped BigOperators

/-- The same positive contractive effect in equal-width source coordinates. -/
def widthEffect {before after : Nat} (widths : before = after)
    {Reference : Register}
    (effect : Effect ((branchRegister after).prod Reference)) :
    Effect ((branchRegister before).prod Reference) := by
  cases widths
  exact effect

/-- Equal-width transport preserves every raw finite-family quadratic form. -/
lemma widthEffect_family_quadratic {before after : Nat} (widths : before = after)
    {Family : Type} [Fintype Family]
    (input : Family → Branch before) (amplitude : Family → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (effect : Effect ((branchRegister after).prod Reference)) :
    HilbertOperator.quadraticWeight (widthEffect widths effect).matrix
        (∑ branch : Family, ∑ ref : Reference.Index,
          (amplitude branch * reference ref) •
            (NormalizedVector.ket
              (R := (branchRegister before).prod Reference)
              (input branch, ref)).vec) =
      HilbertOperator.quadraticWeight effect.matrix
        (∑ branch : Family, ∑ ref : Reference.Index,
          (amplitude branch * reference ref) •
            (NormalizedVector.ket
              (R := (branchRegister after).prod Reference)
              ((Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths) (input branch).1,
                Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths)
                  (input branch).2), ref)).vec) := by
  cases widths
  rfl

/-- Equal-width transport preserves the complete normalized source weight. -/
lemma widthEffect_sourceState_weight {before after : Nat} (widths : before = after)
    {Reference : Register} (reference : NormalizedVector Reference)
    (effect : Effect ((branchRegister after).prod Reference)) :
    (widthEffect widths effect).weight
        (DensityOperator.ofPure (sourceState before reference)) =
      effect.weight
        (DensityOperator.ofPure
          (sourceState after reference)) := by
  cases widths
  rfl

end

end QuantumAlg.EllipticCurve.FullRange.Geometry
