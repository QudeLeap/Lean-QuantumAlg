/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Basic

/-!
# Exact vector action of a finite operator chain

A fixed six-factor product combines its six vector equations and their
complex scalars. The proof treats the operators as abstract matrices, so
consumers can instantiate large circuit matrices without rewriting inside
their definitions. This is ordinary finite-dimensional linear algebra,
with no execution, resource or normalization assumptions.
-/

namespace QuantumAlg.HilbertOperator

/-- Six exact vector actions compose in matrix order, retaining every complex scalar. -/
lemma applyVec_six {R : Register} {A B C D E F : HilbertOperator R}
    {v₀ v₁ v₂ v₃ v₄ v₅ v₆ : HilbertVector R} {a b c d e f : ℂ}
    (first : applyVec A v₀ = a • v₁) (second : applyVec B v₁ = b • v₂)
    (third : applyVec C v₂ = c • v₃) (fourth : applyVec D v₃ = d • v₄)
    (fifth : applyVec E v₄ = e • v₅) (sixth : applyVec F v₅ = f • v₆) :
    applyVec (F * E * D * C * B * A) v₀ = (a * b * c * d * e * f) • v₆ := by
  simp only [mul_applyVec, first, applyVec_smul, second, third, fourth, fifth, sixth,
    smul_smul, mul_assoc]

end QuantumAlg.HilbertOperator
