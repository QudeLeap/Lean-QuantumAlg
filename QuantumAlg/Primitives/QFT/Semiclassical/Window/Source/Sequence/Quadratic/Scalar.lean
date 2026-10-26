/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Quadratic

/-!
# Zero and scalar laws for complete actual outcome sums

These identities follow from the certified complete coherent observation.
They retain every real record and path and apply to raw vectors without a
normalization premise.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source.Stage

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}
  (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
    services).Environment)
  (stages : List (Stage ctx operations services Reference))
  (certificates : Certificates environment stages)
  {History : Type} [Finite History]
  (effects : Circuit.EffectFamily ctx Reference (services.HiddenState × Records stages History))
  (original : Store ctx × (services.HiddenState × History))

/-- An impossible complete vector contributes zero to the actual recursive sum. -/
lemma quadraticSum_zero : quadraticSum environment stages certificates effects original 0 = 0 := by
  rw [← window_sourceSequence_quadratic]
  simp [HilbertOperator.quadraticWeight]

/-- A common scalar retains its squared norm through the full remaining actual observation. -/
lemma quadraticSum_smul (scalar : ℂ) (vector : HilbertVector (ctx.register.prod Reference)) :
    quadraticSum environment stages certificates effects original (scalar • vector) =
      ‖scalar‖ ^ 2 * quadraticSum environment stages certificates effects original vector := by
  rw [← window_sourceSequence_quadratic, ← window_sourceSequence_quadratic]
  unfold HilbertOperator.quadraticWeight
  rw [HilbertOperator.applyVec_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source.Stage
