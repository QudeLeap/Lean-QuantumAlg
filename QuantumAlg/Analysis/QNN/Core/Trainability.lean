/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Trainability: exponential concentration and barren plateaus

The unifying notion behind **barren plateaus** [MBS+18, maintext.tex:91] and
**quantum-kernel concentration** [TWC+22, main-update.tex:658] is *exponential
concentration*: a quantity indexed by system size `n` (a loss, a gradient variance,
or a kernel value) deviates from a fixed value `μ` by at most `C / b ^ n` for some
`b > 1`. The practical consequence is that the quantity becomes exponentially
flat — it converges to `μ`, so resolving it requires exponentially many samples.

This module gives the definition and its convergence consequence, and records the
barren-plateau models on top of it in the `GroverModel`/`ParamShiftModel` style: the
hard Haar / `t`-design / Weingarten input (the variance bound) is bundled as a
hypothesis, and the trainability consequence is derived.

Sources: [MBS+18, maintext.tex:91,148]; [CSV+21, Arxiv_Final.tex:342];
[RBS+23, Arxiv_Final.tex:674-695]; [TWC+22, main-update.tex:655-667].
-/

section

namespace QuantumAlg

open Filter Topology

/-- **Exponential concentration.** `X n` deviates from `μ` by at most `C / b ^ n`
for some base `b > 1` [MBS+18, maintext.tex:91; TWC+22, main-update.tex:658]. -/
public def ExpConcentrated (X : ℕ → ℝ) (μ : ℝ) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |X n - μ| ≤ C / b ^ n

/-- An exponentially concentrated quantity converges to its concentration value:
the landscape becomes exponentially flat. -/
lemma ExpConcentrated.tendsto {X : ℕ → ℝ} {μ : ℝ} (h : ExpConcentrated X μ) :
    Filter.Tendsto X Filter.atTop (nhds μ) := by
  obtain ⟨b, hb, C, _, hbnd⟩ := h
  have key : Filter.Tendsto (fun n => C / b ^ n) Filter.atTop (nhds 0) := by
    have hbpow : Filter.Tendsto (fun n => b ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hb
    have hinv : Filter.Tendsto (fun n => (b ^ n)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hbpow
    simpa [div_eq_mul_inv] using hinv.const_mul C
  have hsq : Filter.Tendsto (fun n => |X n - μ|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbnd key
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using hsq

/-- A model has a **barren plateau** when its loss/gradient variance is
exponentially concentrated to `0` (so the trainable signal vanishes with system
size). -/
public def HasBarrenPlateau (variance : ℕ → ℝ) : Prop := ExpConcentrated variance 0

/-- Under a barren plateau the variance vanishes in the large-system limit. -/
lemma HasBarrenPlateau.variance_tendsto_zero {variance : ℕ → ℝ}
    (h : HasBarrenPlateau variance) :
    Filter.Tendsto variance Filter.atTop (nhds 0) :=
  h.tendsto

/-! ### Cost-function-dependent barren plateaus -/

/-- **Cost-function-dependent barren plateaus** [CSV+21, Arxiv_Final.tex:342]: a global cost
exhibits a barren plateau (exponentially concentrated gradient variance), whereas a
local cost is trainable (its gradient variance has a polynomial lower bound). -/
structure CostDependentBP where
  /-- Gradient variance of the global cost. -/
  globalVariance : ℕ → ℝ
  /-- Gradient variance of the local cost. -/
  localVariance : ℕ → ℝ
  /-- Positive normalization constant in the polynomial local lower bound. -/
  c : ℝ
  /-- The normalization constant is positive. -/
  c_pos : 0 < c
  /-- The global cost has a barren plateau. -/
  global_bp : HasBarrenPlateau globalVariance
  /-- The local cost keeps a polynomial lower bound, up to the positive prefactor `c`. -/
  local_lb : ∀ n : ℕ, 0 < n → c / (n : ℝ) ≤ localVariance n

/-- The global cost's gradient vanishes (barren plateau). -/
lemma CostDependentBP.global_tendsto_zero (M : CostDependentBP) :
    Filter.Tendsto M.globalVariance Filter.atTop (nhds 0) :=
  M.global_bp.variance_tendsto_zero

/-- The local cost's gradient variance stays strictly positive (trainable). -/
lemma CostDependentBP.local_pos (M : CostDependentBP) {n : ℕ} (hn : 0 < n) :
    0 < M.localVariance n :=
  lt_of_lt_of_le (div_pos M.c_pos (Nat.cast_pos.mpr hn)) (M.local_lb n hn)

/-! ### Quantum-kernel concentration -/

/-- **Quantum-kernel concentration** [TWC+22, main-update.tex:658]: the kernel value
concentrates exponentially to a fixed `κ₀`, so a polynomial number of measurement
shots cannot distinguish inputs (the model becomes input-independent).

This is the abstract deterministic-sequence form. The genuine probabilistic result —
a concrete quantum kernel whose data-averaged value provably concentrates exponentially,
derived from first principles with no Haar assumption — is
`QuantumAlg.QuantumKernelConcentration.main` in
`QuantumAlg/Primitives/QKernel/Concentration.lean`,
built on the probabilistic engine `QuantumAlg.ExpConcentratedProb`. -/
def KernelConcentration (kernel : ℕ → ℝ) (κ₀ : ℝ) : Prop := ExpConcentrated kernel κ₀

/-- A concentrated kernel converges to its concentration value. -/
lemma KernelConcentration.tendsto {kernel : ℕ → ℝ} {κ₀ : ℝ}
    (h : KernelConcentration kernel κ₀) :
    Filter.Tendsto kernel Filter.atTop (nhds κ₀) :=
  ExpConcentrated.tendsto h

/-! ### Geometric/equivariant QML trainability -/

/-- **Geometric/equivariant QML trainability** — the trainability counterpart of the Ragone DLA
variance law `Var = P_g(ρ)P_g(O)/dim(g)` [RBS+23, Arxiv_Final.tex:691]: a symmetry-structured model
(in the Geometric-QML sense) whose dynamical Lie algebra has only *polynomial* dimension keeps a
polynomial lower bound on its gradient variance, hence avoids a barren plateau. This is the generic
abstraction of that principle (a polynomial variance lower bound); it does not
re-derive the variance
law. -/
structure GeometricQMLTrainable where
  /-- Gradient variance. -/
  variance : ℕ → ℝ
  /-- Positive normalization constant in the polynomial lower bound. -/
  c : ℝ
  /-- The normalization constant is positive. -/
  c_pos : 0 < c
  /-- Polynomial degree of the lower bound. -/
  deg : ℕ
  /-- The variance is bounded below by `c / n ^ deg` (polynomial trainability). -/
  variance_lb : ∀ n : ℕ, 0 < n → c / (n : ℝ) ^ deg ≤ variance n

/-- A geometric/equivariant model with polynomial dynamical Lie algebra has strictly
positive (not exponentially vanishing) gradient variance: it is trainable. -/
lemma GeometricQMLTrainable.variance_pos (M : GeometricQMLTrainable) {n : ℕ}
    (hn : 0 < n) : 0 < M.variance n :=
  lt_of_lt_of_le (div_pos M.c_pos (pow_pos (Nat.cast_pos.mpr hn) M.deg))
    (M.variance_lb n hn)

end QuantumAlg

end
