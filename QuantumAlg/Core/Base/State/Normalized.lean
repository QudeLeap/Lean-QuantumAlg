/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.State.Basic
import all QuantumAlg.Core.Base.State.Basic

/-!
# Metadata-free normalized vectors

`NormalizedVector R` carries only the mathematical invariant `‖ψ‖ = 1`.  It has
no physical placement or preparation cost and deliberately has no additive or
arbitrary scalar-action structure, since those operations do not preserve norm one.
-/

section

namespace QuantumAlg

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- A unit vector over a finite register, with no preparation metadata. -/
public structure NormalizedVector (R : Register) where
  private mk ::
  /-- Underlying raw Hilbert-space vector. -/
  vec : HilbertVector R
  /-- The vector has norm one. -/
  norm_eq_one : ‖vec‖ = 1

namespace NormalizedVector

noncomputable section

variable {R : Register}

instance : Coe (NormalizedVector R) (HilbertVector R) := ⟨NormalizedVector.vec⟩
instance : CoeTail (NormalizedVector R) (HilbertVector R) := ⟨NormalizedVector.vec⟩
instance : CoeOut (NormalizedVector R) (HilbertVector R) := ⟨NormalizedVector.vec⟩

instance : CoeFun (NormalizedVector R) (fun _ => R.Index → ℂ) :=
  ⟨fun ψ => ψ.vec⟩

instance : Norm (NormalizedVector R) :=
  ⟨fun ψ => ‖(ψ : HilbertVector R)‖⟩

instance : Inner ℂ (NormalizedVector R) :=
  ⟨fun ψ φ => inner ℂ (ψ : HilbertVector R) (φ : HilbertVector R)⟩

instance : HAdd (NormalizedVector R) (NormalizedVector R) (HilbertVector R) :=
  ⟨fun ψ φ => (ψ : HilbertVector R) + (φ : HilbertVector R)⟩

instance : HSub (NormalizedVector R) (NormalizedVector R) (HilbertVector R) :=
  ⟨fun ψ φ => (ψ : HilbertVector R) - (φ : HilbertVector R)⟩

instance : HSMul ℂ (NormalizedVector R) (HilbertVector R) :=
  ⟨fun c ψ => c • (ψ : HilbertVector R)⟩

/-- Certify a raw vector once its norm-one proof is available. -/
@[expose] public def ofVector (vec : HilbertVector R)
    (norm_eq_one : ‖vec‖ = 1) : NormalizedVector R where
  vec := vec
  norm_eq_one := norm_eq_one

@[simp]
public lemma coe_ofVector (vec : HilbertVector R) (h : ‖vec‖ = 1) :
    ((ofVector vec h : NormalizedVector R) : HilbertVector R) = vec := rfl

/-- Normalize a nonzero raw vector.  The nonzero hypothesis is required because
the zero vector has no norm-one representative obtained by scalar rescaling. -/
def ofNeZero (vec : HilbertVector R) (hvec : vec ≠ 0) : NormalizedVector R :=
  ofVector ((‖vec‖ : ℂ)⁻¹ • vec) (by
    rw [norm_smul, norm_inv, Complex.norm_of_nonneg (norm_nonneg vec),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvec)])

/-- Rescaling `ofNeZero` by the original norm reconstructs the raw vector. -/
lemma norm_smul_coe_ofNeZero (vec : HilbertVector R) (hvec : vec ≠ 0) :
    (‖vec‖ : ℂ) • (ofNeZero vec hvec : HilbertVector R) = vec := by
  unfold ofNeZero
  rw [coe_ofVector, smul_smul]
  have hnorm : (‖vec‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hvec
  rw [mul_inv_cancel₀ hnorm, one_smul]

@[ext]
lemma ext {ψ φ : NormalizedVector R} (hvec : ∀ i, ψ i = φ i) : ψ = φ := by
  have hv : ψ.vec = φ.vec := by
    apply WithLp.ofLp_injective
    funext i
    exact hvec i
  cases ψ
  cases φ
  cases hv
  rfl

/-- Computational-basis ket as a metadata-free normalized vector. -/
public def ket (x : R.Index) : NormalizedVector R :=
  ofVector (PiLp.single 2 x 1) (by simp)

@[simp]
public lemma ket_apply (x i : R.Index) :
    ket x i = if i = x then 1 else 0 := by
  simp [ket]

lemma ket_injective : Function.Injective (ket (R := R)) := by
  intro x y hxy
  by_contra hne
  have h := congrArg (fun ψ : NormalizedVector R => ψ x) hxy
  rw [ket_apply, ket_apply, if_pos rfl, if_neg hne] at h
  exact one_ne_zero h

@[simp]
lemma norm_ket (x : R.Index) : ‖(ket x : HilbertVector R)‖ = 1 :=
  (ket x).norm_eq_one

end

end NormalizedVector

end QuantumAlg

end
