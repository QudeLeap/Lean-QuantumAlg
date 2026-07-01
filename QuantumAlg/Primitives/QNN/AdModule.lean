/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.VarianceFormula
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The adjoint action of the dynamical Lie algebra on operator space

The dynamical Lie algebra `g = dynamicalLieAlgebra gens` acts on the operator space
`Matrix (Fin N) (Fin N) ℂ` by the **restricted adjoint action** `x • Y = ⁅x, Y⁆ = x*Y − Y*x`,
obtained by composing the canonical self-action of the ambient matrix Lie ring with the
subalgebra inclusion `g.incl`. This makes the operator space — and hence its tensor square
`g`-module — a genuine `LieModule`, the substrate on which the Ragone second-moment / commutant
argument lives.

`Matrix (Fin N) (Fin N) ℂ` is given a `LieRing` via `LieRing.ofAssociativeRing` (activated
locally, as elsewhere in the QNN development). The `g`-module structure here is built with
`LieRingModule.compLieHom` through that ring's *adjoint* self-action — the bracket resolves to the
commutator `x*Y − Y*x` (`ad_smul_eq`), not to a left-multiplication action.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped TensorProduct Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ} (gens : Set (Matrix (Fin N) (Fin N) ℂ))

/-- The dynamical Lie algebra acts on operator space by the restricted adjoint action
`x • Y = ⁅(x : M_N), Y⁆`, via `compLieHom` through the subalgebra inclusion. -/
@[reducible] noncomputable instance instAdLieRingModule :
    LieRingModule (dynamicalLieAlgebra gens) (Matrix (Fin N) (Fin N) ℂ) :=
  LieRingModule.compLieHom _ (dynamicalLieAlgebra gens).incl

/-- The restricted adjoint action is the genuine commutator `↑x * Y − Y * ↑x` — **not** the
left-multiplication (`•`-)action. This is the load-bearing check that the `g`-module is built on
the adjoint self-action of the matrix Lie ring. -/
theorem ad_bracket_eq (x : dynamicalLieAlgebra gens) (Y : Matrix (Fin N) (Fin N) ℂ) :
    ⁅x, Y⁆ = (x : Matrix (Fin N) (Fin N) ℂ) * Y - Y * (x : Matrix (Fin N) (Fin N) ℂ) := by
  change ⁅((dynamicalLieAlgebra gens).incl x : Matrix (Fin N) (Fin N) ℂ), Y⁆ = _
  rw [Ring.lie_def]
  rfl

/-- The adjoint action is `ℂ`-linear, making operator space a `LieModule` over `g`. -/
noncomputable instance instAdLieModule :
    LieModule ℂ (dynamicalLieAlgebra gens) (Matrix (Fin N) (Fin N) ℂ) :=
  LieModule.compLieHom _ _

/-- The tensor square of operator space is a `g`-module via the diagonal (coproduct) action,
inherited from Mathlib's tensor-product `LieModule` instance. This is the abstract carrier of
`g ⊗ g`; the concrete Kronecker-doubled carrier (where the Casimir `∑ⱼ Bⱼ ⊗ₖ Bⱼ` lives) and the
`projGG` projection onto it are built in the next layer. -/
example :
    LieModule ℂ (dynamicalLieAlgebra gens)
      (Matrix (Fin N) (Fin N) ℂ ⊗[ℂ] Matrix (Fin N) (Fin N) ℂ) :=
  inferInstance

/-! ## The concrete `g ⊗ g` carrier, the HS projection, and the doubled commutant

The Ragone second moment lives in the **concrete Kronecker-doubled space**
`D := Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ` — where the Casimir `∑ⱼ Bⱼ ⊗ₖ Bⱼ` lives — not the
abstract tensor product above. Here we build the objects WP-A freezes its interface on: the
`g ⊗ g` subspace, the Hilbert–Schmidt orthogonal projection onto it, the doubled adjoint action,
and the doubled `g`-commutant. The variance-relevant invariant space is `(g⊗g)^g`, the
intersection `adCommutantGG ⊓ gTensorG`. -/

variable {gens}

/-- The Hilbert–Schmidt linear functional `X ↦ ⟪A, X⟫ = Tr(Aᴴ X)`. -/
noncomputable def hsFunctional (A : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin N × Fin N) ℂ ℂ).comp (LinearMap.mulLeft ℂ Aᴴ)

theorem hsFunctional_apply (A X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    hsFunctional A X = hsInner A X := by
  simp only [hsFunctional, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Matrix.traceLinearMap_apply, hsInner]

/-- The `g ⊗ g` subspace of the doubled operator space: the span of the family `Bᵢ ⊗ₖ Bⱼ`. -/
noncomputable def gTensorG (b : DLAHermBasis gens) :
    Submodule ℂ (Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :=
  Submodule.span ℂ (Set.range fun p : Fin b.dim × Fin b.dim => b.B p.1 ⊗ₖ b.B p.2)

/-- The Hilbert–Schmidt **orthogonal projection onto `g ⊗ g`**, via the orthonormal family
`Bᵢ ⊗ₖ Bⱼ`: `projGG X = ∑ᵢⱼ ⟪Bᵢ⊗ₖBⱼ, X⟫ · (Bᵢ⊗ₖBⱼ)`. -/
noncomputable def projGG (b : DLAHermBasis gens) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ →ₗ[ℂ] Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  ∑ p : Fin b.dim × Fin b.dim,
    (hsFunctional (b.B p.1 ⊗ₖ b.B p.2)).smulRight (b.B p.1 ⊗ₖ b.B p.2)

theorem projGG_apply (b : DLAHermBasis gens) (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    projGG b X = ∑ p : Fin b.dim × Fin b.dim,
      hsInner (b.B p.1 ⊗ₖ b.B p.2) X • (b.B p.1 ⊗ₖ b.B p.2) := by
  simp only [projGG, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    hsFunctional_apply]

/-- The **doubled adjoint action** of `a` on the doubled space: `X ↦ ⁅a⊗ₖ1 + 1⊗ₖa, X⁆`, the
infinitesimal generator of the `U⊗U` conjugation for `U = exp(i a)`. -/
noncomputable def doubledAd (a : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ →ₗ[ℂ] Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  LinearMap.mulLeft ℂ (a ⊗ₖ 1 + 1 ⊗ₖ a) - LinearMap.mulRight ℂ (a ⊗ₖ 1 + 1 ⊗ₖ a)

/-- The **doubled `g`-commutant** on the doubled operator space: the `X` annihilated by the doubled
adjoint action of every basis element (equivalently, commuting with `U⊗U` for each `U = exp(iBⱼ)`).
The variance-relevant invariant space `(g⊗g)^g` is the restriction `adCommutantGG ⊓ gTensorG`. -/
noncomputable def adCommutantGG (b : DLAHermBasis gens) :
    Submodule ℂ (Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :=
  ⨅ j, LinearMap.ker (doubledAd (b.B j))

/-- The variance-relevant invariant subspace `(g⊗g)^g`: the doubled commutant intersected with the
`g⊗g` carrier. WP-A's hypothesis (H2) states this equals `span{Casimir}`. -/
noncomputable def gTensorGInvariant (b : DLAHermBasis gens) :
    Submodule ℂ (Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :=
  adCommutantGG b ⊓ gTensorG b

/-- **Doubled conjugation** by `U⊗U` on the doubled space: `X ↦ (U⊗ₖU) X (U⊗ₖU)ᴴ`. This is the
building block of the second-moment twirl; the ideal ad-twirl is the finite-design average of this
(WP-T1.4), landing in `adCommutantGG`. -/
noncomputable def doubledConj (U : Matrix (Fin N) (Fin N) ℂ)
    (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  (U ⊗ₖ U) * X * (U ⊗ₖ U)ᴴ

end QuantumAlg
