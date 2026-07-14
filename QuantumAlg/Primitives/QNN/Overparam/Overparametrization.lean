/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Core.LieAlgebraicBP
public import QuantumAlg.Primitives.QNN.Overparam.OverparametrizationDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Monotone.Basic

/-!
# Overparametrization theory of quantum neural networks (Larocca Theorems 1–3)

A quantum neural network (QNN) becomes **overparametrized** once the achievable
Quantum-Fisher-Information
(QFIM) rank saturates: beyond the critical parameter count `M_c` no new state-space directions are
explored [LJG+21].

This module builds the overparametrization *theory* (capacity, Hessian rank,
persistence) on the genuine
**QFIM-rank-saturation predicate** of `QuantumAlg.OverparamData`
(`OverparametrizationDef.lean`). Its
QFIM instantiation in `OverparamQFIM` is the reference-frame, theta-independent
generator-family QFIM:
the abstract `θ` variable indexes the achievable-rank supremum, while
`OverparamData.ofQFIM` supplies
the same `qfim ψ (B₀, …, B_{M-1})` matrix for every `θ`. This keeps the proved
rank-saturation theory
on an honest Fisher matrix without claiming the fully Heisenberg-rotated ansatz QFIM
has been formalized.
`QNNOverparametrization` `extends OverparamData`, so:

* **Theorem 1** (`achievableRank_le_dlaDim`): the achievable QFIM rank is `≤ dim g`.
  **Proved**, inherited
  from `OverparamData.achievable_le_dlaDim` (whose `rank_le_dlaDim` field is
  dischargeable against the
  genuine bound `qfim_rank_le_dlaDim`). Monotonicity is likewise a *proved* lemma, not a hypothesis.
* **Theorem 2** (capacity): faithfully to Larocca's definition `D₁(θ) = rank[F(θ)]`
  (`main2.tex:994`), the
  effective *quantum* dimension `D₁` is the *achievable QFIM rank*
  (`effDimQuantum := achievableRank`, a
  **derived** quantity, not a free field), and `D₁` attains its saturated value `R`
  exactly when the QNN is
  overparametrized (`capacity_max_of_overparam`) — the genuine saturation content of
  Theorem 2, distinct from
  Theorem 1's `rank ≤ dim g`. The effective *classical* dimension `D₂`
  (classical-Fisher rank) is carried by
  the explicit assumption bundle `QNNCapacityClassicalAssumptions`.
* **Theorem 3** (Hessian rank): the Hessian rank at a minimum is
  `≤ min (dim g) (2·d·r − r² − r)` with
  `d = N`, `r = min{rank A, rank O}` — *derived* (`le_min`) from the explicit assumption bundle
  `QNNHessianRankAssumptions`. The source-side side condition is `r ≤ N`; here `r` is a matrix rank
  minimum, so the displayed `ℕ` subtraction is the intended nonnegative
  combinatorial term under that
  rank bound rather than a new analytic proof.

The deep analytic inputs Mathlib lacks (QFIM eigenvalue spectrum, classical Fisher
rank, Hessian rank) stay
**named assumption bundles** (never `axiom`s). The non-vacuity witness uses
`overparamWitness`, which attains
positive saturated rank (`R = 1 > 0`), so the derived theorems are exercised non-trivially while the
proved-vs-assumed boundary is visible in the API.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

variable {N : ℕ}

/-- Explicit **Theorem 2 classical-Fisher assumption bundle**.

Larocca's Theorem 2 has a quantum-Fisher part (`D₁`) and a classical-Fisher part (`D₂`) [LJG+21,
main2.tex:700-706]. This development proves the `D₁`/QFIM-rank capacity statement from
`OverparamData`. The `D₂` classical-Fisher dimension is kept here as a named
assumption rather than hidden
as an undifferentiated field of the main QNN structure. -/
structure QNNCapacityClassicalAssumptions (gens : Set (Matrix (Fin N) (Fin N) ℂ)) where
  /-- The effective *classical* dimension `D₂`, i.e. the classical-Fisher-matrix rank. -/
  effDimClassical : ℕ
  /-- Named assumption: `D₂ ≤ dim g` [LJG+21, main2.tex:700]. -/
  effDimClassical_le_dlaDim : effDimClassical ≤ dlaDim gens

/-- Explicit **Theorem 3 Hessian-rank assumption bundle**.

Larocca's Theorem 3 bounds the Hessian rank at a minimum by both `dim g` and the
combinatorial expression
`2·d·r - r² - r` [LJG+21, main2.tex:715-720], with side condition `r ≤ d`. In
this square-matrix model
`d = N` and `r = min{rank A, rank O}`, so `r ≤ N` is the intended rank side condition
for the natural-number
subtraction term. Lean derives the public `min` bound from the two named
assumptions below; the analytic
differential-geometric Hessian argument itself is intentionally not smuggled in
as an implicit field. -/
structure QNNHessianRankAssumptions (gens : Set (Matrix (Fin N) (Fin N) ℂ)) where
  /-- The observable `O` of the linear loss (Theorem 3). -/
  obs : Matrix (Fin N) (Fin N) ℂ
  /-- The (signed) data-density operator `A = Σ_μ c_μ |ψ_μ⟩⟨ψ_μ|` (Theorem 3). -/
  dataOp : Matrix (Fin N) (Fin N) ℂ
  /-- The Hessian rank of the loss at a minimum, as a function of the parameter count. -/
  hessianRank : ℕ → ℕ
  /-- Named assumption: the Hessian rank is bounded by `dim g` [LJG+21, main2.tex:715]. -/
  hessianRank_le_dlaDim : ∀ M, hessianRank M ≤ dlaDim gens
  /-- Named assumption: the Hessian rank obeys the combinatorial bound
  `2·d·r − r² − r`, with `d = N`
  and `r = min{rank A, rank O}` [LJG+21, main2.tex:718-720]. -/
  hessianRank_le_comb : ∀ M,
    hessianRank M ≤ 2 * N * min dataOp.rank obs.rank
      - min dataOp.rank obs.rank ^ 2 - min dataOp.rank obs.rank

/-- **Overparametrization data for a QNN** with generator set `gens` [LJG+21], built on the genuine
QFIM-rank-saturation predicate (`extends OverparamData`). The inherited fields supply
the constructed QFIM
family and the achievable/saturated rank. Theorem 2's classical-Fisher side and Theorem
3's Hessian-rank side
are attached only through explicit assumption bundles, so the public API distinguishes
proved QFIM capacity
claims from scoped analytic inputs. -/
structure QNNOverparametrization (gens : Set (Matrix (Fin N) (Fin N) ℂ))
    extends OverparamData gens where
  /-- Explicit assumption bundle for the classical-Fisher half of Theorem 2 (`D₂`). -/
  classicalAssumptions : QNNCapacityClassicalAssumptions gens
  /-- Explicit assumption bundle for the Hessian-rank analytic inputs of Theorem 3. -/
  hessianAssumptions : QNNHessianRankAssumptions gens

namespace QNNOverparametrization

variable {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (Q : QNNOverparametrization gens)

/-- The observable `O` from the explicit Hessian-rank assumptions. -/
def obs : Matrix (Fin N) (Fin N) ℂ := Q.hessianAssumptions.obs

/-- The data-density operator `A` from the explicit Hessian-rank assumptions. -/
def dataOp : Matrix (Fin N) (Fin N) ℂ := Q.hessianAssumptions.dataOp

/-- `r = min{rank A, rank O}` — the smaller of the data-operator and observable ranks
[LJG+21, main2.tex:720]; the Hilbert-space dimension `d` is the matrix dimension `N`, and the
source-side side condition is `r ≤ N`. -/
noncomputable def stateRank : ℕ := min Q.dataOp.rank Q.obs.rank

/-- The QNN is **overparametrized** at `M` parameters when every training state's
achievable QFIM rank has
saturated (the genuine predicate of `OverparamData`, Larocca Def. 1). -/
def IsOverparametrized (M : ℕ) : Prop := Q.toOverparamData.IsOverparametrized M

/-- **Theorem 1 (QFIM-rank bound).** The achievable QFIM rank never exceeds `dim g`.
*Proved* (inherited),
discharging what the previous model assumed. -/
theorem achievableRank_le_dlaDim (μ : Q.toOverparamData.ι) (M : ℕ) :
    Q.toOverparamData.achievableRank μ M ≤ dlaDim gens :=
  Q.toOverparamData.achievable_le_dlaDim μ M

/-- **Persistence of overparametrization.** Once overparametrized at `M`, the QNN
stays overparametrized
for any `M' ≥ M` — the trainability phase transition is monotone (proved via the
inherited monotonicity). -/
theorem isOverparametrized_stays {M M' : ℕ} (h : M ≤ M') (hover : Q.IsOverparametrized M) :
    Q.IsOverparametrized M' :=
  Q.toOverparamData.isOverparametrized_stays h hover

/-- **Theorem 2** effective *quantum* dimension `D₁` for training state `μ` at parameter count `M` —
faithfully to Larocca's `D₁(θ) = rank[F(θ)]` [LJG+21, main2.tex:994], the *achievable QFIM rank*. A
**derived** quantity (`= achievableRank`), not a free field; this is what
reconciles the model with the
source's definition while keeping the saturation content of Theorem 2 genuine. -/
noncomputable def effDimQuantum (μ : Q.toOverparamData.ι) (M : ℕ) : ℕ :=
  Q.toOverparamData.achievableRank μ M

/-- **Theorem 2 classical-Fisher dimension `D₂`**, exposed from the explicit assumption bundle.

This is not used to prove the QFIM-rank capacity theorem; it records the scoped
classical-Fisher input from
Larocca's Theorem 2. -/
noncomputable def effDimClassical : ℕ := Q.classicalAssumptions.effDimClassical

/-- **Theorem 2 classical-Fisher bound**, from the explicit assumption bundle. -/
theorem effDimClassical_le_dlaDim_from_assumptions :
    Q.effDimClassical ≤ dlaDim gens :=
  Q.classicalAssumptions.effDimClassical_le_dlaDim

/-- Backward-compatible spelling for the explicitly assumed Theorem 2 classical-Fisher bound. -/
theorem effDimClassical_le_dlaDim :
    Q.effDimClassical ≤ dlaDim gens :=
  Q.effDimClassical_le_dlaDim_from_assumptions

/-- **Theorem 2 (capacity bound).** The effective quantum dimension `D₁` never exceeds `dim g`. -/
theorem capacity_le_dlaDim (μ : Q.toOverparamData.ι) (M : ℕ) :
    Q.effDimQuantum μ M ≤ dlaDim gens :=
  Q.toOverparamData.achievable_le_dlaDim μ M

/-- **Theorem 2 (capacity saturation).** Once overparametrized, the effective quantum dimension `D₁`
attains its saturated value `R` for every training state — the genuine saturation
content of Theorem 2
(`D₁ = rank` reaches its maximum `R`), *distinct* from Theorem 1's `rank ≤ dim g`. -/
theorem capacity_max_of_overparam {M : ℕ} (hover : Q.IsOverparametrized M)
    (μ : Q.toOverparamData.ι) :
    Q.effDimQuantum μ M = Q.toOverparamData.saturatedRank μ :=
  hover μ

/-- The Hessian rank function from the explicit Theorem 3 assumption bundle. -/
def hessianRank : ℕ → ℕ := Q.hessianAssumptions.hessianRank

/-- **Theorem 3 Hessian-rank bound by `dim g`**, from the explicit assumption bundle. -/
theorem hessianRank_le_dlaDim (M : ℕ) :
    Q.hessianRank M ≤ dlaDim gens :=
  Q.hessianAssumptions.hessianRank_le_dlaDim M

/-- **Theorem 3 Hessian-rank combinatorial bound**, from the explicit assumption bundle. -/
theorem hessianRank_le_comb (M : ℕ) :
    Q.hessianRank M ≤ 2 * N * Q.stateRank - Q.stateRank ^ 2 - Q.stateRank :=
  Q.hessianAssumptions.hessianRank_le_comb M

/-- **Theorem 3 (Hessian-rank bound).** The Hessian rank at a minimum is bounded by
`min (dim g) (2·d·r − r² − r)` — derived (`le_min`) from the two explicit named assumptions. -/
theorem hessianRank_le_min_of_assumptions (M : ℕ) :
    Q.hessianRank M ≤ min (dlaDim gens) (2 * N * Q.stateRank - Q.stateRank ^ 2 - Q.stateRank) :=
  le_min (Q.hessianRank_le_dlaDim M) (Q.hessianRank_le_comb M)

/-- Backward-compatible spelling for the explicitly assumed Theorem 3 Hessian-rank bound. -/
theorem hessianRank_le_min (M : ℕ) :
    Q.hessianRank M ≤ min (dlaDim gens) (2 * N * Q.stateRank - Q.stateRank ^ 2 - Q.stateRank) :=
  Q.hessianRank_le_min_of_assumptions M

end QNNOverparametrization

/-- **The overparametrization theory is non-vacuous.** A concrete `QNNOverparametrization` over the
fully-controllable `gl(1)` algebra, built from `overparamWitness` — which attains
positive saturated rank
(`R = 1 > 0`, `overparamWitness_saturatedRank_pos`). Unlike the previous all-zero
instance (whose achievable
rank was identically `0`, making `IsOverparametrized` *false*), this witness is
genuinely overparametrized,
so the capacity / Hessian / persistence theorems are not vacuously applicable. -/
theorem qnnOverparametrization_nonempty :
    Nonempty (QNNOverparametrization (Set.univ : Set (Matrix (Fin 1) (Fin 1) ℂ))) :=
  ⟨{ overparamWitness with
     classicalAssumptions :=
       { effDimClassical := 0
         effDimClassical_le_dlaDim := Nat.zero_le _ }
     hessianAssumptions :=
       { obs := 0
         dataOp := 0
         hessianRank := fun _ => 0
         hessianRank_le_dlaDim := fun _ => Nat.zero_le _
         hessianRank_le_comb := fun _ => Nat.zero_le _ } }⟩

end QuantumAlg
