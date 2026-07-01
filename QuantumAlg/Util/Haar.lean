/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic

/-!
# Haar averages (twirl) over finite invariant ensembles

This module builds the Haar-moment prerequisites for the QML trainability results, scoped to the
genuinely achievable core (the `t = 1`, first-moment / adjoint twirl) following the
**invariant-average ⟹ projection** route.

## What is genuinely proved vs. assumed

* **Proved (this file):**
  - For a finite subgroup `H` of the unitary group, the twirl `T_H(X) = (1/|H|) Σ_{g∈H} g X g†`
    is a projection onto the commutant of `H`: it is fixed by conjugation by every `V ∈ H`
    (`unitaryTwirl_conj`), commutes with every `V ∈ H` (`unitaryTwirl_commute`), and is idempotent
    (`unitaryTwirl_idem`). This is the finite invariant-measure instance of the Haar twirl.
  - The single-qubit **Pauli 1-design** identity (`pauliTwirl_eq`):
    `(1/4) Σ_P P X P† = (tr X / 2)·1`,
    the canonical Haar first moment (depolarizing channel) computed concretely.

* **Documented gap (not assumed as an `axiom`):** a normalized Haar *measure* on the full unitary
  group `U(N)` and the resulting general first-moment value `T(X) = (tr X / N)·1` need `U(N)` as a
  compact topological group, which Mathlib does not yet provide. The general second-moment / SWAP
  commutant (t=2) and arbitrary t-designs are tracked as follow-up work.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

noncomputable section

/-! ### Single-qubit Pauli 1-design (concrete Haar first moment) -/

/-- Pauli `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The single-qubit **Pauli twirl** `(1/4)(X + σx X σx + σy X σy + σz X σz)` (depolarizing
channel up to scale). The Paulis are Hermitian, so `σ = σ†`. -/
def pauliTwirl (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 4 : ℂ) • (X + pauliX * X * pauliX + pauliY * X * pauliY + pauliZ * X * pauliZ)

/-- **Pauli 1-design identity (Haar first moment).** The single-qubit Pauli twirl sends every `X`
to `(tr X / 2) · 1`. This is the canonical `t = 1` Haar moment, realized concretely by the
single-qubit Pauli group (a unitary 1-design). -/
theorem pauliTwirl_eq (X : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliTwirl X = (X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.eta_fin_two X]
  simp only [pauliTwirl, pauliX, pauliY, pauliZ, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.smul_apply, smul_eq_mul] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

/-! ### General finite-group twirl: projection onto the commutant

The Haar twirl realized for a finite invariant (counting) measure: a finite group `G` acting
through `u : G → matrices`. With `u` a unitary representation this is exactly the twirl for the
invariant counting measure on the image group; the genuine projection-onto-commutant content is
proved here, parametric in `u`, without needing a Haar *measure* on `U(N)`. -/

variable {N : ℕ} {G : Type*} [Group G] [Fintype G]

/-- The twirl of `X` by a finite group `G` acting through `u : G → matrices`:
`(1/|G|) · Σ_g u g · X · (u g)†`. -/
noncomputable def repTwirl (u : G → Matrix (Fin N) (Fin N) ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, u g * X * (u g)ᴴ

/-- **Conjugation-invariance.** For a multiplicative `u`, the twirl is fixed by conjugation by any
`u V` — the defining property of the invariant (Haar) average, proved by re-indexing the sum. -/
theorem repTwirl_conj (u : G → Matrix (Fin N) (Fin N) ℂ) (hmul : ∀ a b, u (a * b) = u a * u b)
    (X : Matrix (Fin N) (Fin N) ℂ) (V : G) :
    u V * repTwirl u X * (u V)ᴴ = repTwirl u X := by
  unfold repTwirl
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft V) (fun g => u g * X * (u g)ᴴ)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [hmul, Matrix.conjTranspose_mul]
  noncomm_ring

/-- **Idempotence.** The twirl is a projection. -/
theorem repTwirl_idem (u : G → Matrix (Fin N) (Fin N) ℂ) (hmul : ∀ a b, u (a * b) = u a * u b)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    repTwirl u (repTwirl u X) = repTwirl u X := by
  haveI : Nonempty G := ⟨1⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [show repTwirl u (repTwirl u X)
        = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, u g * repTwirl u X * (u g)ᴴ from rfl,
    Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => repTwirl_conj u hmul X g,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- **Commutation with the group.** For a unitary representation `u` the twirl lands in the
commutant: it commutes with every `u V`. -/
theorem repTwirl_commute (u : G → Matrix (Fin N) (Fin N) ℂ) (hmul : ∀ a b, u (a * b) = u a * u b)
    (hunit : ∀ a, (u a)ᴴ * u a = 1) (X : Matrix (Fin N) (Fin N) ℂ) (V : G) :
    u V * repTwirl u X = repTwirl u X * u V := by
  have h := repTwirl_conj u hmul X V
  calc u V * repTwirl u X
      = u V * repTwirl u X * ((u V)ᴴ * u V) := by rw [hunit, mul_one]
    _ = u V * repTwirl u X * (u V)ᴴ * u V := by noncomm_ring
    _ = repTwirl u X * u V := by rw [h]

/-- **Trace preservation.** A unitary twirl preserves the trace (each summand `u g · X · (u g)†`
is trace-equal to `X` by cyclicity and unitarity). -/
theorem repTwirl_trace (u : G → Matrix (Fin N) (Fin N) ℂ) (hunit : ∀ a, (u a)ᴴ * u a = 1)
    (X : Matrix (Fin N) (Fin N) ℂ) : (repTwirl u X).trace = X.trace := by
  haveI : Nonempty G := ⟨1⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ g : G, (u g * X * (u g)ᴴ).trace = X.trace := by
    intro g
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  unfold repTwirl
  rw [Matrix.trace_smul, Matrix.trace_sum, Finset.sum_congr rfl fun g _ => hterm g,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hcard, one_mul]

/-- **First-moment value under irreducibility (t = 1 Haar moment).** If the representation `u` is
irreducible — its commutant is the scalars — then the twirl is the depolarizing map
`X ↦ (tr X / N) · 1`. For the full unitary group (which acts irreducibly on `ℂ^N`) this is the
Haar first moment; concretely it is realised by any 1-design (e.g. `pauliTwirl_eq` for `N = 2`). -/
theorem repTwirl_eq_scalar [NeZero N] (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (hunit : ∀ a, (u a)ᴴ * u a = 1)
    (X : Matrix (Fin N) (Fin N) ℂ)
    (hirr : ∀ M : Matrix (Fin N) (Fin N) ℂ, (∀ g, u g * M = M * u g) → ∃ c : ℂ, M = c • 1) :
    repTwirl u X = (X.trace / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  obtain ⟨c, hc⟩ := hirr (repTwirl u X) (fun g => repTwirl_commute u hmul hunit X g)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have htr : (repTwirl u X).trace = X.trace := repTwirl_trace u hunit X
  rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
  rw [hc]
  congr 1
  rw [eq_div_iff hN]
  exact htr

end

end QuantumAlg
