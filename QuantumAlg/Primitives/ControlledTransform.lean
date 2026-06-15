/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.PhaseKickback
public import QuantumAlg.Primitives.QSP

/-!
# Controlled-unitary transformation (quantum phase processing / QET)

Quantum phase processing (QPP) — equivalently quantum eigenvalue transformation
(QET) — applies a trigonometric transformation to the *eigenphases* of an
`n`-qubit unitary `U` by interleaving the controlled unitary `c-U` with
single-qubit processing rotations on one ancilla
[WZYW23, arxiv_v3.tex:601]. It is the multi-qubit generalization of the
single-qubit trigonometric QSP (`QuantumAlg.Primitives.QSP.Fourier`), obtained
by **replacing the signal gate `R_Z(x)` of QSP with `c-U`**
[WZYW23, arxiv_v3.tex:632].

This module formalizes the eigenstate (decoupled) regime, where the target
holds an eigenstate `U|u⟩ = e^{iθ}|u⟩`. The whole construction then collapses
to single-qubit QSP at the signal `x = θ`:

- on `|u⟩`, the signal `c-U` acts on the ancilla as the controlled-phase gate
  `phaseGate θ = diag(1, e^{iθ})` (eigenvalue phase kickback), which is the QSP
  encoding gate `R_Z(θ) = rotZStd θ` up to the global phase `e^{iθ/2}`
  (`phaseGate_eq_smul_rotZStd`);
- consequently the QPP word `qppYZZYZ U φ θ₀ φ₀ ps` (the YZZYZ trainable blocks
  interleaved with `c-U`) on `|ψ⟩ ⊗ |u⟩` equals
  `(e^{iθ/2})^L · (qspYZZYZ φ θ₀ φ₀ ps θ |ψ⟩) ⊗ |u⟩`, i.e. the single-qubit
  YZZYZ word evaluated at the eigenphase, tensored with the untouched
  eigenstate — the **eigenspace decomposition of QPP**
  [WZYW23, arxiv_v3.tex:641].

Composing with the QSP characterization `qsp_yzzyz_iff` gives the phase-evolution
guarantee [WZYW23, arxiv_v3.tex:650]: every trigonometric transform achievable
by single-qubit QSP is realized on the eigenphase of `U` by a QPP word
(`qpp_realizes_target`).

The number of `c-U` calls equals the number of QSP signal slots, so the global
phase here is `(e^{iθ/2})^L`; Wang's alternating `c-U`/`c-U†` convention instead
leaves only the parity phase `(e^{-iθ/2})^{L mod 2}`.

## Main results

- `QuantumAlg.controlled_apply_eigenstate` — on an eigenstate, `c-U` acts on the
  ancilla as the QSP signal gate up to a global phase:
  `c-U (|ψ⟩ ⊗ |u⟩) = (e^{iθ/2} · rotZStd θ |ψ⟩) ⊗ |u⟩`.
- `QuantumAlg.phaseGate_eq_smul_rotZStd` — `diag(1, e^{iθ}) = e^{iθ/2} · R_Z(θ)`,
  the controlled-phase gate as the QSP encoding gate up to global phase.
- `QuantumAlg.qppYZZYZ_apply_eigenstate` — the eigenspace decomposition: the QPP
  word on `|ψ⟩ ⊗ |u⟩` is `(e^{iθ/2})^L · (qspYZZYZ … θ |ψ⟩) ⊗ |u⟩`.
- `QuantumAlg.qpp_realizes_target` — every `IsYZPair` transform is realized on
  the eigenphase by some QPP word.
-/

@[expose] public section

namespace QuantumAlg

open PureState

noncomputable section

variable {n : ℕ}

/-! ### Single-qubit ancilla decomposition and gate scalars -/

/-- A one-qubit state is its `|0⟩`/`|1⟩` coordinate combination. -/
theorem single_qubit_decomp (ψ : PureState 1) :
    ψ = (ψ 0) • ket0 + (ψ 1) • ket1 := by
  apply WithLp.ofLp_injective
  funext i
  change ψ i = ((ψ 0) • ket0 + (ψ 1) • ket1) i
  fin_cases i <;>
    simp [ket0, ket1, ket_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- Gate scalar multiplication commutes with application:
`(c • G) ψ = c • (G ψ)`. -/
theorem Gate.smul_apply (c : ℂ) (G : Gate n) (ψ : PureState n) :
    (c • G).apply ψ = c • G.apply ψ := by
  apply WithLp.ofLp_injective
  funext i
  change ((c • G).apply ψ) i = (c • G.apply ψ) i
  simp only [Gate.apply_apply, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The controlled-phase action of `c-U` on an eigenstate -/

/-- The controlled-phase gate `diag(1, e^{iθ})`: the action that `c-U` induces on
the ancilla when the target holds an eigenstate of eigenphase `θ`. -/
def phaseGate (θ : ℝ) : Gate 1 := !![1, 0; 0, Complex.exp ((θ : ℝ) * Complex.I)]

@[simp]
theorem phaseGate_apply_ket0 (θ : ℝ) : (phaseGate θ).apply ket0 = ket0 := by
  apply WithLp.ofLp_injective
  funext i
  change (phaseGate θ).apply ket0 i = ket0 i
  rw [ket0, Gate.apply_ket]
  fin_cases i <;> simp [phaseGate, ket_apply]

@[simp]
theorem phaseGate_apply_ket1 (θ : ℝ) :
    (phaseGate θ).apply ket1 = Complex.exp ((θ : ℝ) * Complex.I) • ket1 := by
  apply WithLp.ofLp_injective
  funext i
  change (phaseGate θ).apply ket1 i = (Complex.exp ((θ : ℝ) * Complex.I) • ket1) i
  rw [ket1, Gate.apply_ket]
  fin_cases i <;> simp [phaseGate, ket_apply, PiLp.smul_apply, smul_eq_mul]

/-- The controlled-phase gate on a general ancilla state. -/
theorem phaseGate_apply (θ : ℝ) (ψ : PureState 1) :
    (phaseGate θ).apply ψ
      = (ψ 0) • ket0 + (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • ket1 := by
  conv_lhs => rw [single_qubit_decomp ψ]
  rw [Gate.apply_add, Gate.apply_smul, Gate.apply_smul, phaseGate_apply_ket0,
    phaseGate_apply_ket1, smul_smul, mul_comm (ψ 1)]

/-- **Controlled-phase factorization on an eigenstate.** When the target holds
an eigenstate `U|u⟩ = e^{iθ}|u⟩`, the controlled unitary `c-U` acts on
`|ψ⟩ ⊗ |u⟩` as the controlled-phase gate on the ancilla, leaving the
eigenstate fixed [WZYW23, arxiv_v3.tex:641]. -/
theorem controlled_apply_eigenstate_phase (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.apply u = Complex.exp ((θ : ℝ) * Complex.I) • u) (ψ : PureState 1) :
    (Gate.controlled U).apply (ψ.tensor u) = ((phaseGate θ).apply ψ).tensor u := by
  conv_lhs => rw [single_qubit_decomp ψ]
  rw [eigenvalue_phase_kickback U u θ hu (ψ 0) (ψ 1), phaseGate_apply]

/-! ### The controlled-phase gate is the QSP signal gate up to global phase -/

/-- `diag(1, e^{iθ}) = e^{iθ/2} · R_Z(θ)`: the controlled-phase gate is the QSP
encoding gate `rotZStd θ = R_Z(θ)` up to the global phase `e^{iθ/2}`
[WZYW23, arxiv_v3.tex:632]. -/
theorem phaseGate_eq_smul_rotZStd (θ : ℝ) :
    phaseGate θ = Complex.exp ((θ / 2 : ℝ) * Complex.I) • rotZStd θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGate, rotZStd, rotZ, Matrix.smul_apply, smul_eq_mul]
  · rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    ring
  · rw [← Complex.exp_add]
    congr 1
    ring

/-- `c-U` on a general ancilla, in QSP-signal form: the QSP encoding gate
`rotZStd θ` up to the global phase `e^{iθ/2}`. -/
theorem phaseGate_apply_eq_smul_rotZStd (θ : ℝ) (ψ : PureState 1) :
    (phaseGate θ).apply ψ
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) • (rotZStd θ).apply ψ := by
  rw [phaseGate_eq_smul_rotZStd, Gate.smul_apply]

/-- **Eigenstate reduction of `c-U` to the QSP signal.** On an eigenstate
`U|u⟩ = e^{iθ}|u⟩`, the controlled unitary acts as the QSP encoding gate at
signal `θ`, up to the global phase `e^{iθ/2}`:
`c-U (|ψ⟩ ⊗ |u⟩) = (e^{iθ/2} · R_Z(θ)|ψ⟩) ⊗ |u⟩` [WZYW23, arxiv_v3.tex:641]. -/
theorem controlled_apply_eigenstate (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.apply u = Complex.exp ((θ : ℝ) * Complex.I) • u) (ψ : PureState 1) :
    (Gate.controlled U).apply (ψ.tensor u)
      = (Complex.exp ((θ / 2 : ℝ) * Complex.I) • (rotZStd θ).apply ψ).tensor u := by
  rw [controlled_apply_eigenstate_phase U u θ hu, phaseGate_apply_eq_smul_rotZStd]

/-! ### The QPP word and its eigenspace decomposition -/

/-- The **quantum phase processor** in the YZZYZ (W-Z-W) convention: the QSP
word `qspYZZYZ` with each signal slot `R_Z(x)` replaced by the controlled
unitary `c-U`, the trainable blocks `R_Y(θⱼ)·R_Z(φⱼ)` acting on the ancilla
[WZYW23, arxiv_v3.tex:601]. -/
def qppYZZYZ (U : Gate n) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) : Gate (1 + n) :=
  ps.foldl
    (fun W p => W * (Gate.controlled U * Gate.tensor (rotY p.1 * rotZStd p.2) (1 : Gate n)))
    (Gate.tensor (rotZStd φ * (rotY θ₀ * rotZStd φ₀)) (1 : Gate n))

@[simp]
theorem qppYZZYZ_nil (U : Gate n) (φ θ₀ φ₀ : ℝ) :
    qppYZZYZ U φ θ₀ φ₀ [] = Gate.tensor (rotZStd φ * (rotY θ₀ * rotZStd φ₀)) (1 : Gate n) :=
  rfl

theorem qppYZZYZ_concat (U : Gate n) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (p : ℝ × ℝ) :
    qppYZZYZ U φ θ₀ φ₀ (ps ++ [p])
      = qppYZZYZ U φ θ₀ φ₀ ps
        * (Gate.controlled U * Gate.tensor (rotY p.1 * rotZStd p.2) (1 : Gate n)) := by
  simp [qppYZZYZ, List.foldl_append]

/-- **Eigenspace decomposition of QPP** [WZYW23, arxiv_v3.tex:641]. On an
eigenstate `U|u⟩ = e^{iθ}|u⟩`, the QPP word acts as the single-qubit YZZYZ QSP
word at the signal `θ`, tensored with the untouched eigenstate, up to the
global phase `(e^{iθ/2})^L` (`L` = number of `c-U` calls):
`qppYZZYZ U φ θ₀ φ₀ ps (|ψ⟩ ⊗ |u⟩) = ((e^{iθ/2})^L · qspYZZYZ φ θ₀ φ₀ ps θ |ψ⟩) ⊗ |u⟩`. -/
theorem qppYZZYZ_apply_eigenstate (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.apply u = Complex.exp ((θ : ℝ) * Complex.I) • u)
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) (ψ : PureState 1) :
    (qppYZZYZ U φ θ₀ φ₀ ps).apply (ψ.tensor u)
      = ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ ps.length
          • (qspYZZYZ φ θ₀ φ₀ ps θ).apply ψ).tensor u := by
  induction ps using List.reverseRecOn generalizing ψ with
  | nil =>
      rw [qppYZZYZ_nil, qspYZZYZ_nil, List.length_nil, pow_zero, one_smul,
        Gate.tensor_apply_tensor, Gate.one_apply]
  | append_singleton ps p ih =>
      rw [qppYZZYZ_concat, Gate.mul_apply, Gate.mul_apply,
        Gate.tensor_apply_tensor, Gate.one_apply,
        controlled_apply_eigenstate U u θ hu, ih, qspYZZYZ_concat,
        List.length_append, List.length_singleton]
      congr 1
      rw [Gate.apply_smul, smul_smul, ← pow_succ, ← Gate.mul_apply,
        ← Gate.mul_apply, mul_assoc]

/-! ### Phase evolution: realizing QSP transforms on the eigenphase -/

/-- **Quantum phase evolution** [WZYW23, arxiv_v3.tex:650]. Every trigonometric
transform admissible for single-qubit QSP (an `IsYZPair L A B`) is realized on
the eigenphase of `U` by a QPP word with `L` controlled-unitary calls: there are
angles `(φ, θ₀, φ₀, ps)` such that the QPP word maps `|ψ⟩ ⊗ |u⟩` to
`((e^{iθ/2})^L · qspMatYZ L A B θ |ψ⟩) ⊗ |u⟩` for every ancilla state. -/
theorem qpp_realizes_target (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.apply u = Complex.exp ((θ : ℝ) * Complex.I) • u)
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧ ∀ ψ : PureState 1,
      (qppYZZYZ U φ θ₀ φ₀ ps).apply (ψ.tensor u)
        = ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L
            • (qspMatYZ L A B θ).apply ψ).tensor u := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ := (qsp_yzzyz_iff L A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, fun ψ => ?_⟩
  rw [qppYZZYZ_apply_eigenstate U u θ hu, hlen, hmat]

end

end QuantumAlg
