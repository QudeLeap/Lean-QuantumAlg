/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Cost
public import QuantumAlg.Primitives.QFT
public import QuantumAlg.Primitives.PhaseKickback
public import QuantumAlg.Core.Components.Kets

/-!
# Quantum phase estimation (exact, dyadic eigenphase)

Quantum phase estimation (QPE) reads the eigenphase of a unitary `U` into a
`t`-qubit register [Lin22, phaseestimation.tex:510; CEMM98, cemm6.tex:574]. Given
an eigenstate `U|u⟩ = e^{2πiφ}|u⟩`, the circuit is:

1. prepare the control register in the uniform superposition `H^{⊗t}|0⟩`;
2. apply the controlled-power ladder, control qubit `s` controlling `U^{2^s}`,
   which by phase kickback writes the relative phase `e^{2πiφ·2^s}` onto that
   qubit and leaves the register in the **phase superposition**
   `(1/√N) Σ_k e^{2πiφk}|k⟩`;
3. apply the inverse QFT and measure.

This module formalizes the **exact** regime, where the eigenphase is a dyadic
rational `φ = j / 2^t` for some `j : Fin (2^t)`. The two physically separate
steps are proved independently and then composed:

- `controlled_pow_kickback` reuses `eigenvalue_phase_kickback`
  (`QuantumAlg.Primitives.PhaseKickback`) to derive the per-qubit phase
  `e^{2πiφ·2^s}` from the controlled power `U^{2^s}` — the kickback mechanism;
- `phaseState_eq_qftApplyKet` identifies the assembled phase superposition with
  `QFT|j⟩` exactly when `φ = j/2^t` — the dyadic/Fourier bridge;
- `qpe_readout` inverts the QFT (unitarity) to recover `|j⟩`.

The assembly of the per-qubit kickbacks into the joint `t`-qubit phase
superposition is the tensor-factorization step, taken here as the definition of
`phaseState` (the decoupled register-level model, matching the LCU/amplitude-
amplification style elsewhere in the library). Composing the three results gives
exact QPE: the inverse-QFT readout of `phaseState t (j/2^t)` is `|j⟩`, so a
computational-basis measurement returns `j` with probability one, recovering
`φ = j/2^t` exactly.

## Main results

- `QuantumAlg.Gate.apply_pow_eigenstate` — `(U^m)|u⟩ = λ^m|u⟩` for an
  eigenstate `U|u⟩ = λ|u⟩`.
- `QuantumAlg.controlled_pow_kickback` — the per-control-qubit phase kickback
  `c-U^{2^s} (|+⟩ ⊗ |u⟩)` for an eigenstate `|u⟩`.
- `QuantumAlg.phaseState_eq_qftApplyKet` — `phaseState t (j/2^t) = QFT t |j⟩`.
- `QuantumAlg.QuantumPhaseEstimation.main_exact_dyadic` — exact QPE: the inverse-QFT readout of the phase
  superposition is `|j⟩`.
- `QuantumAlg.qpe_probOutcome_eq_one` — the measurement returns `j` with
  probability one.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-! ### Eigenstates under gate powers -/

/-- An eigenstate of `U` is an eigenstate of every power `U ^ m`, with the
eigenvalue raised to the same power: `U|u⟩ = λ|u⟩ ⟹ (U^m)|u⟩ = λ^m|u⟩`. -/
theorem Gate.apply_pow_eigenstate {n : ℕ} {U : Gate n} {u : PureState n} {lam : ℂ}
    (hu : U.apply u = lam • u) (m : ℕ) : (U ^ m).apply u = lam ^ m • u := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Gate.one_apply, one_smul]
  | succ m ih =>
      rw [pow_succ, Gate.mul_apply, hu, Gate.apply_smul, ih, smul_smul, ← pow_succ']

/-! ### Per-qubit phase kickback (QPE ladder) -/

/-- **Per-control-qubit phase kickback** [CEMM98, cemm6.tex:163]: control qubit
`s` of the QPE ladder controls `U^{2^s}`. On `|+⟩ ⊗ |u⟩` with an eigenstate
`U|u⟩ = e^{2πiφ}|u⟩`, the controlled power leaves `|u⟩` fixed and kicks the
relative phase `e^{2πiφ·2^s}` onto the `|1⟩` branch of the control. -/
theorem controlled_pow_kickback {n : ℕ} (U : Gate n) (u : PureState n) (φ : ℝ)
    (hu : U.apply u = Complex.exp (2 * ↑Real.pi * ↑φ * Complex.I) • u) (s : ℕ) :
    (Gate.controlled (U ^ (2 ^ s))).apply (ketPlus.tensor u)
      = (invSqrt2 • ket0
          + (Complex.exp (↑(2 * Real.pi * (φ * (2 : ℝ) ^ s)) * Complex.I) * invSqrt2)
              • ket1).tensor u := by
  have hpow : (U ^ (2 ^ s)).apply u
      = Complex.exp (↑(2 * Real.pi * (φ * (2 : ℝ) ^ s)) * Complex.I) • u := by
    rw [Gate.apply_pow_eigenstate hu (2 ^ s), ← Complex.exp_nat_mul]
    congr 1
    congr 1
    push_cast
    ring
  rw [show ketPlus = invSqrt2 • ket0 + invSqrt2 • ket1 from by rw [ketPlus, smul_add],
    GeneralizedPhaseKickback.main (U ^ (2 ^ s)) u (2 * Real.pi * (φ * (2 : ℝ) ^ s))
      hpow invSqrt2 invSqrt2]

/-- Source-level exact-QPE input: an `n`-qubit unitary, an eigenstate, and its
eigenphase. The controlled powers of `unitary` are the oracle calls used by the
phase-estimation ladder. -/
structure QPEEigenstateInput (n : ℕ) where
  unitary : Gate n
  eigenstate : PureState n
  phase : ℝ
  eigenstate_eq :
    unitary.apply eigenstate =
      Complex.exp (2 * ↑Real.pi * ↑phase * Complex.I) • eigenstate

/-- The per-control-qubit kickbacks available from a source-level QPE input. -/
def QPEControlledPowerKickbacks {n : ℕ} (P : QPEEigenstateInput n) : Prop :=
  ∀ s : ℕ,
    (Gate.controlled (P.unitary ^ (2 ^ s))).apply (ketPlus.tensor P.eigenstate)
      = (invSqrt2 • ket0
          + (Complex.exp (↑(2 * Real.pi * (P.phase * (2 : ℝ) ^ s)) * Complex.I) * invSqrt2)
              • ket1).tensor P.eigenstate

theorem qpe_eigenstate_controlled_power_kickbacks {n : ℕ}
    (P : QPEEigenstateInput n) :
    QPEControlledPowerKickbacks P := by
  intro s
  exact controlled_pow_kickback P.unitary P.eigenstate P.phase P.eigenstate_eq s

/-! ### Phase superposition and the Fourier bridge -/

/-- The QPE **phase superposition** on a `t`-qubit register for eigenphase `φ`:
`(1/√N) Σ_k e^{2πiφk}|k⟩`, the state of the control register after the
controlled-power ladder (`controlled_pow_kickback`, assembled over all `t`
qubits). -/
def phaseState (t : ℕ) (φ : ℝ) : PureState t :=
  WithLp.toLp 2 fun k : Fin (2 ^ t) =>
    invSqrtN t * Complex.exp (2 * ↑Real.pi * ↑φ * ↑k.val * Complex.I)

@[simp]
theorem phaseState_apply (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) :
    phaseState t φ k =
      invSqrtN t * Complex.exp (2 * ↑Real.pi * ↑φ * ↑k.val * Complex.I) :=
  rfl

/-- **Dyadic/Fourier bridge**: when the eigenphase is the dyadic rational
`φ = j / 2^t`, the QPE phase superposition is exactly `QFT t |j⟩`. -/
theorem phaseState_eq_qftApplyKet (t : ℕ) (j : Fin (2 ^ t)) :
    phaseState t ((j.val : ℝ) / (2 : ℝ) ^ t) = (QFT t).apply (ket j) := by
  apply WithLp.ofLp_injective
  funext k
  change phaseState t ((j.val : ℝ) / (2 : ℝ) ^ t) k = (QFT t).apply (ket j) k
  rw [phaseState_apply, QFT_apply_ket, omega, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

/-! ### Inverse-QFT readout -/

/-- The inverse quantum Fourier transform, `QFT†`. -/
def invQFT (t : ℕ) : Gate t := (QFT t).conjTranspose

/-- The inverse QFT undoes the QFT on a basis ket: `QFT† (QFT|j⟩) = |j⟩`. This
is the readout step of QPE [Lin22, phaseestimation.tex:468], using only
unitarity of the QFT. -/
theorem qpe_readout (t : ℕ) (j : Fin (2 ^ t)) :
    Gate.apply (invQFT t) ((QFT t).apply (ket j)) = ket j := by
  rw [invQFT, ← Gate.mul_apply]
  have h : (QFT t).conjTranspose * QFT t = 1 := by
    have hU := QFT_mem_unitaryGroup t
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
  rw [h, Gate.one_apply]

/-! ### Exact QPE -/

/-- **Exact quantum phase estimation.** If the eigenphase is the dyadic rational
`φ = j / 2^t`, then applying the inverse QFT to the QPE phase superposition
`phaseState t φ` returns the computational-basis state `|j⟩` exactly
[Lin22, phaseestimation.tex:513]. -/
theorem QuantumPhaseEstimation.main_exact_dyadic (t : ℕ) (j : Fin (2 ^ t)) (φ : ℝ)
    (hφ : φ = (j.val : ℝ) / (2 : ℝ) ^ t) :
    Gate.apply (invQFT t) (phaseState t φ) = ket j := by
  subst hφ
  rw [phaseState_eq_qftApplyKet]
  exact qpe_readout t j

/-- The QPE measurement is deterministic: in the exact regime the inverse-QFT
readout of the phase superposition yields outcome `j` with probability one. -/
theorem QuantumPhaseEstimation.main_exact_probability_one (t : ℕ) (j : Fin (2 ^ t)) (φ : ℝ)
    (hφ : φ = (j.val : ℝ) / (2 : ℝ) ^ t) :
    PureState.probOutcome (Gate.apply (invQFT t) (phaseState t φ)) j = 1 := by
  rw [QuantumPhaseEstimation.main_exact_dyadic t j φ hφ, PureState.probOutcome_ket, if_pos rfl]

/-- Trusted resource profile for exact dyadic QPE in the decoupled
phase-register model: a controlled-power ladder with `2^t - 1` unitary-power
uses and a quadratic-size inverse-QFT/readout layer. -/
def qpeExactResourceProfile (t : ℕ) : ResourceProfile where
  oracleQueries := 2 ^ t - 1
  hadamardGates := t
  elementaryGates := t ^ 2
  classicalOps := 0

theorem qpeExactResourceProfile_exact (t : ℕ) :
    ResourceProfile.HasExactCounts
      (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  simp [ResourceProfile.HasExactCounts, qpeExactResourceProfile]

/-- Exact QPE readout with the decoupled phase-register resource profile. -/
theorem QuantumPhaseEstimation.main_exact_dyadic_with_resources (t : ℕ) (j : Fin (2 ^ t)) (φ : ℝ)
    (hφ : φ = (j.val : ℝ) / (2 : ℝ) ^ t) :
    Gate.apply (invQFT t) (phaseState t φ) = ket j ∧
      ResourceProfile.HasExactCounts
        (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  constructor
  · exact QuantumPhaseEstimation.main_exact_dyadic t j φ hφ
  · exact qpeExactResourceProfile_exact t

/-- Exact QPE from the source-level eigenstate/access assumptions, paired with
the trusted controlled-power resource profile. This remains the dyadic exact
regime: approximate precision and confidence amplification are separate
refinements. -/
theorem QuantumPhaseEstimation.main_exact_eigenstate_readout_with_resources {n : ℕ}
    (P : QPEEigenstateInput n) (t : ℕ) (j : Fin (2 ^ t))
    (hphase : P.phase = (j.val : ℝ) / (2 : ℝ) ^ t) :
    QPEControlledPowerKickbacks P ∧
      Gate.apply (invQFT t) (phaseState t P.phase) = ket j ∧
        ResourceProfile.HasExactCounts
          (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  constructor
  · exact qpe_eigenstate_controlled_power_kickbacks P
  · exact QuantumPhaseEstimation.main_exact_dyadic_with_resources t j P.phase hphase

/-- Exact QPE from the source-level eigenstate/access assumptions, phrased as
an exact estimate theorem. In the dyadic regime the phase estimate has zero
error, so it satisfies any nonnegative precision and failure-probability
thresholds. The same controlled-power resource profile is recorded. -/
theorem QuantumPhaseEstimation.main {n : ℕ}
    (P : QPEEigenstateInput n) (t : ℕ) (j : Fin (2 ^ t))
    (eps eta : ℝ) (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hphase : P.phase = (j.val : ℝ) / (2 : ℝ) ^ t) :
    QPEControlledPowerKickbacks P ∧
      Gate.apply (invQFT t) (phaseState t P.phase) = ket j ∧
        |P.phase - (j.val : ℝ) / (2 : ℝ) ^ t| ≤ eps ∧
          1 - PureState.probOutcome
              (Gate.apply (invQFT t) (phaseState t P.phase)) j ≤ eta ∧
            ResourceProfile.HasExactCounts
              (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  refine ⟨qpe_eigenstate_controlled_power_kickbacks P, ?_⟩
  have hreadout : Gate.apply (invQFT t) (phaseState t P.phase) = ket j :=
    QuantumPhaseEstimation.main_exact_dyadic t j P.phase hphase
  refine ⟨hreadout, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [hphase, sub_self, abs_zero]
    exact heps
  · refine ⟨?_, qpeExactResourceProfile_exact t⟩
    rw [QuantumPhaseEstimation.main_exact_probability_one t j P.phase hphase]
    simpa using heta

end

end QuantumAlg
