/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Complex
public import QuantumAlg.Core.Cost
public import QuantumAlg.Core.Circuit
public import QuantumAlg.Primitives.QFT
public import QuantumAlg.Primitives.PhaseKickback
public import QuantumAlg.Core.Components.Kets

/-!
# Quantum phase estimation (exact, dyadic eigenphase)

Quantum phase estimation (QPE) reads the eigenphase of a unitary `U` into a
`t`-qubit register [Lin22, phaseestimation.tex:510; CEMM98, cemm6.tex:574].
This module formalizes the exact dyadic regime, where the eigenphase is
`phi = j / 2^t` for some `j : Fin (2^t)`.

The phase-register superposition is kept at the `StateVector` layer: it is a
linear combination of basis states whose unit-norm proof is not needed until a
result is packaged as a `PureState`. The readout theorem says that inverse QFT
maps that raw phase vector to the computational-basis vector `|j>`.

## Main results

- `QuantumAlg.Gate.applyVec_pow_eigenstate` — `(U^m)|u> = lam^m |u>` for an
  eigenstate, at the raw-vector layer.
- `QuantumAlg.controlled_pow_kickback` — the per-control-qubit phase kickback
  of the QPE controlled-power ladder.
- `QuantumAlg.phaseState_eq_qftApplyKet` — `phaseState t (j/2^t) = QFT t |j>`.
- `QuantumAlg.QuantumPhaseEstimation.main_exact_dyadic` — exact QPE readout.
- `QuantumAlg.QuantumPhaseEstimation.main_exact_probability_one` — the basis
  outcome `j` has probability one after the exact readout.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-! ### Eigenstates under gate powers -/

/-- An eigenstate of `U` is an eigenstate of every power `U ^ m`, with the
eigenvalue raised to the same power. This is stated at the raw-vector layer
because `lam • u` is not itself a `PureState` unless a unit-norm proof is
supplied. -/
theorem Gate.applyVec_pow_eigenstate {n : Nat} {U : Gate (Qubits n)} {u : PureState (Qubits n)}
    {lam : Complex}
    (hu : U.applyVec (u : StateVector (Qubits n)) = lam • (u : StateVector (Qubits n))) (m : Nat) :
    (U ^ m).applyVec (u : StateVector (Qubits n)) = lam ^ m • (u : StateVector (Qubits n)) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Gate.one_applyVec, one_smul]
  | succ m ih =>
      rw [pow_succ, Gate.mul_applyVec, hu, Gate.applyVec_smul, ih, smul_smul,
        ← pow_succ']

/-! ### Per-qubit phase kickback (QPE ladder) -/

/-- Per-control-qubit phase kickback for the QPE ladder. The control qubit `s`
controls `U^{2^s}`. On `|+> ⊗ |u>` with eigenvalue `exp(2*pi*i*phi)`, the
controlled power leaves `|u>` fixed and writes the relative phase
`exp(2*pi*i*phi*2^s)` onto the `|1>` branch. -/
theorem controlled_pow_kickback {n : Nat} (U : Gate (Qubits n))
    (u : PureState (Qubits n)) (phi : Real)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp (2 * Real.pi * phi * Complex.I) • (u : StateVector (Qubits n))) (s : Nat) :
    (Gate.controlled (U ^ (2 ^ s))).applyVec
        (StateVector.tensor (ketPlus : StateVector (Qubits 1)) (u : StateVector (Qubits n)))
      =
      StateVector.tensor
        ((invSqrt2 • ket0
          + (Complex.exp ((2 * Real.pi * (phi * (2 : Real) ^ s) : Real) * Complex.I)
              * invSqrt2) • ket1 : StateVector (Qubits 1)))
        (u : StateVector (Qubits n)) := by
  have hpow : (U ^ (2 ^ s)).applyVec (u : StateVector (Qubits n))
      = Complex.exp ((2 * Real.pi * (phi * (2 : Real) ^ s) : Real) * Complex.I)
          • (u : StateVector (Qubits n)) := by
    rw [Gate.applyVec_pow_eigenstate hu (2 ^ s), ← Complex.exp_nat_mul]
    congr 1
    congr 1
    push_cast
    ring
  rw [show (ketPlus : StateVector (Qubits 1)) =
      (invSqrt2 • ket0 + invSqrt2 • ket1 : StateVector (Qubits 1)) from by
        change ketPlusVec = (invSqrt2 • ket0 + invSqrt2 • ket1 : StateVector (Qubits 1))
        rw [ketPlusVec, smul_add],
    GeneralizedPhaseKickback.main (U ^ (2 ^ s)) u
      (2 * Real.pi * (phi * (2 : Real) ^ s)) hpow invSqrt2 invSqrt2]

/-- Source-level exact-QPE input: an `n`-qubit unitary, an eigenstate, and its
eigenphase. The controlled powers of `unitary` are the oracle calls used by the
phase-estimation ladder. -/
structure QPEEigenstateInput (n : Nat) where
  /-- The unitary whose eigenphase is estimated by controlled powers. -/
  unitary : Gate (Qubits n)
  /-- Normalized eigenstate supplied to the phase-estimation circuit. -/
  eigenstate : PureState (Qubits n)
  /-- Real phase parameter for the eigenvalue `exp (2 * pi * i * phase)`. -/
  phase : Real
  eigenstate_eq :
    unitary.applyVec (eigenstate : StateVector (Qubits n)) =
      Complex.exp (2 * Real.pi * phase * Complex.I) • (eigenstate : StateVector (Qubits n))

/-- The per-control-qubit kickbacks available from a source-level QPE input. -/
def QPEControlledPowerKickbacks {n : Nat} (P : QPEEigenstateInput n) : Prop :=
  forall s : Nat,
    (Gate.controlled (P.unitary ^ (2 ^ s))).applyVec
        (StateVector.tensor (ketPlus : StateVector (Qubits 1))
          (P.eigenstate : StateVector (Qubits n)))
      =
      StateVector.tensor
        ((invSqrt2 • ket0
          + (Complex.exp ((2 * Real.pi * (P.phase * (2 : Real) ^ s) : Real) * Complex.I)
              * invSqrt2) • ket1 : StateVector (Qubits 1)))
        (P.eigenstate : StateVector (Qubits n))

theorem qpe_eigenstate_controlled_power_kickbacks {n : Nat}
    (P : QPEEigenstateInput n) :
    QPEControlledPowerKickbacks P := by
  intro s
  exact controlled_pow_kickback P.unitary P.eigenstate P.phase P.eigenstate_eq s

/-! ### Phase superposition and the Fourier bridge -/

/-- The QPE phase superposition on a `t`-qubit register for eigenphase `phi`:
`(1/sqrt N) * sum_k exp(2*pi*i*phi*k) |k>`. -/
def phaseState (t : Nat) (phi : Real) : StateVector (Qubits t) :=
  WithLp.toLp 2 fun k : Fin (2 ^ t) =>
    invSqrtN t * Complex.exp (2 * Real.pi * phi * k.val * Complex.I)

@[simp]
theorem phaseState_apply (t : Nat) (phi : Real) (k : Fin (2 ^ t)) :
    phaseState t phi k =
      invSqrtN t * Complex.exp (2 * Real.pi * phi * k.val * Complex.I) :=
  rfl

@[simp]
theorem probOutcome_phaseState (t : Nat) (phi : Real) (k : Fin (2 ^ t)) :
    StateVector.probOutcome (phaseState t phi) k = ((2 : ℝ) ^ t)⁻¹ := by
  have hphase :
      ‖Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * (phi : ℂ) *
        (k.val : ℂ) * Complex.I)‖ = 1 := by
    simpa [mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (2 * Real.pi * phi * k.val)
  rw [StateVector.probOutcome, phaseState_apply, norm_mul, norm_invSqrtN,
    hphase, mul_one, inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ t)]

theorem sum_probOutcome_phaseState (t : Nat) (phi : Real) :
    ∑ k : Fin (2 ^ t), StateVector.probOutcome (phaseState t phi) k = 1 := by
  calc
    ∑ k : Fin (2 ^ t), StateVector.probOutcome (phaseState t phi) k =
        ∑ _k : Fin (2 ^ t), ((2 : ℝ) ^ t)⁻¹ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact probOutcome_phaseState t phi k
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_pow]
      exact mul_inv_cancel₀ (pow_ne_zero t (by norm_num : (2 : ℝ) ≠ 0))

theorem norm_phaseState (t : Nat) (phi : Real) :
    ‖phaseState t phi‖ = 1 := by
  have hsq : ‖phaseState t phi‖ ^ 2 = (1 : ℝ) ^ 2 := by
    rw [← StateVector.sum_probOutcome, sum_probOutcome_phaseState]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq

/-- The QPE phase superposition packaged as a pure state for arbitrary
eigenphase. -/
def phasePureState (t : Nat) (phi : Real) : PureState (Qubits t) :=
  PureState.ofVec (phaseState t phi) (norm_phaseState t phi)

/-- Closed-form geometric-sum amplitude for observing phase-register index `j`
after inverse QFT on an eigenphase `phi`. -/
def phaseRegisterGeometricAmplitude (t : Nat) (phi : Real) (j : Fin (2 ^ t)) : ℂ :=
  (((2 : ℝ) ^ t : ℂ))⁻¹ *
    ∑ k : Fin (2 ^ t),
      Complex.exp (2 * Real.pi *
        (((phi - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I)

/-- Dyadic/Fourier bridge: when the eigenphase is `j / 2^t`, the QPE phase
superposition is exactly `QFT t |j>`. -/
theorem phaseState_eq_qftApplyKet (t : Nat) (j : Fin (2 ^ t)) :
    phaseState t ((j.val : Real) / (2 : Real) ^ t)
      = ((QFT t).apply (ket j) : StateVector (Qubits t)) := by
  apply WithLp.ofLp_injective
  funext k
  change phaseState t ((j.val : Real) / (2 : Real) ^ t) k
      = ((QFT t).apply (ket j) : StateVector (Qubits t)) k
  rw [phaseState_apply, QFT_apply_ket, omega, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

/-! ### Inverse-QFT readout -/

/-- The inverse quantum Fourier transform, `QFT†`. -/
def invQFT (t : Nat) : Gate (Qubits t) := (QFT t).conjTranspose

theorem invQFT_phaseState_term_eq (t : Nat) (phi : Real)
    (j k : Fin (2 ^ t)) :
    star (invSqrtN t * omega t ^ (k.val * j.val)) *
        (invSqrtN t * Complex.exp (2 * Real.pi * phi * k.val * Complex.I)) =
      (((2 : ℝ) ^ t : ℂ))⁻¹ *
        Complex.exp (2 * Real.pi *
          (((phi - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
  rw [star_mul', star_invSqrtN, star_pow, star_omega]
  calc
    invSqrtN t * (omega t)⁻¹ ^ (k.val * j.val) *
        (invSqrtN t * Complex.exp (2 * ↑Real.pi * ↑phi * ↑↑k * Complex.I)) =
        (invSqrtN t * invSqrtN t) *
          ((omega t)⁻¹ ^ (k.val * j.val) *
            Complex.exp (2 * ↑Real.pi * ↑phi * ↑↑k * Complex.I)) := by ring
    _ = (((2 : ℝ) ^ t : ℂ))⁻¹ *
        ((omega t)⁻¹ ^ (k.val * j.val) *
          Complex.exp (2 * ↑Real.pi * ↑phi * ↑↑k * Complex.I)) := by
      rw [invSqrtN_mul_self]
      norm_num
    _ = (((2 : ℝ) ^ t : ℂ))⁻¹ *
        Complex.exp (2 * Real.pi *
          (((phi - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
      congr 1
      rw [omega]
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp [pow_ne_zero t (by norm_num : (2 : ℝ) ≠ 0)]
      ring

/-- Inverse QFT converts a QPE phase state into the standard geometric-sum
amplitude formula. -/
theorem invQFT_phaseState_apply_geometricSum (t : Nat) (phi : Real)
    (j : Fin (2 ^ t)) :
    (invQFT t).applyVec (phaseState t phi) j =
      phaseRegisterGeometricAmplitude t phi j := by
  rw [phaseRegisterGeometricAmplitude]
  calc
    (invQFT t).applyVec (phaseState t phi) j =
        ∑ k : Fin (2 ^ t),
          star (invSqrtN t * omega t ^ (k.val * j.val)) *
            (invSqrtN t * Complex.exp (2 * Real.pi * phi * k.val * Complex.I)) := by
      rw [Gate.applyVec_apply]
      simp [invQFT, QFT, QFTMatrix, phaseState, Matrix.conjTranspose_apply]
    _ = ∑ k : Fin (2 ^ t),
        (((2 : ℝ) ^ t : ℂ))⁻¹ *
          Complex.exp (2 * Real.pi *
            (((phi - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact invQFT_phaseState_term_eq t phi j k
    _ = (((2 : ℝ) ^ t : ℂ))⁻¹ *
        ∑ k : Fin (2 ^ t),
          Complex.exp (2 * Real.pi *
            (((phi - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
      rw [Finset.mul_sum]

/-- The inverse QFT undoes the QFT on a basis ket. -/
theorem qpe_readout (t : Nat) (j : Fin (2 ^ t)) :
    Gate.apply (invQFT t) ((QFT t).apply (ket j)) = ket j := by
  rw [invQFT, ← Gate.mul_apply]
  have h : (QFT t).conjTranspose * QFT t = (1 : Gate (Qubits t)) := by
    ext i k
    change ((QFTMatrix t).conjTranspose * QFTMatrix t) i k = (1 : HilbertOperator (Qubits t)) i k
    have hU := QFT_mem_unitaryGroup t
    have hM : (QFTMatrix t).conjTranspose * QFTMatrix t = 1 := by
      rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    rw [hM]
  rw [h, Gate.one_apply]

/-- Raw-vector form of the inverse-QFT readout. -/
theorem qpe_readoutVec (t : Nat) (j : Fin (2 ^ t)) :
    (invQFT t).applyVec (((QFT t).apply (ket j)) : StateVector (Qubits t))
      = (PureState.ket (R := Qubits t) j : StateVector (Qubits t)) := by
  change ((Gate.apply (invQFT t) ((QFT t).apply (ket j))) : StateVector (Qubits t))
      = (PureState.ket (R := Qubits t) j : StateVector (Qubits t))
  rw [qpe_readout]

/-! ### Exact QPE -/

/-- Exact quantum phase estimation. If the eigenphase is the dyadic rational
`phi = j / 2^t`, then applying inverse QFT to the QPE phase superposition returns
the computational-basis vector `|j>` exactly. -/
theorem QuantumPhaseEstimation.main_exact_dyadic (t : Nat) (j : Fin (2 ^ t))
    (phi : Real) (hphi : phi = (j.val : Real) / (2 : Real) ^ t) :
    (invQFT t).applyVec (phaseState t phi)
      = (PureState.ket (R := Qubits t) j : StateVector (Qubits t)) := by
  subst hphi
  rw [phaseState_eq_qftApplyKet]
  exact qpe_readoutVec t j

/-- The exact readout has deterministic basis outcome `j`. -/
theorem QuantumPhaseEstimation.main_exact_probability_one (t : Nat) (j : Fin (2 ^ t))
    (phi : Real) (_hphi : phi = (j.val : Real) / (2 : Real) ^ t) :
    PureState.probOutcome (ket j : PureState (Qubits t)) j = 1 := by
  rw [PureState.probOutcome_ket, if_pos rfl]

/-- Trusted decoupled phase-register resource profile for exact dyadic QPE. -/
def qpeExactResourceProfile (t : Nat) : ResourceProfile where
  oracleQueries := 2 ^ t - 1
  hadamardGates := t
  elementaryGates := t ^ 2
  classicalOps := 0

theorem qpeExactResourceProfile_exact (t : Nat) :
    ResourceProfile.HasExactCounts
      (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  simp [ResourceProfile.HasExactCounts, qpeExactResourceProfile]

/-- Typed circuit witness for the exact QPE phase-register endpoint. -/
def qpeExactCircuit (t : Nat) : Circuit (Qubits t) :=
  Circuit.abstract (Qubits t) "quantum-phase-estimation" (qpeExactResourceProfile t)
    (t ^ 2) (2 ^ t - 1)

/-- Exact QPE readout with the decoupled phase-register resource profile. -/
theorem QuantumPhaseEstimation.main_exact_dyadic_with_resources (t : Nat)
    (j : Fin (2 ^ t)) (phi : Real)
    (hphi : phi = (j.val : Real) / (2 : Real) ^ t) :
    (invQFT t).applyVec (phaseState t phi)
      = (PureState.ket (R := Qubits t) j : StateVector (Qubits t)) ∧
      ResourceProfile.HasExactCounts
        (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  constructor
  · exact QuantumPhaseEstimation.main_exact_dyadic t j phi hphi
  · exact qpeExactResourceProfile_exact t

/-- Exact QPE from the source-level eigenstate/access assumptions, paired with
the trusted controlled-power resource profile. The source describes QFT-based
QPE under an exact binary phase assumption and deterministic recovery
[Lin22, phaseestimation.tex:510-566, 640-666; CEMM98, cemm6.tex:574]. -/
theorem QuantumPhaseEstimation.main_exact_eigenstate_readout_with_resources {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (j : Fin (2 ^ t))
    (hphase : P.phase = (j.val : Real) / (2 : Real) ^ t) :
    QPEControlledPowerKickbacks P ∧
      (invQFT t).applyVec (phaseState t P.phase)
        = (PureState.ket (R := Qubits t) j : StateVector (Qubits t)) ∧
        ResourceProfile.HasExactCounts
          (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  constructor
  · exact qpe_eigenstate_controlled_power_kickbacks P
  · exact QuantumPhaseEstimation.main_exact_dyadic_with_resources t j P.phase hphase

/-- Exact QPE from the source-level eigenstate/access assumptions, phrased as
an exact estimate theorem. In the dyadic regime the phase estimate has zero
error, so it satisfies any nonnegative precision and failure-probability
thresholds. -/
theorem QuantumPhaseEstimation.main {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (j : Fin (2 ^ t))
    (eps eta : ℝ) (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hphase : P.phase = (j.val : Real) / (2 : Real) ^ t) :
    QPEControlledPowerKickbacks P ∧
      (invQFT t).applyVec (phaseState t P.phase)
        = (PureState.ket (R := Qubits t) j : StateVector (Qubits t)) ∧
        |P.phase - (j.val : ℝ) / (2 : ℝ) ^ t| ≤ eps ∧
          1 - PureState.probOutcome (ket j : PureState (Qubits t)) j ≤ eta ∧
            ResourceProfile.HasExactCounts
              (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  refine ⟨qpe_eigenstate_controlled_power_kickbacks P, ?_⟩
  have hreadout :
      (invQFT t).applyVec (phaseState t P.phase)
        = (PureState.ket (R := Qubits t) j : StateVector (Qubits t)) :=
    QuantumPhaseEstimation.main_exact_dyadic t j P.phase hphase
  refine ⟨hreadout, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [hphase, sub_self, abs_zero]
    exact heps
  · refine ⟨?_, qpeExactResourceProfile_exact t⟩
    rw [QuantumPhaseEstimation.main_exact_probability_one t j P.phase hphase]
    simpa using heta

/-- Resource-correct public witness for exact QPE: the correctness theorem and
resource counts refer to one typed circuit boundary. -/
def QuantumPhaseEstimation.mainResourceCorrectWitness {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (j : Fin (2 ^ t))
    (eps eta : ℝ) (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hphase : P.phase = (j.val : Real) / (2 : Real) ^ t) :
    ResourceCorrectWitness (R := Qubits t)
      (QPEControlledPowerKickbacks P ∧
        (invQFT t).applyVec (phaseState t P.phase)
          = (PureState.ket (R := Qubits t) j : StateVector (Qubits t)) ∧
          |P.phase - (j.val : ℝ) / (2 : ℝ) ^ t| ≤ eps ∧
            1 - PureState.probOutcome (ket j : PureState (Qubits t)) j ≤ eta ∧
              ResourceProfile.HasExactCounts
                (qpeExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0)
      (ResourceProfile.HasExactCounts (qpeExactCircuit t).resources
        (2 ^ t - 1) t (t ^ 2) 0) := by
  exact
    { circuit := qpeExactCircuit t
      correctness := QuantumPhaseEstimation.main P t j eps eta heps heta hphase
      resources := by simpa [qpeExactCircuit] using qpeExactResourceProfile_exact t }

end

end QuantumAlg
