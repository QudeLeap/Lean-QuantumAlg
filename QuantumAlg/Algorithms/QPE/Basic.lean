/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Real.Basic
public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.State.Basic
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Basic
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Util.Complex
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Kets

/-!
# Quantum phase estimation foundations and exact dyadic specialization

Quantum phase estimation (QPE) reads the eigenphase of a unitary `U` into a
`t`-qubit register [Lin22, phaseestimation.tex:510; CEMM98, cemm6.tex:574].
This module formalizes the exact dyadic regime, where the eigenphase is
`phi = j / 2^t` for some `j : Fin (2^t)`.

The phase-register superposition is a metadata-free `NormalizedVector`; its
amplitude formula is exposed through coercion and pointwise evaluation. The
readout theorem says that inverse QFT maps that normalized phase vector to the
computational-basis vector `|j>`.

## Main results

- `QuantumAlg.qpeGatePower_applyVec_eigenstate` — `(U^m)|u> = lam^m |u>` for an
  eigenstate, at the raw-vector layer.
- `QuantumAlg.controlled_pow_kickback` — the per-control-qubit phase kickback
  of the QPE controlled-power ladder.
- `QuantumAlg.phaseState_eq_qftApplyKet` — `phaseState t (j/2^t) = QFT t |j>`.
- `QuantumAlg.QuantumPhaseEstimation.main_exact_dyadic` — exact QPE readout.
- `QuantumAlg.QuantumPhaseEstimation.main_exact_probability_one` — the basis
  outcome `j` has probability one after the exact readout.
-/

section

namespace QuantumAlg

open NormalizedVector Gate
open scoped BigOperators

noncomputable section

/-! ### Eigenstates under gate powers -/

/-- A metadata-free power of the source unitary. QPE attaches query and depth
metadata only when this operator is placed in the executable circuit. -/
def qpeGatePower {n : Nat} (U : UnitaryOperator (Qubits n)) (m : Nat) :
    UnitaryOperator (Qubits n) :=
  U ^ m

/-- An eigenstate of `U` is an eigenstate of every power `U ^ m`, with the
eigenvalue raised to the same power. This is stated at the raw-vector layer
because `lam • u` is not itself a `NormalizedVector` without a modulus-one
proof for `lam`. -/
theorem qpeGatePower_applyVec_eigenstate {n : Nat}
    {U : UnitaryOperator (Qubits n)} {u : NormalizedVector (Qubits n)}
    {lam : Complex}
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      lam • (u : HilbertVector (Qubits n))) (m : Nat) :
    (qpeGatePower U m).applyVec (u : HilbertVector (Qubits n)) =
      lam ^ m • (u : HilbertVector (Qubits n)) := by
  change HilbertOperator.applyVec ((U : HilbertOperator (Qubits n)) ^ m)
      (u : HilbertVector (Qubits n)) = lam ^ m • (u : HilbertVector (Qubits n))
  have huOp : HilbertOperator.applyVec (U : HilbertOperator (Qubits n))
      (u : HilbertVector (Qubits n)) = lam • (u : HilbertVector (Qubits n)) := hu
  induction m with
  | zero => rw [pow_zero, pow_zero, HilbertOperator.one_applyVec, one_smul]
  | succ m ih =>
      rw [pow_succ, HilbertOperator.mul_applyVec, huOp,
        HilbertOperator.applyVec_smul, ih, smul_smul,
        ← pow_succ']

/-! ### Per-qubit phase kickback (QPE ladder) -/

/-- Per-control-qubit phase kickback for the QPE ladder. The control qubit `s`
controls `U^{2^s}`. On `|+> ⊗ |u>` with eigenvalue `exp(2*pi*i*phi)`, the
controlled power leaves `|u>` fixed and writes the relative phase
`exp(2*pi*i*phi*2^s)` onto the `|1>` branch. -/
theorem controlled_pow_kickback {n : Nat} (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (φ : Real)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp (2 * Real.pi * φ * Complex.I) • (u : HilbertVector (Qubits n))) (s : Nat) :
    (UnitaryOperator.controlledQubits (qpeGatePower U (2 ^ s))).applyVec
        (HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) (u : HilbertVector (Qubits n)))
      =
      HilbertVector.tensor
        ((invSqrt2 • ket0
          + (Complex.exp ((2 * Real.pi * (φ * (2 : Real) ^ s) : Real) * Complex.I)
              * invSqrt2) • ket1 : HilbertVector (Qubits 1)))
        (u : HilbertVector (Qubits n)) := by
  have hpow : (qpeGatePower U (2 ^ s)).applyVec (u : HilbertVector (Qubits n))
      = Complex.exp ((2 * Real.pi * (φ * (2 : Real) ^ s) : Real) * Complex.I)
          • (u : HilbertVector (Qubits n)) := by
    rw [qpeGatePower_applyVec_eigenstate hu (2 ^ s), ← Complex.exp_nat_mul]
    congr 1
    congr 1
    push_cast
    ring
  rw [show (ketPlus : HilbertVector (Qubits 1)) =
      (invSqrt2 • ket0 + invSqrt2 • ket1 : HilbertVector (Qubits 1)) from by
        rw [ketPlus_coe, smul_add]]
  rw [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.smul_tensor,
    UnitaryOperator.applyVec_add, UnitaryOperator.applyVec_smul,
    UnitaryOperator.applyVec_smul,
    UnitaryOperator.controlledQubits_applyVec_ket0_tensor,
    UnitaryOperator.controlledQubits_applyVec_ket1_tensor]
  rw [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.smul_tensor]
  rw [hpow, HilbertVector.tensor_smul, smul_smul]
  module

/-- Source-level exact-QPE input: an `n`-qubit unitary, an eigenstate, and its
eigenphase. The controlled powers of `unitary` are the oracle calls used by the
phase-estimation ladder. -/
public structure QPEEigenstateInput (n : Nat) where
  /-- The unitary whose eigenphase is estimated by controlled powers. -/
  unitary : UnitaryOperator (Qubits n)
  /-- Normalized eigenstate supplied to the phase-estimation circuit. -/
  eigenstate : NormalizedVector (Qubits n)
  /-- Real phase parameter for the eigenvalue `exp (2 * pi * i * phase)`. -/
  phase : Real
  eigenstate_eq :
    unitary.applyVec (eigenstate : HilbertVector (Qubits n)) =
      Complex.exp (2 * Real.pi * phase * Complex.I) • (eigenstate : HilbertVector (Qubits n))

/-- The per-control-qubit kickbacks available from a source-level QPE input. -/
def QPEControlledPowerKickbacks {n : Nat} (P : QPEEigenstateInput n) : Prop :=
  forall s : Nat,
    (UnitaryOperator.controlledQubits (qpeGatePower P.unitary (2 ^ s))).applyVec
        (HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1))
          (P.eigenstate : HilbertVector (Qubits n)))
      =
      HilbertVector.tensor
        ((invSqrt2 • ket0
          + (Complex.exp ((2 * Real.pi * (P.phase * (2 : Real) ^ s) : Real) * Complex.I)
              * invSqrt2) • ket1 : HilbertVector (Qubits 1)))
        (P.eigenstate : HilbertVector (Qubits n))

theorem qpe_eigenstate_controlled_power_kickbacks {n : Nat}
    (P : QPEEigenstateInput n) :
    QPEControlledPowerKickbacks P := by
  intro s
  exact controlled_pow_kickback P.unitary P.eigenstate P.phase P.eigenstate_eq s

/-! ### Phase superposition and the Fourier bridge -/

private theorem qpe_norm_sq_invSqrtN (t : Nat) :
    ‖invSqrtN t‖ ^ 2 = (((2 ^ t : Nat) : Real)⁻¹) := by
  rw [norm_invSqrtN, inv_pow,
    Real.sq_sqrt (by positivity : (0 : Real) ≤ (2 : Real) ^ t)]
  norm_num

/-- The canonical metadata-free QPE phase superposition:
`(1/sqrt N) * sum_k exp(2*pi*i*phi*k) |k>`. -/
def phaseState (t : Nat) (φ : Real) : NormalizedVector (Qubits t) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 (fun k : Fin (2 ^ t) =>
      invSqrtN t * Complex.exp (2 * Real.pi * φ * k.val * Complex.I)))
    (by
      rw [EuclideanSpace.norm_eq]
      have hsum :
          ∑ k : Fin (2 ^ t),
              ‖invSqrtN t *
                Complex.exp (2 * Real.pi * φ * k.val * Complex.I)‖ ^ 2 = 1 := by
        calc
          _ = ∑ _k : Fin (2 ^ t), ‖invSqrtN t‖ ^ 2 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_mul]
            have hexp :
                ‖Complex.exp (2 * Real.pi * φ * k.val * Complex.I)‖ = 1 := by
              simpa using Complex.norm_exp_ofReal_mul_I
                (2 * Real.pi * φ * (k.val : Real))
            rw [hexp, mul_one]
          _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, qpe_norm_sq_invSqrtN]
            norm_num
      rw [hsum, Real.sqrt_one])

@[simp]
theorem phaseState_coe (t : Nat) (φ : Real) :
    ((phaseState t φ : NormalizedVector (Qubits t)) : HilbertVector (Qubits t)) =
      WithLp.toLp 2 (fun k : Fin (2 ^ t) =>
        invSqrtN t * Complex.exp (2 * Real.pi * φ * k.val * Complex.I)) := rfl

@[simp]
theorem phaseState_apply (t : Nat) (φ : Real) (k : Fin (2 ^ t)) :
    phaseState t φ k =
      invSqrtN t * Complex.exp (2 * Real.pi * φ * k.val * Complex.I) :=
  rfl

/-- Closed-form geometric-sum amplitude for observing phase-register index `j`
after inverse QFT on an eigenphase `phi`. -/
def phaseRegisterGeometricAmplitude (t : Nat) (φ : Real) (j : Fin (2 ^ t)) : ℂ :=
  (((2 : ℝ) ^ t : ℂ))⁻¹ *
    ∑ k : Fin (2 ^ t),
      Complex.exp (2 * Real.pi *
        (((φ - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I)

/-- Dyadic/Fourier bridge: when the eigenphase is `j / 2^t`, the QPE phase
superposition is exactly `QFT t |j>`. -/
theorem phaseState_eq_qftApplyKet (t : Nat) (j : Fin (2 ^ t)) :
    phaseState t ((j.val : Real) / (2 : Real) ^ t) =
      UnitaryCircuit.applyNormalized (QFTCircuit t)
        (NormalizedVector.ket (R := Qubits t) j) := by
  apply NormalizedVector.ext
  intro k
  rw [phaseState_apply, QFT_apply_ket, ω, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

/-! ### Inverse-QFT readout -/

/-- The inverse-QFT readout as the dagger of the same typed QFT circuit. -/
def qpeReadoutCircuit (t : Nat) : UnitaryCircuit (Qubits t) :=
  UnitaryCircuit.dagger (QFTCircuit t)

/-- The metadata-free inverse quantum Fourier transform derived from the
readout circuit. -/
def invQFT (t : Nat) : UnitaryOperator (Qubits t) :=
  (qpeReadoutCircuit t).matrix





/-- Daggering the QFT readout preserves its strict event pool. -/
@[simp]
theorem qpeReadoutCircuit_eventCost (t : Nat) :
    (qpeReadoutCircuit t).eventCost = (QFTCircuit t).eventCost := rfl

/-- Exact strict gate-coordinate multiplicities of QPE's shared inverse-QFT
readout, derived by daggering the same `QFTCircuit` ledger. -/
theorem qpeReadoutCircuit_exact_event_gate_counts (t : Nat) :
    ResourcePool.count (.gate (.builtin "hadamard"))
        (qpeReadoutCircuit t).eventCost = t ∧
      ResourcePool.count (.gate qftControlledPhaseLabel)
          (qpeReadoutCircuit t).eventCost = t * (t - 1) / 2 ∧
      ResourcePool.count (.gate (.builtin "swap"))
          (qpeReadoutCircuit t).eventCost = t / 2 := by
  rw [qpeReadoutCircuit_eventCost]
  exact QFTCircuit_exact_event_gate_counts t

/-- Daggering the QFT readout records the inverse strict event critical path. -/
@[simp]
theorem qpeReadoutCircuit_eventDepth (t : Nat) :
    (qpeReadoutCircuit t).eventDepth = .inverse (QFTCircuit t).eventDepth := rfl

/-- Inversion preserves every evaluated strict-event critical-path length. -/
@[simp]
theorem qpeReadoutCircuit_evaluatedEventDepth
    (t : Nat) (assign : Resource.Event .quantum → Nat) :
    (qpeReadoutCircuit t).evaluatedEventDepth assign =
      (QFTCircuit t).evaluatedEventDepth assign := rfl

theorem invQFT_phaseState_term_eq (t : Nat) (φ : Real)
    (j k : Fin (2 ^ t)) :
    star (invSqrtN t * ω t ^ (k.val * j.val)) *
        (invSqrtN t * Complex.exp (2 * Real.pi * φ * k.val * Complex.I)) =
      (((2 : ℝ) ^ t : ℂ))⁻¹ *
        Complex.exp (2 * Real.pi *
          (((φ - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
  rw [star_mul', star_invSqrtN, star_pow, star_omega]
  calc
    invSqrtN t * (ω t)⁻¹ ^ (k.val * j.val) *
        (invSqrtN t * Complex.exp (2 * ↑Real.pi * ↑φ * ↑↑k * Complex.I)) =
        (invSqrtN t * invSqrtN t) *
          ((ω t)⁻¹ ^ (k.val * j.val) *
            Complex.exp (2 * ↑Real.pi * ↑φ * ↑↑k * Complex.I)) := by ring
    _ = (((2 : ℝ) ^ t : ℂ))⁻¹ *
        ((ω t)⁻¹ ^ (k.val * j.val) *
          Complex.exp (2 * ↑Real.pi * ↑φ * ↑↑k * Complex.I)) := by
      rw [invSqrtN_mul_self]
      norm_num
    _ = (((2 : ℝ) ^ t : ℂ))⁻¹ *
        Complex.exp (2 * Real.pi *
          (((φ - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
      congr 1
      rw [ω]
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp [pow_ne_zero t (by norm_num : (2 : ℝ) ≠ 0)]
      ring

/-- Inverse QFT converts a QPE phase state into the standard geometric-sum
amplitude formula. -/
theorem invQFT_phaseState_apply_geometricSum (t : Nat) (φ : Real)
    (j : Fin (2 ^ t)) :
    (invQFT t).apply (phaseState t φ) j =
      phaseRegisterGeometricAmplitude t φ j := by
  change UnitaryCircuit.applyVec (qpeReadoutCircuit t)
      (phaseState t φ : HilbertVector (Qubits t)) j = _
  rw [phaseRegisterGeometricAmplitude]
  calc
    UnitaryCircuit.applyVec (qpeReadoutCircuit t)
        (phaseState t φ : HilbertVector (Qubits t)) j =
        ∑ k : Fin (2 ^ t),
          star (invSqrtN t * ω t ^ (k.val * j.val)) *
            (invSqrtN t * Complex.exp (2 * Real.pi * φ * k.val * Complex.I)) := by
      rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec_apply]
      simp [qpeReadoutCircuit, QFTCircuit_matrix, QFTOperator_entry, phaseState,
        Matrix.conjTranspose_apply]
    _ = ∑ k : Fin (2 ^ t),
        (((2 : ℝ) ^ t : ℂ))⁻¹ *
          Complex.exp (2 * Real.pi *
            (((φ - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact invQFT_phaseState_term_eq t φ j k
    _ = (((2 : ℝ) ^ t : ℂ))⁻¹ *
        ∑ k : Fin (2 ^ t),
          Complex.exp (2 * Real.pi *
            (((φ - (j.val : ℝ) / (2 : ℝ) ^ t) * k.val : ℝ)) * Complex.I) := by
      rw [Finset.mul_sum]

/-- The inverse-QFT readout preserves normalization in its public contract. -/
theorem qpe_readoutNormalized (t : Nat) (j : Fin (2 ^ t)) :
    UnitaryCircuit.applyNormalized (qpeReadoutCircuit t)
        (UnitaryCircuit.applyNormalized (QFTCircuit t)
          (NormalizedVector.ket (R := Qubits t) j)) =
      NormalizedVector.ket (R := Qubits t) j := by
  apply NormalizedVector.ext
  intro i
  have hunitary := (QFTCircuit t).matrix.property
  have hcancel :
      HilbertOperator.applyVec
          ((QFTCircuit t).matrix : HilbertOperator (Qubits t)).conjTranspose
          (HilbertOperator.applyVec
            ((QFTCircuit t).matrix : HilbertOperator (Qubits t))
            (NormalizedVector.ket (R := Qubits t) j :
              HilbertVector (Qubits t))) =
        (NormalizedVector.ket (R := Qubits t) j : HilbertVector (Qubits t)) := by
    rw [← HilbertOperator.mul_applyVec]
    rw [show ((QFTCircuit t).matrix : HilbertOperator (Qubits t)).conjTranspose *
        ((QFTCircuit t).matrix : HilbertOperator (Qubits t)) = 1 by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp hunitary]
    exact HilbertOperator.one_applyVec _
  exact congrArg (fun ψ : HilbertVector (Qubits t) => ψ i) hcancel

/-! ### Exact QPE -/

/-- Exact quantum phase estimation. If the eigenphase is the dyadic rational
`phi = j / 2^t`, then applying inverse QFT to the QPE phase superposition returns
the computational-basis vector `|j>` exactly. -/
theorem QuantumPhaseEstimation.main_exact_dyadic (t : Nat) (j : Fin (2 ^ t))
    (φ : Real) (hphi : φ = (j.val : Real) / (2 : Real) ^ t) :
    UnitaryCircuit.applyNormalized (qpeReadoutCircuit t) (phaseState t φ) =
      NormalizedVector.ket (R := Qubits t) j := by
  subst hphi
  rw [phaseState_eq_qftApplyKet]
  exact qpe_readoutNormalized t j

/-- Computational-basis probability for a normalized phase-register vector. -/
def qpeBasisProbability {t : Nat} (state : NormalizedVector (Qubits t))
    (outcome : Fin (2 ^ t)) : Real :=
  ‖state outcome‖ ^ 2

/-- The exact readout has deterministic basis outcome `j`. -/
theorem QuantumPhaseEstimation.main_exact_probability_one (t : Nat) (j : Fin (2 ^ t))
    (φ : Real) (_hphi : φ = (j.val : Real) / (2 : Real) ^ t) :
    qpeBasisProbability
        (NormalizedVector.ket (R := Qubits t) j) j = 1 := by
  simp [qpeBasisProbability, NormalizedVector.ket_apply]

end

end QuantumAlg

end
