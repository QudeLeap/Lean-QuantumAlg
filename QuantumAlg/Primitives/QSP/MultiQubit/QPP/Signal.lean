/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Pair

/-!
# QPP alternating circuits

YZZYZ and alternating controlled-unitary QPP words, circuits, and resource profiles.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open PureState Module.End

noncomputable section

variable {n : ℕ}
variable {U : Gate (Qubits n)}

/-! ### The QPP word and its eigenspace decomposition -/

/-- The **quantum phase processor** in the YZZYZ (W-Z-W) convention: the QSP
word `qspYZZYZ` with each signal slot `R_Z(x)` replaced by the controlled
unitary `c-U`, the trainable blocks `R_Y(θⱼ)·R_Z(φⱼ)` acting on the ancilla
[WZYW23, arxiv_v3.tex:601]. -/
def qppYZZYZ (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) : Gate (Qubits (1 + n)) :=
  ps.foldl
    (fun W p =>
      W * (Gate.controlled U *
        Gate.tensor (rotY p.1 * rotZStd p.2) (1 : Gate (Qubits n))))
    (Gate.tensor (rotZStd φ * (rotY θ₀ * rotZStd φ₀))
      (1 : Gate (Qubits n)))

@[simp]
theorem qppYZZYZ_nil (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    qppYZZYZ U φ θ₀ φ₀ [] =
      Gate.tensor (rotZStd φ * (rotY θ₀ * rotZStd φ₀)) (1 : Gate (Qubits n)) :=
  rfl

theorem qppYZZYZ_concat (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (p : ℝ × ℝ) :
    qppYZZYZ U φ θ₀ φ₀ (ps ++ [p])
      = qppYZZYZ U φ θ₀ φ₀ ps
        * (Gate.controlled U * Gate.tensor (rotY p.1 * rotZStd p.2) (1 : Gate (Qubits n))) := by
  simp [qppYZZYZ, List.foldl_append]

/-- **Eigenspace decomposition of QPP** [WZYW23, arxiv_v3.tex:641]. On an
eigenstate `U|u⟩ = e^{iθ}|u⟩`, the QPP word acts as the single-qubit YZZYZ QSP
word at the signal `θ`, tensored with the untouched eigenstate, up to the
global phase `(e^{iθ/2})^L` (`L` = number of `c-U` calls):
`qppYZZYZ U φ θ₀ φ₀ ps (|ψ⟩ ⊗ |u⟩) = ((e^{iθ/2})^L · qspYZZYZ φ θ₀ φ₀ ps θ |ψ⟩) ⊗ |u⟩`. -/
theorem QPP.eigenstate_decomposition (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) (ψ : StateVector (Qubits 1)) :
    (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n)))
      = StateVector.tensor
          ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ ps.length
            • (qspYZZYZ φ θ₀ φ₀ ps θ).applyVec ψ)
          (u : StateVector (Qubits n)) := by
  induction ps using List.reverseRecOn generalizing ψ with
  | nil =>
      rw [qppYZZYZ_nil, qspYZZYZ_nil, List.length_nil, pow_zero, one_smul,
        Gate.tensor_applyVec_tensor, Gate.one_applyVec]
  | append_singleton ps p ih =>
      rw [qppYZZYZ_concat, Gate.mul_applyVec, Gate.mul_applyVec,
        Gate.tensor_applyVec_tensor, Gate.one_applyVec,
        QPP.eigenstate_reductionVec U u θ hu, ih, qspYZZYZ_concat,
        List.length_append, List.length_singleton]
      congr 1
      rw [Gate.applyVec_smul, smul_smul, ← pow_succ, ← Gate.mul_applyVec,
        ← Gate.mul_applyVec, mul_assoc]

/-! ### Phase evolution: realizing QSP transforms on the eigenphase -/

/-- **Quantum phase evolution** [WZYW23, arxiv_v3.tex:650]. Every trigonometric
transform admissible for single-qubit QSP (an `IsYZPair L A B`) is realized on
the eigenphase of `U` by a QPP word with `L` controlled-unitary calls: there are
angles `(φ, θ₀, φ₀, ps)` such that the QPP word maps `|ψ⟩ ⊗ |u⟩` to
`((e^{iθ/2})^L · qspMatYZ L A B θ |ψ⟩) ⊗ |u⟩` for every ancilla state. -/
theorem QPP.realizes_target (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧ ∀ ψ : PureState (Qubits 1),
      (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
          (StateVector.tensor (ψ : StateVector (Qubits 1)) (u : StateVector (Qubits n)))
        = StateVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L
              • HilbertOperator.applyVec (qspMatYZ L A B θ) (ψ : StateVector (Qubits 1)))
            (u : StateVector (Qubits n)) := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ := (TrigonometricQuantumSignalProcessing.main L A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, fun ψ => ?_⟩
  rw [QPP.eigenstate_decomposition U u θ hu, hlen]
  have happly := congrArg
    (fun A : HilbertOperator (Qubits 1) => HilbertOperator.applyVec A (ψ : StateVector (Qubits 1)))
    (hmat θ)
  simpa [Gate.applyVec] using congrArg
    (fun v : StateVector (Qubits 1) =>
      StateVector.tensor
        ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L • v)
        (u : StateVector (Qubits n)))
    happly

/-- Trusted resource profile for the YZZYZ QPP word currently formalized here:
`L` controlled-`U` signal calls and `2L+3` one-qubit processing rotations. -/
def qppYZZYZResourceProfile (L : ℕ) : ResourceProfile where
  oracleQueries := L
  hadamardGates := 0
  elementaryGates := 2 * L + 3
  classicalOps := 0

theorem qppYZZYZResourceProfile_exact (L : ℕ) :
    ResourceProfile.HasExactCounts
      (qppYZZYZResourceProfile L) L 0 (2 * L + 3) 0 := by
  simp [ResourceProfile.HasExactCounts, qppYZZYZResourceProfile]

/-- Typed circuit for the source YZZYZ QPP word.  This is the circuit-level
counterpart of `qppYZZYZ`: its matrix is the same gate used in the eigenphase
correctness proof, and its resources are the source `L`-signal-call counters
[WZYW23, arxiv_v3.tex:635-666]. -/
def qppYZZYZCircuit (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    Circuit (Qubits (1 + n)) :=
  Circuit.ofGate "qpp-yzzyz" (qppYZZYZ U φ θ₀ φ₀ ps)
    (qppYZZYZResourceProfile ps.length) (2 * ps.length + 3) ps.length

@[simp]
theorem qppYZZYZCircuit_matrix (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    ((qppYZZYZCircuit U φ θ₀ φ₀ ps).matrix : HilbertOperator (Qubits (1 + n))) =
      (qppYZZYZ U φ θ₀ φ₀ ps : HilbertOperator (Qubits (1 + n))) := by
  simp [qppYZZYZCircuit]

theorem qppYZZYZCircuit_resources_exact
    (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    ResourceProfile.HasExactCounts
      (qppYZZYZCircuit U φ θ₀ φ₀ ps).resources
      ps.length 0 (2 * ps.length + 3) 0 := by
  simpa [qppYZZYZCircuit] using qppYZZYZResourceProfile_exact ps.length

/-- QPP realization paired with the resource profile of the YZZYZ convention
formalized in this file. Conventions with alternating `controlled-U` and
`controlled-U†` have a different resource profile. -/
theorem qpp_realizes_target_with_resources (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    (∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧ ∀ ψ : PureState (Qubits 1),
      (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
          (StateVector.tensor (ψ : StateVector (Qubits 1)) (u : StateVector (Qubits n)))
        = StateVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L
              • HilbertOperator.applyVec (qspMatYZ L A B θ) (ψ : StateVector (Qubits 1)))
            (u : StateVector (Qubits n))) ∧
      ResourceProfile.HasExactCounts (qppYZZYZResourceProfile L) L 0 (2 * L + 3) 0 := by
  constructor
  · exact QPP.realizes_target U u θ hu L A B h
  · exact qppYZZYZResourceProfile_exact L

/-- Resource profile for an alternating controlled-`U` / controlled-`U†`
schedule of length `steps`: one controlled-unitary query and two one-qubit
processing rotations per schedule entry, plus the three front rotations. -/
def qppAlternatingScheduleResourceProfile (steps : ℕ) : ResourceProfile where
  oracleQueries := steps
  hadamardGates := 0
  elementaryGates := 2 * steps + 3
  classicalOps := 0

theorem qppAlternatingScheduleResourceProfile_exact (steps : ℕ) :
    ResourceProfile.HasExactCounts
      (qppAlternatingScheduleResourceProfile steps) steps 0 (2 * steps + 3) 0 := by
  simp [ResourceProfile.HasExactCounts, qppAlternatingScheduleResourceProfile]

/-- Resource profile for the source QPP theorem with a degree-`L` Laurent target:
the alternating schedule has length `2L`, hence `2L` controlled-unitary queries
and `4L+3` one-qubit processing rotations. -/
def qppAlternatingControlledResourceProfile (L : ℕ) : ResourceProfile where
  oracleQueries := 2 * L
  hadamardGates := 0
  elementaryGates := 4 * L + 3
  classicalOps := 0

theorem qppAlternatingControlledResourceProfile_exact (L : ℕ) :
    ResourceProfile.HasExactCounts
      (qppAlternatingControlledResourceProfile L) (2 * L) 0 (4 * L + 3) 0 := by
  simp [ResourceProfile.HasExactCounts, qppAlternatingControlledResourceProfile]

/-- The three one-qubit rotations at the front of the alternating QPP word. -/
def qppAlternatingInitialResourceProfile : ResourceProfile where
  oracleQueries := 0
  hadamardGates := 0
  elementaryGates := 3
  classicalOps := 0

/-- One alternating controlled-`U` / controlled-`U†` step: one controlled query
and one trainable `R_Y R_Z` processing block. Even zero-based indices are the
`[U†,0;0,I]` branch, odd indices are the `[I,0;0,U]` branch
[WZYW23, arxiv_v3.tex:601-609]. -/
def qppAlternatingStepResourceProfile : ResourceProfile where
  oracleQueries := 1
  hadamardGates := 0
  elementaryGates := 2
  classicalOps := 0

/-- Initial gate for the alternating controlled-`U` / controlled-`U†` QPP word. -/
def qppAlternatingInitialGate (n : ℕ) (φ θ₀ φ₀ : ℝ) : Gate (Qubits (1 + n)) :=
  Gate.tensor (rotZStd φ * (rotY θ₀ * rotZStd φ₀)) (1 : Gate (Qubits n))

/-- One source-aligned alternating QPP step. At even zero-based indices this is
`[U†,0;0,I] R_Y(θ_j)R_Z(φ_j)`; at odd indices it is
`[I,0;0,U] R_Y(θ_j)R_Z(φ_j)` [WZYW23, arxiv_v3.tex:601-609]. -/
def qppAlternatingStepGate (U : Gate (Qubits n)) (j : ℕ) (p : ℝ × ℝ) :
    Gate (Qubits (1 + n)) :=
  (if j % 2 = 0 then Gate.controlledOnZero U.conjTranspose else Gate.controlled U) *
    Gate.tensor (rotY p.1 * rotZStd p.2) (1 : Gate (Qubits n))

/-- One source-aligned alternating QPP step reduces to the corresponding
one-qubit phase signal on an eigenstate: even zero-based indices use
`diag(e^{-iθ},1)`, odd indices use `diag(1,e^{iθ})`
[WZYW23, arxiv_v3.tex:601-609,641]. -/
theorem QPP.qppAlternatingStep_eigenstate_reductionVec
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (j : ℕ) (p : ℝ × ℝ) (ψ : StateVector (Qubits 1)) :
    (qppAlternatingStepGate U j p).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n))) =
      StateVector.tensor
        ((if j % 2 = 0 then phaseGateOnZero (-θ) else phaseGate θ).applyVec
          ((rotY p.1 * rotZStd p.2).applyVec ψ))
        (u : StateVector (Qubits n)) := by
  rw [qppAlternatingStepGate, Gate.mul_applyVec, Gate.tensor_applyVec_tensor,
    Gate.one_applyVec]
  by_cases h : j % 2 = 0
  · simp [h, QPP.controlledOnZero_conjTranspose_apply_eigenstate_phaseVec U u θ hu]
  · simp [h, controlled_apply_eigenstate_phaseVec U u θ hu]

/-- The one-qubit signal step induced by Wang's alternating QPP word on an
eigenphase `θ`. -/
def qppAlternatingSignalStep (θ : ℝ) (j : ℕ) (p : ℝ × ℝ) : Gate (Qubits 1) :=
  (if j % 2 = 0 then phaseGateOnZero (-θ) else phaseGate θ) *
    (rotY p.1 * rotZStd p.2)

/-- The global phase contributed by the `j`-th source QPP signal block after
reducing it to the YZZYZ `R_Z(θ)` signal on an eigenspace
[WZYW23, arxiv_v3.tex:641]. -/
def qppAlternatingStepScalar (θ : ℝ) (j : ℕ) : ℂ :=
  if j % 2 = 0 then
    Complex.exp (-(θ / 2 : ℝ) * Complex.I)
  else
    Complex.exp ((θ / 2 : ℝ) * Complex.I)

/-- Product of the source global phases over an indexed alternating QPP
schedule. -/
def qppAlternatingSignalScalarFrom (θ : ℝ) (start : ℕ) : List (ℝ × ℝ) → ℂ
  | [] => 1
  | _ :: rest =>
      qppAlternatingStepScalar θ start *
        qppAlternatingSignalScalarFrom θ (start + 1) rest

/-- Product of the source global phases in the alternating QPP schedule. -/
def qppAlternatingSignalScalar (θ : ℝ) (ps : List (ℝ × ℝ)) : ℂ :=
  qppAlternatingSignalScalarFrom θ 0 ps

/-- One source alternating signal step is the YZZYZ signal step times its
source global phase on every one-qubit vector. -/
theorem QPP.qppAlternatingSignalStep_applyVec_eq_scalar_yzzyz_step
    (θ : ℝ) (j : ℕ) (p : ℝ × ℝ) (ψ : StateVector (Qubits 1)) :
    (qppAlternatingSignalStep θ j p).applyVec ψ =
      qppAlternatingStepScalar θ j •
        ((rotZStd θ * (rotY p.1 * rotZStd p.2)).applyVec ψ) := by
  rw [qppAlternatingSignalStep, Gate.mul_applyVec, Gate.mul_applyVec]
  by_cases hj : j % 2 = 0
  · rw [if_pos hj, qppAlternatingStepScalar, if_pos hj,
      phaseGateOnZero_applyVec_eq_smul_rotZStd]
    rw [Gate.mul_applyVec, Gate.mul_applyVec]
  · rw [if_neg hj, qppAlternatingStepScalar, if_neg hj,
      phaseGate_applyVec_eq_smul_rotZStd]
    rw [Gate.mul_applyVec, Gate.mul_applyVec]

/-- The one-qubit alternating signal word obtained from the source QPP word on
an eigenphase `θ` [WZYW23, arxiv_v3.tex:641]. -/
def qppAlternatingSignalGate (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    Gate (Qubits 1) :=
  ps.zipIdx.foldl
    (fun W jp => W * qppAlternatingSignalStep θ jp.2 jp.1)
    (rotZStd φ * (rotY θ₀ * rotZStd φ₀))

/-- Indexed-fold version of the alternating one-qubit signal word. -/
theorem qppAlternatingSignalGate_eq_foldlIdx
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    qppAlternatingSignalGate θ φ θ₀ φ₀ ps =
      ps.foldlIdx (fun j W p => W * qppAlternatingSignalStep θ j p)
        (rotZStd φ * (rotY θ₀ * rotZStd φ₀)) 0 := by
  rw [qppAlternatingSignalGate, List.foldlIdx_eq_foldl_zipIdx]

/-- General indexed-fold reduction of the source alternating signal word to
the YZZYZ word, keeping the accumulated source global phase explicit. -/
theorem QPP.qppAlternatingSignal_fold_applyVec_eq_scalar_yzzyz_fold
    (θ : ℝ) (ps : List (ℝ × ℝ)) (start : ℕ)
    (W Q : Gate (Qubits 1)) (c : ℂ)
    (hW : ∀ ψ : StateVector (Qubits 1), W.applyVec ψ = c • Q.applyVec ψ)
    (ψ : StateVector (Qubits 1)) :
    (ps.foldlIdx (fun j W p => W * qppAlternatingSignalStep θ j p) W start).applyVec ψ =
      (c * qppAlternatingSignalScalarFrom θ start ps) •
        ((ps.foldl
          (fun Q p => Q * (rotZStd θ * (rotY p.1 * rotZStd p.2))) Q).applyVec ψ) := by
  induction ps generalizing start W Q c ψ with
  | nil =>
      simpa [qppAlternatingSignalScalarFrom] using hW ψ
  | cons p ps ih =>
      simp only [List.foldlIdx_cons, List.foldl_cons, qppAlternatingSignalScalarFrom]
      have hnext := ih (start + 1)
        (W * qppAlternatingSignalStep θ start p)
        (Q * (rotZStd θ * (rotY p.1 * rotZStd p.2)))
        (c * qppAlternatingStepScalar θ start)
        (by
          intro ψ'
          simp [Gate.mul_applyVec,
            QPP.qppAlternatingSignalStep_applyVec_eq_scalar_yzzyz_step,
            hW, smul_smul])
        ψ
      simpa [mul_assoc] using hnext

/-- Adjacent alternating source phases cancel. -/
theorem qppAlternatingStepScalar_mul_succ (θ : ℝ) (j : ℕ) :
    qppAlternatingStepScalar θ j * qppAlternatingStepScalar θ (j + 1) = 1 := by
  unfold qppAlternatingStepScalar
  by_cases hj : j % 2 = 0
  · have hj1 : (j + 1) % 2 ≠ 0 := by omega
    rw [if_pos hj, if_neg hj1]
    rw [← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero]
  · have hj1 : (j + 1) % 2 = 0 := by omega
    rw [if_neg hj, if_pos hj1]
    rw [← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero]

/-- The accumulated alternating source phase is determined by the schedule
length parity.  This is Wang's eigenspace-decomposition parity phase in list
form [WZYW23, arxiv_v3.tex:641]. -/
theorem qppAlternatingSignalScalarFrom_eq_if_length_mod
    (θ : ℝ) (ps : List (ℝ × ℝ)) (start : ℕ) :
    qppAlternatingSignalScalarFrom θ start ps =
      if ps.length % 2 = 0 then 1 else qppAlternatingStepScalar θ start := by
  induction ps generalizing start with
  | nil =>
      simp [qppAlternatingSignalScalarFrom]
  | cons p rest ih =>
      rw [qppAlternatingSignalScalarFrom, ih (start + 1)]
      by_cases hrest : rest.length % 2 = 0
      · have htotal : (rest.length + 1) % 2 ≠ 0 := by omega
        simp [hrest, htotal]
      · have htotal : (rest.length + 1) % 2 = 0 := by omega
        simp [hrest, htotal, qppAlternatingStepScalar_mul_succ θ start]

/-- Even-length alternating QPP schedules have no residual global phase. -/
theorem qppAlternatingSignalScalar_eq_one_of_even_length
    (θ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ} (h : ps.length = 2 * L) :
    qppAlternatingSignalScalar θ ps = 1 := by
  have hmod : ps.length % 2 = 0 := by
    rw [h]
    omega
  simp [qppAlternatingSignalScalar, qppAlternatingSignalScalarFrom_eq_if_length_mod θ ps 0,
    hmod]

/-- The alternating source one-qubit word is the YZZYZ QSP word times the
accumulated source global phase. -/
theorem QPP.qppAlternatingSignalGate_applyVec_eq_scalar_yzzyz
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) (ψ : StateVector (Qubits 1)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ =
      qppAlternatingSignalScalar θ ps •
        (qspYZZYZ φ θ₀ φ₀ ps θ).applyVec ψ := by
  have h :=
    QPP.qppAlternatingSignal_fold_applyVec_eq_scalar_yzzyz_fold
      θ ps 0
      (rotZStd φ * (rotY θ₀ * rotZStd φ₀))
      (rotZStd φ * (rotY θ₀ * rotZStd φ₀))
      (1 : ℂ)
      (by intro ψ'; simp)
      ψ
  simpa [qppAlternatingSignalGate_eq_foldlIdx, qppAlternatingSignalScalar,
    qppAlternatingSignalScalarFrom, qspYZZYZ] using h

/-- For the source QPP theorem schedule length `2L`, the alternating
one-qubit signal word is exactly the YZZYZ QSP word on vectors: the source
global phases cancel in pairs [WZYW23, arxiv_v3.tex:641]. -/
theorem QPP.qppAlternatingSignalGate_applyVec_eq_yzzyz_of_even_length
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ} (hps : ps.length = 2 * L)
    (ψ : StateVector (Qubits 1)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ =
      (qspYZZYZ φ θ₀ φ₀ ps θ).applyVec ψ := by
  rw [QPP.qppAlternatingSignalGate_applyVec_eq_scalar_yzzyz]
  rw [qppAlternatingSignalScalar_eq_one_of_even_length θ ps hps]
  simp

/-- The evaluated alternating controlled-`U` / controlled-`U†` QPP gate. -/
def qppAlternatingControlledGate (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : Gate (Qubits (1 + n)) :=
  ps.zipIdx.foldl
    (fun W jp => W * qppAlternatingStepGate U jp.2 jp.1)
    (qppAlternatingInitialGate n φ θ₀ φ₀)

/-- Source-aligned eigenspace decomposition of the alternating QPP word:
on an eigenstate of `U`, the multi-qubit word reduces to the one-qubit
alternating signal word tensored with the unchanged eigenstate
[WZYW23, arxiv_v3.tex:641]. -/
theorem QPP.qppAlternating_eigenstate_decompositionVec
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) (ψ : StateVector (Qubits 1)) :
    (qppAlternatingControlledGate U φ θ₀ φ₀ ps).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n))) =
      StateVector.tensor
        ((qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ)
        (u : StateVector (Qubits n)) := by
  let schedule := ps.zipIdx
  let initialSignal : Gate (Qubits 1) := rotZStd φ * (rotY θ₀ * rotZStd φ₀)
  let initialGate : Gate (Qubits (1 + n)) := qppAlternatingInitialGate n φ θ₀ φ₀
  have hfold :
      ∀ (schedule : List ((ℝ × ℝ) × ℕ))
        (W : Gate (Qubits (1 + n))) (S : Gate (Qubits 1)),
        (∀ ψ : StateVector (Qubits 1),
          W.applyVec (StateVector.tensor ψ (u : StateVector (Qubits n))) =
            StateVector.tensor (S.applyVec ψ) (u : StateVector (Qubits n))) →
        ∀ ψ : StateVector (Qubits 1),
          (schedule.foldl
              (fun W jp => W * qppAlternatingStepGate U jp.2 jp.1) W).applyVec
              (StateVector.tensor ψ (u : StateVector (Qubits n))) =
            StateVector.tensor
              ((schedule.foldl
                (fun S jp => S * qppAlternatingSignalStep θ jp.2 jp.1) S).applyVec ψ)
              (u : StateVector (Qubits n)) := by
    intro schedule
    induction schedule with
    | nil =>
        intro W S hbase ψ
        exact hbase ψ
    | cons jp rest ih =>
        intro W S hbase ψ
        apply ih
        intro ψ'
        rw [Gate.mul_applyVec, QPP.qppAlternatingStep_eigenstate_reductionVec U u θ hu]
        rw [hbase]
        by_cases hj : jp.2 % 2 = 0
        · simp [qppAlternatingSignalStep, hj, Gate.mul_applyVec]
        · simp [qppAlternatingSignalStep, hj, Gate.mul_applyVec]
  have hbase : ∀ ψ : StateVector (Qubits 1),
      initialGate.applyVec (StateVector.tensor ψ (u : StateVector (Qubits n))) =
        StateVector.tensor (initialSignal.applyVec ψ) (u : StateVector (Qubits n)) := by
    intro ψ
    dsimp [initialGate, initialSignal, qppAlternatingInitialGate]
    rw [Gate.tensor_applyVec_tensor, Gate.one_applyVec]
  simpa [qppAlternatingControlledGate, qppAlternatingSignalGate, schedule,
    initialGate, initialSignal] using
    hfold schedule initialGate initialSignal hbase ψ

/-- Source-aligned eigenspace decomposition of Wang's alternating QPP word for
the even schedule length `2L` used in the public QPP theorem.  The residual
global phase in [WZYW23, arxiv_v3.tex:641] is trivial for this length. -/
theorem QPP.qppAlternating_eigenstate_decomposition_evenVec
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : StateVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ} (hps : ps.length = 2 * L)
    (ψ : StateVector (Qubits 1)) :
    (qppAlternatingControlledGate U φ θ₀ φ₀ ps).applyVec
        (StateVector.tensor ψ (u : StateVector (Qubits n))) =
      StateVector.tensor
        ((qspYZZYZ φ θ₀ φ₀ ps θ).applyVec ψ)
        (u : StateVector (Qubits n)) := by
  rw [QPP.qppAlternating_eigenstate_decompositionVec U u θ hu]
  rw [QPP.qppAlternatingSignalGate_applyVec_eq_yzzyz_of_even_length θ φ θ₀ φ₀ ps hps]

/-- Source-aligned phase-evolution theorem for Wang's alternating
controlled-`U`/`U†` QPP word on an eigenspace.  The schedule has length `2L`,
so the parity phase in [WZYW23, arxiv_v3.tex:641] cancels, and the output is
the single-qubit trigonometric-QSP matrix from [WZYW23, arxiv_v3.tex:650]. -/
theorem QPP.alternating_realizes_target_on_eigenstate
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : StateVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair (2 * L) A B) :
    ∃ φ θ₀ φ₀ : ℝ, ∃ ps : List (ℝ × ℝ),
      ps.length = 2 * L ∧
        ∀ ψ : PureState (Qubits 1),
          (qppAlternatingControlledGate U φ θ₀ φ₀ ps).applyVec
              (StateVector.tensor (ψ : StateVector (Qubits 1))
                (u : StateVector (Qubits n))) =
            StateVector.tensor
              (HilbertOperator.applyVec (qspMatYZ (2 * L) A B θ)
                (ψ : StateVector (Qubits 1)))
              (u : StateVector (Qubits n)) := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ :=
    (TrigonometricQuantumSignalProcessing.main (2 * L) A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, ?_⟩
  intro ψ
  rw [QPP.qppAlternating_eigenstate_decomposition_evenVec U u θ hu φ θ₀ φ₀ ps hlen]
  have happly := congrArg
    (fun M : HilbertOperator (Qubits 1) =>
      HilbertOperator.applyVec M (ψ : StateVector (Qubits 1)))
    (hmat θ)
  simpa [Gate.applyVec] using congrArg
    (fun v : StateVector (Qubits 1) =>
      StateVector.tensor v (u : StateVector (Qubits n)))
    happly

/-- Initial typed circuit for the alternating QPP word. -/
def qppAlternatingInitialCircuit (n : ℕ) (φ θ₀ φ₀ : ℝ) :
    Circuit (Qubits (1 + n)) :=
  Circuit.ofGate "qpp-initial" (qppAlternatingInitialGate n φ θ₀ φ₀)
    qppAlternatingInitialResourceProfile 3 0

/-- One typed source-aligned alternating QPP step. -/
def qppAlternatingStepCircuit (U : Gate (Qubits n)) (j : ℕ) (p : ℝ × ℝ) :
    Circuit (Qubits (1 + n)) :=
  Circuit.ofGate "qpp-alternating-step" (qppAlternatingStepGate U j p)
    qppAlternatingStepResourceProfile 2 1

/-- Typed circuit for the alternating controlled-`U` / controlled-`U†` QPP
word, keeping the phase schedule as one symbolic list product. -/
def qppAlternatingControlledCircuit (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : Circuit (Qubits (1 + n)) :=
  Circuit.indexedProductList "qpp-alternating-controlled"
    (qppAlternatingInitialCircuit n φ θ₀ φ₀) ps.zipIdx
    (fun jp => qppAlternatingStepCircuit U jp.2 jp.1)

@[simp] theorem qppAlternatingControlledCircuit_matrix
    (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
        HilbertOperator (Qubits (1 + n))) =
      (qppAlternatingControlledGate U φ θ₀ φ₀ ps :
        HilbertOperator (Qubits (1 + n))) := by
  simp [qppAlternatingControlledCircuit, qppAlternatingControlledGate,
    qppAlternatingInitialCircuit, qppAlternatingStepCircuit]

theorem qppAlternatingControlledCircuit_resources_exact
    (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    ResourceProfile.HasExactCounts
      (qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).resources
      ps.length 0 (2 * ps.length + 3) 0 := by
  let step : (ℝ × ℝ) × ℕ → Circuit (Qubits (1 + n)) :=
    fun jp => qppAlternatingStepCircuit U jp.2 jp.1
  have hseq :
      ∀ (start : Circuit (Qubits (1 + n))) (q e : ℕ)
        (schedule : List ((ℝ × ℝ) × ℕ)),
        ResourceProfile.HasExactCounts start.resources q 0 e 0 →
        ResourceProfile.HasExactCounts
          (Circuit.sequenceList start (schedule.map step)).resources
          (q + schedule.length) 0 (e + 2 * schedule.length) 0 := by
    intro start q e schedule hstart
    induction schedule generalizing start q e with
    | nil =>
        simpa [ResourceProfile.HasExactCounts] using hstart
    | cons jp rest ih =>
        rw [List.map_cons, Circuit.sequenceList_cons]
        have hstep :
            ResourceProfile.HasExactCounts
              (Circuit.seq start (step jp)).resources (q + 1) 0 (e + 2) 0 := by
          rcases hstart with ⟨hq, hhad, helem, hclassical⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [step, qppAlternatingStepCircuit,
              qppAlternatingStepResourceProfile, Circuit.seq_resources,
              Circuit.ofGate_resources, ResourceProfile.sequential_oracleQueries]
            omega
          · simp only [step, qppAlternatingStepCircuit,
              qppAlternatingStepResourceProfile, Circuit.seq_resources,
              Circuit.ofGate_resources, ResourceProfile.sequential_hadamardGates]
            omega
          · simp only [step, qppAlternatingStepCircuit,
              qppAlternatingStepResourceProfile, Circuit.seq_resources,
              Circuit.ofGate_resources, ResourceProfile.sequential_elementaryGates]
            omega
          · simp only [step, qppAlternatingStepCircuit,
              qppAlternatingStepResourceProfile, Circuit.seq_resources,
              Circuit.ofGate_resources, ResourceProfile.sequential_classicalOps]
            omega
        have hrest := ih (Circuit.seq start (step jp)) (q + 1) (e + 2) hstep
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add,
          Nat.add_mul] using hrest
  have hstart :
      ResourceProfile.HasExactCounts
        (qppAlternatingInitialCircuit n φ θ₀ φ₀).resources 0 0 3 0 := by
    simp [qppAlternatingInitialCircuit, qppAlternatingInitialResourceProfile,
      ResourceProfile.HasExactCounts]
  have h := hseq (qppAlternatingInitialCircuit n φ θ₀ φ₀) 0 3 ps.zipIdx hstart
  simpa [qppAlternatingControlledCircuit, step, List.length_zipIdx,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- A counted source-level alternating controlled-`U` / controlled-`U†` QPP
word.  The evaluated gate and resource profile are bundled together so public
resource claims cannot drift away from the circuit used for the projected-block
correctness statement. -/
def qppAlternatingControlled (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : CountedGateWord (Qubits (1 + n)) where
  matrix := qppAlternatingControlledGate U φ θ₀ φ₀ ps
  resources := qppAlternatingScheduleResourceProfile ps.length

namespace QPP.Signal

/-- Namespace-local spelling of the alternating QPP controlled gate. -/
abbrev qppAlternatingControlledGate (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : Gate (Qubits (1 + n)) :=
  QuantumAlg.QSP.MultiQubit.qppAlternatingControlledGate U φ θ₀ φ₀ ps

/-- Namespace-local spelling of the counted alternating QPP controlled circuit. -/
abbrev qppAlternatingControlledCircuit (U : Gate (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : Circuit (Qubits (1 + n)) :=
  QuantumAlg.QSP.MultiQubit.qppAlternatingControlledCircuit U φ θ₀ φ₀ ps

/-- Staged signal-level phase-evolution theorem for the alternating QPP word. -/
theorem alternating_realizes_target_on_eigenstate
    (U : Gate (Qubits n)) (u : PureState (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : StateVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : StateVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair (2 * L) A B) :
    ∃ φ θ₀ φ₀ : ℝ, ∃ ps : List (ℝ × ℝ),
      ps.length = 2 * L ∧
        ∀ ψ : PureState (Qubits 1),
          (QuantumAlg.QSP.MultiQubit.qppAlternatingControlledGate U φ θ₀ φ₀ ps).applyVec
              (StateVector.tensor (ψ : StateVector (Qubits 1))
                (u : StateVector (Qubits n))) =
            StateVector.tensor
              (HilbertOperator.applyVec (qspMatYZ (2 * L) A B θ)
                (ψ : StateVector (Qubits 1)))
              (u : StateVector (Qubits n)) :=
  QuantumAlg.QSP.MultiQubit.QPP.alternating_realizes_target_on_eigenstate
    U u θ hu L A B h

end QPP.Signal



end

end QSP.MultiQubit

end QuantumAlg
