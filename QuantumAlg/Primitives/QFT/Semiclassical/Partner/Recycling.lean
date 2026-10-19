/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import all QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases

/-!
# One recycled control with a persistent arbitrary partner and reference

Source-only candidate: no Lean acceptance is claimed. Each branch is the literal
H/controlled-U/phase/H/Z-measure/reset matrix. Both sides retain the complete
unnormalized partner/reference operator. The old measured bank and the new zero
control have separate rectangular embeddings; their different Hilbert spaces
are never equated. No per-bit or inter-stream partner reinitialization occurs.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

open QuantumAlg.MeasurementInstrument NormalizedVector
open scoped Kronecker

variable {S : Register}

/-- The actual control-only phase matrix acts as identity on the partner. -/
public def phaseBlock (phase : ℂ) : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ :=
  leading (Matrix.diagonal (fun bit : Fin 2 => if bit = 0 then 1 else phase))

private lemma phaseBlock_native (angle : ℝ) :
    phaseBlock (S := S) (Complex.exp ((angle : ℂ) * Complex.I)) =
      leading (phaseGateOp angle : HilbertOperator (Qubits 1)) := by
  rw [phaseGateOp_diagonal]
  rfl

/-- H, controlled U, phase, H, Z projector and reset, in their actual order. -/
public def nativeBranch (operator : HilbertOperator S) (phase : ℂ) (outcome : Fin 2) :
    Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ :=
  bankEmbedding (0 : Fin 2) * selectHead outcome * leading Gate.HOp *
    phaseBlock phase * controlled (selected operator) * leading Gate.HOp

private lemma nativeBranch_zero_column (operator : HilbertOperator S) (phase : ℂ)
    (outcome : Fin 2) (row : Fin 2 × S.Index) (column : S.Index) :
    nativeBranch operator phase outcome row (0, column) =
      if row.1 = 0 then halfSum operator phase outcome row.2 column else 0 := by
  rcases row with ⟨bit, seed⟩
  by_cases same : seed = column <;> fin_cases bit <;> fin_cases outcome <;>
    simp [same, nativeBranch, bankEmbedding, selectHead, leading, phaseBlock, controlled,
      selected, halfSum, Gate.HOp, UnitaryOperator.coe_ofMatrix, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.smul_apply, smul_eq_mul, mul_ite, ite_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq'] <;>
    ring_nf <;> simp only [invSqrt2_sq] <;> ring

/-- Exact intertwining includes the native measured/reset control and every partner column. -/
public lemma qftPartner_nativeBranch_intertwines (operator : HilbertOperator S) (phase : ℂ)
    (outcome : Fin 2) :
    nativeBranch operator phase outcome * bankEmbedding (0 : Fin 2) =
      bankEmbedding (0 : Fin 2) * halfSum operator phase outcome := by
  ext row column
  calc
    _ = nativeBranch operator phase outcome row (0, column) := by
      simp [Matrix.mul_apply, Fintype.sum_prod_type, bankEmbedding, mul_ite]
    _ = if row.1 = 0 then halfSum operator phase outcome row.2 column else 0 :=
      nativeBranch_zero_column operator phase outcome row column
    _ = _ := by
      by_cases zero : row.1 = 0 <;> simp [Matrix.mul_apply, bankEmbedding, zero, ite_mul]

/-- The real feedback angle update sums the previously selected native rotation angles. -/
public def updatedAngles (inverse : Bool) (n : Nat) (angles : Fin (n + 1) → ℝ)
    (head : Fin 2) : Fin n → ℝ :=
  fun index => angles index.succ +
    if head = 1 then
      if inverse then -(Source.phaseAngle index.val) else Source.phaseAngle index.val
    else 0

/-- Multiplicative phases are exactly exponentials of the additive native feedback angles. -/
public lemma qftPartner_updatedPhases_exp (inverse : Bool) (n : Nat)
    (angles : Fin (n + 1) → ℝ) (head : Fin 2) :
    updatedPhases inverse n (fun index => Complex.exp ((angles index : ℂ) * Complex.I)) head =
      fun index => Complex.exp ((updatedAngles inverse n angles head index : ℂ) * Complex.I) :=
    by
  funext index
  unfold updatedPhases updatedAngles feedbackPhases rotation
  by_cases selected : head = 1
  · simp only [selected, ↓reduceIte, Complex.ofReal_add, add_mul, Complex.exp_add]
    cases inverse
    · rfl
    · simp only [↓reduceIte, Complex.ofReal_neg]
  · simp [selected]

/-- The same half-sum product written with real native feedback-angle parameters. -/
public def angleKraus (inverse : Bool) : (n : Nat) →
    (Fin n → HilbertOperator S) → (Fin n → ℝ) → Bits n → HilbertOperator S
  | 0, _, _, _ => 1
  | n + 1, operators, angles, output =>
      angleKraus inverse n (fun index => operators index.succ)
        (updatedAngles inverse n angles output.1) output.2 *
          halfSum (operators 0) (Complex.exp ((angles 0 : ℂ) * Complex.I)) output.1

/-- Every factor is `(I + (-1)^y exp(i theta) U) / 2` for the actual prior-bit angle. -/
public lemma qftPartner_recycledKraus_exp (inverse : Bool) :
    ∀ (n : Nat) (operators : Fin n → HilbertOperator S) (angles : Fin n → ℝ)
      (output : Bits n),
    recycledKraus inverse n operators
        (fun index => Complex.exp ((angles index : ℂ) * Complex.I)) output =
      angleKraus inverse n operators angles output := by
  intro n
  induction n with
  | zero => intro operators angles output; rfl
  | succ n ih =>
      intro operators angles output
      rcases output with ⟨head, tail⟩
      simp only [recycledKraus, angleKraus, qftPartner_updatedPhases_exp, ih]

/-- An initially unphased old bank gives the native zero-initialized feedback-angle product. -/
public lemma qftPartner_oldKraus_eq_angleKraus (inverse : Bool) (n : Nat)
    (operators : Fin n → UnitaryOperator S) (output : Bits n) :
    oldKraus inverse n (fun index => (operators index : HilbertOperator S)) output =
      angleKraus inverse n (fun index => (operators index : HilbertOperator S))
        (fun _ => 0) output := by
  rw [qftPartner_oldKraus_eq_recycled]
  have initial : (fun _ : Fin n => (1 : ℂ)) =
      fun _ : Fin n => Complex.exp (((0 : ℝ) : ℂ) * Complex.I) := by
    funext index
    simp
  rw [initial, qftPartner_recycledKraus_exp]

/-- The control is reset to zero after each factor and physically reused by the next factor. -/
public def nativeProduct (inverse : Bool) : (n : Nat) →
    (Fin n → HilbertOperator S) → (Fin n → ℂ) → Bits n →
      Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ
  | 0, _, _, _ => 1
  | n + 1, operators, phases, output =>
      nativeProduct inverse n (fun index => operators index.succ)
        (updatedPhases inverse n phases output.1) output.2 *
          nativeBranch (operators 0) (phases 0) output.1

/-- A repeated native branch uses the same zero-control embedding at every step. -/
public lemma qftPartner_nativeProduct_intertwines (inverse : Bool) :
    ∀ (n : Nat) (operators : Fin n → HilbertOperator S) (phases : Fin n → ℂ)
      (output : Bits n),
    nativeProduct inverse n operators phases output * bankEmbedding (0 : Fin 2) =
      bankEmbedding (0 : Fin 2) * recycledKraus inverse n operators phases output := by
  intro n
  induction n with
  | zero => intro operators phases output; simp only [nativeProduct, recycledKraus,
      Matrix.one_mul, Matrix.mul_one]
  | succ n ih =>
      intro operators phases output
      rcases output with ⟨head, tail⟩
      simp only [nativeProduct, recycledKraus]
      rw [Matrix.mul_assoc, qftPartner_nativeBranch_intertwines, ← Matrix.mul_assoc, ih]
      rw [Matrix.mul_assoc]

private lemma conjugation_intertwines {P Q : Type} [Fintype P] [Fintype Q]
    (injection : Matrix Q P ℂ) (native : Matrix Q Q ℂ) (source : Matrix P P ℂ)
    (derived : native * injection = injection * source) (density : Matrix P P ℂ) :
    native * (injection * density * injection.conjTranspose) * native.conjTranspose =
      injection * (source * density * source.conjTranspose) * injection.conjTranspose := by
  have adjoint := congrArg Matrix.conjTranspose derived
  simp only [Matrix.conjTranspose_mul] at adjoint
  calc
    _ = (native * injection) * density *
        (injection.conjTranspose * native.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [derived, adjoint]; simp only [Matrix.mul_assoc]

private lemma halfSum_reference (operator : HilbertOperator S) (phase : ℂ)
    (outcome : Fin 2) (Reference : Register) :
    halfSum (S := S.prod Reference) (operator ⊗ₖ (1 : HilbertOperator Reference)) phase outcome =
      halfSum operator phase outcome ⊗ₖ (1 : HilbertOperator Reference) := by
  simp only [halfSum, Matrix.smul_kronecker, Matrix.add_kronecker,
    Matrix.one_kronecker_one]

/-- An arbitrary untouched reference passes through every ordered half-sum factor. -/
public lemma qftPartner_recycledKraus_reference (inverse : Bool) (Reference : Register) :
    ∀ (n : Nat) (operators : Fin n → HilbertOperator S) (phases : Fin n → ℂ)
      (output : Bits n),
    recycledKraus (S := S.prod Reference) inverse n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference))
        phases output =
      recycledKraus inverse n operators phases output ⊗ₖ (1 : HilbertOperator Reference) :=
    by
  intro n
  induction n with
  | zero => intro operators phases output; exact Matrix.one_kronecker_one.symm
  | succ n ih =>
      intro operators phases output
      rcases output with ⟨head, tail⟩
      simp only [recycledKraus, ih, halfSum_reference]
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- The old actual controlled/Fourier execution retains arbitrary entanglement to a reference. -/
public lemma qftPartner_oldKraus_reference (inverse : Bool) (n : Nat)
    (operators : Fin n → HilbertOperator S) (output : Bits n) (Reference : Register) :
    oldKraus (S := S.prod Reference) inverse n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference)) output =
      oldKraus inverse n operators output ⊗ₖ (1 : HilbertOperator Reference) := by
  simp only [qftPartner_oldKraus_contraction, qftPartner_contraction_eq_recycled,
    qftPartner_recycledKraus_reference]

/-- Common unnormalized conditional partner/reference matrix after removing the old bank. -/
public def σ (inverse : Bool) (n : Nat) (operators : Fin n → HilbertOperator S)
    (output : Bits n) (Reference : Register) (density : HilbertOperator (S.prod Reference)) :
    HilbertOperator (S.prod Reference) :=
  let kraus : HilbertOperator (S.prod Reference) :=
    oldKraus inverse n operators output ⊗ₖ (1 : HilbertOperator Reference)
  kraus * density * kraus.conjTranspose

/-- Exact equality of all mixed-state entries, including the partner/reference coherences. -/
public lemma qftPartner_sigma_eq_recycled (inverse : Bool) (n : Nat)
    (operators : Fin n → UnitaryOperator S) (output : Bits n) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    σ inverse n (fun index => (operators index : HilbertOperator S)) output Reference density =
      let kraus : HilbertOperator (S.prod Reference) :=
        recycledKraus inverse n (fun index => (operators index : HilbertOperator S))
          (fun _ => 1) output ⊗ₖ (1 : HilbertOperator Reference)
      kraus * density * kraus.conjTranspose := by
  simp only [σ, qftPartner_oldKraus_eq_recycled]

/-- Old projector-after-Fourier branch, including its physically retained measured bank. -/
public def oldBankBranch (inverse : Bool) (n : Nat) (operators : Fin n → HilbertOperator S)
    (output : Bits n) (Reference : Register) (density : HilbertOperator (S.prod Reference)) :
    Matrix (Bits n × (S.prod Reference).Index) (Bits n × (S.prod Reference).Index) ℂ :=
  let kraus : Matrix (Bits n × (S.prod Reference).Index) (S.prod Reference).Index ℂ :=
    bankKraus output (rowKraus (fourierRows inverse n) output) *
      preparation (S := S.prod Reference) n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference))
  kraus * density * kraus.conjTranspose

/-- The measured old bank is explicitly `|output><output|`, on its own Hilbert space. -/
public lemma qftPartner_oldBank_factor (inverse : Bool) (n : Nat)
    (operators : Fin n → HilbertOperator S) (output : Bits n) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    oldBankBranch inverse n operators output Reference density =
      bankEmbedding output * σ inverse n operators output Reference density *
        (bankEmbedding output).conjTranspose := by
  have factor : bankKraus output (rowKraus (fourierRows inverse n) output) *
      preparation (S := S.prod Reference) n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference)) =
      bankEmbedding output * oldKraus (S := S.prod Reference) inverse n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference)) output := by
    simp only [bankKraus, oldKraus, Matrix.mul_assoc]
  unfold oldBankBranch
  rw [factor]
  rw [qftPartner_oldKraus_reference]
  simp only [σ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- New native branch, retaining only the recycled physical control in its reset state. -/
public def newBankBranch (inverse : Bool) (n : Nat) (operators : Fin n → HilbertOperator S)
    (output : Bits n) (Reference : Register) (density : HilbertOperator (S.prod Reference)) :
    Matrix (Fin 2 × (S.prod Reference).Index) (Fin 2 × (S.prod Reference).Index) ℂ :=
  let kraus := nativeProduct (S := S.prod Reference) inverse n
    (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference)) (fun _ => 1) output
  kraus * (bankEmbedding (0 : Fin 2) * density *
    (bankEmbedding (0 : Fin 2)).conjTranspose) * kraus.conjTranspose

/-- The new zero control embeds the same partner/reference branch; no unequal-space equality. -/
public lemma qftPartner_newBank_factor (inverse : Bool) (n : Nat)
    (operators : Fin n → UnitaryOperator S) (output : Bits n) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    newBankBranch inverse n (fun index => (operators index : HilbertOperator S))
        output Reference density =
      bankEmbedding (0 : Fin 2) *
        σ inverse n (fun index => (operators index : HilbertOperator S))
          output Reference density *
          (bankEmbedding (0 : Fin 2)).conjTranspose := by
  rw [qftPartner_sigma_eq_recycled]
  unfold newBankBranch
  rw [conjugation_intertwines _ _ _ (qftPartner_nativeProduct_intertwines _ _ _ _ _)]
  rw [qftPartner_recycledKraus_reference]

/-- Both complete native branches factor through the identical partner/reference posterior. -/
public lemma qftPartner_recycling_complete (inverse : Bool) (n : Nat)
    (operators : Fin n → UnitaryOperator S) (output : Bits n) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    oldKraus inverse n (fun index => (operators index : HilbertOperator S)) output =
        recycledKraus inverse n (fun index => (operators index : HilbertOperator S))
          (fun _ => 1) output ∧
      oldBankBranch inverse n (fun index => (operators index : HilbertOperator S))
          output Reference density =
        bankEmbedding output *
          σ inverse n (fun index => (operators index : HilbertOperator S))
            output Reference density * (bankEmbedding output).conjTranspose ∧
      newBankBranch inverse n (fun index => (operators index : HilbertOperator S))
          output Reference density =
        bankEmbedding (0 : Fin 2) *
          σ inverse n (fun index => (operators index : HilbertOperator S))
            output Reference density * (bankEmbedding (0 : Fin 2)).conjTranspose := by
  exact ⟨qftPartner_oldKraus_eq_recycled inverse n operators output,
    qftPartner_oldBank_factor inverse n _ output Reference density,
    qftPartner_newBank_factor inverse n operators output Reference density⟩

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
