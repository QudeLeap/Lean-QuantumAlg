/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliStringDLA

/-!
# The Pauli-string product algebra and its symplectic structure

Reusable Pauli-string algebra underpinning the Schur one-dimensionality `(g⊗g)^g = span{C}` for the
Pauli-realized simple Lie algebras. The single-qubit Pauli labels `{I,X,Y,Z} = Fin 4` carry the
Klein-four group structure of the symplectic encoding `σ = X^x Z^z`
(`I↦(0,0)`, `X↦(1,0)`, `Y↦(1,1)`,
`Z↦(0,1)`), so the product closes on a single label up to phase:

* `pauli1_mul_closed` — `σ_a σ_b = phase1(a,b) · σ_{a⊕b}` on one qubit (`a⊕b = xor4 a b`).
* `pauliMat_mul_closed` — `P_s P_t = pauliPhase(s,t) · P_{s⊕t}` on the
  `n`-qubit register, a single string.
* `pauliMat_bracket_closed` — the commutator `⁅P_s, P_t⁆` is again a single string,
  zero iff `P_s,P_t`
  commute (`pauliOmega s t = 0`).
* `pauliOmega_nondeg` — the symplectic form is non-degenerate; `pauliAnticomm_connected` — the
  anticommutation graph on nonzero strings is connected.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Single-qubit Klein-four product table -/

/-- The Klein-four group law on single-qubit Pauli labels (`σ = X^x Z^z`, componentwise XOR of the
symplectic `(x,z)` bits): `I↦(0,0)`, `X↦(1,0)`, `Y↦(1,1)`, `Z↦(0,1)`. -/
def xor4 (a b : Fin 4) : Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a b

/-- The single-qubit product phase: `σ_a σ_b = phase1(a,b) · σ_{a⊕b}`, valued in `{1, ±i}`. -/
noncomputable def phase1 (a b : Fin 4) : ℂ :=
  ![![1, 1, 1, 1], ![1, 1, Complex.I, -Complex.I], ![1, -Complex.I, 1, Complex.I],
    ![1, Complex.I, -Complex.I, 1]] a b

/-- The single-qubit symplectic form: `omega4 a b = 1` iff `σ_a, σ_b` anticommute. -/
def omega4 (a b : Fin 4) : ZMod 2 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 1, 0]] a b

/-- **Single-qubit Pauli product closes on one label up to phase**:
`σ_a σ_b = phase1(a,b)·σ_{a⊕b}`. -/
theorem pauli1_mul_closed (a b : Fin 4) :
    pauli1 a * pauli1 b = phase1 a b • pauli1 (xor4 a b) := by
  fin_cases a <;> fin_cases b <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli1, phase1, xor4, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.one_apply])

/-! ### `n`-qubit Pauli-string product -/

/-- The pointwise Klein-four product of two `n`-qubit Pauli-string labels: `(s⊕t)ₖ = sₖ⊕tₖ`. -/
def pauliXor {n : ℕ} (s t : Fin n → Fin 4) : Fin n → Fin 4 := fun k => xor4 (s k) (t k)

/-- The total `n`-qubit product phase `Γ(s,t) = ∏ₖ phase1(sₖ,tₖ)`. -/
noncomputable def pauliPhase {n : ℕ} (s t : Fin n → Fin 4) : ℂ := ∏ k, phase1 (s k) (t k)

/-- The total `n`-qubit symplectic form `ω(s,t) = ∑ₖ omega4(sₖ,tₖ)` (in `ZMod 2`). -/
def pauliOmega {n : ℕ} (s t : Fin n → Fin 4) : ZMod 2 := ∑ k, omega4 (s k) (t k)

/-- The Pauli-string matrix product factorises over qubits (entrywise). -/
private theorem pauliStr_mul_factor {n : ℕ} (s t : Fin n → Fin 4) (i j : Fin n → Fin 2) :
    (pauliStr s * pauliStr t) i j = ∏ k, (pauli1 (s k) * pauli1 (t k)) (i k) (j k) := by
  simp only [Matrix.mul_apply, pauliStr, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 2)))
      (fun k a => pauli1 (s k) (i k) a * pauli1 (t k) a (j k))]

/-- **The `n`-qubit Pauli string product closes on a single string up to phase**:
`P_s P_t = Γ(s,t) · P_{s⊕t}`. -/
theorem pauliStr_mul_closed {n : ℕ} (s t : Fin n → Fin 4) :
    pauliStr s * pauliStr t = pauliPhase s t • pauliStr (pauliXor s t) := by
  ext i j
  rw [pauliStr_mul_factor]
  simp only [Matrix.smul_apply, pauliStr, Matrix.of_apply, smul_eq_mul, pauliPhase, pauliXor,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [pauli1_mul_closed, Matrix.smul_apply, smul_eq_mul]

/-- **The `Fin (2ⁿ)`-reindexed Pauli string product**: `P_s P_t = Γ(s,t) · P_{s⊕t}`. -/
theorem pauliMat_mul_closed {n : ℕ} (s t : Fin n → Fin 4) :
    pauliMat s * pauliMat t = pauliPhase s t • pauliMat (pauliXor s t) := by
  rw [pauliMat, pauliMat, Matrix.submatrix_mul_equiv, pauliStr_mul_closed, pauliMat]
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.smul_apply]

/-- Every single-qubit Pauli squares to the identity. -/
theorem pauli1_sq (a : Fin 4) : pauli1 a * pauli1 a = 1 := by
  fin_cases a <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli1, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.I_mul_I])

/-- Every Pauli string squares to the identity. -/
theorem pauliStr_sq {n : ℕ} (s : Fin n → Fin 4) : pauliStr s * pauliStr s = 1 := by
  ext i j
  rw [pauliStr_mul_factor]
  simp only [pauli1_sq, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- **The `n`-qubit Pauli strings are involutions:** `P_s * P_s = 1`. Together with
`pauliMat_isHermitian`, this is the basic algebraic fact used by Pauli-matrix generators. -/
theorem pauliMat_sq {n : ℕ} (s : Fin n → Fin 4) : pauliMat s * pauliMat s = 1 := by
  rw [pauliMat, Matrix.submatrix_mul_equiv, pauliStr_sq, Matrix.submatrix_one_equiv]

/-- Pauli strings are unitary matrices. -/
theorem pauliMat_unitary {n : ℕ} (s : Fin n → Fin 4) : (pauliMat s)ᴴ * pauliMat s = 1 := by
  rw [pauliMat_isHermitian, pauliMat_sq]

/-! ### The single-term commutator -/

theorem xor4_comm (a b : Fin 4) : xor4 a b = xor4 b a := by revert a b; decide

/-- Zero is the left identity for Pauli-label XOR. -/
theorem xor4_zero_left (a : Fin 4) : xor4 0 a = a := by revert a; decide

/-- Zero is the right identity for Pauli-label XOR. -/
theorem xor4_zero_right (a : Fin 4) : xor4 a 0 = a := by revert a; decide

/-- Pauli-label XOR is associative. -/
theorem xor4_assoc (a b c : Fin 4) : xor4 (xor4 a b) c = xor4 a (xor4 b c) := by
  revert a b c; decide

/-- Every Pauli label is its own XOR inverse. -/
theorem xor4_self_left (a b : Fin 4) : xor4 a (xor4 a b) = b := by
  revert a b; decide

/-- Every Pauli label is its own left XOR inverse. Compatibility spelling for Schur proofs. -/
theorem xor4_self_inv (a b : Fin 4) : xor4 a (xor4 a b) = b :=
  xor4_self_left a b

/-- Every Pauli label is its own right XOR inverse. -/
theorem xor4_xor_self_right (a b : Fin 4) : xor4 (xor4 a b) b = a := by
  revert a b; decide

/-- The Klein-four product of string labels is commutative. -/
theorem pauliXor_comm {n : ℕ} (s t : Fin n → Fin 4) : pauliXor s t = pauliXor t s :=
  funext fun k => xor4_comm (s k) (t k)

/-- Zero is the left identity for Pauli-string XOR. -/
theorem pauliXor_zero_left {n : ℕ} (s : Fin n → Fin 4) :
    pauliXor 0 s = s := funext fun k => xor4_zero_left (s k)

/-- Zero is the right identity for Pauli-string XOR. -/
theorem pauliXor_zero_right {n : ℕ} (s : Fin n → Fin 4) :
    pauliXor s 0 = s := funext fun k => xor4_zero_right (s k)

/-- Pauli-string XOR is associative. -/
theorem pauliXor_assoc {n : ℕ} (a b c : Fin n → Fin 4) :
    pauliXor (pauliXor a b) c = pauliXor a (pauliXor b c) :=
  funext fun k => xor4_assoc (a k) (b k) (c k)

/-- Every Pauli string is its own XOR inverse. -/
theorem pauliXor_self_left {n : ℕ} (a b : Fin n → Fin 4) :
    pauliXor a (pauliXor a b) = b :=
  funext fun k => xor4_self_left (a k) (b k)

/-- Every Pauli string is its own left XOR inverse. Compatibility spelling for Schur proofs. -/
theorem pauliXor_self_inv {n : ℕ} (a b : Fin n → Fin 4) :
    pauliXor a (pauliXor a b) = b :=
  pauliXor_self_left a b

/-- Every Pauli string is its own right XOR inverse. -/
theorem pauliXor_xor_self_right {n : ℕ} (a b : Fin n → Fin 4) :
    pauliXor (pauliXor a b) b = a :=
  funext fun k => xor4_xor_self_right (a k) (b k)

/-- **The Pauli-string commutator is a single string**:
`⁅P_s, P_t⁆ = (Γ(s,t) − Γ(t,s)) · P_{s⊕t}`. -/
theorem pauliMat_bracket_closed {n : ℕ} (s t : Fin n → Fin 4) :
    ⁅pauliMat s, pauliMat t⁆ = (pauliPhase s t - pauliPhase t s) • pauliMat (pauliXor s t) := by
  rw [Ring.lie_def, pauliMat_mul_closed s t, pauliMat_mul_closed t s, pauliXor_comm t s, sub_smul]

/-! ### The symplectic sign and the commute/anticommute dichotomy -/

/-- The `±1` sign of a `ZMod 2` parity, as a complex number. -/
def negOnePow (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

@[simp] theorem negOnePow_zero : negOnePow 0 = 1 := by simp [negOnePow]

@[simp] theorem negOnePow_one : negOnePow 1 = -1 := by simp [negOnePow]

theorem negOnePow_add (x y : ZMod 2) : negOnePow (x + y) = negOnePow x * negOnePow y := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h x with rfl | rfl <;> rcases h y with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 from by decide]

theorem negOnePow_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    ∏ k ∈ s, negOnePow (f k) = negOnePow (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, negOnePow_add]

/-- Single-qubit phase swap: `phase1(b,a) = (−1)^{ω(a,b)}·phase1(a,b)`. -/
theorem phase1_swap (a b : Fin 4) : phase1 b a = negOnePow (omega4 a b) * phase1 a b := by
  fin_cases a <;> fin_cases b <;> simp [phase1, omega4, negOnePow]

theorem phase1_ne_zero (a b : Fin 4) : phase1 a b ≠ 0 := by
  fin_cases a <;> fin_cases b <;> simp [phase1]

/-- **String phase swap**: `Γ(t,s) = (−1)^{ω(s,t)}·Γ(s,t)`. -/
theorem pauliPhase_swap {n : ℕ} (s t : Fin n → Fin 4) :
    pauliPhase t s = negOnePow (pauliOmega s t) * pauliPhase s t := by
  rw [pauliPhase, pauliPhase, pauliOmega, ← negOnePow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => phase1_swap (s k) (t k)

theorem pauliPhase_ne_zero {n : ℕ} (s t : Fin n → Fin 4) : pauliPhase s t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => phase1_ne_zero (s k) (t k)

/-- **Anticommuting strings give a nonzero single-term commutator coefficient.** -/
theorem pauliPhase_sub_ne_zero {n : ℕ} {s t : Fin n → Fin 4} (h : pauliOmega s t = 1) :
    pauliPhase s t - pauliPhase t s ≠ 0 := by
  rw [pauliPhase_swap s t, h, negOnePow_one, neg_one_mul, sub_neg_eq_add, ← two_mul]
  exact mul_ne_zero two_ne_zero (pauliPhase_ne_zero s t)

/-- **Commuting strings give a vanishing single-term commutator coefficient.** -/
theorem pauliPhase_sub_eq_zero {n : ℕ} {s t : Fin n → Fin 4} (h : pauliOmega s t = 0) :
    pauliPhase s t - pauliPhase t s = 0 := by
  rw [pauliPhase_swap s t, h, negOnePow_zero, one_mul, sub_self]

/-! ### Non-degeneracy of the symplectic form -/

theorem omega4_comm (a b : Fin 4) : omega4 a b = omega4 b a := by
  fin_cases a <;> fin_cases b <;> rfl

theorem omega4_zero_left (a : Fin 4) : omega4 0 a = 0 := by fin_cases a <;> rfl

theorem omega4_self_zero (a : Fin 4) : omega4 a a = 0 := by fin_cases a <;> rfl

/-- Every non-identity single-qubit Pauli anticommutes with some single-qubit Pauli. -/
theorem omega4_anticomm_of_ne {a : Fin 4} (h : a ≠ 0) : ∃ b, omega4 a b = 1 := by
  fin_cases a
  · exact absurd rfl h
  · exact ⟨2, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩

/-- **The symplectic form is non-degenerate**: every nonzero Pauli string anticommutes with some
single-site Pauli string (a genuine nonzero basis element). -/
theorem pauliOmega_nondeg {n : ℕ} {r : Fin n → Fin 4} (h : r ≠ 0) :
    ∃ s, pauliOmega s r = 1 := by
  obtain ⟨q, hq⟩ := Function.ne_iff.mp h
  have hrq : r q ≠ 0 := by simpa using hq
  obtain ⟨b, hb⟩ := omega4_anticomm_of_ne hrq
  refine ⟨Function.update 0 q b, ?_⟩
  rw [pauliOmega, Finset.sum_eq_single q]
  · rw [Function.update_self, omega4_comm, hb]
  · intro k _ hk
    rw [Function.update_of_ne hk, Pi.zero_apply, omega4_zero_left]
  · intro hq'; exact absurd (Finset.mem_univ q) hq'

/-! ### Connectivity of the anticommutation graph -/

theorem omega4_xor_left (a b c : Fin 4) :
    omega4 (xor4 a b) c = omega4 a c + omega4 b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem pauliOmega_zero_left {n : ℕ} (r : Fin n → Fin 4) : pauliOmega 0 r = 0 := by
  rw [pauliOmega]
  exact Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, omega4_zero_left]

theorem pauliOmega_self_zero {n : ℕ} (r : Fin n → Fin 4) : pauliOmega r r = 0 := by
  rw [pauliOmega]
  exact Finset.sum_eq_zero fun k _ => by rw [omega4_self_zero]

theorem pauliOmega_comm {n : ℕ} (s t : Fin n → Fin 4) : pauliOmega s t = pauliOmega t s := by
  rw [pauliOmega, pauliOmega]
  exact Finset.sum_congr rfl fun k _ => omega4_comm (s k) (t k)

/-- **Bilinearity of the symplectic form** in the first argument. -/
theorem pauliOmega_xor_left {n : ℕ} (a b c : Fin n → Fin 4) :
    pauliOmega (pauliXor a b) c = pauliOmega a c + pauliOmega b c := by
  rw [pauliOmega, pauliOmega, pauliOmega, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => omega4_xor_left (a k) (b k) (c k)

/-- **Bilinearity of the symplectic form** in the second argument. -/
theorem pauliOmega_xor_right {n : ℕ} (a b c : Fin n → Fin 4) :
    pauliOmega a (pauliXor b c) = pauliOmega a b + pauliOmega a c := by
  rw [pauliOmega_comm a (pauliXor b c), pauliOmega_xor_left, pauliOmega_comm b a,
    pauliOmega_comm c a]

theorem zmod2_ne_one {z : ZMod 2} (h : z ≠ 1) : z = 0 := by
  have hz : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hz z with h0 | h1
  · exact h0
  · exact absurd h1 h

/-- **Two nonzero strings share a common anticommuting partner.** This is the diameter-`≤2`
core of connectivity: for any nonzero `r, r'` there is an `x` anticommuting with both. -/
theorem exists_anticomm_both {n : ℕ} {r r' : Fin n → Fin 4} (hr : r ≠ 0) (hr' : r' ≠ 0) :
    ∃ x, pauliOmega x r = 1 ∧ pauliOmega x r' = 1 := by
  obtain ⟨a, ha⟩ := pauliOmega_nondeg hr
  obtain ⟨b, hb⟩ := pauliOmega_nondeg hr'
  by_cases hab : pauliOmega a r' = 1
  · exact ⟨a, ha, hab⟩
  · by_cases hba : pauliOmega b r = 1
    · exact ⟨b, hba, hb⟩
    · refine ⟨pauliXor a b, ?_, ?_⟩
      · rw [pauliOmega_xor_left, ha, zmod2_ne_one hba, add_zero]
      · rw [pauliOmega_xor_left, zmod2_ne_one hab, hb, zero_add]

/-- **The anticommutation graph is connected (constancy form).** Any function `t` constant across
anticommuting nonzero strings is constant on all nonzero strings. -/
theorem pauliAnticomm_const {n : ℕ} {α : Type*} {t : (Fin n → Fin 4) → α}
    (ht : ∀ a b : Fin n → Fin 4, pauliOmega a b = 1 → t a = t b)
    {r r' : Fin n → Fin 4} (hr : r ≠ 0) (hr' : r' ≠ 0) : t r = t r' := by
  obtain ⟨x, hxr, hxr'⟩ := exists_anticomm_both hr hr'
  have e1 : t r = t x := ht r x (by rw [pauliOmega_comm]; exact hxr)
  have e2 : t r' = t x := ht r' x (by rw [pauliOmega_comm]; exact hxr')
  rw [e1, e2]

end QuantumAlg
