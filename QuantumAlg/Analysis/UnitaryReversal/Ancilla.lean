/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized

public import QuantumAlg.Analysis.UnitaryReversal.Encoding
public import QuantumAlg.Core.Base.State.Normalized

/-!
# Ancilla transformations for unitary reversal

Coordinate matrices for the two-qudit ancilla subspaces and controlled
reflections used in the duality construction [CML+24, main.tex:935].
The total formulas include dimensions where a normalized ancilla is unavailable;
the action identities state their required dimension hypotheses.
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

-- Preserve symbolic basis coefficients until a proof requests their entry formula.
attribute [-simp] NormalizedVector.ket_apply

variable {d : ℕ}

local notation "k₀" => (NormalizedVector.ket (R := Qubits 1) 0)
local notation "k₁" => (NormalizedVector.ket (R := Qubits 1) 1)


/-- Pauli-`X` on one qubit: `X|0⟩ = |1⟩`, `X|1⟩ = |0⟩`. -/
def quraX2 : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.of (fun i j => if i.val ≠ j.val then 1 else 0), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]⟩

local notation "X₂" => (quraX2 : Matrix (Fin 2) (Fin 2) ℂ)

@[simp]
theorem quraX2_apply (i j : Fin 2) : X₂ i j = if i.val ≠ j.val then 1 else 0 := by
  rfl

/-- The coordinate formula for `|00⟩` on two `d`-dimensional factors, also defined at `d = 0`. -/
def quraKet00 (d : ℕ) : Fin d × Fin d → ℂ :=
  fun a => if a.1.val = 0 ∧ a.2.val = 0 then 1 else 0

/-- `|00⊥⟩` — uniform superposition over the non-`|00⟩` basis states. -/
def quraKet00Perp (d : ℕ) : Fin d × Fin d → ℂ :=
  fun a => if a.1.val = 0 ∧ a.2.val = 0 then 0
    else ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹

/-- `|++⟩` on the two control qudits. -/
@[nolint unusedArguments]
def quraKetPlusPlus (d : ℕ) : Fin d × Fin d → ℂ :=
  fun _ => invSqrtD d * invSqrtD d

/-- `cos Δ_d = √(d²−1)/d` with `Δ_d = arcsin(1/d)`. -/
def quraCosDelta (d : ℕ) : ℂ :=
  ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) / (d : ℂ)

/-- `|++⟩ = sin Δ_d · |00⟩ + cos Δ_d · |00⊥⟩`. -/
lemma quraPlusPlus_decompose (hd : 2 ≤ d) :
    quraKetPlusPlus d = (1 / (d : ℂ)) • quraKet00 d + quraCosDelta d • quraKet00Perp d := by
  ext a
  by_cases h0 : a.1.val = 0 ∧ a.2.val = 0
  · have hd0 : (d : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    simp [quraKetPlusPlus, quraKet00, quraKet00Perp, quraCosDelta, h0]
    field_simp [hd0]
    rw [pow_two, invSqrtD_mul_self]
    rw [← Complex.ofReal_natCast]
    have hX : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    rw [inv_mul_cancel₀ hX]
  · have hd0 : (d : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    have hsqrt : (Real.sqrt ((d : ℝ) ^ 2 - 1) : ℂ) ≠ 0 := by
      have hsqrtR : Real.sqrt ((d : ℝ) ^ 2 - 1) ≠ 0 := by
        apply Real.sqrt_ne_zero'.mpr
        have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        nlinarith
      exact_mod_cast hsqrtR
    simp [quraKetPlusPlus, quraKet00, quraKet00Perp, quraCosDelta, h0]
    field_simp [hd0, hsqrt]
    rw [pow_two, invSqrtD_mul_self]
    rw [← Complex.ofReal_natCast]
    have hX : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    rw [inv_mul_cancel₀ hX]

/-- A vector on the two control qudits tensored with the identity on the target. -/
def quraVecState (d : ℕ) (v : Fin d × Fin d → ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  Matrix.of fun a s => v (a.1, a.2.1) * (if a.2.2 = s then 1 else 0)

@[simp]
theorem quraVecState_apply (d : ℕ) (v : Fin d × Fin d → ℂ)
    (a : Fin d × (Fin d × Fin d)) (s : Fin d) :
    quraVecState d v a s = v (a.1, a.2.1) * (if a.2.2 = s then 1 else 0) := by
  rfl

lemma quraVecState_add (d : ℕ) (v w : Fin d × Fin d → ℂ) :
    quraVecState d (v + w) = quraVecState d v + quraVecState d w := by
  ext a s
  simp [Pi.add_apply]
  by_cases hs : a.2.2 = s
  · simp [hs]
  · simp [hs]

lemma quraVecState_smul (d : ℕ) (c : ℂ) (v : Fin d × Fin d → ℂ) :
    quraVecState d (c • v) = c • quraVecState d v := by
  ext a s
  simp [Pi.smul_apply]

/-- `|++⟩ ⊗ I = sin Δ · |00⟩ ⊗ I + cos Δ · |00⊥⟩ ⊗ I`. -/
lemma qudPlusState_decompose (hd : 2 ≤ d) :
    qudPlusState d = (1 / (d : ℂ)) • quraVecState d (quraKet00 d) +
      quraCosDelta d • quraVecState d (quraKet00Perp d) := by
  rw [show qudPlusState d = quraVecState d (quraKetPlusPlus d) by
    ext a s
    simp [qudPlusState_apply, quraVecState_apply, quraKetPlusPlus, invSqrtD_mul_self]]
  rw [quraPlusPlus_decompose hd]
  rw [quraVecState_add, quraVecState_smul, quraVecState_smul]

/-- `Ψ₀ = |00⟩ ⊗ U†` (paper Eq. `eqn:Psi0` without the ancilla). -/
def quraPsi0 (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  quraTarget d U

/-- `Ψ⊥ = D(U)† · (|00⊥⟩ ⊗ I)`. -/
def quraPsiPerp (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  (quraDecoder U).conjTranspose * quraVecState d (quraKet00Perp d)

/-- `Λ⊥ = D(U) · (|00⊥⟩ ⊗ U†)`. -/
def quraLambdaPerp (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  quraDecoder U * (Matrix.of fun a s => quraKet00Perp d (a.1, a.2.1) * U.conjTranspose a.2.2 s)

/-- Lemma A.2 (`lem:preparation` / `lem:Lambda_perp`, first part):
`E(U)·Λ₀ = sin Δ_d · Ψ₀ + cos Δ_d · Ψ⊥`. -/
lemma E_Lambda0_decompose [NeZero d] (hd : 2 ≤ d) (U : Matrix (Fin d) (Fin d) ℂ) :
    quraEncoder U * quraLambda0 d =
      (1 / (d : ℂ)) • quraPsi0 d U + quraCosDelta d • quraPsiPerp d U := by
  rw [qura_duality (by omega : d ≠ 0) U]
  calc
    (quraDecoder U).conjTranspose * qudPlusState d
        = (quraDecoder U).conjTranspose *
            ((1 / (d : ℂ)) • quraVecState d (quraKet00 d) +
              quraCosDelta d • quraVecState d (quraKet00Perp d)) := by
          rw [qudPlusState_decompose hd]
    _ = (1 / (d : ℂ)) • ((quraDecoder U).conjTranspose * quraVecState d (quraKet00 d)) +
          quraCosDelta d • ((quraDecoder U).conjTranspose * quraVecState d (quraKet00Perp d)) := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
    _ = (1 / (d : ℂ)) • quraTarget d U + quraCosDelta d • quraPsiPerp d U := by
          have h00 : (quraDecoder U).conjTranspose * quraVecState d (quraKet00 d) = quraTarget d U
          := by
            have hvec : quraVecState d (quraKet00 d) = quraLambda0 d := by
              ext a s
              simp [quraVecState_apply, quraKet00, quraLambda0]
            rw [hvec]
            exact D_dag_lambda0 U
          rw [h00]
          rfl
/-- The vector `|v⟩ = |00⊥⟩ − |00⟩` defining the Householder reflection `F = I − |v⟩⟨v|`. -/
def quraV (d : ℕ) : Fin d × Fin d → ℂ :=
  fun a => quraKet00Perp d a - quraKet00 d a

/-- The Householder reflection `F = I − |v⟩⟨v|` with `F|00⟩ = |00⊥⟩`. -/
def quraF (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) - quraV d a * star (quraV d b)

@[simp]
theorem quraF_apply (d : ℕ) (a b : Fin d × Fin d) :
    quraF d a b = (if a = b then 1 else 0) - quraV d a * star (quraV d b) := by
  rfl

/-- `v` is real-valued: `star (v a) = v a`. -/
lemma quraV_star (d : ℕ) [NeZero d] (a : Fin d × Fin d) : star (quraV d a) = quraV d a := by
  by_cases h0 : a.1 = 0 ∧ a.2 = 0
  · simp [quraV, quraKet00Perp, quraKet00, h0]
  · simp [quraV, quraKet00Perp, quraKet00, h0, star_inv₀]

/-- `|00⊥⟩` is normalized: `Σ_b star(perp b)·perp b = 1`. -/
lemma quraPerp_dot_perp [NeZero d] (hd : 2 ≤ d) :
    (∑ b : Fin d × Fin d, star (quraKet00Perp d b) * quraKet00Perp d b) = 1 := by
  have hstar : ∀ b : Fin d × Fin d, star (quraKet00Perp d b) = quraKet00Perp d b := by
    intro b
    by_cases h0 : b.1 = 0 ∧ b.2 = 0
    · simp [quraKet00Perp, h0]
    · simp [quraKet00Perp, h0, star_inv₀]
  simp_rw [hstar]
  -- Σ_b perp b·perp b — entries are s⁻¹·s⁻¹ for b ≠ 00, 0 otherwise
  let c : ℂ := ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹
  have hsplit : ∀ b : Fin d × Fin d,
      quraKet00Perp d b * quraKet00Perp d b =
        c * (if b.1.val = 0 ∧ b.2.val = 0 then 0 else 1) := by
    intro b
    dsimp [c]
    by_cases h0 : b.1 = 0 ∧ b.2 = 0
    · simp [quraKet00Perp, h0]
    · simp [quraKet00Perp, h0]
  simp_rw [hsplit]
  rw [← Finset.mul_sum]
  -- count of b ≠ 00 is d² − 1
  have hcount : (∑ b : Fin d × Fin d, (if b.1.val = 0 ∧ b.2.val = 0 then 0 else 1)) =
      (d : ℂ) ^ 2 - 1 := by
    have hsum' : (∑ b : Fin d × Fin d, (if b.1.val = 0 ∧ b.2.val = 0 then 0 else 1)) =
        ((Finset.univ : Finset (Fin d × Fin d)).card : ℂ) - 1 := by
      have hsplit : ∀ b : Fin d × Fin d,
          (if b.1.val = 0 ∧ b.2.val = 0 then (0 : ℂ) else 1) =
            1 - (if b.1.val = 0 ∧ b.2.val = 0 then (1 : ℂ) else 0) := by
        intro b
        by_cases h0 : b.1 = 0 ∧ b.2 = 0
        · have h0v : b.1.val = 0 ∧ b.2.val = 0 :=
            ⟨congrArg Fin.val h0.1, congrArg Fin.val h0.2⟩
          rw [if_pos h0v, if_pos h0v]
          norm_num
        · have h0v : ¬(b.1.val = 0 ∧ b.2.val = 0) := by
            intro h
            apply h0
            exact ⟨Fin.ext h.1, Fin.ext h.2⟩
          rw [if_neg h0v, if_neg h0v]
          norm_num
      calc
        (∑ b : Fin d × Fin d, (if b.1.val = 0 ∧ b.2.val = 0 then 0 else 1))
            = ∑ b : Fin d × Fin d, (1 - (if b.1.val = 0 ∧ b.2.val = 0 then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro b hb
              exact hsplit b
        _ = (∑ b : Fin d × Fin d, (1 : ℂ)) - (∑ b : Fin d × Fin d,
              (if b.1.val = 0 ∧ b.2.val = 0 then 1 else 0)) := by
              rw [Finset.sum_sub_distrib]
        _ = ((Finset.univ : Finset (Fin d × Fin d)).card : ℂ) - 1 := by
              have h1 : (∑ b : Fin d × Fin d, (1 : ℂ)) = (Fintype.card (Fin d × Fin d) : ℂ) := by
                have hnat : (∑ b : Fin d × Fin d, (1 : ℕ)) = Fintype.card (Fin d × Fin d) := by
                  exact Fintype.card_eq_sum_ones.symm
                have hnat' : (∑ b : Fin d × Fin d, ((1 : ℕ) : ℂ)) =
                    (Fintype.card (Fin d × Fin d) : ℂ) := by
                  rw [← Nat.cast_sum]
                  rw [hnat]
                simp
              have hδ : (∑ b : Fin d × Fin d, (if b.1.val = 0 ∧ b.2.val = 0 then (1 : ℂ) else 0)) =
              1 := by
                rw [Finset.sum_eq_single (0, 0)]
                · simp
                · intro b hb hne
                  have hnot : ¬(b.1 = 0 ∧ b.2 = 0) := by
                    intro h
                    apply hne
                    apply Prod.ext
                    · exact h.1
                    · exact h.2
                  simp [hnot]
                · intro h
                  exact False.elim (h (Finset.mem_univ (0, 0)))
              rw [h1]
              conv_lhs =>
                rhs
                rw [hδ]
              rfl
    calc
      (∑ b : Fin d × Fin d, (if b.1.val = 0 ∧ b.2.val = 0 then 0 else 1))
          = ((Finset.univ : Finset (Fin d × Fin d)).card : ℂ) - 1 := hsum'
      _ = (d : ℂ) ^ 2 - 1 := by
          have hc' : ((Finset.univ : Finset (Fin d × Fin d)).card : ℂ) = (↑d : ℂ) ^ 2 := by
            have hc : (Finset.univ : Finset (Fin d × Fin d)).card = d ^ 2 := by
              simp [Fintype.card_prod, pow_two]
            calc
              ((Finset.univ : Finset (Fin d × Fin d)).card : ℂ) = (↑(d ^ 2 : ℕ) : ℂ) :=
                congrArg (fun n : ℕ => (n : ℂ)) hc
              _ = (↑d : ℂ) ^ 2 := by exact (Nat.cast_pow d 2)
          rw [hc']
  rw [hcount]
  -- c · (d²−1) = 1
  dsimp [c]
  have hs : (Real.sqrt ((d : ℝ) ^ 2 - 1) : ℂ) ≠ 0 := by
    have hsqrtR : Real.sqrt ((d : ℝ) ^ 2 - 1) ≠ 0 := by
      apply Real.sqrt_ne_zero'.mpr
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
    exact_mod_cast hsqrtR
  have hs2 : ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) *
      ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) = (d : ℂ) ^ 2 - 1 := by
    rw [← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt]
    · norm_num
    · have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
  rw [← hs2]
  field_simp [hs]

-- Declaration-scoped exception: simp reduces the selected ket00 term before the basis split.
set_option linter.flexible false in
/-- `F|00⟩ = |00⊥⟩`. -/
lemma quraF_mulVec_ket00 (d : ℕ) [NeZero d] :
    Matrix.mulVec (quraF d) (quraKet00 d) = quraKet00Perp d := by
  ext a
  change (∑ b : Fin d × Fin d, quraF d a b * quraKet00 d b) = quraKet00Perp d a
  rw [Finset.sum_eq_single (0, 0)]
  · -- main: b = (0,0)
    have hv00 : quraV d (0, 0) = -1 := by
      simp [quraV, quraKet00Perp, quraKet00]
    have hv00s : star (quraV d (0, 0)) = -1 := by
      rw [quraV_star, hv00]
    simp [quraF_apply, quraKet00, hv00s]
    by_cases ha : a.1 = 0 ∧ a.2 = 0
    · have hva : quraV d a = -1 := by simp [quraV, quraKet00Perp, quraKet00, ha]
      have hpa : quraKet00Perp d a = 0 := by simp [quraKet00Perp, ha]
      have ha00 : a = (0, 0) := by
        apply Prod.ext
        · exact ha.1
        · exact ha.2
      have hv00' : quraV d (0, 0) = -1 := by simpa [ha00] using hva
      have hp00' : quraKet00Perp d (0, 0) = 0 := by simpa [ha00] using hpa
      rw [ha00, hv00', hp00']
      norm_num
    · have hva : quraV d a = quraKet00Perp d a := by simp [quraV, quraKet00, ha]
      have ha00 : ¬(a = (0, 0)) := by
        intro h
        apply ha
        exact ⟨congrArg (fun x : Fin d × Fin d => x.1) h, congrArg (fun x : Fin d × Fin d => x.2) h⟩
      simp [hva, ha00]
  · intro b hb hne
    have hnot : ¬(b.1 = 0 ∧ b.2 = 0) := by
      intro h
      apply hne
      apply Prod.ext
      · exact h.1
      · exact h.2
    simp [quraKet00, hnot]
  · intro h
    exact False.elim (h (Finset.mem_univ (0, 0)))

/-- `F|00⊥⟩ = |00⟩`. -/
lemma quraF_mulVec_ket00Perp (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    Matrix.mulVec (quraF d) (quraKet00Perp d) = quraKet00 d := by
  ext a
  change (∑ b : Fin d × Fin d, quraF d a b * quraKet00Perp d b) = quraKet00 d a
  -- ∑ b, (δ_{a,b} − v a·star(v b))·perp b = perp a − v a·(∑ b, v b·perp b) = perp a − v a = ket00 a
  have hdot : (∑ b : Fin d × Fin d, quraV d b * quraKet00Perp d b) = 1 := by
    -- ∑ v b·perp b = ∑ (perp b − ket00 b)·perp b = ∑ perp² − ∑ ket00·perp = 1 − 0
    have hperpstar : ∀ b : Fin d × Fin d, star (quraKet00Perp d b) = quraKet00Perp d b := by
      intro b
      by_cases h0 : b.1 = 0 ∧ b.2 = 0
      · simp [quraKet00Perp, h0]
      · simp [quraKet00Perp, h0, star_inv₀]
    have hperp : (∑ b : Fin d × Fin d, quraKet00Perp d b * quraKet00Perp d b) = 1 := by
      simpa [hperpstar] using quraPerp_dot_perp hd
    have horth : (∑ b : Fin d × Fin d, quraKet00 d b * quraKet00Perp d b) = 0 := by
      -- ket00·perp = 0 everywhere (disjoint supports)
      apply Finset.sum_eq_zero
      intro b hb
      by_cases h0 : b.1 = 0 ∧ b.2 = 0
      · simp [quraKet00, quraKet00Perp, h0]
      · simp [quraKet00, quraKet00Perp, h0]
    calc
      (∑ b : Fin d × Fin d, quraV d b * quraKet00Perp d b)
          = ∑ b : Fin d × Fin d, (quraKet00Perp d b - quraKet00 d b) * quraKet00Perp d b := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [quraV]
      _ = ∑ b : Fin d × Fin d, (quraKet00Perp d b * quraKet00Perp d b -
          quraKet00 d b * quraKet00Perp d b) := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
      _ = (∑ b : Fin d × Fin d, quraKet00Perp d b * quraKet00Perp d b) -
          (∑ b : Fin d × Fin d, quraKet00 d b * quraKet00Perp d b) := by
            rw [Finset.sum_sub_distrib]
      _ = 1 - 0 := by rw [hperp, horth]
      _ = 1 := by norm_num
  -- now the main computation
  simp only [quraF_apply]
  -- ∑ b, (δ_{a,b} − v a·star(v b))·perp b — split the sum
  have hsplit : (∑ x : Fin d × Fin d,
      ((if a = x then 1 else 0) - quraV d a * star (quraV d x)) * quraKet00Perp d x) =
      (∑ x : Fin d × Fin d, (if a = x then 1 else 0) * quraKet00Perp d x) -
      (∑ x : Fin d × Fin d, quraV d a * star (quraV d x) * quraKet00Perp d x) := by
    calc
      (∑ x : Fin d × Fin d,
          ((if a = x then 1 else 0) - quraV d a * star (quraV d x)) * quraKet00Perp d x)
          = ∑ x : Fin d × Fin d,
              ((if a = x then 1 else 0) * quraKet00Perp d x -
                quraV d a * star (quraV d x) * quraKet00Perp d x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = (∑ x : Fin d × Fin d, (if a = x then 1 else 0) * quraKet00Perp d x) -
          (∑ x : Fin d × Fin d, quraV d a * star (quraV d x) * quraKet00Perp d x) := by
            rw [Finset.sum_sub_distrib]
  rw [hsplit]
  -- ∑ b, δ_{a,b}·perp b = perp a
  have hδsum : (∑ b : Fin d × Fin d, (if a = b then 1 else 0) * quraKet00Perp d b) =
      quraKet00Perp d a := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hne
      simp [show ¬(a = b) from fun h => hne h.symm]
    · intro h
      exact False.elim (h (Finset.mem_univ a))
  -- ∑ b, v a·star(v b)·perp b = v a·(∑ b, star(v b)·perp b) = v a·1
  have hvsum : (∑ b : Fin d × Fin d, quraV d a * star (quraV d b) * quraKet00Perp d b) =
      quraV d a := by
    -- pull the v a out
    calc
      (∑ b : Fin d × Fin d, quraV d a * star (quraV d b) * quraKet00Perp d b)
          = ∑ b : Fin d × Fin d, quraV d a * (star (quraV d b) * quraKet00Perp d b) := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
      _ = quraV d a * (∑ b : Fin d × Fin d, star (quraV d b) * quraKet00Perp d b) := by
            rw [← Finset.mul_sum]
      _ = quraV d a * 1 := by
            have hdot' : (∑ b : Fin d × Fin d, star (quraV d b) * quraKet00Perp d b) = 1 := by
              calc
                (∑ b : Fin d × Fin d, star (quraV d b) * quraKet00Perp d b)
                    = ∑ b : Fin d × Fin d, quraV d b * quraKet00Perp d b := by
                      apply Finset.sum_congr rfl
                      intro b hb
                      rw [quraV_star]
                _ = 1 := hdot
            rw [hdot']
      _ = quraV d a := by simp
  rw [hδsum, hvsum]
  -- perp a − v a = ket00 a
  rw [quraV]
  ring

/-- `F†|00⊥⟩ = |00⟩`. -/
lemma quraF_conjTranspose_ket00Perp (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    Matrix.mulVec (quraF d).conjTranspose (quraKet00Perp d) = quraKet00 d := by
  -- F† = F since F is real-symmetric
  have hsym : (quraF d).conjTranspose = quraF d := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [quraF_apply]
      ring
    · simp [quraF_apply, hab, show ¬(b = a) from fun h => hab h.symm]
      ring
  rw [hsym]
  exact quraF_mulVec_ket00Perp d hd


/-- `A = |1⟩⟨1| ⊗ F + |0⟩⟨0| ⊗ I` on the ancilla plus two control qudits. -/
def quraG1 (d : ℕ) : Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ :=
  Matrix.of fun a b =>
    (if a.1 = 1 ∧ b.1 = 1 then quraF d a.2 b.2 else 0) +
    (if a.1 = 0 ∧ b.1 = 0 then (if a.2 = b.2 then 1 else 0) else 0)

/-- `B = (X₂ − I₂) ⊗ |00⟩⟨00| + I₂ ⊗ I` on the ancilla plus two control qudits. -/
def quraG2 (d : ℕ) : Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ :=
  Matrix.of fun a b =>
    (X₂ a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 * quraKet00 d b.2 +
    (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0)

/-- `G = A·B` (paper Eq. `eqn:G and D`). -/
def quraG (d : ℕ) : Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ :=
  quraG1 d * quraG2 d

@[simp]
theorem quraG1_apply (d : ℕ) (a b : Fin 2 × (Fin d × Fin d)) :
    quraG1 d a b =
      (if a.1 = 1 ∧ b.1 = 1 then quraF d a.2 b.2 else 0) +
      (if a.1 = 0 ∧ b.1 = 0 then (if a.2 = b.2 then 1 else 0) else 0) := by
  rfl

@[simp]
theorem quraG2_apply (d : ℕ) (a b : Fin 2 × (Fin d × Fin d)) :
    quraG2 d a b =
      (X₂ a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 * quraKet00 d b.2 +
      (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) := by
  rfl

/-- `|0⟩ ⊗ |00⟩`. -/
def quraV00 (d : ℕ) : Fin 2 × (Fin d × Fin d) → ℂ :=
  fun a => k₀ a.1 * quraKet00 d a.2

/-- `|1⟩ ⊗ |00⊥⟩`. -/
def quraV1perp (d : ℕ) : Fin 2 × (Fin d × Fin d) → ℂ :=
  fun a => k₁ a.1 * quraKet00Perp d a.2

/-- `B|0⟩|00⟩ = |1⟩|00⟩`. -/
lemma quraG2_mulVec_ket0_ket00 (d : ℕ) [NeZero d] :
    Matrix.mulVec (quraG2 d) (quraV00 d) = fun a => k₁ a.1 * quraKet00 d a.2 := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG2 d a b * quraV00 d b) = k₁ a.1 * quraKet00 d a.2
  -- B·(|0⟩|00⟩) = ((X₂−I₂)|0⟩)·|00⟩⟨00|·|00⟩ + |0⟩|00⟩ = (|1⟩−|0⟩)|00⟩ + |0⟩|00⟩ = |1⟩|00⟩
  -- split the sum over the two parts of quraG2
  have hsplit : (∑ b : Fin 2 × (Fin d × Fin d), quraG2 d a b * quraV00 d b) =
      (∑ b : Fin 2 × (Fin d × Fin d),
        (X₂ a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 *
          quraKet00 d b.2 * quraV00 d b) +
      (∑ b : Fin 2 × (Fin d × Fin d),
        (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) * quraV00 d b) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h1 : a.1 = b.1
    · by_cases h2 : a.2 = b.2
      · -- both match: summand = (X₂ a.1 b.1 − 1)·k a.2·k b.2·v + k·v
        by_cases hk : b.2.1 = 0 ∧ b.2.2 = 0
        · by_cases hb0 : b.1 = 0
          · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, hb0,
            NormalizedVector.ket_apply]
          · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, hb0,
            NormalizedVector.ket_apply]
        · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, NormalizedVector.ket_apply]
      · -- a.2 ≠ b.2: the second part vanishes; first part has k b.2 ≠ k a.2 (still ite algebra)
        by_cases hk : b.2.1 = 0 ∧ b.2.2 = 0
        · by_cases hk2 : a.2.1 = 0 ∧ a.2.2 = 0
          · -- b.2 = (0,0) but a.2 ≠ b.2 with a.2 = (0,0): contradiction
            exfalso
            apply h2
            apply Prod.ext
            · exact hk2.1.trans hk.1.symm
            · exact hk2.2.trans hk.2.symm
          · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, hk2,
            NormalizedVector.ket_apply]
        · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, NormalizedVector.ket_apply]
    · -- a.1 ≠ b.1: the X₂−δ part is ±1 and the δ part vanishes
      by_cases h2 : a.2 = b.2
      · by_cases hk : b.2.1 = 0 ∧ b.2.2 = 0
        · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, NormalizedVector.ket_apply]
        · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, NormalizedVector.ket_apply]
      · by_cases hk : b.2.1 = 0 ∧ b.2.2 = 0
        · by_cases hk2 : a.2.1 = 0 ∧ a.2.2 = 0
          · exfalso
            apply h2
            apply Prod.ext
            · exact hk2.1.trans hk.1.symm
            · exact hk2.2.trans hk.2.symm
          · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, hk2,
            NormalizedVector.ket_apply]
        · simp [quraG2_apply, quraV00, quraKet00, quraX2, h1, h2, hk, NormalizedVector.ket_apply]
  rw [hsplit]
  -- second part: Σ_b δ_{a.1,b.1}·δ_{a.2,b.2}·(ket0 b.1·ket00 b.2) = ket0 a.1·ket00 a.2
  have h2 : (∑ b : Fin 2 × (Fin d × Fin d),
      (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) * quraV00 d b) =
      quraV00 d a := by
    rw [Finset.sum_eq_single a]
    · simp [quraV00]
    · intro b hb hne
      have hnot : ¬(a.1 = b.1 ∧ a.2 = b.2) := by
        intro h
        apply hne
        apply Prod.ext
        · exact h.1.symm
        · exact h.2.symm
      by_cases h1 : a.1 = b.1
      · by_cases h2 : a.2 = b.2
        · exfalso
          exact hnot ⟨h1, h2⟩
        · simp [h2]
      · simp [h1]
    · intro h
      exact False.elim (h (Finset.mem_univ a))
  -- first part: Σ_b (X₂ a.1 b.1 − δ)·ket00 a.2·ket00 b.2·(ket0 b.1·ket00 b.2)
  --   = ket00 a.2 · (X₂ a.1 0 − δ_{a.1,0})  (only b = (0, (0,0)) contributes)
  have h1 : (∑ b : Fin 2 × (Fin d × Fin d),
      (X₂ a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 *
        quraKet00 d b.2 * quraV00 d b) =
      quraKet00 d a.2 * (X₂ a.1 0 - (if a.1 = 0 then 1 else 0)) := by
    -- collapse b to (0, (0, 0))
    rw [Finset.sum_eq_single (0, (0, 0))]
    · -- main: b = (0, (0,0))
      have hk0 : quraKet00 d (0, 0) = 1 := by
        simp [quraKet00]
      have hv0 : quraV00 d (0, (0, 0)) = 1 := by
        simp [quraV00, quraKet00, NormalizedVector.ket_apply]
      simp [hk0, hv0]
      ring
    · intro b hb hne
      -- b ≠ (0,(0,0)): either b.1 ≠ 0 or b.2 ≠ (0,0)
      by_cases hb1 : b.1 = 0
      · -- b.2 ≠ (0,0) → ket00 b.2 = 0
        have hb2 : b.2 ≠ (0, 0) := by
          intro h
          apply hne
          apply Prod.ext
          · exact hb1
          · exact h
        have hk : quraKet00 d b.2 = 0 := by
          have hnot : ¬(b.2.1 = 0 ∧ b.2.2 = 0) := by
            intro h
            apply hb2
            apply Prod.ext
            · exact h.1
            · exact h.2
          simp [quraKet00, hnot]
        simp [hk]
      · -- b.1 ≠ 0 → ket0 b.1 = 0
        have hk0 : k₀ b.1 = 0 := by
          simp [hb1, NormalizedVector.ket_apply]
        simp [quraV00, hk0]
    · intro h
      exact False.elim (h (Finset.mem_univ (0, (0, 0))))
  rw [h1, h2]
  -- total: ket00 a.2·(X₂ a.1 0 − δ_{a.1,0}) + ket0 a.1·ket00 a.2 = ket1 a.1·ket00 a.2
  by_cases ha0 : a.1 = 0
  · have ha' : a = (0, a.2) := by
      apply Prod.ext
      · exact ha0
      · rfl
    rw [ha']
    have hx : X₂ 0 0 = 0 := by simp [quraX2]
    have hk0 : k₀ 0 = 1 := by simp [NormalizedVector.ket_apply]
    have hk1 : k₁ 0 = 0 := by simp [NormalizedVector.ket_apply]
    simp [quraV00, hk0, hk1]
  · have ha1 : a.1 = 1 := by
      apply Fin.ext
      have hlt : a.1.val < 2 := a.1.isLt
      have hne0 : a.1.val ≠ 0 := by
        intro h
        apply ha0
        apply Fin.ext
        exact h
      omega
    have ha' : a = (1, a.2) := by
      apply Prod.ext
      · exact ha1
      · rfl
    rw [ha']
    have hx : X₂ 1 0 = 1 := by simp [quraX2]
    have hk0 : k₀ 1 = 0 := by simp [NormalizedVector.ket_apply]
    have hk1 : k₁ 1 = 1 := by simp [NormalizedVector.ket_apply]
    simp [quraV00, hk0, hk1]

/-- `A|1⟩|00⟩ = |1⟩|00⊥⟩`. -/
lemma quraG1_mulVec_ket1_ket00 (d : ℕ) [NeZero d] :
    Matrix.mulVec (quraG1 d) (fun a => k₁ a.1 * quraKet00 d a.2) = quraV1perp d := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG1 d a b * (k₁ b.1 * quraKet00 d b.2)) = k₁ a.1 * quraKet00Perp d a.2
  by_cases ha1 : a.1 = 1
  · have ha' : a = (1, a.2) := by
      apply Prod.ext
      · exact ha1
      · rfl
    rw [ha']
    -- collapse b to (1, (0, 0)): only ket1 b.1 · ket00 b.2 ≠ 0 there
    rw [Finset.sum_eq_single (1, (0, 0))]
    · -- main: b = (1, (0,0))
      have hk1 : k₁ 1 = 1 := by simp [NormalizedVector.ket_apply]
      have hk00 : quraKet00 d (0, 0) = 1 := by simp [quraKet00]
      have hF00 : quraF d a.2 (0, 0) = quraKet00Perp d a.2 := by
        -- (F·ket00)(a.2) = F a.2 (0,0) = perp a.2
        have h := congrArg (fun v : Fin d × Fin d → ℂ => v a.2) (quraF_mulVec_ket00 d)
        have hcoll : (Matrix.mulVec (quraF d) (quraKet00 d)) a.2 = quraF d a.2 (0, 0) := by
          rw [Matrix.mulVec]
          change (∑ b : Fin d × Fin d, quraF d a.2 b * quraKet00 d b) = quraF d a.2 (0, 0)
          rw [Finset.sum_eq_single (0, 0)]
          · simp [quraKet00]
          · intro b hb hne
            have hnot : ¬(b.1 = 0 ∧ b.2 = 0) := by
              intro h
              apply hne
              apply Prod.ext
              · exact h.1
              · exact h.2
            simp [quraKet00, hnot]
          · intro h
            exact False.elim (h (Finset.mem_univ (0, 0)))
        rw [← hcoll]
        exact h
      rw [quraG1_apply, hF00]
      simp [hk1, hk00]
    · intro b hb hne
      -- b ≠ (1,(0,0)) → ket1 b.1·ket00 b.2 = 0
      by_cases hb1 : b.1 = 1
      · -- b.2 ≠ (0,0) → ket00 b.2 = 0
        have hb2 : b.2 ≠ (0, 0) := by
          intro h
          apply hne
          apply Prod.ext
          · exact hb1
          · exact h
        have hk : quraKet00 d b.2 = 0 := by
          have hnot : ¬(b.2.1 = 0 ∧ b.2.2 = 0) := by
            intro h
            apply hb2
            apply Prod.ext
            · exact h.1
            · exact h.2
          simp [quraKet00, hnot]
        simp [hk]
      · -- b.1 ≠ 1 → ket1 b.1 = 0
        have hk1 : k₁ b.1 = 0 := by simp [hb1, NormalizedVector.ket_apply]
        simp [hk1]
    · intro h
      exact False.elim (h (Finset.mem_univ (1, (0, 0))))
  · -- a.1 ≠ 1, i.e. a.1 = 0: the whole sum is 0
    have ha0 : a.1 = 0 := by
      apply Fin.ext
      have hlt : a.1.val < 2 := a.1.isLt
      have hne1 : a.1.val ≠ 1 := by
        intro h
        apply ha1
        apply Fin.ext
        exact h
      omega
    have ha' : a = (0, a.2) := by
      apply Prod.ext
      · exact ha0
      · rfl
    rw [ha']
    -- every summand is 0: quraG1 d (0, a.2) b needs b.1 = 0 for the identity part, but ket1 b.1 =
    -- 0 there
    have hsum0 : (∑ b : Fin 2 × (Fin d × Fin d),
        quraG1 d (0, a.2) b * (k₁ b.1 * quraKet00 d b.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hb1 : b.1 = 0
      · -- ket1 0 = 0
        have hk1 : k₁ b.1 = 0 := by simp [hb1, NormalizedVector.ket_apply]
        simp [hk1]
      · -- b.1 = 1: the identity part of quraG1 needs b.1 = 0
        have hb1' : b.1 = 1 := by
          apply Fin.ext
          have hlt : b.1.val < 2 := b.1.isLt
          have hne0 : b.1.val ≠ 0 := by
            intro h
            apply hb1
            apply Fin.ext
            exact h
          omega
        have hg1 : quraG1 d (0, a.2) b = 0 := by
          simp [quraG1_apply, hb1']
        rw [hg1]
        simp
    -- RHS: ket1 0 · perp = 0
    have hk1 : k₁ 0 = 0 := by simp [NormalizedVector.ket_apply]
    rw [hsum0, hk1]
    simp

/-- `A|1⟩|00⊥⟩ = |1⟩|00⟩`. -/
lemma quraG1_mulVec_ket1_ket00Perp (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    Matrix.mulVec (quraG1 d) (fun a => k₁ a.1 * quraKet00Perp d a.2) =
      fun a => k₁ a.1 * quraKet00 d a.2 := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG1 d a b * (k₁ b.1 * quraKet00Perp d b.2)) = k₁ a.1 * quraKet00 d a.2
  by_cases ha1 : a.1 = 1
  · have ha' : a = (1, a.2) := by
      apply Prod.ext
      · exact ha1
      · rfl
    rw [ha']
    -- the sum over b: only b.1 = 1 contributes (the F part); Σ_p F a.2 p·perp p = (F·perp)(a.2) =
    -- ket00 a.2
    have hsum : (∑ b : Fin 2 × (Fin d × Fin d),
        quraG1 d (1, a.2) b * (k₁ b.1 * quraKet00Perp d b.2)) = quraKet00 d a.2 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single 1]
      · -- i = 1: Σ_p F a.2 p·ket1 1·perp p = (F·perp)(a.2) = ket00 a.2
        have hk1 : k₁ 1 = 1 := by simp [NormalizedVector.ket_apply]
        have hF : (Matrix.mulVec (quraF d) (quraKet00Perp d)) a.2 = quraKet00 d a.2 := by
          exact congrArg (fun v : Fin d × Fin d → ℂ => v a.2) (quraF_mulVec_ket00Perp d hd)
        have hFsum : (∑ p : Fin d × Fin d, quraF d a.2 p * quraKet00Perp d p) =
            quraKet00 d a.2 := by
          rw [Matrix.mulVec] at hF
          change (∑ p : Fin d × Fin d, quraF d a.2 p * quraKet00Perp d p) = quraKet00 d a.2 at hF
          exact hF
        calc
          (∑ p : Fin d × Fin d, quraG1 d (1, a.2) (1, p) * (k₁ 1 * quraKet00Perp d p))
              = ∑ p : Fin d × Fin d, quraF d a.2 p * quraKet00Perp d p := by
                apply Finset.sum_congr rfl
                intro p hp
                simp [quraG1_apply, hk1]
          _ = quraKet00 d a.2 := hFsum
      · intro i hi hne
        -- i ≠ 1 → ket1 i = 0
        have hk : k₁ i = 0 := by
          by_cases hi1 : i = 1
          · exfalso
            apply hne
            exact hi1
          · simp [hi1, NormalizedVector.ket_apply]
        -- the whole inner sum is 0
        apply Finset.sum_eq_zero
        intro p hp
        simp [hk]
      · intro h
        exact False.elim (h (Finset.mem_univ 1))
    have hk1 : k₁ 1 = 1 := by simp [NormalizedVector.ket_apply]
    rw [hsum, hk1]
    simp
  · -- a.1 ≠ 1 → a.1 = 0: the whole sum is 0
    have ha0 : a.1 = 0 := by
      apply Fin.ext
      have hlt : a.1.val < 2 := a.1.isLt
      have hne1 : a.1.val ≠ 1 := by
        intro h
        apply ha1
        apply Fin.ext
        exact h
      omega
    have ha' : a = (0, a.2) := by
      apply Prod.ext
      · exact ha0
      · rfl
    rw [ha']
    have hsum0 : (∑ b : Fin 2 × (Fin d × Fin d),
        quraG1 d (0, a.2) b * (k₁ b.1 * quraKet00Perp d b.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hb1 : b.1 = 0
      · have hk : k₁ b.1 = 0 := by simp [hb1, NormalizedVector.ket_apply]
        simp [hk]
      · have hb1' : b.1 = 1 := by
          apply Fin.ext
          have hlt : b.1.val < 2 := b.1.isLt
          have hne0 : b.1.val ≠ 0 := by
            intro h
            apply hb1
            apply Fin.ext
            exact h
          omega
        have hg : quraG1 d (0, a.2) b = 0 := by simp [quraG1_apply, hb1']
        rw [hg]
        simp
    have hk1 : k₁ 0 = 0 := by simp [NormalizedVector.ket_apply]
    rw [hsum0, hk1]
    simp

/-- `F` has real entries: `star (F a b) = F a b`. -/
lemma quraF_star_apply (d : ℕ) [NeZero d] (a b : Fin d × Fin d) :
    star (quraF d a b) = quraF d a b := by
  rw [quraF_apply]
  by_cases h : a = b
  · subst b
    simp [quraV_star]
  · simp [h, quraV_star]

/-- `F` is symmetric: `F b a = F a b`. -/
lemma quraF_symm_apply (d : ℕ) [NeZero d] (a b : Fin d × Fin d) :
    quraF d b a = quraF d a b := by
  rw [quraF_apply]
  by_cases h : a = b
  · subst b
    rfl
  · have hne : ¬ b = a := fun hh => h hh.symm
    simp [h, hne, quraV_star]
    ring

-- Declaration-scoped exception: simp removes ancilla cases before applying F's symmetry.
set_option linter.flexible false in
/-- `A` is real-symmetric: `A† = A`. -/
lemma quraG1_conjTranspose (d : ℕ) [NeZero d] :
    (quraG1 d).conjTranspose = quraG1 d := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  have hFsym : star (quraF d b.2 a.2) = quraF d a.2 b.2 := by
    rw [quraF_star_apply d b.2 a.2, quraF_symm_apply d b.2 a.2]
  -- handle the four cases of the ancilla bits
  by_cases ha1 : a.1 = 1
  · by_cases hb1 : b.1 = 1
    · -- both 1: F parts
      -- expand quraG1 on both sides without unfolding F
      change star ((if b.1 = 1 ∧ a.1 = 1 then quraF d b.2 a.2 else 0) +
          (if b.1 = 0 ∧ a.1 = 0 then (if b.2 = a.2 then 1 else 0) else 0)) =
          (if a.1 = 1 ∧ b.1 = 1 then quraF d a.2 b.2 else 0) +
          (if a.1 = 0 ∧ b.1 = 0 then (if a.2 = b.2 then 1 else 0) else 0)
      simp [ha1, hb1, -quraF_apply]
      exact hFsym
    · -- a.1 = 1, b.1 ≠ 1
      have hb0 : b.1 = 0 := by
        apply Fin.ext
        have hlt : b.1.val < 2 := b.1.isLt
        have hne1 : b.1.val ≠ 1 := by
          intro hh
          apply hb1
          apply Fin.ext
          exact hh
        omega
      have ha0 : ¬(a.1 = 0) := by
        intro hh
        rw [hh] at ha1
        norm_num at ha1
      change star ((if b.1 = 1 ∧ a.1 = 1 then quraF d b.2 a.2 else 0) +
          (if b.1 = 0 ∧ a.1 = 0 then (if b.2 = a.2 then 1 else 0) else 0)) =
          (if a.1 = 1 ∧ b.1 = 1 then quraF d a.2 b.2 else 0) +
          (if a.1 = 0 ∧ b.1 = 0 then (if a.2 = b.2 then 1 else 0) else 0)
      simp [ha1, hb0]
  · -- a.1 ≠ 1
    have ha0 : a.1 = 0 := by
      apply Fin.ext
      have hlt : a.1.val < 2 := a.1.isLt
      have hne1 : a.1.val ≠ 1 := by
        intro hh
        apply ha1
        apply Fin.ext
        exact hh
      omega
    by_cases hb1 : b.1 = 1
    · -- a.1 = 0, b.1 = 1
      have hb0 : ¬(b.1 = 0) := by
        intro hh
        rw [hh] at hb1
        norm_num at hb1
      change star ((if b.1 = 1 ∧ a.1 = 1 then quraF d b.2 a.2 else 0) +
          (if b.1 = 0 ∧ a.1 = 0 then (if b.2 = a.2 then 1 else 0) else 0)) =
          (if a.1 = 1 ∧ b.1 = 1 then quraF d a.2 b.2 else 0) +
          (if a.1 = 0 ∧ b.1 = 0 then (if a.2 = b.2 then 1 else 0) else 0)
      simp [ha0, hb1]
    · -- both 0: identity parts
      have hb0 : b.1 = 0 := by
        apply Fin.ext
        have hlt : b.1.val < 2 := b.1.isLt
        have hne1 : b.1.val ≠ 1 := by
          intro hh
          apply hb1
          apply Fin.ext
          exact hh
        omega
      change star ((if b.1 = 1 ∧ a.1 = 1 then quraF d b.2 a.2 else 0) +
          (if b.1 = 0 ∧ a.1 = 0 then (if b.2 = a.2 then 1 else 0) else 0)) =
          (if a.1 = 1 ∧ b.1 = 1 then quraF d a.2 b.2 else 0) +
          (if a.1 = 0 ∧ b.1 = 0 then (if a.2 = b.2 then 1 else 0) else 0)
      simp [ha0, hb0]
      by_cases h : a.2 = b.2
      · simp [h]
      · simp [h, show ¬(b.2 = a.2) from fun hh => h hh.symm]

/-- `X₂` is symmetric: `X₂ i j = X₂ j i`. -/
lemma quraX2_symm (i j : Fin 2) : X₂ i j = X₂ j i := by
  rw [quraX2_apply, quraX2_apply]
  by_cases h : i = j
  · subst j
    rfl
  · have h1 : i.val ≠ j.val := fun hh => h (Fin.ext hh)
    have h2 : j.val ≠ i.val := fun hh => h1 hh.symm
    simp [h1, h2]

/-- `X₂` has real entries. -/
lemma quraX2_star (i j : Fin 2) : star (X₂ i j) = X₂ i j := by
  rw [quraX2_apply]
  by_cases h : i = j
  · subst j
    simp
  · have h1 : i.val ≠ j.val := fun hh => h (Fin.ext hh)
    simp [h1]

/-- `|00⟩` has real entries. -/
lemma quraKet00_star (d : ℕ) (a : Fin d × Fin d) : star (quraKet00 d a) = quraKet00 d a := by
  simp [quraKet00]

/-- `B` is real-symmetric: `B† = B`. -/
lemma quraG2_conjTranspose (d : ℕ) :
    (quraG2 d).conjTranspose = quraG2 d := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [quraG2_apply]
  by_cases h1 : a.1 = b.1
  · rw [h1]
    by_cases h2 : a.2 = b.2
    · rw [h2]
      simp [quraX2, quraKet00_star]
    · have h2' : ¬ b.2 = a.2 := fun hh => h2 hh.symm
      simp [quraX2, h2, h2', quraKet00_star]
      ring
  · by_cases h2 : a.2 = b.2
    · rw [h2]
      have h1' : ¬ b.1 = a.1 := fun hh => h1 hh.symm
      have hv : a.1.val ≠ b.1.val := fun hh => h1 (Fin.ext hh)
      have hv' : b.1.val ≠ a.1.val := fun hh => hv hh.symm
      simp [quraX2, h1, h1', hv, hv', quraKet00_star]
    · have h1' : ¬ b.1 = a.1 := fun hh => h1 hh.symm
      have h2' : ¬ b.2 = a.2 := fun hh => h2 hh.symm
      have hv : a.1.val ≠ b.1.val := fun hh => h1 (Fin.ext hh)
      have hv' : b.1.val ≠ a.1.val := fun hh => hv hh.symm
      simp [quraX2, h1, h1', h2, h2', hv, hv', quraKet00_star]
      ring

/-- `G† = B†·A† = B·A`. -/
lemma quraG_conjTranspose (d : ℕ) [NeZero d] :
    (quraG d).conjTranspose = quraG2 d * quraG1 d := by
  rw [quraG, Matrix.conjTranspose_mul]
  rw [quraG1_conjTranspose, quraG2_conjTranspose]

lemma quraG_mulVec_ket0_ket00 (d : ℕ) [NeZero d] :
    Matrix.mulVec (quraG d) (quraV00 d) = quraV1perp d := by
  -- G = A·B; G|0⟩|00⟩ = A(B|0⟩|00⟩) = A|1⟩|00⟩ = |1⟩|00⊥⟩
  rw [quraG, ← Matrix.mulVec_mulVec]
  rw [quraG2_mulVec_ket0_ket00]
  exact quraG1_mulVec_ket1_ket00 d


lemma quraG2_mulVec_ket0_of_perp (d : ℕ) [NeZero d] (x : Fin d × Fin d → ℂ)
    (hx : x (0, 0) = 0) :
    Matrix.mulVec (quraG2 d) (fun a => k₀ a.1 * x a.2) =
      fun a => k₀ a.1 * x a.2 := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG2 d a b * (k₀ b.1 * x b.2)) = k₀ a.1 * x a.2
  rw [Finset.sum_eq_single a]
  · -- main: b = a
    -- summand = [(X₂ a.1 a.1 − 1)·k a.2·k a.2 + 1]·ket0 a.1·x a.2 — with k a.2·x a.2 = k a.2²·x a.2
    by_cases hk : a.2.1 = 0 ∧ a.2.2 = 0
    · -- a.2 = (0,0): x a.2 = 0 kills everything
      have ha2 : a.2 = (0, 0) := by
        apply Prod.ext
        · exact hk.1
        · exact hk.2
      have hx0 : x a.2 = 0 := by
        rw [ha2]
        exact hx
      simp [quraG2_apply, quraKet00, quraX2, hx0, NormalizedVector.ket_apply]
    · -- k a.2 = 0: the X−δ part has k a.2 = 0
      have hk0 : quraKet00 d a.2 = 0 := by
        have hnot : ¬(a.2.1 = 0 ∧ a.2.2 = 0) := by
          intro h
          apply hk
          exact h
        simp [quraKet00, hnot]
      simp [quraG2_apply, quraX2, hk0, NormalizedVector.ket_apply]
  · intro b hb hne
    -- b ≠ a: either b.2 ≠ (0,0) (→ k b.2 = 0) or b.2 = (0,0) (→ x b.2 = 0)
    by_cases hb00 : b.2.1 = 0 ∧ b.2.2 = 0
    · -- b.2 = (0,0): x b.2 = 0
      have hb2 : b.2 = (0, 0) := by
        apply Prod.ext
        · exact hb00.1
        · exact hb00.2
      have hx0 : x b.2 = 0 := by
        rw [hb2]
        exact hx
      simp [hx0]
    · -- k b.2 = 0
      have hk : quraKet00 d b.2 = 0 := by
        have hnot : ¬(b.2.1 = 0 ∧ b.2.2 = 0) := by
          intro h
          apply hb00
          exact h
        simp [quraKet00, hnot]
      by_cases h1 : a.1 = b.1
      · by_cases h2 : a.2 = b.2
        · exfalso
          apply hne
          apply Prod.ext
          · exact h1.symm
          · exact h2.symm
        · simp [hk, h2]
      · simp [hk, h1]
  · intro h
    exact False.elim (h (Finset.mem_univ a))

/-- `A|0⟩⊗x = |0⟩⊗x` for any `x`. -/
lemma quraG1_mulVec_ket0 (d : ℕ) (x : Fin d × Fin d → ℂ) :
    Matrix.mulVec (quraG1 d) (fun a => k₀ a.1 * x a.2) =
      fun a => k₀ a.1 * x a.2 := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG1 d a b * (k₀ b.1 * x b.2)) = k₀ a.1 * x a.2
  by_cases ha0 : a.1 = 0
  · -- a.1 = 0: collapse b = a
    have ha' : a = (0, a.2) := by
      apply Prod.ext
      · exact ha0
      · rfl
    rw [ha']
    rw [Finset.sum_eq_single (0, a.2)]
    · simp [quraG1_apply, NormalizedVector.ket_apply]
    · intro b hb hne
      -- b ≠ (0, a.2): either b.1 ≠ 0 (identity part gives 0 since a.1 = 0 ≠ b.1) or b.2 ≠ a.2
      by_cases hb1 : b.1 = 0
      · -- b.2 ≠ a.2: the identity part needs b.2 = a.2 → 0
        have hb2 : b.2 ≠ a.2 := by
          intro h
          apply hne
          apply Prod.ext
          · exact hb1
          · exact h
        by_cases hb1b : b.1 = 0
        · -- b.1 = 0 and b.2 ? a.2: the identity part needs b.2 = a.2 → 0
          have hg : quraG1 d (0, a.2) b = 0 := by
            have hnot : ¬(a.2 = b.2) := fun h => hb2 h.symm
            simp [quraG1_apply, hb1, hnot]
          rw [hg]
          simp
        · -- b.1 ? 0 → identity part 0
          have hb1' : b.1 = 1 := by
            apply Fin.ext
            have hlt : b.1.val < 2 := b.1.isLt
            have hne0 : b.1.val ≠ 0 := by
              intro h
              apply hb1b
              apply Fin.ext
              exact h
            omega
          have hg : quraG1 d (0, a.2) b = 0 := by
            simp [quraG1_apply, hb1']
          rw [hg]
          simp
      · -- b.1 ≠ 0: the identity part needs b.1 = 0 → 0
        have hb1' : b.1 = 1 := by
          apply Fin.ext
          have hlt : b.1.val < 2 := b.1.isLt
          have hne0 : b.1.val ≠ 0 := by
            intro h
            apply hb1
            apply Fin.ext
            exact h
          omega
        simp [quraG1_apply, hb1']
    · intro h
      exact False.elim (h (Finset.mem_univ (0, a.2)))
  · -- a.1 = 1: every summand has ket0 b.1 = 0 (since b.1 = 1 for the F-part, ket0 1 = 0)
    have ha1 : a.1 = 1 := by
      apply Fin.ext
      have hlt : a.1.val < 2 := a.1.isLt
      have hne0 : a.1.val ≠ 0 := by
        intro h
        apply ha0
        apply Fin.ext
        exact h
      omega
    have ha' : a = (1, a.2) := by
      apply Prod.ext
      · exact ha1
      · rfl
    rw [ha']
    have hsum0 : (∑ b : Fin 2 × (Fin d × Fin d),
        quraG1 d (1, a.2) b * (k₀ b.1 * x b.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hb1 : b.1 = 1
      · have hk : k₀ b.1 = 0 := by simp [hb1, NormalizedVector.ket_apply]
        simp [hk]
      · have hb1' : b.1 = 0 := by
          apply Fin.ext
          have hlt : b.1.val < 2 := b.1.isLt
          have hne1 : b.1.val ≠ 1 := by
            intro h
            apply hb1
            apply Fin.ext
            exact h
          omega
        have hg : quraG1 d (1, a.2) b = 0 := by simp [quraG1_apply, hb1']
        rw [hg]
        simp
    have hk1 : k₀ 1 = 0 := by simp [NormalizedVector.ket_apply]
    rw [hsum0, hk1]
    simp


/-- `B|1⟩|00⟩ = |0⟩|00⟩`. -/
lemma quraG2_mulVec_ket1_ket00 (d : ℕ) [NeZero d] :
    Matrix.mulVec (quraG2 d) (fun a => k₁ a.1 * quraKet00 d a.2) =
      fun a => k₀ a.1 * quraKet00 d a.2 := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG2 d a b * (k₁ b.1 * quraKet00 d b.2)) = k₀ a.1 * quraKet00 d a.2
  -- B·(|1⟩|00⟩) = ((X₂−I₂)|1⟩)|00⟩ + |1⟩|00⟩ = (|0⟩−|1⟩)|00⟩ + |1⟩|00⟩ = |0⟩|00⟩
  have hsplit : (∑ b : Fin 2 × (Fin d × Fin d), quraG2 d a b * (k₁ b.1 * quraKet00 d b.2)) =
      (∑ b : Fin 2 × (Fin d × Fin d),
        (X₂ a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 *
          quraKet00 d b.2 * (k₁ b.1 * quraKet00 d b.2)) +
      (∑ b : Fin 2 × (Fin d × Fin d),
        (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) *
          (k₁ b.1 * quraKet00 d b.2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    simp [quraG2_apply]
    by_cases h1 : a.1 = b.1
    · by_cases h2 : a.2 = b.2
      · simp [h1, h2]
        ring
      · simp [h1, h2]
    · by_cases h2 : a.2 = b.2
      · simp [h1, h2]
      · simp [h1, h2]
  rw [hsplit]
  -- second part: collapse to b = a
  have h2 : (∑ b : Fin 2 × (Fin d × Fin d),
      (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) *
        (k₁ b.1 * quraKet00 d b.2)) = k₁ a.1 * quraKet00 d a.2 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hne
      have hnot : ¬(a.1 = b.1 ∧ a.2 = b.2) := by
        intro h
        apply hne
        apply Prod.ext
        · exact h.1.symm
        · exact h.2.symm
      by_cases h1 : a.1 = b.1
      · by_cases h2 : a.2 = b.2
        · exfalso
          exact hnot ⟨h1, h2⟩
        · simp [h2]
      · simp [h1]
    · intro h
      exact False.elim (h (Finset.mem_univ a))
  -- first part: collapse to b = (1, (0,0)) — the ket1 b.1·ket00 b.2 forces that
  have h1 : (∑ b : Fin 2 × (Fin d × Fin d),
      (X₂ a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 *
        quraKet00 d b.2 * (k₁ b.1 * quraKet00 d b.2)) =
      quraKet00 d a.2 * (X₂ a.1 1 - (if a.1 = 1 then 1 else 0)) := by
    rw [Finset.sum_eq_single (1, (0, 0))]
    · -- main: b = (1, (0,0))
      have hk1 : k₁ 1 = 1 := by simp [NormalizedVector.ket_apply]
      have hk00 : quraKet00 d (0, 0) = 1 := by simp [quraKet00]
      simp [hk1, hk00]
      ring
    · intro b hb hne
      by_cases hb1 : b.1 = 1
      · -- b.2 ≠ (0,0) → ket00 b.2 = 0
        have hb2 : b.2 ≠ (0, 0) := by
          intro h
          apply hne
          apply Prod.ext
          · exact hb1
          · exact h
        have hk : quraKet00 d b.2 = 0 := by
          have hnot : ¬(b.2.1 = 0 ∧ b.2.2 = 0) := by
            intro h
            apply hb2
            apply Prod.ext
            · exact h.1
            · exact h.2
          simp [quraKet00, hnot]
        simp [hk]
      · -- b.1 ≠ 1 → ket1 b.1 = 0
        have hk1 : k₁ b.1 = 0 := by simp [hb1, NormalizedVector.ket_apply]
        simp [hk1]
    · intro h
      exact False.elim (h (Finset.mem_univ (1, (0, 0))))
  rw [h1, h2]
  -- total: ket00 a.2·(X₂ a.1 1 − δ_{a.1,1}) + ket1 a.1·ket00 a.2 = ket0 a.1·ket00 a.2
  by_cases ha0 : a.1 = 0
  · have ha' : a = (0, a.2) := by
      apply Prod.ext
      · exact ha0
      · rfl
    rw [ha']
    have hx : X₂ 0 1 = 1 := by simp [quraX2]
    have hk0 : k₀ 0 = 1 := by simp [NormalizedVector.ket_apply]
    have hk1 : k₁ 0 = 0 := by simp [NormalizedVector.ket_apply]
    simp [hk0, hk1]
  · have ha1 : a.1 = 1 := by
      apply Fin.ext
      have hlt : a.1.val < 2 := a.1.isLt
      have hne0 : a.1.val ≠ 0 := by
        intro h
        apply ha0
        apply Fin.ext
        exact h
      omega
    have ha' : a = (1, a.2) := by
      apply Prod.ext
      · exact ha1
      · rfl
    rw [ha']
    have hx : X₂ 1 1 = 0 := by simp [quraX2]
    have hk0 : k₀ 1 = 0 := by simp [NormalizedVector.ket_apply]
    have hk1 : k₁ 1 = 1 := by simp [NormalizedVector.ket_apply]
    simp [hk0, hk1]


/-- `G|0⟩⊗x = |0⟩⊗x` when `x` has no `|00⟩` component. -/
lemma quraG_mulVec_ket0_of_perp (d : ℕ) [NeZero d] (x : Fin d × Fin d → ℂ)
    (hx : x (0, 0) = 0) :
    Matrix.mulVec (quraG d) (fun a => k₀ a.1 * x a.2) =
      fun a => k₀ a.1 * x a.2 := by
  rw [quraG, ← Matrix.mulVec_mulVec]
  rw [quraG2_mulVec_ket0_of_perp d x hx]
  exact quraG1_mulVec_ket0 d x

/-- `G†|1⟩|00⊥⟩ = |0⟩|00⟩`. -/
lemma quraG_conjTranspose_ket1_ket00Perp (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    Matrix.mulVec (quraG d).conjTranspose (quraV1perp d) = quraV00 d := by
  rw [quraG_conjTranspose]
  rw [← Matrix.mulVec_mulVec]
  change (quraG2 d).mulVec ((quraG1 d).mulVec
      (fun a => k₁ a.1 * quraKet00Perp d a.2)) = quraV00 d
  rw [quraG1_mulVec_ket1_ket00Perp d hd]
  exact quraG2_mulVec_ket1_ket00 d

/-- `G†|0⟩⊗x = |0⟩⊗x` when `x` has no `|00⟩` component. -/
lemma quraG_conjTranspose_ket0_of_perp (d : ℕ) [NeZero d] (x : Fin d × Fin d → ℂ)
    (hx : x (0, 0) = 0) :
    Matrix.mulVec (quraG d).conjTranspose (fun a => k₀ a.1 * x a.2) =
      fun a => k₀ a.1 * x a.2 := by
  rw [quraG_conjTranspose]
  rw [← Matrix.mulVec_mulVec]
  rw [quraG1_mulVec_ket0 d x]
  exact quraG2_mulVec_ket0_of_perp d x hx
end

end QuantumAlg.UnitaryReversal
