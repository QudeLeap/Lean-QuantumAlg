/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Pauli.JordanWigner.Hopping
import all QuantumAlg.Components.Pauli.JordanWigner.Hopping
import all QuantumAlg.Components.Pauli.JordanWigner.Majoranas
import all QuantumAlg.Components.Pauli.JordanWigner.Ladders
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import Mathlib.Tactic

/-!
# Local Majorana algebra

The indexed Clifford relations make locality independent of the length of a
Jordan–Wigner parity string. They are algebraic consequences of the encoding
in [WBA11, h2.arxiv2.tex:329-346].
-/

@[expose] public section

namespace QuantumAlg.JordanWigner

noncomputable section

/-- The two genuine Majorana flavors, indexed without the identity and Z letters. -/
def majoranaAt {n : ℕ} (j : Fin n × Fin 2) : UnitaryOperator (Qubits n) :=
  majorana j.1 (if j.2 = 0 then .x else .y)

lemma majoranaAt_square {n : ℕ} (j : Fin n × Fin 2) :
    (majoranaAt j : HilbertOperator (Qubits n)) * majoranaAt j = 1 :=
  majorana_square _ _

lemma majoranaAt_anticommute {n : ℕ} (j k : Fin n × Fin 2) (hjk : j ≠ k) :
    (majoranaAt j : HilbertOperator (Qubits n)) * majoranaAt k =
      -((majoranaAt k : HilbertOperator (Qubits n)) * majoranaAt j) := by
  rcases j with ⟨p, a⟩
  rcases k with ⟨q, b⟩
  by_cases hpq : p = q
  · subst q
    fin_cases a <;> fin_cases b
    · exact (hjk rfl).elim
    · simpa [majoranaAt] using majorana_xy_anticommute p
    · simpa [majoranaAt] using
        congrArg Neg.neg (majorana_xy_anticommute p).symm
    · exact (hjk rfl).elim
  · exact majorana_anticommute_ne p q hpq _ _
      (by split_ifs <;> simp) (by split_ifs <;> simp)

/-- The Clifford relation including repeated Majorana indices. -/
lemma majoranaAt_car {n : ℕ} (j k : Fin n × Fin 2) :
    (majoranaAt j : HilbertOperator (Qubits n)) * majoranaAt k +
      (majoranaAt k : HilbertOperator (Qubits n)) * majoranaAt j =
        if j = k then (2 : ℂ) • 1 else 0 := by
  by_cases h : j = k
  · subst k
    rw [if_pos rfl, majoranaAt_square]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · simp [h, majoranaAt_anticommute j k h]

/-- A quadratic Majorana monomial acts only at its two endpoints. -/
lemma majoranaAt_pair_lie {n : ℕ} (j k r : Fin n × Fin 2) :
    ⁅(majoranaAt j : HilbertOperator (Qubits n)) * majoranaAt k,
      (majoranaAt r : HilbertOperator (Qubits n))⁆ =
        (if k = r then (2 : ℂ) • (majoranaAt j : HilbertOperator (Qubits n)) else 0) -
        (if j = r then (2 : ℂ) • (majoranaAt k : HilbertOperator (Qubits n)) else 0) := by
  calc
    _ = (majoranaAt j : HilbertOperator (Qubits n)) *
          ((majoranaAt k : HilbertOperator (Qubits n)) * majoranaAt r +
            (majoranaAt r : HilbertOperator (Qubits n)) * majoranaAt k) -
        ((majoranaAt r : HilbertOperator (Qubits n)) * majoranaAt j +
          (majoranaAt j : HilbertOperator (Qubits n)) * majoranaAt r) * majoranaAt k := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = _ := by
      rw [majoranaAt_car, majoranaAt_car]
      by_cases hkr : k = r <;> by_cases hjr : j = r <;>
        simp [hkr, hjr, eq_comm]

/-- The complete hopping operator as two quadratic Majorana monomials. -/
lemma hopping_eq_majoranas {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    (hopping p q : HilbertOperator (Qubits n)) =
      (Complex.I / 2) •
        ((majoranaAt (p, 0) : HilbertOperator (Qubits n)) * majoranaAt (q, 1) -
          (majoranaAt (p, 1) : HilbertOperator (Qubits n)) * majoranaAt (q, 0)) := by
  rw [hopping_eq_ladders p q hpq]
  simp only [creation, annihilation, majoranaAt, Fin.isValue, ↓reduceIte,
    smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add]
  rw [majorana_anticommute_ne q p hpq.symm .x .x (Or.inl rfl) (Or.inl rfl),
    majorana_anticommute_ne q p hpq.symm .x .y (Or.inl rfl) (Or.inr rfl),
    majorana_anticommute_ne q p hpq.symm .y .x (Or.inr rfl) (Or.inl rfl),
    majorana_anticommute_ne q p hpq.symm .y .y (Or.inr rfl) (Or.inr rfl)]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring_nf
  simp
  ring

/-- The scalar sign in the adjoint action of a complete hopping bond. -/
def hoppingMajoranaPhase (a : Fin 2) : ℂ :=
  if a = 0 then -Complex.I else Complex.I

@[simp] lemma hoppingMajoranaPhase_norm (a : Fin 2) :
    ‖hoppingMajoranaPhase a‖ = 1 := by
  fin_cases a <;> simp [hoppingMajoranaPhase]

/-- One complete bond moves a Majorana to the opposite flavor at its other end. -/
lemma hopping_lie_majoranaAt {n : ℕ} (p q : Fin n) (hpq : p ≠ q)
    (r : Fin n) (a : Fin 2) :
    ⁅(hopping p q : HilbertOperator (Qubits n)),
      (majoranaAt (r, a) : HilbertOperator (Qubits n))⁆ =
        hoppingMajoranaPhase a •
          ((if p = r then (majoranaAt (q, a.rev) : HilbertOperator (Qubits n)) else 0) +
            (if q = r then (majoranaAt (p, a.rev) : HilbertOperator (Qubits n)) else 0)) := by
  rw [hopping_eq_majoranas p q hpq]
  have hlin (X Y Z : HilbertOperator (Qubits n)) (c : ℂ) :
      ⁅c • (X - Y), Z⁆ = c • (⁅X, Z⁆ - ⁅Y, Z⁆) := by
    simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub, mul_sub, sub_mul]
    module
  rw [hlin, majoranaAt_pair_lie, majoranaAt_pair_lie]
  have hrev₀ : (0 : Fin 2).rev = 1 := by decide
  have hrev₁ : (1 : Fin 2).rev = 0 := by decide
  fin_cases a <;> by_cases hpr : p = r <;> by_cases hqr : q = r
  all_goals
    simp only [hoppingMajoranaPhase, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Prod.mk.injEq, one_ne_zero, zero_ne_one, and_false, and_true,
      hpr, hqr, ↓reduceIte, zero_sub, sub_zero, hrev₀, hrev₁,
      smul_add, smul_zero, smul_smul, add_zero, zero_add]
  all_goals
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring

/-- A parity operator commutes with a Majorana at every other fermionic mode. -/
lemma modeZ_majoranaAt_commute {n : ℕ} (p q : Fin n) (hpq : p ≠ q) (a : Fin 2) :
    Commute ((modeZ p).op : HilbertOperator (Qubits n))
      (majoranaAt (q, a) : HilbertOperator (Qubits n)) := by
  apply (PauliString.commute_iff_op_commute _ _).mp
  have hpoint : ∀ j : Fin n,
      (if PauliLetter.anticommutes (modeZ p j)
        (majoranaString q (if a = 0 then .x else .y) j) then 1 else 0 : ℕ) = 0 := by
    intro j
    fin_cases a <;>
      simp only [modeZ, majoranaString, Fin.isValue] <;>
      split_ifs <;> simp_all [PauliLetter.anticommutes]
  simp only [PauliString.Commute, PauliString.anticommutingCount, hpoint]
  simp

/-- At its own fermionic mode, parity anticommutes with either Majorana flavor. -/
lemma modeZ_majoranaAt_anticommute {n : ℕ} (p : Fin n) (a : Fin 2) :
    ((modeZ p).op : HilbertOperator (Qubits n)) * majoranaAt (p, a) =
      -((majoranaAt (p, a) : HilbertOperator (Qubits n)) * (modeZ p).op) := by
  apply (PauliString.antiCommute_iff_op_anticommute _ _).mp
  have hpoint : ∀ j : Fin n,
      (if PauliLetter.anticommutes (modeZ p j)
        (majoranaString p (if a = 0 then .x else .y) j) then 1 else 0 : ℕ) =
          if j = p then 1 else 0 := by
    intro j
    fin_cases a <;>
      simp only [modeZ, majoranaString, Fin.isValue] <;>
      split_ifs <;> simp_all [PauliLetter.anticommutes]
  simp only [PauliString.AntiCommute, PauliString.anticommutingCount, hpoint]
  simp

end

end QuantumAlg.JordanWigner
