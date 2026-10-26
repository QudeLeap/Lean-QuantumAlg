/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Modes
public import QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.JordanWigner.Ladders
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.Pauli.Letter
import all QuantumAlg.Core.Base.Hamiltonian

/-!
# On-site Hubbard interaction and chemical potential

Occupation is (I-Z)/2 [WBA11, h2.arxiv2.tex:921]. The full interaction u n_up n_down
minus μ(n_up+n_down) retains the identity term and both linear Z terms.
The coefficient choice μ=u/2 removes the linear terms mathematically; their
zero coefficients remain in the literal Pauli presentation.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- The phase-free identity string on the complete register. -/
@[expose] def identityString (L : ℕ) : PauliString (2 * L ^ 2) := fun _ => .i

lemma identityString_op (L : ℕ) : (identityString L).op = 1 := by
  apply mul_left_cancel (a := (identityString L).op)
  rw [mul_one]
  apply Subtype.ext
  change ((identityString L).op : HilbertOperator (Qubits (2 * L ^ 2))) *
    ((identityString L).op : HilbertOperator (Qubits (2 * L ^ 2))) = _
  rw [PauliString.op_mul_op]
  have hm : (identityString L).mul (identityString L) = identityString L := by
    funext j
    rfl
  rw [hm]
  simp [identityString, PauliString.mulPhase, PauliLetter.mulPhase]

private lemma modeZ_commute {n : ℕ} (p q : Fin n) :
    Commute ((JordanWigner.modeZ p).op : HilbertOperator (Qubits n))
      ((JordanWigner.modeZ q).op : HilbertOperator (Qubits n)) := by
  apply (PauliString.commute_iff_op_commute _ _).mp
  have h (j : Fin n) : ¬PauliLetter.anticommutes
      (JordanWigner.modeZ p j) (JordanWigner.modeZ q j) := by
    by_cases hp : j = p <;> by_cases hq : j = q <;>
      simp [JordanWigner.modeZ, hp, hq, PauliLetter.anticommutes]
  simp [PauliString.Commute, PauliString.anticommutingCount, h]

lemma mode_number_commute {n : ℕ} (p q : Fin n) :
    Commute (JordanWigner.number p : HilbertOperator (Qubits n))
      (JordanWigner.number q : HilbertOperator (Qubits n)) := by
  change ((1 / 2 : ℂ) • (1 - ((JordanWigner.modeZ p).op : HilbertOperator (Qubits n)))) *
    ((1 / 2 : ℂ) • (1 - ((JordanWigner.modeZ q).op : HilbertOperator (Qubits n)))) =
    ((1 / 2 : ℂ) • (1 - ((JordanWigner.modeZ q).op : HilbertOperator (Qubits n)))) *
    ((1 / 2 : ℂ) • (1 - ((JordanWigner.modeZ p).op : HilbertOperator (Qubits n))))
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  rw [(modeZ_commute p q).eq]
  abel

/-- Product of the two commuting occupation observables. -/
@[expose] def occupationPair {L : ℕ} (p : Site L) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  ⟨(JordanWigner.number (mode 0 p) : HilbertOperator (Qubits (2 * L ^ 2))) *
    (JordanWigner.number (mode 1 p) : HilbertOperator (Qubits (2 * L ^ 2))), by
      rw [Matrix.IsHermitian]
      rw [Matrix.conjTranspose_mul, (JordanWigner.number (mode 1 p)).isHermitian,
        (JordanWigner.number (mode 0 p)).isHermitian]
      exact (mode_number_commute (mode 0 p) (mode 1 p)).eq.symm⟩

/-- Spin-up times spin-down parity at one physical site. -/
@[expose] def onsiteZZ {L : ℕ} (p : Site L) : PauliString (2 * L ^ 2) :=
  (JordanWigner.modeZ (mode 0 p)).mul (JordanWigner.modeZ (mode 1 p))

lemma onsiteZZ_op {L : ℕ} (p : Site L) :
    ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) =
      ((JordanWigner.modeZ (mode 0 p)).op : HilbertOperator (Qubits (2 * L ^ 2))) *
        ((JordanWigner.modeZ (mode 1 p)).op : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [PauliString.op_mul_op]
  have hphase : PauliString.mulPhase (JordanWigner.modeZ (mode 0 p))
      (JordanWigner.modeZ (mode 1 p)) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    simp only [JordanWigner.modeZ]
    split_ifs <;> rfl
  rw [hphase, one_smul]
  rfl

/-- Physical on-site interaction and chemical potential. -/
@[expose] def siteHamiltonian {L : ℕ} (u μ : ℝ) (p : Site L) :
    Hamiltonian (Qubits (2 * L ^ 2)) :=
  (Hamiltonian.instSub (R := Qubits (2 * L ^ 2))).sub
    ((Hamiltonian.instSMulReal (R := Qubits (2 * L ^ 2))).smul u (occupationPair p))
    ((Hamiltonian.instSMulReal (R := Qubits (2 * L ^ 2))).smul μ
      (Hamiltonian.add (JordanWigner.number (mode 0 p)) (JordanWigner.number (mode 1 p))))

/-- Four literal on-site entries: ZZ, Z-up, Z-down and the identity phase. -/
@[expose] def siteTerms {L : ℕ} (u μ : ℝ) (p : Site L) : PauliSum (2 * L ^ 2) :=
  ⟨[(u / 4, onsiteZZ p), (μ / 2 - u / 4, JordanWigner.modeZ (mode 0 p)),
    (μ / 2 - u / 4, JordanWigner.modeZ (mode 1 p)), (u / 4 - μ, identityString L)]⟩

/-- The complete chemical shift, including its scalar phase, is exact. -/
lemma siteTerms_toHamiltonian {L : ℕ} (u μ : ℝ) (p : Site L) :
    (siteTerms u μ p).toHamiltonian = siteHamiltonian u μ p := by
  apply Hamiltonian.ext
  rw [PauliSum.coe_toHamiltonian]
  simp only [siteTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    PauliSum.coe_termHamiltonian, onsiteZZ_op, identityString_op, Submonoid.coe_one,
    siteHamiltonian]
  let Z0 : HilbertOperator (Qubits (2 * L ^ 2)) := (JordanWigner.modeZ (mode 0 p)).op
  let Z1 : HilbertOperator (Qubits (2 * L ^ 2)) := (JordanWigner.modeZ (mode 1 p)).op
  change _ = (u : ℂ) • (((1 / 2 : ℂ) • (1 - Z0)) * ((1 / 2 : ℂ) • (1 - Z1))) -
    (μ : ℂ) • ((1 / 2 : ℂ) • (1 - Z0) + (1 / 2 : ℂ) • (1 - Z1))
  dsimp only [Z0, Z1]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, one_mul, mul_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- All on-site terms in the fixed physical-site order. -/
@[expose] def onsite (L : ℕ) (u μ : ℝ) : PauliSum (2 * L ^ 2) :=
  PauliSum.ofFamily (fun j : Fin (L ^ 2) => siteTerms u μ (siteAt L j))

/-- The physical sum of all on-site interactions. -/
@[expose] def onsiteHamiltonian (L : ℕ) (u μ : ℝ) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  Hamiltonian.sum (fun p : Site L => siteHamiltonian u μ p)

lemma onsite_toHamiltonian (L : ℕ) (u μ : ℝ) :
    (onsite L u μ).toHamiltonian = onsiteHamiltonian L u μ := by
  rw [onsite, PauliSum.ofFamily_toHamiltonian]
  apply Hamiltonian.ext
  simp only [Hamiltonian.coe_sum, siteTerms_toHamiltonian, onsiteHamiltonian]
  exact sum_siteAt (L := L)
    (fun p => (siteHamiltonian u μ p : HilbertOperator (Qubits (2 * L ^ 2))))

end
end QuantumAlg.FermiHubbard
