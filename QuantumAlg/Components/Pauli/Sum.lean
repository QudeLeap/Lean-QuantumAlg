/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.Pauli.String
public import QuantumAlg.Core.Base.Hamiltonian
import all QuantumAlg.Core.Base.Hamiltonian
import all QuantumAlg.Core.Base.Gate.OperatorNorm
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn

/-!
# Real weighted Pauli sums

Pauli tensor strings provide the operator vocabulary for qubit Hamiltonians
[WBA11, h2.arxiv2.tex:310]. An ordered list of real weighted strings defines a
Hermitian operator. Its coefficient one-norm bounds its operator norm by the
triangle inequality and unitarity of each string.

The representation preserves order, repeated strings and zero coefficients.
The one-norm belongs to this presentation and need not equal the operator norm.
-/

@[expose] public section

namespace QuantumAlg

/-- An ordered, real weighted list of Pauli tensor strings. -/
structure PauliSum (n : ℕ) where
  /-- Original real coefficients and strings, in their supplied order. -/
  terms : List (ℝ × PauliString n)

namespace PauliSum

variable {n : ℕ}

noncomputable section

/-- The Hermitian operator of one real weighted Pauli string. -/
def termHamiltonian (term : ℝ × PauliString n) : Hamiltonian (Qubits n) :=
  (Hamiltonian.instSMulReal (R := Qubits n)).smul term.1 term.2.hamiltonian

@[simp]
lemma coe_termHamiltonian (term : ℝ × PauliString n) :
    (termHamiltonian term : HilbertOperator (Qubits n)) =
      (term.1 : ℂ) • (term.2.op : HilbertOperator (Qubits n)) :=
  rfl

/-- The finite family indexed by the original term positions. -/
def family (H : PauliSum n) (j : Fin H.terms.length) : Hamiltonian (Qubits n) :=
  termHamiltonian (H.terms.get j)

/-- A Pauli sum as a certified Hermitian operator. -/
def toHamiltonian (H : PauliSum n) : Hamiltonian (Qubits n) :=
  Hamiltonian.sum H.family

/-- The raw matrix view of a Pauli sum. -/
def op (H : PauliSum n) : HilbertOperator (Qubits n) :=
  H.toHamiltonian

lemma family_sum_eq_toHamiltonian (H : PauliSum n) :
    Hamiltonian.sum H.family = H.toHamiltonian :=
  rfl

/-- The finite family preserves exactly the input list's weighted sum. -/
lemma coe_toHamiltonian (H : PauliSum n) :
    (H.toHamiltonian : HilbertOperator (Qubits n)) =
      (H.terms.map fun term => (termHamiltonian term : HilbertOperator (Qubits n))).sum := by
  change (∑ j : Fin H.terms.length,
    (termHamiltonian (H.terms.get j) : HilbertOperator (Qubits n))) = _
  rw [← List.sum_ofFn]
  congr 1
  simpa only [List.get_eq_getElem] using
    (List.ofFn_getElem_eq_map H.terms
      (fun term => (termHamiltonian term : HilbertOperator (Qubits n))))

lemma pauliSum_op_isHermitian (H : PauliSum n) : H.op.IsHermitian :=
  H.toHamiltonian.2

instance : Zero (PauliSum n) := ⟨⟨[]⟩⟩

instance : Add (PauliSum n) := ⟨fun H K => ⟨H.terms ++ K.terms⟩⟩

@[simp]
lemma pauliSum_terms_zero : (0 : PauliSum n).terms = [] :=
  rfl

@[simp]
lemma pauliSum_terms_add (H K : PauliSum n) : (H + K).terms = H.terms ++ K.terms :=
  rfl

lemma toHamiltonian_add (H K : PauliSum n) :
    (H + K).toHamiltonian = Hamiltonian.add H.toHamiltonian K.toHamiltonian := by
  apply Hamiltonian.ext
  simp [coe_toHamiltonian, List.map_append, List.sum_append]

@[simp]
lemma pauliSum_op_zero : (0 : PauliSum n).op = 0 := by
  simp [op, coe_toHamiltonian]

lemma op_add (H K : PauliSum n) : (H + K).op = H.op + K.op := by
  simp only [op, toHamiltonian_add, Hamiltonian.coe_add]

/-- The sum of absolute coefficients of this ordered presentation. -/
def oneNorm (H : PauliSum n) : ℝ :=
  (H.terms.map fun term => |term.1|).sum

lemma oneNorm_nonneg (H : PauliSum n) : 0 ≤ H.oneNorm := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

@[simp]
lemma pauliSum_oneNorm_zero : (0 : PauliSum n).oneNorm = 0 :=
  rfl

lemma oneNorm_add (H K : PauliSum n) : (H + K).oneNorm = H.oneNorm + K.oneNorm := by
  simp [oneNorm, List.map_append, List.sum_append]

lemma termHamiltonian_opNorm (term : ℝ × PauliString n) :
    (termHamiltonian term).opNorm = |term.1| := by
  rw [Hamiltonian.opNorm_eq, coe_termHamiltonian, HilbertOperator.opNorm_smul,
    HilbertOperator.opNorm_unitary (R := Qubits n) term.2.op, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- The coefficient one-norm bounds the operator norm of a real Pauli sum. -/
public theorem opNorm_toHamiltonian_le_oneNorm (H : PauliSum n) :
    Hamiltonian.opNorm H.toHamiltonian ≤ H.oneNorm := by
  calc
    H.toHamiltonian.opNorm ≤ ∑ j, (H.family j).opNorm :=
      Hamiltonian.opNorm_sum_le H.family
    _ = H.oneNorm := by
      simp only [family, termHamiltonian_opNorm]
      rw [← List.sum_ofFn]
      exact congrArg List.sum
        (List.ofFn_getElem_eq_map H.terms (fun term => |term.1|))

end

end PauliSum
end QuantumAlg
