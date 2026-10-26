/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Core.Base.Hamiltonian
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import Mathlib.Data.Fintype.Basic

/-!
# Pauli letters

The identity and three Pauli matrices use the signs in [WBA11, h2.arxiv2.tex:307].
The multiplication table retains the complex phase explicitly.
-/

public section

namespace QuantumAlg

/-- The four phase-free one-qubit Pauli letters. -/
inductive PauliLetter
  | i | x | y | z
  deriving DecidableEq

instance : Fintype PauliLetter :=
  ⟨{.i, .x, .y, .z}, by intro a; cases a <;> simp⟩

namespace PauliLetter

/-- Certified operator for one Pauli letter. -/
noncomputable def op (a : PauliLetter) : UnitaryOperator (Qubits 1) := by
  exact match a with
  | .i => 1
  | .x => Gate.XOp
  | .y => Gate.YOp
  | .z => Gate.ZOp

/-- Phase-free part of the product of two Pauli letters. -/
@[expose] def mulLetter : PauliLetter → PauliLetter → PauliLetter
  | .i, b => b
  | a, .i => a
  | .x, .x | .y, .y | .z, .z => .i
  | .x, .y | .y, .x => .z
  | .y, .z | .z, .y => .x
  | .z, .x | .x, .z => .y

/-- Complex phase in the ordered Pauli multiplication table. -/
@[expose] noncomputable def mulPhase : PauliLetter → PauliLetter → ℂ
  | .x, .y | .y, .z | .z, .x => Complex.I
  | .y, .x | .z, .y | .x, .z => -Complex.I
  | _, _ => 1

/-- The local condition for anticommutation. -/
@[expose] def anticommutes (a b : PauliLetter) : Prop := a ≠ .i ∧ b ≠ .i ∧ a ≠ b

instance (a b : PauliLetter) : Decidable (anticommutes a b) :=
  inferInstanceAs (Decidable (a ≠ .i ∧ b ≠ .i ∧ a ≠ b))

/-- Explicit entries of the four one-qubit operators. -/
lemma letter_op_apply (a : PauliLetter) (j k : Fin 2) :
    a.op j k = (match a with
      | .i => !![(1 : ℂ), 0; 0, 1]
      | .x => !![(0 : ℂ), 1; 1, 0]
      | .y => !![(0 : ℂ), -Complex.I; Complex.I, 0]
      | .z => !![(1 : ℂ), 0; 0, -1]) j k := by
  cases a <;> fin_cases j <;> fin_cases k <;>
    simp [op, Gate.XOp, Gate.YOp, Gate.ZOp, UnitaryOperator.ofPerm_entry]

/-- Every letter is Hermitian. -/
lemma letter_op_isHermitian (a : PauliLetter) :
    (a.op : HilbertOperator (Qubits 1)).IsHermitian := by
  cases a <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [Matrix.conjTranspose_apply, letter_op_apply]

/-- The complete ordered multiplication table, including its phase. -/
lemma letter_op_mul_op (a b : PauliLetter) :
    (a.op : HilbertOperator (Qubits 1)) * (b.op : HilbertOperator (Qubits 1)) =
      mulPhase a b • ((mulLetter a b).op : HilbertOperator (Qubits 1)) := by
  cases a <;> cases b <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, letter_op_apply, mulLetter, mulPhase]

/-- All table phases have unit modulus. -/
lemma mulPhase_norm (a b : PauliLetter) : ‖mulPhase a b‖ = 1 := by
  cases a <;> cases b <;> simp [mulPhase]

/-- The phase-free table is symmetric. -/
lemma mulLetter_comm (a b : PauliLetter) : mulLetter a b = mulLetter b a := by
  cases a <;> cases b <;> rfl

/-- Swapping two different nonidentity letters introduces a minus sign. -/
lemma letter_phase_swap (a b : PauliLetter) :
    mulPhase a b = (if anticommutes a b then (-1 : ℂ) else 1) * mulPhase b a := by
  cases a <;> cases b <;> simp [mulPhase, anticommutes]

end PauliLetter
end QuantumAlg
