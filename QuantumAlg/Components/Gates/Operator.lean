/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Util.Complex

/-!
# Named elementary qubit operators

Pauli, Hadamard, CNOT, S and T operators and their exact algebra are mathematical
objects. Native gate models and circuit constructors reuse these same operators
without making the operator layer depend on a chosen execution language.
-/

section

namespace QuantumAlg.Gate

open NormalizedVector

noncomputable section

/-- Metadata-free Hadamard operator `H = (1/sqrt 2) [[1, 1], [1, -1]]`. -/
@[expose] public def HOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (invSqrt2 • !![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm,
        star_invSqrt2, invSqrt2_mul_self]
      have hstar : star (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
          = !![(1 : ℂ), 1; 1, -1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
      have hmul :
          (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
            * !![(1 : ℂ), 1; 1, -1] = (2 : ℂ) • 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
      rw [hstar, hmul, smul_smul]
      norm_num)

/-- Metadata-free Pauli-X (NOT) operator. -/
@[expose]
public def XOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofPerm (Equiv.swap 0 1)

/-- The canonical addressed-X operator specializes to the named one-qubit
Pauli-X operator. -/
lemma qubitPrimitive_x_operator :
    (QubitPrimitive.operator (.x 0 : QubitPrimitive 1)) = XOp := by
  unfold QubitPrimitive.operator XOp
  apply congrArg (UnitaryOperator.ofPerm (R := Qubits 1))
  ext label
  fin_cases label <;> decide

/-- Metadata-free Pauli-Y operator `[[0, -i], [i, 0]]`. -/
def YOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(0 : ℂ), -Complex.I; Complex.I, 0] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply])

/-- Metadata-free Pauli-Z operator `[[1, 0], [0, -1]]`. -/
def ZOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(1 : ℂ), 0; 0, -1] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply])

/-- Metadata-free controlled-NOT operator, control = qubit 0. -/
@[expose] public def CNOTOp : UnitaryOperator (Qubits 2) :=
  UnitaryOperator.ofPerm (Equiv.swap 2 3)

/-- The canonical addressed-CNOT operator specializes to the named two-qubit
controlled-NOT operator. -/
lemma qubitPrimitive_cnot_operator :
    (QubitPrimitive.operator (.cnot 0 1 (by decide) : QubitPrimitive 2)) = CNOTOp := by
  unfold QubitPrimitive.operator CNOTOp
  apply congrArg (UnitaryOperator.ofPerm (R := Qubits 2))
  ext label
  fin_cases label <;> decide

/-- `e^{iπ/4} · e^{iπ/4} = i`. -/
lemma exp_pi_div_four_mul_I_mul_self :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
        Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = Complex.I := by
  rw [← Complex.exp_add]
  have h : (Real.pi : ℂ) / 4 * Complex.I + (Real.pi : ℂ) / 4 * Complex.I =
      (Real.pi : ℂ) / 2 * Complex.I := by
    ring
  rw [h]
  exact Complex.exp_pi_div_two_mul_I

/-- The one-branch phase matrix `diag(1, e^{iφ})` is unitary. -/
lemma phaseDiag_mem_unitaryGroup (φ : ℝ) :
    (!![1, 0; 0, Complex.exp ((φ : ℝ) * Complex.I)] : HilbertOperator (Qubits 1)) ∈
      Matrix.unitaryGroup (Qubits 1).Index ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I, exp_I_mul_exp_neg_I]

/-- Metadata-free phase operator `S = diag(1, i)`. -/
public def SOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(1 : ℂ), 0; 0, Complex.I] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply])

/-- Metadata-free phase operator `T = diag(1, e^{iπ/4})`. -/
public def TOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![1, 0; 0, Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)] :
      HilbertOperator (Qubits 1))
    (phaseDiag_mem_unitaryGroup (Real.pi / 4))

/-! ### Clifford+T generator algebra -/

lemma ZOp_mul_ZOp : ZOp * ZOp = 1 := by
  apply Subtype.ext
  change ((ZOp : HilbertOperator (Qubits 1)) * (ZOp : HilbertOperator (Qubits 1))) =
    (1 : HilbertOperator (Qubits 1))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ZOp, Matrix.mul_apply]

lemma SOp_mul_SOp : SOp * SOp = ZOp := by
  apply Subtype.ext
  change ((SOp : HilbertOperator (Qubits 1)) * (SOp : HilbertOperator (Qubits 1))) =
    (ZOp : HilbertOperator (Qubits 1))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SOp, ZOp, Matrix.mul_apply]

lemma TOp_mul_TOp : TOp * TOp = SOp := by
  apply Subtype.ext
  change ((TOp : HilbertOperator (Qubits 1)) * (TOp : HilbertOperator (Qubits 1))) =
    (SOp : HilbertOperator (Qubits 1))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TOp, SOp, Matrix.mul_apply, exp_pi_div_four_mul_I_mul_self]

lemma SOp_pow_four : SOp ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, SOp_mul_SOp, ZOp_mul_ZOp]

lemma TOp_pow_eight : TOp ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, sq, TOp_mul_TOp, SOp_pow_four]

/-- `S† = S³`, so the adjoint has an exact word over `{S}`. -/
lemma star_SOp : star SOp = SOp ^ 3 := by
  rw [Unitary.star_eq_inv]
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact SOp_pow_four

/-- `T† = T⁷`. -/
lemma star_TOp : star TOp = TOp ^ 7 := by
  rw [Unitary.star_eq_inv]
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact TOp_pow_eight

/-- `T† = T · S³`, so the adjoint has an exact word over `{S, T}` with one `T`. -/
lemma star_TOp_eq_TOp_mul_SOp_pow_three : star TOp = TOp * SOp ^ 3 := by
  rw [star_TOp, show (7 : ℕ) = 1 + 2 * 3 from rfl, pow_add, pow_one TOp, pow_mul, sq,
    TOp_mul_TOp]

end

end QuantumAlg.Gate

end
