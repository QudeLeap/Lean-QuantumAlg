/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Mathematics
public import QuantumAlg.Components.Oracle.Xor.Operator
import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Primitives.WalshHadamard.Uniform
import all QuantumAlg.Components.Oracle.Xor.Operator
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact Walsh phase-query states

The original input, XOR kickback and final tensor factorization retain their
normalized state semantics [dW19, qcnotes.tex:1005-1006,1149-1173]. Executable
native instructions and oracle access are supplied by the implementation layer.
-/

namespace QuantumAlg.WalshHadamard

open NormalizedVector Gate

noncomputable section

variable {n : Nat}

/-- The mathematical XOR operator fixed by the supplied Boolean function. -/
abbrev oracleOperator (function : Oracle n) : UnitaryOperator (Qubits (n + 1)) :=
  xorOracleOp function

/-- The metadata-free Hadamard operator sends `|0^n⟩` to the uniform
superposition. -/
@[simp]
public lemma hadamardLayerOperator_apply_zero :
    (hadamardLayerOperator n).apply
        (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))) =
      uniformState n := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (hadamardLayerOperator n : HilbertOperator (Qubits n))
      (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
        HilbertVector (Qubits n)) i = _
  rw [HilbertOperator.applyVec_ket]
  rw [hadamardLayerOperator_apply]
  simp [walshSign, dotParity, bit]


/-- Normalized algorithm input `|0^n⟩ ⊗ |1⟩`. The target Hadamard that
prepares `|−⟩` is part of the circuit rather than hidden in the input. -/
def input (n : ℕ) : NormalizedVector (Qubits (n + 1)) :=
  (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))).tensor ket1

/-- Metadata-free first Hadamard layer. -/
def initialHadamardOperator (n : ℕ) : UnitaryOperator (Qubits (n + 1)) :=
  (hadamardLayerOperator n).tensor HOp


/-- Metadata-free final Hadamard layer. -/
def finalHadamardOperator (n : ℕ) : UnitaryOperator (Qubits (n + 1)) :=
  (hadamardLayerOperator n).tensor (1 : UnitaryOperator (Qubits 1))


/-- The joint state queried by the XOR oracle, obtained by applying the first
Hadamard layer to `|0^n⟩ ⊗ |1⟩`. -/
def initialState (n : ℕ) : NormalizedVector (Qubits (n + 1)) :=
  (initialHadamardOperator n).apply (input n)

/-- The queried state is the uniform input register tensored with `|−⟩`. -/
lemma initialState_eq_uniform_tensor :
    initialState n = (uniformState n).tensor ketMinus := by
  have hH : HOp.apply ket1 = ketMinus := by
    apply NormalizedVector.ext
    intro index
    change HilbertOperator.applyVec (HOp : HilbertOperator (Qubits 1))
      (NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) : HilbertVector (Qubits 1)) index =
        ketMinus index
    rw [HilbertOperator.applyVec_ket]
    fin_cases index <;> simp [HOp, ketMinus_apply]
  rw [initialState, input, initialHadamardOperator,
    UnitaryOperator.tensor_apply_tensor, hadamardLayerOperator_apply_zero, hH]

/-- The post-query normalized joint state under the metadata-free XOR oracle. -/
def postOracleState (f : Oracle n) : NormalizedVector (Qubits (n + 1)) :=
  (oracleOperator f).apply (initialState n)

/-- Normalized input-register vector after the phase query. -/
def afterPhaseQuery (f : Oracle n) : NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun x => invSqrtCard n * phaseSign f x)
    (by
      rw [EuclideanSpace.norm_eq]
      have hsum :
          ∑ x : Fin (2 ^ n), ‖invSqrtCard n * phaseSign f x‖ ^ 2 = 1 := by
        calc
          ∑ x : Fin (2 ^ n), ‖invSqrtCard n * phaseSign f x‖ ^ 2
              = ∑ _x : Fin (2 ^ n), ‖invSqrtCard n‖ ^ 2 := by
                  refine Finset.sum_congr rfl fun x _ => ?_
                  rw [norm_mul, norm_phaseSign, mul_one]
          _ = 1 := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul, norm_sq_invSqrtCard]
                  norm_num
      rw [hsum, Real.sqrt_one])

@[simp]
lemma afterPhaseQuery_apply (f : Oracle n) (x : Fin (2 ^ n)) :
    afterPhaseQuery f x = invSqrtCard n * phaseSign f x := rfl

/-- The actual XOR-oracle query on the uniform input register and `|−⟩`
target is exactly the phase-query state tensored with the unchanged target. -/
lemma postOracleState_eq_afterPhaseQuery_tensor (f : Oracle n) :
    postOracleState f = (afterPhaseQuery f).tensor ketMinus := by
  apply NormalizedVector.ext
  intro i
  change (oracleOperator f).applyVec (initialState n : HilbertVector (Qubits (n + 1))) i =
    (((afterPhaseQuery f).tensor ketMinus : NormalizedVector (Qubits (n + 1))) :
      HilbertVector (Qubits (n + 1))) i
  rw [initialState_eq_uniform_tensor]
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨x, b⟩, rfl⟩
  rw [xorOracleOp_apply, NormalizedVector.tensor_apply_prod,
    NormalizedVector.tensor_apply_prod]
  simp only [Equiv.symm_apply_apply, xorPerm_apply]
  by_cases h : f x
  · fin_cases b <;> simp [h, phaseSign, ketMinus_apply]
  · simp [h, phaseSign, ketMinus_apply]

/-- The normalized final input-register state after the second Hadamard layer. -/
def finalState (f : Oracle n) : NormalizedVector (Qubits n) :=
  (hadamardLayerOperator n).apply (afterPhaseQuery f)

/-- The actual final joint state: apply the second Hadamard layer to the
input register and leave the target qubit alone. -/
def finalJointState (f : Oracle n) : NormalizedVector (Qubits (n + 1)) :=
  (finalHadamardOperator n).apply (postOracleState f)

/-- The actual final joint state factors as the final input-register state
and the unchanged `|−⟩` target. -/
lemma finalJointState_eq_finalState_tensor (f : Oracle n) :
    finalJointState f = (finalState f).tensor ketMinus := by
  have hOne : (1 : UnitaryOperator (Qubits 1)).apply ketMinus = ketMinus := by
    apply NormalizedVector.ext
    intro i
    change (1 : UnitaryOperator (Qubits 1)).applyVec
        (ketMinus : HilbertVector (Qubits 1)) i = ketMinus i
    rw [UnitaryOperator.one_applyVec]
  rw [finalJointState, postOracleState_eq_afterPhaseQuery_tensor,
    finalHadamardOperator, UnitaryOperator.tensor_apply_tensor, finalState, hOne]


end

end QuantumAlg.WalshHadamard
