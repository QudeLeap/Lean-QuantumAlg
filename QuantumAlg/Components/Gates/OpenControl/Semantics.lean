/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.OpenControl.Construction
public import QuantumAlg.Components.Control
public import QuantumAlg.Components.Gates.Swap.Register
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Gates.OpenControl.Construction
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Gates.Hadamard.Action
import all QuantumAlg.Components.Gates.Pauli
import all QuantumAlg.Components.Gates.Swap.Register
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.SingleQubit.Last.Binary
import all QuantumAlg.Components.GateModel.Algorithm.Permutation
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact semantics of the native open-control words

The matrix statements below concern the complete generated words.  They show
that the descriptive macros implement a leading control active on zero on
arbitrary two-qubit inputs, including entangled inputs and relative phase.
-/

namespace QuantumAlg.Gate.OpenControl

noncomputable section

open NormalizedVector

/-- Exchange the two physical qubit coordinates. -/
public abbrev swapQubitIndex : Equiv.Perm (Fin (2 ^ 2)) :=
  swapRegistersPerm 1

/-- A zero-controlled one-qubit operator whose target is physically first and
whose control is physically second. -/
public def rightControlledQubitsOnZero (operator : UnitaryOperator (Qubits 1)) :
    UnitaryOperator (Qubits 2) :=
  UnitaryOperator.reindex swapQubitIndex
    (UnitaryOperator.controlledQubitsOnZero operator)

/-- Swapping two one-qubit basis coordinates exchanges arbitrary raw tensor
factors. -/
public theorem reindex_swapQubitIndex_tensor
    (left right : HilbertVector (Qubits 1)) :
    HilbertVector.reindex swapQubitIndex (HilbertVector.tensor left right) =
      HilbertVector.tensor right left := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := 1) (n := 1)).surjective index with
    ⟨⟨leftIndex, rightIndex⟩, rfl⟩
  simp [HilbertVector.tensor_apply, swapQubitIndex, swapRegistersPerm]
  ring

/-- A trailing zero control activates the operator on the leading target. -/
public theorem rightControlledQubitsOnZero_applyVec_tensor_ket0
    (operator : UnitaryOperator (Qubits 1))
    (target : HilbertVector (Qubits 1)) :
    (rightControlledQubitsOnZero operator).applyVec
        (HilbertVector.tensor target (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (operator.applyVec target)
        (ket0 : HilbertVector (Qubits 1)) := by
  rw [← reindex_swapQubitIndex_tensor
    (ket0 : HilbertVector (Qubits 1)) target]
  unfold rightControlledQubitsOnZero
  rw [UnitaryOperator.reindex_applyVec,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor,
    reindex_swapQubitIndex_tensor]

/-- A trailing one control leaves the leading target unchanged. -/
public theorem rightControlledQubitsOnZero_applyVec_tensor_ket1
    (operator : UnitaryOperator (Qubits 1))
    (target : HilbertVector (Qubits 1)) :
    (rightControlledQubitsOnZero operator).applyVec
        (HilbertVector.tensor target (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor target (ket1 : HilbertVector (Qubits 1)) := by
  rw [← reindex_swapQubitIndex_tensor
    (ket1 : HilbertVector (Qubits 1)) target]
  unfold rightControlledQubitsOnZero
  rw [UnitaryOperator.reindex_applyVec,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor,
    reindex_swapQubitIndex_tensor]

/-- The canonical native CNOT has its standard binary-coordinate operator. -/
private theorem cnot_binaryMatrix (oracles : OracleModel) :
    (cnot oracles).binaryMatrix = Gate.CNOTOp := by
  unfold UnitaryCircuit.binaryMatrix cnot
  rw [UnitaryCircuit.native_matrix,
    GateModel.Application.gateApplication_canonical_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm Gate.CNOTOp) =
      Gate.CNOTOp
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv 2).symm _

/-- Placing a complete two-qubit word in reversed physical order is exactly
the corresponding exchange of its binary basis coordinates. -/
private theorem swappedPlacement_binaryMatrix (oracles : OracleModel)
    (body : UnitaryCircuit AlgorithmGate.model oracles layout) :
    (UnitaryCircuit.placeAt layout layout swappedPosition
      swappedDimensions body).binaryMatrix =
        UnitaryOperator.reindex swapQubitIndex body.binaryMatrix := by
  apply Subtype.ext
  ext row column
  unfold UnitaryCircuit.binaryMatrix
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rw [UnitaryCircuit.placeAt_matrix,
    UnitaryCircuit.operatorAt_entry_of_surjective layout layout swappedPosition
      swappedDimensions (by
        intro index
        fin_cases index
        · exact ⟨1, rfl⟩
        · exact ⟨0, rfl⟩)]
  change body.matrix
      (UnitaryCircuit.basisAt layout layout swappedPosition
        swappedDimensions
        ((QuantumSignature.qubitsIndexEquiv 2).symm row))
      (UnitaryCircuit.basisAt layout layout swappedPosition
        swappedDimensions
        ((QuantumSignature.qubitsIndexEquiv 2).symm column)) =
    body.matrix
      ((QuantumSignature.qubitsIndexEquiv 2).symm (swapQubitIndex.symm row))
      ((QuantumSignature.qubitsIndexEquiv 2).symm (swapQubitIndex.symm column))
  have rowBasis :
      UnitaryCircuit.basisAt layout layout swappedPosition swappedDimensions
          ((QuantumSignature.qubitsIndexEquiv 2).symm row) =
        (QuantumSignature.qubitsIndexEquiv 2).symm (swapQubitIndex.symm row) := by
    funext index
    fin_cases row <;> fin_cases index <;> rfl
  have columnBasis :
      UnitaryCircuit.basisAt layout layout swappedPosition swappedDimensions
          ((QuantumSignature.qubitsIndexEquiv 2).symm column) =
        (QuantumSignature.qubitsIndexEquiv 2).symm (swapQubitIndex.symm column) := by
    funext index
    fin_cases column <;> fin_cases index <;> rfl
  rw [rowBasis, columnBasis]

/-- A parallel local pair is exactly the tensor of its two supplied operators. -/
private theorem prefixBasis (basis : layout.Basis) :
    (QuantumLayout.appendBasisEquiv (Gate.HadamardLayer.layout 1)
      (Gate.HadamardLayer.lastLayout 1)
      (Gate.HadamardLayer.hadamardLayer_layout_disjoint 1)
      ((Gate.HadamardLayer.hadamardLayer_layout_append 1).symm ▸ basis)).1 =
        (fun index : Fin 1 => basis index.castSucc) := by
  funext index
  apply Fin.ext
  exact UnitaryCircuit.castLayout_basis_value
    (Gate.HadamardLayer.hadamardLayer_layout_append 1).symm basis
    (Fin.castAdd 1 index)

private theorem suffixBasis (basis : layout.Basis) :
    (QuantumLayout.appendBasisEquiv (Gate.HadamardLayer.layout 1)
      (Gate.HadamardLayer.lastLayout 1)
      (Gate.HadamardLayer.hadamardLayer_layout_disjoint 1)
      ((Gate.HadamardLayer.hadamardLayer_layout_append 1).symm ▸ basis)).2 =
        (fun _ : Fin 1 => basis 1) := by
  funext index
  fin_cases index
  apply Fin.ext
  exact UnitaryCircuit.castLayout_basis_value
    (Gate.HadamardLayer.hadamardLayer_layout_append 1).symm basis
    (Fin.natAdd 1 0)

private theorem firstGate_entry (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1))
    (qubit : ((Gate.HadamardLayer.layout 1).wire 0).dimension = 2)
    (row column : (Gate.HadamardLayer.layout 1).Basis) :
    (Gate.singleQubitAt (Gate.HadamardLayer.layout 1) oracles operator 0 qubit).matrix
        row column = operator (row 0) (column 0) := by
  let application := Gate.singleQubitApplication
    (Gate.HadamardLayer.layout 1) operator 0 qubit
  have complement : (application.basisEquiv row).2 = (application.basisEquiv column).2 := by
    funext index
    have same : application.embedding.position (0 : Fin 1) = index.val :=
      Subsingleton.elim _ _
    exact False.elim ((Finset.mem_compl.mp index.property)
      (same ▸ Finset.mem_map_of_mem application.embedding.position
        (Finset.mem_univ (0 : Fin 1))))
  rw [Gate.singleQubitAt_matrix_entry, if_pos complement, mul_one]
  congr 1

private theorem lastGate_entry (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1))
    (qubit : ((Gate.HadamardLayer.lastLayout 1).wire 0).dimension = 2)
    (row column : (Gate.HadamardLayer.lastLayout 1).Basis) :
    (Gate.singleQubitAt (Gate.HadamardLayer.lastLayout 1) oracles operator 0
      qubit).matrix row column =
        operator (row 0) (column 0) := by
  let application := Gate.singleQubitApplication
    (Gate.HadamardLayer.lastLayout 1) operator 0
      qubit
  have complement : (application.basisEquiv row).2 = (application.basisEquiv column).2 := by
    funext index
    have same : application.embedding.position (0 : Fin 1) = index.val :=
      Subsingleton.elim _ _
    exact False.elim ((Finset.mem_compl.mp index.property)
      (same ▸ Finset.mem_map_of_mem application.embedding.position
        (Finset.mem_univ (0 : Fin 1))))
  rw [Gate.singleQubitAt_matrix_entry, if_pos complement, mul_one]
  congr 1

private theorem parallelPair_matrix_entry (oracles : OracleModel)
    (controlOp targetOp : UnitaryOperator (Qubits 1)) (row column : layout.Basis) :
    (parallelPair oracles controlOp targetOp).matrix row column =
      controlOp (row 0) (column 0) * targetOp (row 1) (column 1) := by
  rw [parallelPair, UnitaryCircuit.castLayout_matrix_entry,
    UnitaryCircuit.tensor_native_matrix_entry, prefixBasis, prefixBasis,
    suffixBasis, suffixBasis, firstGate_entry]
  let targetRow : (Gate.HadamardLayer.lastLayout 1).Basis := fun _ => row 1
  let targetColumn : (Gate.HadamardLayer.lastLayout 1).Basis := fun _ => column 1
  have targetEntry := lastGate_entry oracles targetOp
    (Gate.HadamardLayer.hadamardLayer_last_dimension 1) targetRow targetColumn
  change controlOp (row (Fin.castSucc 0)) (column (Fin.castSucc 0)) *
      (Gate.singleQubitAt (Gate.HadamardLayer.lastLayout 1) oracles targetOp 0 _).matrix
        targetRow targetColumn = _
  rw [targetEntry]
  rfl

private theorem parallelPair_binaryMatrix (oracles : OracleModel)
    (controlOp targetOp : UnitaryOperator (Qubits 1)) :
    (parallelPair oracles controlOp targetOp).binaryMatrix =
      controlOp.tensor targetOp := by
  ext row column
  rw [UnitaryOperator.tensor_apply]
  change (parallelPair oracles controlOp targetOp).matrix
      ((QuantumSignature.qubitsIndexEquiv 2).symm row)
      ((QuantumSignature.qubitsIndexEquiv 2).symm column) = _
  rw [parallelPair_matrix_entry]
  fin_cases row <;> fin_cases column <;> rfl

/-- A local target gate is identity tensor its supplied operator. -/
private theorem targetGate_binaryMatrix (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    (targetGate oracles operator).binaryMatrix =
      (1 : UnitaryOperator (Qubits 1)).tensor operator := by
  exact Gate.singleQubitAt_last_binaryMatrix oracles 1 operator

/-- A local control gate is its supplied operator tensor identity. -/
private theorem controlGate_binaryMatrix (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    (controlGate oracles operator).binaryMatrix =
      operator.tensor (1 : UnitaryOperator (Qubits 1)) := by
  exact Gate.singleQubitAt_first_binaryMatrix oracles 1 operator

/-- Exact binary matrix of the literal open-controlled rotation word. -/
private theorem rotY_binary_word (oracles : OracleModel) (angle : Real) :
    (rotY oracles angle).binaryMatrix =
      (Gate.XOp.tensor (1 : UnitaryOperator (Qubits 1))) * Gate.CNOTOp *
        ((1 : UnitaryOperator (Qubits 1)).tensor (rotYOp (-(angle / 2)))) *
        Gate.CNOTOp * (Gate.XOp.tensor (rotYOp (angle / 2))) := by
  simp only [rotY,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_macroCall,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, cnot_binaryMatrix,
    parallelPair_binaryMatrix, targetGate_binaryMatrix, controlGate_binaryMatrix]
  noncomm_ring

/-- Exact binary matrix of the literal open-controlled Hadamard word. -/
private theorem hadamard_binary_word (oracles : OracleModel) :
    (hadamard oracles).binaryMatrix =
      (Gate.XOp.tensor (rotYOp (-(Real.pi / 4)))) * Gate.CNOTOp *
        (Gate.XOp.tensor (rotYOp (Real.pi / 4))) := by
  simp only [hadamard,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_macroCall,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, cnot_binaryMatrix,
    parallelPair_binaryMatrix]
  noncomm_ring

private abbrev basisKetVec {width : Nat} (index : Fin (2 ^ width)) :
    HilbertVector (Qubits width) :=
  (NormalizedVector.ket (R := Qubits width) index).vec

@[simp] private theorem basisKetVec_zero :
    basisKetVec (width := 1) (0 : Fin 2) =
      (ket0 : HilbertVector (Qubits 1)) := rfl

@[simp] private theorem basisKetVec_one :
    basisKetVec (width := 1) (1 : Fin 2) =
      (ket1 : HilbertVector (Qubits 1)) := rfl

private theorem raw_tensor_ket {m n : Nat}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) :
    HilbertVector.tensor (basisKetVec left) (basisKetVec right) =
      basisKetVec (prodEquiv (m := m) (n := n) (left, right)) := by
  simpa [basisKetVec] using congrArg
    (fun state : NormalizedVector (Qubits (m + n)) =>
      (state : HilbertVector (Qubits (m + n))))
    (NormalizedVector.tensor_ket left right)

private theorem unitary_eq_of_applyVec_ket {R : Register}
    (left right : UnitaryOperator R)
    (same : ∀ input : R.Index,
      left.applyVec (NormalizedVector.ket input : HilbertVector R) =
        right.applyVec (NormalizedVector.ket input : HilbertVector R)) :
    left = right := by
  apply Subtype.ext
  ext output input
  have point := congrArg (fun state : HilbertVector R => state output) (same input)
  change HilbertOperator.applyVec (left : HilbertOperator R)
      (NormalizedVector.ket input : HilbertVector R) output =
    HilbertOperator.applyVec (right : HilbertOperator R)
      (NormalizedVector.ket input : HilbertVector R) output at point
  simpa only [HilbertOperator.applyVec_ket] using point

@[simp] private theorem XOp_applyVec_ket0 :
    Gate.XOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ket1 : HilbertVector (Qubits 1)) := by
  have same := congrArg
    (fun state : NormalizedVector (Qubits 1) => (state : HilbertVector (Qubits 1)))
    Gate.pauliXOperator_apply_ket0
  simpa only [UnitaryOperator.apply_coe] using same

@[simp] private theorem XOp_applyVec_ket1 :
    Gate.XOp.applyVec (ket1 : HilbertVector (Qubits 1)) =
      (ket0 : HilbertVector (Qubits 1)) := by
  have same := congrArg
    (fun state : NormalizedVector (Qubits 1) => (state : HilbertVector (Qubits 1)))
    Gate.pauliXOperator_apply_ket1
  simpa only [UnitaryOperator.apply_coe] using same

/-- The named CNOT is the standard leading-control Pauli-X operator. -/
private theorem CNOTOp_eq_controlled :
    Gate.CNOTOp = UnitaryOperator.controlledQubits Gate.XOp := by
  apply Subtype.ext
  ext row column
  rcases (prodEquiv (m := 1) (n := 1)).surjective row with
    ⟨⟨rowControl, rowTarget⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := 1)).surjective column with
    ⟨⟨columnControl, columnTarget⟩, rfl⟩
  unfold Gate.CNOTOp UnitaryOperator.controlledQubits
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  change (UnitaryOperator.ofPerm (R := Qubits 2)
      (Equiv.swap (2 : Fin 4) (3 : Fin 4)))
        (prodEquiv (m := 1) (n := 1) (rowControl, rowTarget))
        (prodEquiv (m := 1) (n := 1) (columnControl, columnTarget)) =
    UnitaryOperator.controlled (Qubits 1) (1 : Fin 2) Gate.XOp
      (rowControl, rowTarget) (columnControl, columnTarget)
  fin_cases rowControl <;> fin_cases rowTarget <;>
    fin_cases columnControl <;> fin_cases columnTarget <;>
    simp +decide [UnitaryOperator.ofPerm_entry,
      UnitaryOperator.controlled_apply, Gate.XOp, prodEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat]

private theorem rotYOp_mul (left right : Real) :
    (rotYOp left : HilbertOperator (Qubits 1)) *
        (rotYOp right : HilbertOperator (Qubits 1)) =
      (rotYOp (left + right) : HilbertOperator (Qubits 1)) := by
  have half : (left + right) / 2 = left / 2 + right / 2 := by ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [rotYOp, Matrix.mul_apply, Fin.sum_univ_two, half,
      Real.sin_add, Real.cos_add] <;> ring

private theorem rotYOp_zero :
    (rotYOp 0 : HilbertOperator (Qubits 1)) = 1 := by
  ext output input
  fin_cases output <;> fin_cases input <;> simp [rotYOp]

private theorem rotYOp_neg_mul_rotYOp (angle : Real) :
    (rotYOp (-angle) : HilbertOperator (Qubits 1)) *
        (rotYOp angle : HilbertOperator (Qubits 1)) = 1 := by
  rw [rotYOp_mul, neg_add_cancel, rotYOp_zero]

private theorem XOp_mul_rotYOp_neg_mul_XOp (angle : Real) :
    ((Gate.XOp : HilbertOperator (Qubits 1)) *
        (rotYOp (-angle) : HilbertOperator (Qubits 1))) *
        (Gate.XOp : HilbertOperator (Qubits 1)) =
      (rotYOp angle : HilbertOperator (Qubits 1)) := by
  have half : (-angle) / 2 = -(angle / 2) := by ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, rotYOp, Matrix.mul_apply,
      Fin.sum_univ_two, Equiv.swap_apply_def, half,
      Real.sin_neg, Real.cos_neg]

private theorem controlledRotY_target_operator (angle : Real) :
    (((Gate.XOp : HilbertOperator (Qubits 1)) *
          (rotYOp (-(angle / 2)) : HilbertOperator (Qubits 1))) *
        (Gate.XOp : HilbertOperator (Qubits 1))) *
        (rotYOp (angle / 2) : HilbertOperator (Qubits 1)) =
      (rotYOp angle : HilbertOperator (Qubits 1)) := by
  rw [XOp_mul_rotYOp_neg_mul_XOp, rotYOp_mul]
  congr 2
  ring

private theorem rotY_cancel_applyVec (angle : Real)
    (state : HilbertVector (Qubits 1)) :
    (rotYOp (-angle)).applyVec ((rotYOp angle).applyVec state) = state := by
  change HilbertOperator.applyVec (rotYOp (-angle) : HilbertOperator (Qubits 1))
      (HilbertOperator.applyVec
        (rotYOp angle : HilbertOperator (Qubits 1)) state) = state
  rw [← HilbertOperator.mul_applyVec, rotYOp_neg_mul_rotYOp,
    HilbertOperator.one_applyVec]

private theorem controlledRotY_target_applyVec (angle : Real)
    (state : HilbertVector (Qubits 1)) :
    Gate.XOp.applyVec
        ((rotYOp (-(angle / 2))).applyVec
          (Gate.XOp.applyVec ((rotYOp (angle / 2)).applyVec state))) =
      (rotYOp angle).applyVec state := by
  change HilbertOperator.applyVec (Gate.XOp : HilbertOperator (Qubits 1))
      (HilbertOperator.applyVec
        (rotYOp (-(angle / 2)) : HilbertOperator (Qubits 1))
        (HilbertOperator.applyVec (Gate.XOp : HilbertOperator (Qubits 1))
          (HilbertOperator.applyVec
            (rotYOp (angle / 2) : HilbertOperator (Qubits 1)) state))) = _
  rw [← HilbertOperator.mul_applyVec, ← HilbertOperator.mul_applyVec,
    ← HilbertOperator.mul_applyVec, controlledRotY_target_operator]
  rfl

/-- The generated word is exactly the complete open-controlled rotation operator. -/
public theorem rotY_binaryMatrix (oracles : OracleModel) (angle : Real) :
    (rotY oracles angle).binaryMatrix =
      UnitaryOperator.controlledQubitsOnZero (rotYOp angle) := by
  rw [rotY_binary_word]
  apply unitary_eq_of_applyVec_ket
  intro input
  rcases (prodEquiv (m := 1) (n := 1)).surjective input with
    ⟨⟨control, target⟩, rfl⟩
  change ((Gate.XOp.tensor (1 : UnitaryOperator (Qubits 1))) * Gate.CNOTOp *
      ((1 : UnitaryOperator (Qubits 1)).tensor (rotYOp (-(angle / 2)))) *
      Gate.CNOTOp * (Gate.XOp.tensor (rotYOp (angle / 2)))).applyVec
        (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target))) =
    (UnitaryOperator.controlledQubitsOnZero (rotYOp angle)).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target)))
  rw [← raw_tensor_ket control target]
  rcases show control = 0 ∨ control = 1 by fin_cases control <;> simp with
    controlZero | controlOne
  · subst control
    simp only [UnitaryOperator.mul_applyVec, UnitaryOperator.tensor_applyVec_tensor,
      basisKetVec_zero, UnitaryOperator.one_applyVec,
      XOp_applyVec_ket0, XOp_applyVec_ket1,
      CNOTOp_eq_controlled,
      UnitaryOperator.controlledQubits_applyVec_ket1_tensor,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor,
      controlledRotY_target_applyVec]
  · subst control
    simp only [UnitaryOperator.mul_applyVec, UnitaryOperator.tensor_applyVec_tensor,
      basisKetVec_one, UnitaryOperator.one_applyVec,
      XOp_applyVec_ket0, XOp_applyVec_ket1,
      CNOTOp_eq_controlled,
      UnitaryOperator.controlledQubits_applyVec_ket0_tensor,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor,
      rotY_cancel_applyVec]

/-- The reoriented native word is the complete trailing-zero-control
rotation operator, including exact phase on arbitrary inputs. -/
public theorem rotYRight_binaryMatrix (oracles : OracleModel) (angle : Real) :
    (rotYRight oracles angle).binaryMatrix =
      rightControlledQubitsOnZero (rotYOp angle) := by
  rw [rotYRight, swappedPlacement_binaryMatrix, rotY_binaryMatrix]
  rfl

/-- On target one with a trailing zero control, the literal reoriented
rotation word produces its exact signed two-branch decomposition. -/
public theorem rotYRight_applyVec_ket1_tensor_ket0
    (oracles : OracleModel) (angle : Real) :
    (rotYRight oracles angle).binaryMatrix.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      (-(Real.sin (angle / 2)) : ℂ) •
          HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (ket0 : HilbertVector (Qubits 1)) +
        (Real.cos (angle / 2) : ℂ) •
          HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
            (ket0 : HilbertVector (Qubits 1)) := by
  rw [rotYRight_binaryMatrix,
    rightControlledQubitsOnZero_applyVec_tensor_ket0,
    rotYOp_applyVec_ket1, HilbertVector.add_tensor,
    HilbertVector.smul_tensor, HilbertVector.smul_tensor]

private theorem rotYOp_neg_mul_XOp (angle : Real) :
    (rotYOp (-angle) : HilbertOperator (Qubits 1)) *
        (Gate.XOp : HilbertOperator (Qubits 1)) =
      (Gate.XOp : HilbertOperator (Qubits 1)) *
        (rotYOp angle : HilbertOperator (Qubits 1)) := by
  have half : (-angle) / 2 = -(angle / 2) := by ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, rotYOp, Matrix.mul_apply,
      Fin.sum_univ_two, Equiv.swap_apply_def, half,
      Real.sin_neg, Real.cos_neg]

private theorem XOp_mul_rotYOp_pi_div_two :
    (Gate.XOp : HilbertOperator (Qubits 1)) *
        (rotYOp (Real.pi / 2) : HilbertOperator (Qubits 1)) =
      (Gate.HOp : HilbertOperator (Qubits 1)) := by
  have sqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr (by norm_num))
  have sqrt_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have inverse : NormalizedVector.invSqrt2 = (Real.sqrt 2 : ℂ) / 2 := by
    rw [NormalizedVector.invSqrt2]
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    calc
      (Real.sqrt 2 : ℂ)⁻¹ * 2 =
          (Real.sqrt 2 : ℂ)⁻¹ *
            ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) := by rw [sqrt_sq]
      _ = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) *
          (Real.sqrt 2 : ℂ) := by ring
      _ = (Real.sqrt 2 : ℂ) := by rw [inv_mul_cancel₀ sqrt_ne, one_mul]
  have half : (Real.pi / 2) / 2 = Real.pi / 4 := by ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, Gate.HOp, rotYOp,
      Matrix.mul_apply, inverse, half]

private theorem controlledH_target_operator :
    ((rotYOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1)) *
        (Gate.XOp : HilbertOperator (Qubits 1))) *
        (rotYOp (Real.pi / 4) : HilbertOperator (Qubits 1)) =
      (Gate.HOp : HilbertOperator (Qubits 1)) := by
  rw [rotYOp_neg_mul_XOp, Matrix.mul_assoc, rotYOp_mul]
  rw [show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring,
    XOp_mul_rotYOp_pi_div_two]

private theorem controlledH_target_applyVec (state : HilbertVector (Qubits 1)) :
    (rotYOp (-(Real.pi / 4))).applyVec
        (Gate.XOp.applyVec ((rotYOp (Real.pi / 4)).applyVec state)) =
      Gate.HOp.applyVec state := by
  change HilbertOperator.applyVec
      (rotYOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1))
      (HilbertOperator.applyVec (Gate.XOp : HilbertOperator (Qubits 1))
        (HilbertOperator.applyVec
          (rotYOp (Real.pi / 4) : HilbertOperator (Qubits 1)) state)) = _
  rw [← HilbertOperator.mul_applyVec, ← HilbertOperator.mul_applyVec,
    controlledH_target_operator]
  rfl

/-- The generated word is exactly the complete open-controlled Hadamard operator. -/
public theorem hadamard_binaryMatrix (oracles : OracleModel) :
    (hadamard oracles).binaryMatrix =
      UnitaryOperator.controlledQubitsOnZero Gate.HOp := by
  rw [hadamard_binary_word]
  apply unitary_eq_of_applyVec_ket
  intro input
  rcases (prodEquiv (m := 1) (n := 1)).surjective input with
    ⟨⟨control, target⟩, rfl⟩
  change ((Gate.XOp.tensor (rotYOp (-(Real.pi / 4)))) * Gate.CNOTOp *
      (Gate.XOp.tensor (rotYOp (Real.pi / 4)))).applyVec
        (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target))) =
    (UnitaryOperator.controlledQubitsOnZero Gate.HOp).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target)))
  rw [← raw_tensor_ket control target]
  rcases show control = 0 ∨ control = 1 by fin_cases control <;> simp with
    controlZero | controlOne
  · subst control
    simp only [UnitaryOperator.mul_applyVec, UnitaryOperator.tensor_applyVec_tensor,
      basisKetVec_zero, XOp_applyVec_ket0, XOp_applyVec_ket1,
      CNOTOp_eq_controlled,
      UnitaryOperator.controlledQubits_applyVec_ket1_tensor,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor,
      controlledH_target_applyVec]
  · subst control
    simp only [UnitaryOperator.mul_applyVec, UnitaryOperator.tensor_applyVec_tensor,
      basisKetVec_one, XOp_applyVec_ket0, XOp_applyVec_ket1,
      CNOTOp_eq_controlled,
      UnitaryOperator.controlledQubits_applyVec_ket0_tensor,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor,
      rotY_cancel_applyVec]

/-- On an active zero control and zero target, the literal open-controlled
Hadamard word creates the physical `|+>` target. -/
public theorem hadamard_applyVec_ket0_tensor_ket0 (oracles : OracleModel) :
    (hadamard oracles).binaryMatrix.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ketPlus : HilbertVector (Qubits 1)) := by
  rw [hadamard_binaryMatrix,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor,
    Gate.hadamardOperator_applyVec_ket0]

end

end QuantumAlg.Gate.OpenControl
