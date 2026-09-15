/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Util.Complex

/-!
# Named gates

The standard named unitary operators and their sealed `UnitaryCircuit` realizations.
The `*Op` declarations are metadata-free `UnitaryOperator`s; each executable
object is one declared primitive circuit leaf.
-/

section

namespace QuantumAlg

open NormalizedVector

noncomputable section

namespace Gate

/-! ## Pauli, Hadamard, and CNOT -/

/-- One strict execution event for a declared atomic gate. -/
def atomicEvent (label : Resource.GateLabel) : Resource.Event .quantum :=
  .gate label

/-- One occurrence of a declared atomic gate event. -/
def atomicEventCost (label : Resource.GateLabel) : ResourcePool .quantum :=
  ResourcePool.singleton (atomicEvent label)

/-- One symbolic event-depth layer for a declared atomic gate. -/
def atomicEventDepth (label : Resource.GateLabel) :
    DepthExpr (Resource.Event .quantum) :=
  .atom (atomicEvent label)





/-! ## Finite-cyclic range preparation -/

/-- Fixed declaration coordinate for exact finite-cyclic range preparation. -/
def finiteCyclicRangePreparationGateLabel : Resource.GateLabel :=
  { family := "finite-cyclic-dlp"
    name := "finite-cyclic-dlp-range-preparation" }

/-- Strict event coordinate for exact finite-cyclic range preparation. -/
def finiteCyclicRangePreparationEvent : Resource.Event .quantum :=
  .gate finiteCyclicRangePreparationGateLabel



/-- The requested target gives an orthonormal family on the singleton zero
basis index. -/
theorem finiteCyclicRangePreparation_singleton_orthonormal
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    Orthonormal ℂ
      (({0} : Set (Fin (2 ^ n))).domRestrict
        (fun _ : Fin (2 ^ n) =>
          (target : HilbertVector (Qubits n)))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := by
    apply Subtype.ext
    simpa using i.property.trans j.property.symm
  subst j
  rw [if_pos rfl]
  exact inner_self_eq_one_of_norm_eq_one target.norm_eq_one

/-- Every normalized target extends from the zero index to an orthonormal
basis. -/
theorem exists_finiteCyclicRangePreparationBasis
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    ∃ b : OrthonormalBasis (Fin (2 ^ n)) ℂ
        (HilbertVector (Qubits n)),
      ∀ i ∈ ({0} : Set (Fin (2 ^ n))),
        b i = (target : HilbertVector (Qubits n)) :=
  Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (s := ({0} : Set (Fin (2 ^ n))))
    (v := fun _ : Fin (2 ^ n) =>
      (target : HilbertVector (Qubits n)))
    (by simp) (finiteCyclicRangePreparation_singleton_orthonormal target)

/-- An orthonormal basis whose zero column is the requested target state. -/
noncomputable def finiteCyclicRangePreparationBasis
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    OrthonormalBasis (Fin (2 ^ n)) ℂ (HilbertVector (Qubits n)) :=
  Classical.choose (exists_finiteCyclicRangePreparationBasis target)

/-- The selected basis has the requested target as its zero column. -/
theorem finiteCyclicRangePreparationBasis_zero
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    finiteCyclicRangePreparationBasis target 0 =
      (target : HilbertVector (Qubits n)) := by
  exact (Classical.choose_spec
    (exists_finiteCyclicRangePreparationBasis target)) 0 (by simp)

/-- Basis-change operator whose zero column is the requested target state. -/
def finiteCyclicRangePreparationOp {n : Nat}
    (target : NormalizedVector (Qubits n)) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofMatrix
    ((EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toBasis.toMatrix
      (finiteCyclicRangePreparationBasis target))
    ((EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toMatrix_orthonormalBasis_mem_unitary
        (finiteCyclicRangePreparationBasis target))

/-- The component basis change prepares its requested target from zero. -/
@[simp] theorem finiteCyclicRangePreparationOp_apply_zero {n : Nat}
    (target : NormalizedVector (Qubits n)) :
    (finiteCyclicRangePreparationOp target).apply
        (NormalizedVector.ket (R := Qubits n) 0) = target := by
  apply NormalizedVector.ext
  intro i
  change
    HilbertOperator.applyVec
        (finiteCyclicRangePreparationOp target : HilbertOperator (Qubits n))
        (NormalizedVector.ket (R := Qubits n) 0) i = _
  rw [HilbertOperator.applyVec_ket]
  change
    (EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toBasis.toMatrix
        (finiteCyclicRangePreparationBasis target) i 0 = _
  rw [Module.Basis.toMatrix_apply]
  change
    (EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toBasis.repr
        (finiteCyclicRangePreparationBasis target 0) i = _
  rw [finiteCyclicRangePreparationBasis_zero,
    EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr]

/-- Declare one exact finite-cyclic range-preparation family member at a
caller-supplied placement. -/
def finiteCyclicRangePreparationLeafAt {n : Nat}
    (target : NormalizedVector (Qubits n)) (systemIdx : List Nat) :
    UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.gate finiteCyclicRangePreparationGateLabel systemIdx
    (finiteCyclicRangePreparationOp target)

@[simp] theorem finiteCyclicRangePreparationLeafAt_event {n : Nat}
    (target : NormalizedVector (Qubits n)) (systemIdx : List Nat) :
    (finiteCyclicRangePreparationLeafAt target systemIdx).event =
      finiteCyclicRangePreparationEvent :=
  rfl

/-- Metadata-free Hadamard operator `H = (1/sqrt 2) [[1, 1], [1, -1]]`. -/
def HOp : UnitaryOperator (Qubits 1) :=
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

/-- Sealed Hadamard declaration at a caller-supplied physical placement. -/
def hadamardLeafAt (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate (.builtin "hadamard") systemIdx HOp

/-- Sealed Hadamard leaf on the canonical one-qubit placement. -/
def hadamardLeaf : UnitaryLeaf (Qubits 1) :=
  hadamardLeafAt [0]

/-- The Hadamard circuit at a caller-supplied duplicate-free placement. -/
def hadamardAt (systemIdx : List Nat) (systemIdxNodup : systemIdx.Nodup) :
    UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf (hadamardLeafAt systemIdx) systemIdxNodup

/-- The Hadamard circuit, derived from its sealed primitive declaration. -/
def H : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf hadamardLeaf (by simp [hadamardLeaf, hadamardLeafAt])

@[simp]
theorem H_matrix : H.matrix = HOp :=
  rfl

/-- Metadata-free Hadamard action on the leading qubit of a larger register. -/
def leadingHadamardOp (n : Nat) : UnitaryOperator (Qubits (1 + n)) :=
  HOp.tensor (1 : UnitaryOperator (Qubits n))

/-- Sealed leading-qubit Hadamard declaration at a caller-supplied placement. -/
def leadingHadamardLeafAt (n : Nat) (systemIdx : List Nat) :
    UnitaryLeaf (Qubits (1 + n)) :=
  UnitaryLeaf.gate (.builtin "hadamard") systemIdx (leadingHadamardOp n)

/-- A leading-qubit Hadamard circuit at a duplicate-free physical placement. -/
def leadingHadamardAt (n : Nat) (systemIdx : List Nat)
    (systemIdxNodup : systemIdx.Nodup) : UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.ofLeaf (leadingHadamardLeafAt n systemIdx) systemIdxNodup

/-- Metadata-free Pauli-X (NOT) operator. -/
def XOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofPerm (Equiv.swap 0 1)

/-- The canonical addressed-X operator specializes to the named one-qubit
Pauli-X operator. -/
theorem qubitPrimitive_x_operator :
    (QubitPrimitive.operator (.x 0 : QubitPrimitive 1)) = XOp := by
  unfold QubitPrimitive.operator XOp
  apply congrArg (UnitaryOperator.ofPerm (R := Qubits 1))
  ext label
  fin_cases label <;> decide

/-- The Pauli-X (NOT) circuit, as the basis permutation `|0> ↔ |1>`. -/
def X : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf (QubitPrimitive.leaf (.x 0))
    (QubitPrimitive.systemIdx_nodup (.x 0))

/-- Metadata-free Pauli-Y operator `[[0, -i], [i, 0]]`. -/
def YOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(0 : ℂ), -Complex.I; Complex.I, 0] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply])

/-- Sealed Pauli-Y declaration at a caller-supplied physical placement. -/
def pauliYLeafAt (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate
    (.declared "QuantumAlg.Components.Gate" "pauli-y") systemIdx YOp

/-- Sealed Pauli-Y leaf on the canonical one-qubit placement. -/
def pauliYLeaf : UnitaryLeaf (Qubits 1) :=
  pauliYLeafAt [0]

/-- The Pauli-Y circuit, derived from its sealed primitive declaration. -/
def Y : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf pauliYLeaf (by simp [pauliYLeaf, pauliYLeafAt])

@[simp]
theorem Y_matrix : Y.matrix = YOp :=
  rfl

/-- Metadata-free Pauli-Z operator `[[1, 0], [0, -1]]`. -/
def ZOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(1 : ℂ), 0; 0, -1] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply])

/-- Sealed Pauli-Z declaration at a caller-supplied physical placement. -/
def pauliZLeafAt (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate
    (.declared "QuantumAlg.Components.Gate" "pauli-z") systemIdx ZOp

/-- Sealed Pauli-Z leaf on the canonical one-qubit placement. -/
def pauliZLeaf : UnitaryLeaf (Qubits 1) :=
  pauliZLeafAt [0]

/-- The Pauli-Z circuit, derived from its sealed primitive declaration. -/
def Z : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf pauliZLeaf (by simp [pauliZLeaf, pauliZLeafAt])

@[simp]
theorem Z_matrix : Z.matrix = ZOp :=
  rfl

/-- Metadata-free controlled-NOT operator, control = qubit 0. -/
def CNOTOp : UnitaryOperator (Qubits 2) :=
  UnitaryOperator.ofPerm (Equiv.swap 2 3)

/-- The canonical addressed-CNOT operator specializes to the named two-qubit
controlled-NOT operator. -/
theorem qubitPrimitive_cnot_operator :
    (QubitPrimitive.operator (.cnot 0 1 (by decide) : QubitPrimitive 2)) = CNOTOp := by
  unfold QubitPrimitive.operator CNOTOp
  apply congrArg (UnitaryOperator.ofPerm (R := Qubits 2))
  ext label
  fin_cases label <;> decide

/-- The controlled-NOT circuit on two qubits, control = qubit 0. -/
def CNOT : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.ofLeaf (QubitPrimitive.leaf (.cnot 0 1 (by decide)))
    (QubitPrimitive.systemIdx_nodup (.cnot 0 1 (by decide)))

@[simp]
theorem X_matrix : X.matrix = XOp := by
  change QubitPrimitive.operator (.x 0 : QubitPrimitive 1) = XOp
  exact qubitPrimitive_x_operator

@[simp]
theorem CNOT_matrix : CNOT.matrix = CNOTOp := by
  change QubitPrimitive.operator (.cnot 0 1 (by decide) : QubitPrimitive 2) = CNOTOp
  exact qubitPrimitive_cnot_operator

@[simp]
theorem H_eventTrace : H.eventTrace = [atomicEvent (.builtin "hadamard")] :=
  rfl

@[simp]
theorem H_eventCost : H.eventCost = atomicEventCost (.builtin "hadamard") :=
  rfl

@[simp]
theorem H_eventDepth : H.eventDepth = atomicEventDepth (.builtin "hadamard") :=
  rfl

theorem H_event_count :
    ResourcePool.count (atomicEvent (.builtin "hadamard")) H.eventCost = 1 := by
  simp [H_eventCost, atomicEventCost]

theorem H_resourcesFromEventDepth : H.resourcesFromEventDepth = H.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost H

@[simp]
theorem H_unit_event_depth : H.evaluatedEventDepth (fun _ => 1) = 1 :=
  rfl

@[simp]
theorem CNOT_eventTrace : CNOT.eventTrace = [atomicEvent (.builtin "cnot")] :=
  rfl

@[simp]
theorem CNOT_eventCost : CNOT.eventCost = atomicEventCost (.builtin "cnot") :=
  rfl

@[simp]
theorem CNOT_eventDepth : CNOT.eventDepth = atomicEventDepth (.builtin "cnot") :=
  rfl

theorem CNOT_event_count :
    ResourcePool.count (atomicEvent (.builtin "cnot")) CNOT.eventCost = 1 := by
  simp [CNOT_eventCost, atomicEventCost]





@[simp]
theorem H_system_idx : H.physical_idx = [0] := rfl









/-- Metadata-free action `H |0> = |+>`. -/
@[simp]
theorem H_apply_ket0 :
    H.applyNormalized ket0 = ketPlus := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (HOp : HilbertOperator (Qubits 1))
    (ket0 : HilbertVector (Qubits 1)) i = ketPlus i
  rw [ket0, HilbertOperator.applyVec_ket, ketPlus_apply]
  fin_cases i <;> simp [HOp]

/-- Metadata-free action `H |1> = |->`. -/
@[simp]
theorem H_apply_ket1 :
    H.applyNormalized ket1 = ketMinus := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (HOp : HilbertOperator (Qubits 1))
    (ket1 : HilbertVector (Qubits 1)) i = ketMinus i
  rw [ket1, HilbertOperator.applyVec_ket, ketMinus_apply]
  fin_cases i <;> simp [HOp]

/-- `CNOT` permutes the basis by swapping `|10> ↔ |11>` (indices 2 ↔ 3). -/
theorem CNOT_apply_ket (x : Fin (2 ^ 2)) :
    CNOT.applyNormalized (NormalizedVector.ket x) =
      NormalizedVector.ket
        (Equiv.swap (2 : Fin (2 ^ 2)) (3 : Fin (2 ^ 2)) x) := by
  change CNOT.matrix.apply (NormalizedVector.ket x) = _
  rw [CNOT_matrix]
  change (UnitaryOperator.ofPerm (R := Qubits 2)
      (Equiv.swap (2 : Fin (2 ^ 2)) (3 : Fin (2 ^ 2)))).apply
      (NormalizedVector.ket (R := Qubits 2) x) = _
  rw [UnitaryOperator.ofPerm_apply_ket]
  rw [Equiv.swap_inv]

/-- Metadata-free action `X |0> = |1>`. -/
@[simp]
theorem X_apply_ket0 :
    X.applyNormalized ket0 = ket1 := by
  apply NormalizedVector.ext
  intro i
  change X.matrix.apply ket0 i = ket1 i
  rw [X_matrix]
  change HilbertOperator.applyVec
    ((Equiv.swap (0 : Fin (2 ^ 1)) 1).permMatrix ℂ)
    (ket0 : HilbertVector (Qubits 1)) i = ket1 i
  unfold HilbertOperator.applyVec
  rw [Matrix.permMatrix_mulVec]
  fin_cases i <;> simp [ket0, ket1, NormalizedVector.ket_apply]

/-- Metadata-free action `X |1> = |0>`. -/
@[simp]
theorem X_apply_ket1 :
    X.applyNormalized ket1 = ket0 := by
  apply NormalizedVector.ext
  intro i
  change X.matrix.apply ket1 i = ket0 i
  rw [X_matrix]
  change HilbertOperator.applyVec
    ((Equiv.swap (0 : Fin (2 ^ 1)) 1).permMatrix ℂ)
    (ket1 : HilbertVector (Qubits 1)) i = ket0 i
  unfold HilbertOperator.applyVec
  rw [Matrix.permMatrix_mulVec]
  fin_cases i <;> simp [ket0, ket1, NormalizedVector.ket_apply]

/-- Metadata-free action `Z |0> = |0>`. -/
@[simp]
theorem Z_apply_ket0 :
    Z.applyNormalized ket0 = ket0 := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (ZOp : HilbertOperator (Qubits 1))
    (ket0 : HilbertVector (Qubits 1)) i = ket0 i
  rw [ket0, HilbertOperator.applyVec_ket, ket_apply]
  fin_cases i <;> simp [ZOp]

/-- Raw vector view of the metadata-free action `Z |1> = -|1>`. -/
theorem coe_Z_apply_ket1 :
    ((Z.applyNormalized ket1 : NormalizedVector (Qubits 1)) :
      HilbertVector (Qubits 1)) = -(ket1 : HilbertVector (Qubits 1)) := by
  ext i
  change HilbertOperator.applyVec (ZOp : HilbertOperator (Qubits 1))
      (ket1 : HilbertVector (Qubits 1)) i =
    -(ket1 : HilbertVector (Qubits 1)) i
  rw [ket1, HilbertOperator.applyVec_ket]
  fin_cases i <;> simp [ZOp, NormalizedVector.ket_apply]

/-- The underlying Hadamard operator squares to the identity. -/
theorem H_mul_H :
    (H.matrix : HilbertOperator (Qubits 1)) *
        (H.matrix : HilbertOperator (Qubits 1)) = 1 := by
  ext i j
  change ((HOp : HilbertOperator (Qubits 1)) *
    (HOp : HilbertOperator (Qubits 1))) i j =
      (1 : HilbertOperator (Qubits 1)) i j
  have h : (HOp : HilbertOperator (Qubits 1)) *
      (HOp : HilbertOperator (Qubits 1)) = (1 : HilbertOperator (Qubits 1)) := by
    rw [HOp, UnitaryOperator.coe_ofMatrix, smul_mul_smul_comm,
      invSqrt2_mul_self]
    have hmul :
        (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
          * !![(1 : ℂ), 1; 1, -1] = (2 : ℂ) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
    rw [hmul, smul_smul]
    norm_num
  rw [h]

/-- Metadata-free action `H |+> = |0>`. -/
@[simp]
theorem H_apply_ketPlus :
    H.applyNormalized ketPlus = ket0 := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (H.matrix : HilbertOperator (Qubits 1))
      (ketPlus : HilbertVector (Qubits 1)) i = ket0 i
  have hplus : (ketPlus : HilbertVector (Qubits 1)) =
      HilbertOperator.applyVec (H.matrix : HilbertOperator (Qubits 1))
        (ket0 : HilbertVector (Qubits 1)) := by
    exact (congrArg (fun ψ : NormalizedVector (Qubits 1) =>
      (ψ : HilbertVector (Qubits 1))) H_apply_ket0).symm
  rw [hplus, ← HilbertOperator.mul_applyVec, H_mul_H,
    HilbertOperator.one_applyVec]

/-- Metadata-free action `H |-> = |1>`. -/
@[simp]
theorem H_apply_ketMinus :
    H.applyNormalized ketMinus = ket1 := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (H.matrix : HilbertOperator (Qubits 1))
      (ketMinus : HilbertVector (Qubits 1)) i = ket1 i
  have hminus : (ketMinus : HilbertVector (Qubits 1)) =
      HilbertOperator.applyVec (H.matrix : HilbertOperator (Qubits 1))
        (ket1 : HilbertVector (Qubits 1)) := by
    exact (congrArg (fun ψ : NormalizedVector (Qubits 1) =>
      (ψ : HilbertVector (Qubits 1))) H_apply_ket1).symm
  rw [hminus, ← HilbertOperator.mul_applyVec, H_mul_H,
    HilbertOperator.one_applyVec]

/-! ## `CNOT` on the tensor basis -/

/-- `CNOT |00> = |00>`. -/
@[simp]
theorem CNOT_apply_ket0_tensor_ket0 :
    CNOT.applyNormalized (ket0.tensor ket0) = ket0.tensor ket0 := by
  have h00 : ket0.tensor ket0 =
      NormalizedVector.ket (0 : Fin (2 ^ 2)) := by
    rw [ket0, NormalizedVector.tensor_ket]
    exact congrArg NormalizedVector.ket (by decide)
  rw [h00]
  simpa only [show Equiv.swap (2 : Fin (2 ^ 2)) 3 0 = 0 from by decide] using
    CNOT_apply_ket 0

/-- `CNOT |01> = |01>`. -/
@[simp]
theorem CNOT_apply_ket0_tensor_ket1 :
    CNOT.applyNormalized (ket0.tensor ket1) = ket0.tensor ket1 := by
  have h01 : ket0.tensor ket1 =
      NormalizedVector.ket (1 : Fin (2 ^ 2)) := by
    rw [ket0, ket1, NormalizedVector.tensor_ket]
    exact congrArg NormalizedVector.ket (by decide)
  rw [h01]
  simpa only [show Equiv.swap (2 : Fin (2 ^ 2)) 3 1 = 1 from by decide] using
    CNOT_apply_ket 1

/-- `CNOT |10> = |11>`. -/
@[simp]
theorem CNOT_apply_ket1_tensor_ket0 :
    CNOT.applyNormalized (ket1.tensor ket0) = ket1.tensor ket1 := by
  have h10 : ket1.tensor ket0 =
      NormalizedVector.ket (2 : Fin (2 ^ 2)) := by
    rw [ket0, ket1, NormalizedVector.tensor_ket]
    exact congrArg NormalizedVector.ket (by decide)
  have h11 : ket1.tensor ket1 =
      NormalizedVector.ket (3 : Fin (2 ^ 2)) := by
    rw [ket1, NormalizedVector.tensor_ket]
    exact congrArg NormalizedVector.ket (by decide)
  rw [h10, h11]
  simpa only [show Equiv.swap (2 : Fin (2 ^ 2)) 3 2 = 3 from by decide] using
    CNOT_apply_ket 2

/-- `CNOT |11> = |10>`. -/
@[simp]
theorem CNOT_apply_ket1_tensor_ket1 :
    CNOT.applyNormalized (ket1.tensor ket1) = ket1.tensor ket0 := by
  have h11 : ket1.tensor ket1 =
      NormalizedVector.ket (3 : Fin (2 ^ 2)) := by
    rw [ket1, NormalizedVector.tensor_ket]
    exact congrArg NormalizedVector.ket (by decide)
  have h10 : ket1.tensor ket0 =
      NormalizedVector.ket (2 : Fin (2 ^ 2)) := by
    rw [ket0, ket1, NormalizedVector.tensor_ket]
    exact congrArg NormalizedVector.ket (by decide)
  rw [h11, h10]
  simpa only [show Equiv.swap (2 : Fin (2 ^ 2)) 3 3 = 2 from by decide] using
    CNOT_apply_ket 3

/-! ## Phase gates `S` and `T`

`S = diag(1, i)` and `T = diag(1, e^{iπ/4})` are the two non-Hadamard
single-qubit generators of the Clifford+T gate set. Their strict events use the
builtin coordinates `"s"` and `"t"`; `tEvent` is the coordinate that fault-tolerant
resource statements count. -/

/-- `e^{iπ/4} · e^{iπ/4} = i`. -/
theorem exp_pi_div_four_mul_I_mul_self :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
        Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = Complex.I := by
  rw [← Complex.exp_add]
  have h : (Real.pi : ℂ) / 4 * Complex.I + (Real.pi : ℂ) / 4 * Complex.I =
      (Real.pi : ℂ) / 2 * Complex.I := by
    ring
  rw [h]
  exact Complex.exp_pi_div_two_mul_I

/-- The one-branch phase matrix `diag(1, e^{iφ})` is unitary. -/
theorem phaseDiag_mem_unitaryGroup (φ : ℝ) :
    (!![1, 0; 0, Complex.exp ((φ : ℝ) * Complex.I)] : HilbertOperator (Qubits 1)) ∈
      Matrix.unitaryGroup (Qubits 1).Index ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I, exp_I_mul_exp_neg_I]

/-- Metadata-free phase operator `S = diag(1, i)`. -/
def SOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(1 : ℂ), 0; 0, Complex.I] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply])

/-- Metadata-free phase operator `T = diag(1, e^{iπ/4})`. -/
def TOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![1, 0; 0, Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)] :
      HilbertOperator (Qubits 1))
    (phaseDiag_mem_unitaryGroup (Real.pi / 4))

/-- Sealed `S` declaration at a caller-supplied physical placement. -/
def sLeafAt (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate (.builtin "s") systemIdx SOp

/-- Sealed `S` leaf on the canonical one-qubit placement. -/
def sLeaf : UnitaryLeaf (Qubits 1) :=
  sLeafAt [0]

/-- The `S` circuit, derived from its sealed primitive declaration. -/
def S : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf sLeaf (by simp [sLeaf, sLeafAt])

/-- Sealed `T` declaration at a caller-supplied physical placement. -/
def tLeafAt (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate (.builtin "t") systemIdx TOp

/-- Sealed `T` leaf on the canonical one-qubit placement. -/
def tLeaf : UnitaryLeaf (Qubits 1) :=
  tLeafAt [0]

/-- The `T` circuit, derived from its sealed primitive declaration. -/
def T : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf tLeaf (by simp [tLeaf, tLeafAt])

/-- The strict event coordinate of one `T` gate. -/
def tEvent : Resource.Event .quantum :=
  atomicEvent (.builtin "t")

@[simp]
theorem S_matrix : S.matrix = SOp :=
  rfl

@[simp]
theorem T_matrix : T.matrix = TOp :=
  rfl

@[simp]
theorem S_eventTrace : S.eventTrace = [atomicEvent (.builtin "s")] :=
  rfl

@[simp]
theorem S_eventCost : S.eventCost = atomicEventCost (.builtin "s") :=
  rfl

@[simp]
theorem S_eventDepth : S.eventDepth = atomicEventDepth (.builtin "s") :=
  rfl

theorem S_event_count :
    ResourcePool.count (atomicEvent (.builtin "s")) S.eventCost = 1 := by
  simp [S_eventCost, atomicEventCost]

@[simp]
theorem S_unit_event_depth : S.evaluatedEventDepth (fun _ => 1) = 1 :=
  rfl

@[simp]
theorem S_system_idx : S.physical_idx = [0] := rfl

@[simp]
theorem T_eventTrace : T.eventTrace = [tEvent] :=
  rfl

@[simp]
theorem T_eventCost : T.eventCost = ResourcePool.singleton tEvent :=
  rfl

@[simp]
theorem T_eventDepth : T.eventDepth = atomicEventDepth (.builtin "t") :=
  rfl

theorem T_event_count : ResourcePool.count tEvent T.eventCost = 1 := by
  simp [T_eventCost]

@[simp]
theorem T_unit_event_depth : T.evaluatedEventDepth (fun _ => 1) = 1 :=
  rfl

@[simp]
theorem T_system_idx : T.physical_idx = [0] := rfl

/-! ### Clifford+T generator algebra -/

theorem ZOp_mul_ZOp : ZOp * ZOp = 1 := by
  apply Subtype.ext
  change ((ZOp : HilbertOperator (Qubits 1)) * (ZOp : HilbertOperator (Qubits 1))) =
    (1 : HilbertOperator (Qubits 1))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ZOp, Matrix.mul_apply]

theorem SOp_mul_SOp : SOp * SOp = ZOp := by
  apply Subtype.ext
  change ((SOp : HilbertOperator (Qubits 1)) * (SOp : HilbertOperator (Qubits 1))) =
    (ZOp : HilbertOperator (Qubits 1))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SOp, ZOp, Matrix.mul_apply]

theorem TOp_mul_TOp : TOp * TOp = SOp := by
  apply Subtype.ext
  change ((TOp : HilbertOperator (Qubits 1)) * (TOp : HilbertOperator (Qubits 1))) =
    (SOp : HilbertOperator (Qubits 1))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TOp, SOp, Matrix.mul_apply, exp_pi_div_four_mul_I_mul_self]

theorem SOp_pow_four : SOp ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, SOp_mul_SOp, ZOp_mul_ZOp]

theorem TOp_pow_eight : TOp ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, sq, TOp_mul_TOp, SOp_pow_four]

/-- `S† = S³`, so the adjoint has an exact word over `{S}`. -/
theorem star_SOp : star SOp = SOp ^ 3 := by
  rw [Unitary.star_eq_inv]
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact SOp_pow_four

/-- `T† = T⁷`. -/
theorem star_TOp : star TOp = TOp ^ 7 := by
  rw [Unitary.star_eq_inv]
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact TOp_pow_eight

/-- `T† = T · S³`, so the adjoint has an exact word over `{S, T}` with one `T`. -/
theorem star_TOp_eq_TOp_mul_SOp_pow_three : star TOp = TOp * SOp ^ 3 := by
  rw [star_TOp, show (7 : ℕ) = 1 + 2 * 3 from rfl, pow_add, pow_one TOp, pow_mul, sq,
    TOp_mul_TOp]

end Gate

/-! ## T-count -/

namespace UnitaryCircuit

/-- Number of strict `T` events in a circuit's event pool. -/
def tCount {R : Register} (circuit : UnitaryCircuit R) : Nat :=
  ResourcePool.count Gate.tEvent circuit.eventCost

@[simp]
theorem tCount_identity (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup) :
    (identity R physical_idx physical_idx_nodup).tCount = 0 := by
  simp [tCount, identity_eventCost]

@[simp]
theorem tCount_ofLeaf {R : Register} (leaf : UnitaryLeaf R)
    (systemIdxNodup : leaf.systemIdx.Nodup) :
    (ofLeaf leaf systemIdxNodup).tCount = if leaf.event = Gate.tEvent then 1 else 0 := by
  simp [tCount, leaf_eventCost]

@[simp]
theorem tCount_seq {R : Register} (left right : UnitaryCircuit R) :
    (seq left right).tCount = left.tCount + right.tCount := by
  simp [tCount]

@[simp]
theorem tCount_dagger {R : Register} (body : UnitaryCircuit R) :
    body.dagger.tCount = body.tCount := by
  simp [tCount]

@[simp]
theorem tCount_iterate {R : Register} (count : Nat) (body : UnitaryCircuit R) :
    (iterate count body).tCount = count * body.tCount := by
  simp [tCount]

@[simp]
theorem tCount_reindex {R S : Register} (equiv : R.Index ≃ S.Index) (body : UnitaryCircuit R) :
    (reindex equiv body).tCount = body.tCount := by
  simp [tCount]

@[simp]
theorem tCount_tensor {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).tCount = left.tCount + right.tCount := by
  simp [tCount, tensor_eventCost]

@[simp]
theorem tCount_relabel {R : Register} (circuit : UnitaryCircuit R) {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).tCount = circuit.tCount := by
  simp [tCount, relabel_eventCost]

theorem tCount_sequenceList {R : Register} (start : UnitaryCircuit R)
    (steps : List (UnitaryCircuit R)) :
    (sequenceList start steps).tCount = start.tCount + (steps.map tCount).sum := by
  induction steps generalizing start with
  | nil => simp [sequenceList_nil]
  | cons step steps ih =>
      rw [sequenceList_cons, ih, tCount_seq, List.map_cons, List.sum_cons, add_assoc]

/-- Controlling a circuit turns each `T` event into a controlled-`T` event; the
number of those is the body's T-count. Decomposing controlled-`T` back into
plain `T` gates is a separate compilation step. -/
theorem count_controlForDimension_tEvent_control {R : Register} (control : Register)
    [LE control.Index] [OrderTop control.Index] (controlSystemIdx : List Nat)
    (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    ResourcePool.count
        (Gate.tEvent.controlForDimension (Fintype.card control.Index))
        (UnitaryCircuit.control control controlSystemIdx body layout activationValue).eventCost =
      body.tCount :=
  count_control_eventCost Gate.tEvent control controlSystemIdx body layout activationValue

end UnitaryCircuit

namespace Gate

@[simp]
theorem T_tCount : T.tCount = 1 := by
  rw [UnitaryCircuit.tCount, T_eventCost, ResourcePool.count_singleton_self]

@[simp]
theorem S_tCount : S.tCount = 0 := by
  rw [UnitaryCircuit.tCount, S_eventCost, atomicEventCost, ResourcePool.count_singleton]
  decide

@[simp]
theorem H_tCount : H.tCount = 0 := by
  rw [UnitaryCircuit.tCount, H_eventCost, atomicEventCost, ResourcePool.count_singleton]
  decide

@[simp]
theorem CNOT_tCount : CNOT.tCount = 0 := by
  rw [UnitaryCircuit.tCount, CNOT_eventCost, atomicEventCost, ResourcePool.count_singleton]
  decide

end Gate

/-! ## Register SWAP declaration -/

/-- The permutation of joint basis labels that exchanges two `n`-qubit
registers. -/
def swapRegistersPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ (n + n))) :=
  ((prodEquiv (m := n) (n := n)).symm.trans
    (Equiv.prodComm (Fin (2 ^ n)) (Fin (2 ^ n)))).trans prodEquiv

/-- Metadata-free unitary operator that exchanges two `n`-qubit registers. -/
def swapRegistersOp (n : ℕ) : UnitaryOperator (Qubits (n + n)) :=
  UnitaryOperator.ofPerm (swapRegistersPerm n)

/-- Sealed register-SWAP declaration at a caller-supplied physical placement. -/
def swapRegistersLeafAt (n : ℕ) (systemIdx : List Nat) :
    UnitaryLeaf (Qubits (n + n)) :=
  UnitaryLeaf.gate (.builtin "swap") systemIdx (swapRegistersOp n)

/-- Declared register-SWAP leaf on the canonical joint-register placement. -/
def swapRegistersLeaf (n : ℕ) : UnitaryLeaf (Qubits (n + n)) :=
  swapRegistersLeafAt n (List.range (n + n))

@[simp]
theorem swapRegistersLeaf_event (n : ℕ) :
    (swapRegistersLeaf n).event =
      (Resource.Event.gate (.builtin "swap") : Resource.Event .quantum) :=
  rfl



/-! ## Addressed QFT decomposition gates -/

/-- Stable gate coordinate for one controlled phase in the standard QFT
decomposition. -/
public def qftControlledPhaseLabel : Resource.GateLabel :=
  (Resource.GateLabel.declared "qft" "phase-rotation").controlForDimension 2

/-- Computational-basis phase contributed by one addressed controlled-phase
rotation.  The phase is present exactly when both addressed wires are set. -/
def qftControlledPhaseFactor {n : Nat} (control target : Fin n)
    (angle : Real) (basis : Fin (2 ^ n)) : Complex :=
  if basis.val.testBit (WireAddress.bitIndex control).val &&
      basis.val.testBit (WireAddress.bitIndex target).val then
    Complex.exp (angle * Complex.I)
  else 1

/-- Certified addressed controlled-phase operator. -/
def qftControlledPhaseOperator {n : Nat} (control target : Fin n)
    (angle : Real) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofMatrix
    (Matrix.diagonal (qftControlledPhaseFactor control target angle)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl]
        simp only [Matrix.star_apply]
        rw [Finset.sum_eq_single i]
        · simp only [Matrix.diagonal_apply_eq]
          by_cases hphase :
              i.val.testBit (WireAddress.bitIndex control).val &&
                i.val.testBit (WireAddress.bitIndex target).val
          · simp only [qftControlledPhaseFactor, hphase, if_pos]
            change Complex.exp ((angle : Complex) * Complex.I) *
                starRingEnd Complex
                  (Complex.exp ((angle : Complex) * Complex.I)) = 1
            rw [conj_exp_I, exp_I_mul_exp_neg_I]
          · simp [qftControlledPhaseFactor, hphase]
        · intro k _ hki
          rw [Matrix.diagonal_apply_ne _ (Ne.symm hki), zero_mul]
        · simp
      · rw [Matrix.mul_apply, Matrix.one_apply, if_neg hij]
        simp only [Matrix.star_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hik : i = k
        · subst k
          rw [Matrix.diagonal_apply_eq,
            Matrix.diagonal_apply_ne _ (Ne.symm hij)]
          simp
        · rw [Matrix.diagonal_apply_ne _ hik, zero_mul])

/-- Sealed addressed controlled-phase declaration.  The source coordinate and
operator family are fixed here; callers supply only the occurrence placement
and mathematical phase parameters. -/
def qftControlledPhaseLeafAt {n : Nat} (control target : Fin n)
    (angle : Real) (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.gate qftControlledPhaseLabel systemIdx
    (qftControlledPhaseOperator control target angle)

/-- A genuine addressed wire swap, decomposed semantically into the usual
three addressed CNOT permutations. -/
def qftSwapOperator {n : Nat} (left right : Fin n) (hne : left ≠ right) :
    UnitaryOperator (Qubits n) :=
  Mul.mul
    (Mul.mul
      (QubitPrimitive.operator (.cnot left right hne))
      (QubitPrimitive.operator (.cnot right left hne.symm)))
    (QubitPrimitive.operator (.cnot left right hne))

/-- Sealed source-level SWAP declaration.  Its operator has three-CNOT
semantics, while its fixed resource coordinate remains one atomic SWAP leaf. -/
def qftSwapLeafAt {n : Nat} (left right : Fin n) (hne : left ≠ right)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.gate (.builtin "swap") systemIdx
    (qftSwapOperator left right hne)

/-! ## Single-qubit QSP signal gates -/

/-- Fixed resource coordinate for the Chebyshev O-convention signal gate. -/
def qspSignalOGateLabel : Resource.GateLabel :=
  .declared "qsp" "qsp-signal-o"

/-- Certified Chebyshev O-convention signal operator on its physical domain. -/
def qspSignalOOp (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(x : ℂ), -(Real.sqrt (1 - x ^ 2) : ℂ);
      (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)] :
        HilbertOperator (Qubits 1)) (by
      have hs := sq_sqrt_one_sub_sq hx
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        linear_combination hs
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        linear_combination hs)

/-- Sealed Chebyshev O-convention signal declaration at a caller-supplied
placement. -/
def qspSignalOLeafAt (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate qspSignalOGateLabel systemIdx (qspSignalOOp x hx)

/-- Fixed resource coordinate for the Chebyshev Wx-convention signal gate. -/
def qspSignalWGateLabel : Resource.GateLabel :=
  .declared "qsp" "qsp-signal-w"

/-- Certified Chebyshev Wx-convention signal operator on its physical domain. -/
def qspSignalWOp (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(x : ℂ), Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ);
      Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)] :
        HilbertOperator (Qubits 1)) (by
      have hs := sq_sqrt_one_sub_sq hx
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring_nf
        rw [Complex.I_sq]
        linear_combination hs
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring_nf
        rw [Complex.I_sq]
        linear_combination hs)

/-- Sealed Chebyshev Wx-convention signal declaration at a caller-supplied
placement. -/
def qspSignalWLeafAt (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate qspSignalWGateLabel systemIdx (qspSignalWOp x hx)

/-! ## Rotation gates (QSP / QNN conventions) -/

/-- Metadata-free processing rotation `e^{i phi Z}`. -/
def rotZOp (φ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![Complex.exp (φ * Complex.I), 0; 0,
      Complex.exp (-(φ * Complex.I))] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
          conj_exp_neg_I, exp_I_mul_exp_neg_I, exp_neg_I_mul_exp_I])

/-- Sealed processing-rotation declaration at a caller-supplied placement. -/
def rotZLeafAt (φ : ℝ) (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate
    (.declared "QuantumAlg.Components.Gate" "rotation-z") systemIdx (rotZOp φ)

/-- Sealed processing-rotation leaf on the canonical one-qubit placement. -/
def rotZLeaf (φ : ℝ) : UnitaryLeaf (Qubits 1) :=
  rotZLeafAt φ [0]

@[simp]
theorem rotZLeaf_operator (φ : ℝ) :
    (rotZLeaf φ).operator = rotZOp φ :=
  rfl

@[simp]
theorem rotZLeaf_event (φ : ℝ) :
    (rotZLeaf φ).event =
      (Resource.Event.gate
        (.declared "QuantumAlg.Components.Gate" "rotation-z") :
          Resource.Event .quantum) :=
  rfl



/-- The processing rotation `e^{i phi Z}`. -/
def rotZ (φ : ℝ) : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf (rotZLeaf φ) (by simp [rotZLeaf, rotZLeafAt])

@[simp]
theorem rotZ_eventCost (φ : ℝ) :
    (rotZ φ).eventCost = ResourcePool.singleton (rotZLeaf φ).event :=
  rfl

@[simp]
theorem rotZ_matrix (φ : ℝ) :
    ((rotZ φ).matrix : HilbertOperator (Qubits 1)) = rotZOp φ :=
  rfl

theorem rotZ_mul_rotZ (a b : ℝ) :
    ((rotZ a).matrix : HilbertOperator (Qubits 1)) *
        ((rotZ b).matrix : HilbertOperator (Qubits 1)) =
      ((rotZ (a + b)).matrix : HilbertOperator (Qubits 1)) := by
  ext i j
  change ((rotZOp a : HilbertOperator (Qubits 1)) *
    (rotZOp b : HilbertOperator (Qubits 1))) i j =
      (rotZOp (a + b) : HilbertOperator (Qubits 1)) i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZOp, Matrix.mul_apply, ← Complex.exp_add]
  · congr 1; ring
  · congr 1; ring

theorem rotZ_zero :
    ((rotZ 0).matrix : HilbertOperator (Qubits 1)) = 1 := by
  ext i j
  change (rotZOp 0 : HilbertOperator (Qubits 1)) i j =
    (1 : HilbertOperator (Qubits 1)) i j
  fin_cases i <;> fin_cases j <;> simp [rotZOp]

theorem rotZ_comm (a b : ℝ) :
    ((rotZ a).matrix : HilbertOperator (Qubits 1)) *
        ((rotZ b).matrix : HilbertOperator (Qubits 1)) =
      ((rotZ b).matrix : HilbertOperator (Qubits 1)) *
        ((rotZ a).matrix : HilbertOperator (Qubits 1)) := by
  rw [rotZ_mul_rotZ, rotZ_mul_rotZ, add_comm]

theorem rotZ_neg_mul_rotZ (φ : ℝ) :
    ((rotZ (-φ)).matrix : HilbertOperator (Qubits 1)) *
        ((rotZ φ).matrix : HilbertOperator (Qubits 1)) = 1 := by
  rw [rotZ_mul_rotZ, neg_add_cancel, rotZ_zero]

theorem rotZ_mul_rotZ_neg (φ : ℝ) :
    ((rotZ φ).matrix : HilbertOperator (Qubits 1)) *
        ((rotZ (-φ)).matrix : HilbertOperator (Qubits 1)) = 1 := by
  rw [rotZ_mul_rotZ, add_neg_cancel, rotZ_zero]

/-- Metadata-free standard `R_Y(theta)`. -/
def rotYOp (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
      (Real.sin (θ / 2) : ℂ),
      (Real.cos (θ / 2) : ℂ)] : HilbertOperator (Qubits 1)) (by
      have hcs' : (Real.sin (θ / 2) : ℂ) ^ 2
          + (Real.cos (θ / 2) : ℂ) ^ 2 = 1 := by
        have h := Real.sin_sq_add_cos_sq (θ / 2)
        exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h
      rw [Matrix.mem_unitaryGroup_iff]
      generalize Real.cos (θ / 2) = c at hcs' ⊢
      generalize Real.sin (θ / 2) = s at hcs' ⊢
      ext i j
      fin_cases i <;> fin_cases j <;>
        · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
          try ring_nf
          try linear_combination hcs')

/-- Sealed Y-rotation declaration at a caller-supplied placement. -/
def rotYLeafAt (θ : ℝ) (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate
    (.declared "QuantumAlg.Components.Gate" "rotation-y") systemIdx (rotYOp θ)

/-- Sealed Y-rotation leaf on the canonical one-qubit placement. -/
def rotYLeaf (θ : ℝ) : UnitaryLeaf (Qubits 1) :=
  rotYLeafAt θ [0]

@[simp]
theorem rotYLeaf_operator (θ : ℝ) :
    (rotYLeaf θ).operator = rotYOp θ :=
  rfl

@[simp]
theorem rotYLeaf_event (θ : ℝ) :
    (rotYLeaf θ).event =
      (Resource.Event.gate
        (.declared "QuantumAlg.Components.Gate" "rotation-y") :
          Resource.Event .quantum) :=
  rfl



/-- The standard `R_Y(theta)` circuit. -/
def rotY (θ : ℝ) : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf (rotYLeaf θ) (by simp [rotYLeaf, rotYLeafAt])

@[simp]
theorem rotY_eventCost (θ : ℝ) :
    (rotY θ).eventCost = ResourcePool.singleton (rotYLeaf θ).event :=
  rfl

/-- Metadata-free standard `R_Z(phi) = e^{-i phi Z/2}`. -/
public def rotZStdOp (φ : ℝ) : UnitaryOperator (Qubits 1) := rotZOp (-(φ / 2))

@[simp]
theorem rotZStdOp_zero : rotZStdOp 0 = 1 := by
  apply Subtype.ext
  change (rotZOp (-(0 / 2)) : HilbertOperator (Qubits 1)) = 1
  rw [show -(0 / 2 : ℝ) = 0 by norm_num]
  exact rotZ_zero

/-- Sealed standard Z-rotation declaration at a caller-supplied placement. -/
def rotZStdLeafAt (φ : ℝ) (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  rotZLeafAt (-(φ / 2)) systemIdx

/-- Sealed standard Z-rotation leaf on the canonical one-qubit placement. -/
def rotZStdLeaf (φ : ℝ) : UnitaryLeaf (Qubits 1) :=
  rotZStdLeafAt φ [0]

@[simp]
theorem rotZStdLeaf_operator (φ : ℝ) :
    (rotZStdLeaf φ).operator = rotZStdOp φ :=
  rfl

@[simp]
theorem rotZStdLeaf_event (φ : ℝ) :
    (rotZStdLeaf φ).event =
      (Resource.Event.gate
        (.declared "QuantumAlg.Components.Gate" "rotation-z") :
          Resource.Event .quantum) :=
  rfl



/-- The standard `R_Z(phi) = e^{-i phi Z/2}` circuit. -/
def rotZStd (φ : ℝ) : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf (rotZStdLeaf φ)
    (by simp [rotZStdLeaf, rotZStdLeafAt, rotZLeafAt])

@[simp]
theorem rotZStd_eventCost (φ : ℝ) :
    (rotZStd φ).eventCost = ResourcePool.singleton (rotZStdLeaf φ).event :=
  rfl

@[simp]
theorem coe_rotZStd (φ : ℝ) :
    ((rotZStd φ).matrix : HilbertOperator (Qubits 1)) =
      rotZStdOp φ :=
  rfl

theorem rotZStd_zero :
    ((rotZStd 0).matrix : HilbertOperator (Qubits 1)) = 1 := by
  change (rotZOp (-(0 / 2)) : HilbertOperator (Qubits 1)) = 1
  rw [show -(0 / 2 : ℝ) = 0 by norm_num]
  exact rotZ_zero

/-! ## Phase gates -/

/-- A one-qubit state is its `|0⟩`/`|1⟩` coordinate combination. -/
theorem single_qubit_vec_decomp (ψ : HilbertVector (Qubits 1)) :
    ψ =
      (ψ 0) • (ket0 : HilbertVector (Qubits 1)) + (ψ 1) • (ket1 : HilbertVector (Qubits 1)) := by
  ext i
  fin_cases i <;>
    simp [ket0, ket1, ket_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem single_qubit_decomp (ψ : NormalizedVector (Qubits 1)) :
    (ψ : HilbertVector (Qubits 1)) =
      (ψ 0) • (ket0 : HilbertVector (Qubits 1)) + (ψ 1) • (ket1 : HilbertVector (Qubits 1)) :=
  single_qubit_vec_decomp (ψ : HilbertVector (Qubits 1))

/-- Metadata-free phase operator `diag(1, e^{iθ})`. -/
def phaseGateOp (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![1, 0; 0, Complex.exp ((θ : ℝ) * Complex.I)] :
      HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
          exp_I_mul_exp_neg_I])

/-- Sealed one-branch phase declaration at a caller-supplied placement. -/
def phaseGateLeafAt (θ : ℝ) (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate
    (.declared "QuantumAlg.Components.Gate" "phase") systemIdx (phaseGateOp θ)

/-- Sealed one-branch phase leaf on the canonical one-qubit placement. -/
def phaseGateLeaf (θ : ℝ) : UnitaryLeaf (Qubits 1) :=
  phaseGateLeafAt θ [0]

/-- Single-qubit phase gate with phases `1` and `exp (i * theta)`. -/
def phaseGate (θ : ℝ) : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf (phaseGateLeaf θ) (by simp [phaseGateLeaf, phaseGateLeafAt])

@[simp]
theorem coe_phaseGate (θ : ℝ) :
    ((phaseGate θ).matrix : HilbertOperator (Qubits 1)) =
      phaseGateOp θ :=
  rfl

/-- `T` is the phase gate with angle `π / 4`. -/
theorem Gate.TOp_eq_phaseGateOp : Gate.TOp = phaseGateOp (Real.pi / 4) :=
  rfl

/-- `S` is the phase gate with angle `π / 2`. -/
theorem Gate.SOp_eq_phaseGateOp : Gate.SOp = phaseGateOp (Real.pi / 2) := by
  apply Subtype.ext
  have h : Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) = Complex.I :=
    Complex.exp_pi_div_two_mul_I
  simp [Gate.SOp, phaseGateOp, h]

/-- Metadata-free zero-branch phase operator `diag(e^{iθ}, 1)`. -/
def phaseGateOnZeroOp (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![Complex.exp ((θ : ℝ) * Complex.I), 0; 0, 1] :
      HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
          exp_I_mul_exp_neg_I])

/-- Sealed zero-branch phase declaration at a caller-supplied placement. -/
def phaseGateOnZeroLeafAt (θ : ℝ) (systemIdx : List Nat) :
    UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate
    (.declared "QuantumAlg.Components.Gate" "phase-on-zero") systemIdx
    (phaseGateOnZeroOp θ)

/-- Sealed zero-branch phase leaf on the canonical one-qubit placement. -/
def phaseGateOnZeroLeaf (θ : ℝ) : UnitaryLeaf (Qubits 1) :=
  phaseGateOnZeroLeafAt θ [0]

/-- Single-qubit phase gate with phases `exp (i * theta)` and `1`. -/
def phaseGateOnZero (θ : ℝ) : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.ofLeaf (phaseGateOnZeroLeaf θ)
    (by simp [phaseGateOnZeroLeaf, phaseGateOnZeroLeafAt])

@[simp]
theorem coe_phaseGateOnZero (θ : ℝ) :
    ((phaseGateOnZero θ).matrix : HilbertOperator (Qubits 1)) =
      phaseGateOnZeroOp θ :=
  rfl

@[simp]
theorem phaseGate_apply_ket0 (θ : ℝ) :
    (phaseGate θ).applyNormalized ket0 = ket0 := by
  apply NormalizedVector.ext
  intro i
  change HilbertOperator.applyVec (phaseGateOp θ : HilbertOperator (Qubits 1))
    (ket0 : HilbertVector (Qubits 1)) i = ket0 i
  rw [ket0, HilbertOperator.applyVec_ket, ket_apply]
  fin_cases i <;> simp [phaseGateOp]

theorem phaseGate_apply_ket1 (θ : ℝ) :
    (((phaseGate θ).applyNormalized ket1 : NormalizedVector (Qubits 1)) :
      HilbertVector (Qubits 1)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (ket1 : HilbertVector (Qubits 1)) := by
  ext i
  change HilbertOperator.applyVec (phaseGateOp θ : HilbertOperator (Qubits 1))
      (ket1 : HilbertVector (Qubits 1)) i =
    (Complex.exp ((θ : ℝ) * Complex.I) •
      (ket1 : HilbertVector (Qubits 1))) i
  rw [ket1, HilbertOperator.applyVec_ket]
  fin_cases i <;>
    simp [phaseGateOp, NormalizedVector.ket_apply, PiLp.smul_apply, smul_eq_mul]

/-- The controlled-phase gate on a general ancilla state. -/
theorem phaseGate_applyVec (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGate θ).applyVec ψ
      = (ψ 0) • (ket0 : HilbertVector (Qubits 1)) +
        (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [UnitaryCircuit.applyVec, phaseGate, phaseGateLeaf, phaseGateLeafAt, phaseGateOp,
      ket0, ket1, NormalizedVector.ket, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem phaseGate_apply (θ : ℝ) (ψ : NormalizedVector (Qubits 1)) :
    (((phaseGate θ).applyNormalized ψ : NormalizedVector (Qubits 1)) :
      HilbertVector (Qubits 1))
      = (ψ 0) • (ket0 : HilbertVector (Qubits 1)) +
        (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : HilbertVector (Qubits 1)) :=
  phaseGate_applyVec θ (ψ : HilbertVector (Qubits 1))

/-- The zero-branch controlled-phase gate on a general ancilla state. -/
theorem phaseGateOnZero_applyVec (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOnZero θ).applyVec ψ
      = (Complex.exp ((θ : ℝ) * Complex.I) * ψ 0) •
          (ket0 : HilbertVector (Qubits 1)) +
        (ψ 1) • (ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [UnitaryCircuit.applyVec, phaseGateOnZero, phaseGateOnZeroLeaf, phaseGateOnZeroLeafAt,
      phaseGateOnZeroOp, ket0, ket1, NormalizedVector.ket, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]

/-- `diag(1,e^{iθ}) = e^{iθ/2} · R_Z(θ)`. -/
theorem phaseGate_signal (θ : ℝ) :
    ((phaseGate θ).matrix : HilbertOperator (Qubits 1)) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        ((rotZStd θ).matrix : HilbertOperator (Qubits 1)) := by
  rw [coe_phaseGate, coe_rotZStd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [phaseGateOp, rotZStdOp, rotZOp, UnitaryOperator.coe_ofMatrix,
      Nat.reducePow, Fin.zero_eta, Fin.mk_one, Fin.isValue, Complex.ofReal_div,
      Complex.ofReal_ofNat, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.smul_apply, smul_eq_mul, mul_zero]
  · rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf
  · rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf

/-- `diag(e^{-iθ},1) = e^{-iθ/2} · R_Z(θ)`. -/
theorem phaseGateOnZero_signal (θ : ℝ) :
    ((phaseGateOnZero (-θ)).matrix : HilbertOperator (Qubits 1)) =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        ((rotZStd θ).matrix : HilbertOperator (Qubits 1)) := by
  rw [coe_phaseGateOnZero, coe_rotZStd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [phaseGateOnZeroOp, rotZStdOp, rotZOp,
      UnitaryOperator.coe_ofMatrix, Nat.reducePow,
      Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Complex.ofReal_div, Complex.ofReal_ofNat, neg_mul, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_apply, smul_eq_mul,
      mul_zero]
  · rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf
  · rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf

/-- `diag(1,e^{iθ})` on a vector is `e^{iθ/2}` times the QSP signal
`R_Z(θ)` on that vector. -/
theorem phaseGate_applyVec_eq_smul_rotZStd (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGate θ).applyVec ψ
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStd θ).applyVec ψ := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits 1) => HilbertOperator.applyVec A ψ)
    (phaseGate_signal θ)
  rw [HilbertOperator.smul_applyVec] at h
  exact h

/-- `diag(e^{-iθ},1)` on a vector is `e^{-iθ/2}` times the QSP signal
`R_Z(θ)` on that vector. -/
theorem phaseGateOnZero_applyVec_eq_smul_rotZStd (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOnZero (-θ)).applyVec ψ
      = Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        (rotZStd θ).applyVec ψ := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits 1) => HilbertOperator.applyVec A ψ)
    (phaseGateOnZero_signal θ)
  rw [HilbertOperator.smul_applyVec] at h
  exact h

theorem phaseGate_apply_eq_smul_rotZStd (θ : ℝ)
    (ψ : NormalizedVector (Qubits 1)) :
    (((phaseGate θ).applyNormalized ψ : NormalizedVector (Qubits 1)) :
      HilbertVector (Qubits 1))
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (((rotZStd θ).applyNormalized ψ : NormalizedVector (Qubits 1)) :
          HilbertVector (Qubits 1)) :=
  phaseGate_applyVec_eq_smul_rotZStd θ (ψ : HilbertVector (Qubits 1))

end

end QuantumAlg

end
