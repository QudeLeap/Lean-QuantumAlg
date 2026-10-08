/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Oracle.QPP
public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
public import QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.Oracle.QPP
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Native QPP alternating word

The actual word has one signal ancilla, the supplied target register and only
the two controlled queries granted by `QPPOracle.model`. Every processing
rotation is a default-model single-qubit gate on the original leading wire.
Its binary matrix and event pool are both projections of this same circuit.
The even step uses zero-controlled `U†`, followed by the odd step's
one-controlled `U`, exactly as in [WZYW23, arxiv_v3.tex:598-618].
-/

namespace QuantumAlg.QSP.MultiQubit.QPP.Native

noncomputable section

/-- Canonical physical word containing the signal ancilla and target qubits. -/
public abbrev layout (n : Nat) :=
  (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout

/-- One actual processing gate on the signal ancilla. -/
public def ancillaGate {n : Nat} (U : UnitaryOperator (Qubits n))
    (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  Gate.singleQubitAt (layout n) (QPPOracle.model U) operator
    (0 : Fin (1 + n)) rfl

/-- The gate acts on the original ancilla, leaving every target wire fixed. -/
public theorem ancillaGate_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (operator : UnitaryOperator (Qubits 1)) :
    (ancillaGate U operator).binaryMatrix =
      operator.tensor (1 : UnitaryOperator (Qubits n)) :=
  Gate.singleQubitAt_first_binaryMatrix (QPPOracle.model U) n operator

/-- A supplied one-qubit operator costs one actual default-model gate. -/
public theorem ancillaGate_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (operator : UnitaryOperator (Qubits 1)) :
    (ancillaGate U operator).eventCost =
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model U))
        (.gate .singleQubit) :=
  Gate.singleQubitAt_eventCost (layout n) (QPPOracle.model U) operator
    (0 : Fin (1 + n)) rfl

/-- Three front processing rotations in their original execution order. -/
public def initial {n : Nat} (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  ((ancillaGate U (rotZStdOp φ₀)).seq (ancillaGate U (rotYOp θ₀))).seq
    (ancillaGate U (rotZStdOp φ))

/-- The two trainable rotations preceding one controlled signal query. -/
public def processingPair {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  (ancillaGate U (rotZStdOp angles.2)).seq (ancillaGate U (rotYOp angles.1))

/-- The first three native gates retain the exact source rotation product. -/
public theorem initial_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) :
    (initial U φ θ₀ φ₀).binaryMatrix =
      (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀)).tensor
        (1 : UnitaryOperator (Qubits n)) := by
  simp only [initial, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    ancillaGate_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor (rotZStdOp φ : HilbertOperator (Qubits 1)) 1 *
      (HilbertOperator.tensor (rotYOp θ₀ : HilbertOperator (Qubits 1)) 1 *
        HilbertOperator.tensor (rotZStdOp φ₀ : HilbertOperator (Qubits 1)) 1) = _
  rw [HilbertOperator.tensor_mul_tensor, Matrix.one_mul,
    HilbertOperator.tensor_mul_tensor, Matrix.one_mul]
  rfl

/-- Two native rotations have exactly the source processing-pair operator. -/
public theorem processingPair_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    (processingPair U angles).binaryMatrix =
      (rotYOp angles.1 * rotZStdOp angles.2).tensor
        (1 : UnitaryOperator (Qubits n)) := by
  simp only [processingPair, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    ancillaGate_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor (rotYOp angles.1 : HilbertOperator (Qubits 1)) 1 *
      HilbertOperator.tensor (rotZStdOp angles.2 : HilbertOperator (Qubits 1)) 1 = _
  rw [HilbertOperator.tensor_mul_tensor, Matrix.one_mul]
  rfl

/-- The alternating query explicitly selects zero-controlled `U†` or controlled `U`. -/
public def oracle {n : Nat} (U : UnitaryOperator (Qubits n)) (index : Nat) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  if index % 2 = 0 then QPPOracle.circuit U .inverseZero
  else QPPOracle.circuit U .forward

/-- The query's exact binary matrix preserves both activation conventions. -/
public theorem oracle_binaryMatrix_even {n : Nat} (U : UnitaryOperator (Qubits n))
    {index : Nat} (even : index % 2 = 0) :
    (oracle U index).binaryMatrix =
      UnitaryOperator.controlledQubitsOnZero U⁻¹ := by
  simp [oracle, even, QPPOracle.circuit_inverseZero_binaryMatrix]

public theorem oracle_binaryMatrix_odd {n : Nat} (U : UnitaryOperator (Qubits n))
    {index : Nat} (odd : index % 2 ≠ 0) :
    (oracle U index).binaryMatrix = UnitaryOperator.controlledQubits U := by
  simp only [oracle, if_neg odd, QPPOracle.circuit_forward_binaryMatrix]

/-- The full oracle call emits one controlled-query event in either branch. -/
public theorem oracle_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (index : Nat) :
    (oracle U index).eventCost = ResourcePool.singleton (QPPOracle.event U) := by
  by_cases even : index % 2 = 0
  · simp [oracle, even, QPPOracle.circuit_eventCost]
  · simp [oracle, even, QPPOracle.circuit_eventCost]

/-- One source-aligned step executes two rotations and then the controlled query. -/
public def step {n : Nat} (U : UnitaryOperator (Qubits n)) (index : Nat)
    (angles : Real × Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  (processingPair U angles).seq (oracle U index)

public theorem step_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (index : Nat) (angles : Real × Real) :
    (step U index angles).binaryMatrix =
      (oracle U index).binaryMatrix *
        (rotYOp angles.1 * rotZStdOp angles.2).tensor
          (1 : UnitaryOperator (Qubits n)) := by
  rw [step, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    processingPair_binaryMatrix]

/-- The schedule has the original input wire order and exactly one ancilla. -/
public def circuit {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  angles.zipIdx.foldl
    (fun accumulated item => (step U item.2 item.1).seq accumulated)
    (initial U φ θ₀ φ₀)

/-- A direct YZZYZ step always uses the one-controlled `U` grant. -/
public def directStep {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  (processingPair U angles).seq (QPPOracle.circuit U .forward)

public theorem directStep_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    (directStep U angles).binaryMatrix =
      UnitaryOperator.controlledQubits U *
        (rotYOp angles.1 * rotZStdOp angles.2).tensor
          (1 : UnitaryOperator (Qubits n)) := by
  rw [directStep, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    QPPOracle.circuit_forward_binaryMatrix, processingPair_binaryMatrix]

/-- The direct YZZYZ word uses the same native placement and access model. -/
public def directCircuit {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n) :=
  angles.foldl (fun accumulated item => (directStep U item).seq accumulated)
    (initial U φ θ₀ φ₀)

private theorem circuitFold_binaryMatrix {n : Nat} {α : Type}
    (U : UnitaryOperator (Qubits n)) (schedule : List α)
    (start : UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n))
    (atom : α → UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n)) :
    (schedule.foldl (fun accumulated item => (atom item).seq accumulated)
      start).binaryMatrix =
        schedule.foldl (fun accumulated item => accumulated * (atom item).binaryMatrix)
          start.binaryMatrix := by
  induction schedule generalizing start with
  | nil => rfl
  | cons item tail ih =>
      simp only [List.foldl_cons]
      rw [ih, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]

/-- The whole circuit matrix is the ordered product of its actual native steps. -/
public theorem circuit_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    (circuit U φ θ₀ φ₀ angles).binaryMatrix =
      angles.zipIdx.foldl
        (fun accumulated item => accumulated * (step U item.2 item.1).binaryMatrix)
        (initial U φ θ₀ φ₀).binaryMatrix := by
  exact circuitFold_binaryMatrix U angles.zipIdx (initial U φ θ₀ φ₀)
    (fun item => step U item.2 item.1)

public theorem directCircuit_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    (directCircuit U φ θ₀ φ₀ angles).binaryMatrix =
      angles.foldl
        (fun accumulated item => accumulated * (directStep U item).binaryMatrix)
        (initial U φ θ₀ φ₀).binaryMatrix := by
  exact circuitFold_binaryMatrix U angles (initial U φ θ₀ φ₀) (directStep U)

/-- Count the actual controlled source queries of the native word. -/
public def queryCount {n : Nat} (U : UnitaryOperator (Qubits n))
    (resources : ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model U))) : Nat :=
  ResourcePool.count (QPPOracle.event U) resources

/-- Count the actual default-model one-qubit gates of the native word. -/
public def rotationCount {n : Nat} (U : UnitaryOperator (Qubits n))
    (resources : ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model U))) : Nat :=
  ResourcePool.count
    (model := .quantum AlgorithmGate.model (QPPOracle.model U))
    (.gate .singleQubit) resources

/-- The front block contains exactly three native one-qubit gates. -/
public theorem initial_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) :
    (initial U φ θ₀ φ₀).eventCost =
      3 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model U))
        (.gate .singleQubit) := by
  simp only [initial, UnitaryCircuit.seq_eventCost, ancillaGate_eventCost,
    show (3 : Nat) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]

/-- The processing pair contains precisely two native one-qubit gates. -/
public theorem processingPair_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    (processingPair U angles).eventCost =
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model U))
        (.gate .singleQubit) := by
  simp only [processingPair, UnitaryCircuit.seq_eventCost,
    ancillaGate_eventCost, two_nsmul]

/-- One step contains one granted controlled query and two native rotations. -/
public theorem step_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (index : Nat) (angles : Real × Real) :
    (step U index angles).eventCost =
      ResourcePool.singleton (QPPOracle.event U) +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model U))
          (.gate .singleQubit) := by
  rw [step, UnitaryCircuit.seq_eventCost, processingPair_eventCost,
    oracle_eventCost]
  ac_rfl

public theorem directStep_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    (directStep U angles).eventCost =
      ResourcePool.singleton (QPPOracle.event U) +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model U))
          (.gate .singleQubit) := by
  rw [directStep, UnitaryCircuit.seq_eventCost, processingPair_eventCost,
    QPPOracle.circuit_eventCost]
  ac_rfl

private theorem circuitFold_eventCost {n : Nat} {α : Type}
    (U : UnitaryOperator (Qubits n)) (schedule : List α)
    (start : UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n))
    (atom : α → UnitaryCircuit AlgorithmGate.model (QPPOracle.model U) (layout n))
    (cost : ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model U)))
    (atomCost : ∀ item, (atom item).eventCost = cost) :
    (schedule.foldl (fun accumulated item => (atom item).seq accumulated)
      start).eventCost = schedule.length • cost + start.eventCost := by
  induction schedule generalizing start with
  | nil => simp
  | cons item tail ih =>
      simp only [List.foldl_cons, List.length_cons, ih,
        UnitaryCircuit.seq_eventCost, atomCost, add_nsmul, one_nsmul]
      ac_rfl

/-- No hidden gate or uncontrolled query occurs in the native QPP word. -/
public theorem circuit_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    (circuit U φ θ₀ φ₀ angles).eventCost =
      angles.length • ResourcePool.singleton (QPPOracle.event U) +
        (2 * angles.length + 3) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model U))
          (.gate .singleQubit) := by
  rw [circuit, circuitFold_eventCost U angles.zipIdx
    (initial U φ θ₀ φ₀) (fun item => step U item.2 item.1)
    (ResourcePool.singleton (QPPOracle.event U) +
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model U))
        (.gate .singleQubit)) (fun item => step_eventCost U item.2 item.1)]
  rw [List.length_zipIdx, initial_eventCost, smul_add, smul_smul]
  rw [add_assoc, ← add_nsmul, Nat.mul_comm angles.length 2]

/-- The direct YZZYZ word has the same exact query and native-rotation ledger. -/
public theorem directCircuit_eventCost {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    (directCircuit U φ θ₀ φ₀ angles).eventCost =
      angles.length • ResourcePool.singleton (QPPOracle.event U) +
        (2 * angles.length + 3) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model U))
          (.gate .singleQubit) := by
  rw [directCircuit, circuitFold_eventCost U angles (initial U φ θ₀ φ₀)
    (directStep U)
    (ResourcePool.singleton (QPPOracle.event U) +
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model U))
        (.gate .singleQubit)) (fun item => directStep_eventCost U item)]
  rw [initial_eventCost, smul_add, smul_smul]
  rw [add_assoc, ← add_nsmul, Nat.mul_comm angles.length 2]

/-- Every word has one controlled query per step and exactly `2L+3` native
one-qubit gates, both read from the same executable circuit. -/
public theorem circuit_counts {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    queryCount U (circuit U φ θ₀ φ₀ angles).eventCost = angles.length ∧
      rotationCount U (circuit U φ θ₀ φ₀ angles).eventCost =
        2 * angles.length + 3 := by
  rw [circuit_eventCost]
  constructor <;> simp [queryCount, rotationCount, QPPOracle.event]

public theorem directCircuit_counts {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    queryCount U (directCircuit U φ θ₀ φ₀ angles).eventCost = angles.length ∧
      rotationCount U (directCircuit U φ θ₀ φ₀ angles).eventCost =
        2 * angles.length + 3 := by
  rw [directCircuit_eventCost]
  constructor <;> simp [queryCount, rotationCount, QPPOracle.event]

end

end QuantumAlg.QSP.MultiQubit.QPP.Native
