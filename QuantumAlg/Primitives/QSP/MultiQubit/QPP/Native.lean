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
public def ancillaGate (n : Nat)
    (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  Gate.singleQubitAt (layout n) (QPPOracle.model n) operator
    (0 : Fin (1 + n)) rfl

/-- The gate acts on the original ancilla, leaving every target wire fixed. -/
public lemma ancillaGate_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (operator : UnitaryOperator (Qubits 1)) :
    ((ancillaGate n operator).binaryMatrix (QPPOracle.interpretation U)) =
      operator.tensor (1 : UnitaryOperator (Qubits n)) :=
  Gate.singleQubitAt_first_binaryMatrix (QPPOracle.model n) n operator
    (QPPOracle.interpretation U)

/-- A supplied one-qubit operator costs one actual default-model gate. -/
public lemma ancillaGate_eventCost (n : Nat)
    (operator : UnitaryOperator (Qubits 1)) :
    (ancillaGate n operator).eventCost =
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model n))
        (.gate .singleQubit) :=
  Gate.singleQubitAt_eventCost (layout n) (QPPOracle.model n) operator
    (0 : Fin (1 + n)) rfl

/-- Three front processing rotations in their original execution order. -/
public def initial (n : Nat) (φ θ₀ φ₀ : Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  ((ancillaGate n (rotZStdOp φ₀)).seq (ancillaGate n (rotYOp θ₀))).seq
    (ancillaGate n (rotZStdOp φ))

/-- The two trainable rotations preceding one controlled signal query. -/
public def processingPair (n : Nat)
    (angles : Real × Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  (ancillaGate n (rotZStdOp angles.2)).seq (ancillaGate n (rotYOp angles.1))

/-- The first three native gates retain the exact source rotation product. -/
public lemma initial_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) :
    ((initial n φ θ₀ φ₀).binaryMatrix (QPPOracle.interpretation U)) =
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
public lemma processingPair_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    ((processingPair n angles).binaryMatrix (QPPOracle.interpretation U)) =
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
public def oracle (n : Nat) (index : Nat) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  if index % 2 = 0 then QPPOracle.circuit n .inverseZero
  else QPPOracle.circuit n .forward

/-- The query's exact binary matrix preserves both activation conventions. -/
public lemma oracle_binaryMatrix_even {n : Nat} (U : UnitaryOperator (Qubits n))
    {index : Nat} (even : index % 2 = 0) :
    ((oracle n index).binaryMatrix (QPPOracle.interpretation U)) =
      UnitaryOperator.controlledQubitsOnZero U⁻¹ := by
  simp [oracle, even, QPPOracle.circuit_inverseZero_binaryMatrix]

public lemma oracle_binaryMatrix_odd {n : Nat} (U : UnitaryOperator (Qubits n))
    {index : Nat} (odd : index % 2 ≠ 0) :
    ((oracle n index).binaryMatrix (QPPOracle.interpretation U))
      = UnitaryOperator.controlledQubits U := by
  simp only [oracle, if_neg odd, QPPOracle.circuit_forward_binaryMatrix]

/-- The full oracle call emits one controlled-query event in either branch. -/
public lemma oracle_eventCost (n : Nat)
    (index : Nat) :
    (oracle n index).eventCost = ResourcePool.singleton (QPPOracle.event n) := by
  by_cases even : index % 2 = 0
  · simp [oracle, even, QPPOracle.circuit_eventCost]
  · simp [oracle, even, QPPOracle.circuit_eventCost]

/-- One source-aligned step executes two rotations and then the controlled query. -/
public def step (n : Nat) (index : Nat)
    (angles : Real × Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  (processingPair n angles).seq (oracle n index)

public lemma step_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (index : Nat) (angles : Real × Real) :
    ((step n index angles).binaryMatrix (QPPOracle.interpretation U)) =
      ((oracle n index).binaryMatrix (QPPOracle.interpretation U)) *
        (rotYOp angles.1 * rotZStdOp angles.2).tensor
          (1 : UnitaryOperator (Qubits n)) := by
  rw [step, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    processingPair_binaryMatrix]

/-- The schedule has the original input wire order and exactly one ancilla. -/
public def circuit (n : Nat)
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  angles.zipIdx.foldl
    (fun accumulated item => (step n item.2 item.1).seq accumulated)
    (initial n φ θ₀ φ₀)

/-- A direct YZZYZ step always uses the one-controlled `U` grant. -/
public def directStep (n : Nat)
    (angles : Real × Real) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  (processingPair n angles).seq (QPPOracle.circuit n .forward)

public lemma directStep_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (angles : Real × Real) :
    ((directStep n angles).binaryMatrix (QPPOracle.interpretation U)) =
      UnitaryOperator.controlledQubits U *
        (rotYOp angles.1 * rotZStdOp angles.2).tensor
          (1 : UnitaryOperator (Qubits n)) := by
  rw [directStep, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    QPPOracle.circuit_forward_binaryMatrix, processingPair_binaryMatrix]

/-- The direct YZZYZ word uses the same native placement and access model. -/
public def directCircuit (n : Nat)
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n) :=
  angles.foldl (fun accumulated item => (directStep n item).seq accumulated)
    (initial n φ θ₀ φ₀)

private lemma circuitFold_binaryMatrix {n : Nat} {α : Type}
    (U : UnitaryOperator (Qubits n)) (schedule : List α)
    (start : UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n))
    (atom : α → UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n)) :
    ((schedule.foldl (fun accumulated item => (atom item).seq accumulated)
      start).binaryMatrix (QPPOracle.interpretation U)) =
        schedule.foldl (fun accumulated item
          => accumulated * ((atom item).binaryMatrix (QPPOracle.interpretation U)))
          (start.binaryMatrix (QPPOracle.interpretation U)) := by
  induction schedule generalizing start with
  | nil => rfl
  | cons item tail ih =>
      simp only [List.foldl_cons]
      rw [ih, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]

/-- The whole circuit matrix is the ordered product of its actual native steps. -/
public lemma circuit_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    ((circuit n φ θ₀ φ₀ angles).binaryMatrix (QPPOracle.interpretation U)) =
      angles.zipIdx.foldl
        (fun accumulated item
          => accumulated * ((step n item.2 item.1).binaryMatrix (QPPOracle.interpretation U)))
        ((initial n φ θ₀ φ₀).binaryMatrix (QPPOracle.interpretation U)) := by
  exact circuitFold_binaryMatrix U angles.zipIdx (initial n φ θ₀ φ₀)
    (fun item => step n item.2 item.1)

public lemma directCircuit_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    ((directCircuit n φ θ₀ φ₀ angles).binaryMatrix (QPPOracle.interpretation U)) =
      angles.foldl
        (fun accumulated item
          => accumulated * ((directStep n item).binaryMatrix (QPPOracle.interpretation U)))
        ((initial n φ θ₀ φ₀).binaryMatrix (QPPOracle.interpretation U)) := by
  exact circuitFold_binaryMatrix U angles (initial n φ θ₀ φ₀) (directStep n)

/-- Count the actual controlled source queries of the native word. -/
public def queryCount (n : Nat)
    (resources : ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model n))) : Nat :=
  ResourcePool.count (QPPOracle.event n) resources

/-- Count the actual default-model one-qubit gates of the native word. -/
public def rotationCount (n : Nat)
    (resources : ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model n))) : Nat :=
  ResourcePool.count
    (model := .quantum AlgorithmGate.model (QPPOracle.model n))
    (.gate .singleQubit) resources

/-- The front block contains exactly three native one-qubit gates. -/
public lemma initial_eventCost (n : Nat)
    (φ θ₀ φ₀ : Real) :
    (initial n φ θ₀ φ₀).eventCost =
      3 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model n))
        (.gate .singleQubit) := by
  simp only [initial, UnitaryCircuit.seq_eventCost, ancillaGate_eventCost,
    show (3 : Nat) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]

/-- The processing pair contains precisely two native one-qubit gates. -/
public lemma processingPair_eventCost (n : Nat)
    (angles : Real × Real) :
    (processingPair n angles).eventCost =
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model n))
        (.gate .singleQubit) := by
  simp only [processingPair, UnitaryCircuit.seq_eventCost,
    ancillaGate_eventCost, two_nsmul]

/-- One step contains one granted controlled query and two native rotations. -/
public lemma step_eventCost (n : Nat)
    (index : Nat) (angles : Real × Real) :
    (step n index angles).eventCost =
      ResourcePool.singleton (QPPOracle.event n) +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model n))
          (.gate .singleQubit) := by
  rw [step, UnitaryCircuit.seq_eventCost, processingPair_eventCost,
    oracle_eventCost]
  ac_rfl

public lemma directStep_eventCost (n : Nat)
    (angles : Real × Real) :
    (directStep n angles).eventCost =
      ResourcePool.singleton (QPPOracle.event n) +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model n))
          (.gate .singleQubit) := by
  rw [directStep, UnitaryCircuit.seq_eventCost, processingPair_eventCost,
    QPPOracle.circuit_eventCost]
  ac_rfl

private lemma circuitFold_eventCost {α : Type}
    (n : Nat) (schedule : List α)
    (start : UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n))
    (atom : α → UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (layout n))
    (cost : ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model n)))
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
public lemma circuit_eventCost (n : Nat)
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    (circuit n φ θ₀ φ₀ angles).eventCost =
      angles.length • ResourcePool.singleton (QPPOracle.event n) +
        (2 * angles.length + 3) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model n))
          (.gate .singleQubit) := by
  rw [circuit, circuitFold_eventCost n angles.zipIdx
    (initial n φ θ₀ φ₀) (fun item => step n item.2 item.1)
    (ResourcePool.singleton (QPPOracle.event n) +
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model n))
        (.gate .singleQubit)) (fun item => step_eventCost n item.2 item.1)]
  rw [List.length_zipIdx, initial_eventCost, smul_add, smul_smul]
  rw [add_assoc, ← add_nsmul, Nat.mul_comm angles.length 2]

/-- The direct YZZYZ word has the same exact query and native-rotation ledger. -/
public lemma directCircuit_eventCost (n : Nat)
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    (directCircuit n φ θ₀ φ₀ angles).eventCost =
      angles.length • ResourcePool.singleton (QPPOracle.event n) +
        (2 * angles.length + 3) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (QPPOracle.model n))
          (.gate .singleQubit) := by
  rw [directCircuit, circuitFold_eventCost n angles (initial n φ θ₀ φ₀)
    (directStep n)
    (ResourcePool.singleton (QPPOracle.event n) +
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (QPPOracle.model n))
        (.gate .singleQubit)) (fun item => directStep_eventCost n item)]
  rw [initial_eventCost, smul_add, smul_smul]
  rw [add_assoc, ← add_nsmul, Nat.mul_comm angles.length 2]

/-- Every word has one controlled query per step and exactly `2L+3` native
one-qubit gates, both read from the same executable circuit. -/
public lemma circuit_counts (n : Nat)
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    queryCount n (circuit n φ θ₀ φ₀ angles).eventCost = angles.length ∧
      rotationCount n (circuit n φ θ₀ φ₀ angles).eventCost =
        2 * angles.length + 3 := by
  rw [circuit_eventCost]
  constructor <;> simp [queryCount, rotationCount, QPPOracle.event]

public lemma directCircuit_counts (n : Nat)
    (φ θ₀ φ₀ : Real) (angles : List (Real × Real)) :
    queryCount n (directCircuit n φ θ₀ φ₀ angles).eventCost = angles.length ∧
      rotationCount n (directCircuit n φ θ₀ φ₀ angles).eventCost =
        2 * angles.length + 3 := by
  rw [directCircuit_eventCost]
  constructor <;> simp [queryCount, rotationCount, QPPOracle.event]

end

end QuantumAlg.QSP.MultiQubit.QPP.Native
