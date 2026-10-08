/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Native
public import QuantumAlg.Primitives.QFT.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Native
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Scalar
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources
import all QuantumAlg.Primitives.QFT.Native.Inverse.Depth
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence

/-!
# Native exponent preparation and readout circuits

Two actual range-preparation words and two generated inverse Fourier words
occupy consecutive physical intervals. Their matrices, native event pools and
parallel dependency depths come from those same words. The known order itself
determines the preparation's canonical binary expansion.
-/

namespace QuantumAlg.FiniteCyclicDLP.ConcreteCircuitAccess

noncomputable section

universe u

variable {G : Type u} [Group G]

private theorem consecutiveSelections_disjoint (n : Nat) :
    Disjoint (UnitaryCircuit.binaryPrefixEmbedding n n).selection
      (UnitaryCircuit.binarySuffixEmbedding n n).selection := by
  classical
  apply Finset.disjoint_left.mpr
  intro index inLeft inRight
  obtain ⟨left, _, leftEq⟩ := Finset.mem_map.mp inLeft
  obtain ⟨right, _, rightEq⟩ := Finset.mem_map.mp inRight
  have leftValue := congrArg Fin.val leftEq
  have rightValue := congrArg Fin.val rightEq
  change left.val = index.val at leftValue
  change n + right.val = index.val at rightValue
  have leftBound : left.val < n := left.isLt
  omega

/-- Execute two identical native words on disjoint consecutive qubit blocks.
The result type fixes every physical identity and dimension. -/
def pairConsecutiveCircuit {gates : GateModel} {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits (n + n)).canonicalPlacement.layout :=
  UnitaryCircuit.parallel body (body.relabel (UnitaryCircuit.binarySuffixShift n))
    (UnitaryCircuit.binaryPrefixEmbedding n n)
    (UnitaryCircuit.binarySuffixEmbedding n n) (consecutiveSelections_disjoint n)

/-- Both copies retain their actual native event sequences. -/
@[simp] theorem pairConsecutiveCircuit_eventTrace
    {gates : GateModel} {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (pairConsecutiveCircuit body).eventTrace = body.eventTrace ++ body.eventTrace := by
  change body.eventTrace ++
    (body.relabel (UnitaryCircuit.binarySuffixShift n)).eventTrace = _
  rw [UnitaryCircuit.relabel_eventTrace]

/-- Parallel placement adds the native event pools of both actual words. -/
@[simp] theorem pairConsecutiveCircuit_eventCost
    {gates : GateModel} {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (pairConsecutiveCircuit body).eventCost = body.eventCost + body.eventCost := by
  rw [pairConsecutiveCircuit, UnitaryCircuit.parallel_eventCost,
    UnitaryCircuit.relabel_eventCost]

/-- The physically disjoint words retain a parallel dependency boundary. -/
@[simp] theorem pairConsecutiveCircuit_eventDepth
    {gates : GateModel} {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (pairConsecutiveCircuit body).eventDepth =
      .tensor body.eventDepth body.eventDepth := by
  change DepthExpr.tensor body.eventDepth
    (body.relabel (UnitaryCircuit.binarySuffixShift n)).eventDepth = _
  rw [UnitaryCircuit.relabel_eventDepth]

/-- Two identical parallel words have one branch's depth for every duration assignment. -/
@[simp] theorem pairConsecutiveCircuit_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (pairConsecutiveCircuit body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rw [pairConsecutiveCircuit, UnitaryCircuit.evaluatedEventDepth_parallel,
    UnitaryCircuit.relabel_evaluatedEventDepth, Nat.max_self]

/-- The paired native word is exactly the tensor of the original operators,
including their phases and action away from the prepared zero input. -/
theorem pairConsecutiveCircuit_binaryMatrix
    {gates : GateModel} {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout) :
    (pairConsecutiveCircuit body).binaryMatrix = body.binaryMatrix.tensor body.binaryMatrix := by
  have sameMatrix : (pairConsecutiveCircuit body).binaryMatrix =
      ((body.onBinaryPrefix n).seq (body.onBinarySuffix n)).binaryMatrix := rfl
  rw [sameMatrix, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor 1 (body.binaryMatrix : HilbertOperator (Qubits n)) *
      HilbertOperator.tensor (body.binaryMatrix : HilbertOperator (Qubits n)) 1 =
    HilbertOperator.tensor (body.binaryMatrix : HilbertOperator (Qubits n))
      (body.binaryMatrix : HilbertOperator (Qubits n))
  rw [HilbertOperator.tensor_mul_tensor, one_mul, mul_one]

/-- The actual pair acts factorwise on arbitrary subsystem vectors. -/
theorem pairConsecutiveCircuit_applyBinaryVec_tensor
    {gates : GateModel} {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits n).canonicalPlacement.layout)
    (left right : HilbertVector (Qubits n)) :
    (pairConsecutiveCircuit body).applyBinaryVec (HilbertVector.tensor left right) =
      HilbertVector.tensor (body.applyBinaryVec left) (body.applyBinaryVec right) := by
  exact (congrArg (fun operator => UnitaryOperator.applyVec operator
    (HilbertVector.tensor left right)) (pairConsecutiveCircuit_binaryMatrix body)).trans
      (UnitaryOperator.tensor_applyVec_tensor body.binaryMatrix body.binaryMatrix left right)

/-- Two parallel exact range-uniform preparations from the known order's
canonical expansion, including orders one and powers of two. -/
public def exponentPreparationCircuit (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (orderWidth P + orderWidth P)).canonicalPlacement.layout :=
  pairConsecutiveCircuit (OrderPreparation.Native.circuit oracles P
    (OrderExpansion.canonical P.order P.order_pos))

/-- The complete zero input is mapped to the two source range-uniform states. -/
theorem exponentPreparationCircuit_apply_zero
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    (exponentPreparationCircuit P oracles).binaryMatrix.apply
        (NormalizedVector.ket (R := Qubits (orderWidth P + orderWidth P)) 0) =
      (OrderPreparation.state P).tensor (OrderPreparation.state P) := by
  have zeroPair :
      (NormalizedVector.ket (R := Qubits (orderWidth P)) 0).tensor
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0) =
        NormalizedVector.ket (R := Qubits (orderWidth P + orderWidth P)) 0 := by
    rw [NormalizedVector.tensor_ket]
    congr 2
  rw [← zeroPair, exponentPreparationCircuit, pairConsecutiveCircuit_binaryMatrix,
    UnitaryOperator.tensor_apply_tensor]
  simp only [OrderPreparation.Native.circuit_apply_zero]

/-- Exact one-qubit count of the two native range preparations. -/
theorem exponentPreparationCircuit_singleQubit_count
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (exponentPreparationCircuit P oracles).eventCost =
      2 * OrderPreparation.singleQubitCount (OrderExpansion.canonical P.order P.order_pos) := by
  simp only [exponentPreparationCircuit, pairConsecutiveCircuit_eventCost, ResourcePool.count_add,
    OrderPreparation.Native.circuit_singleQubit_count]
  omega

/-- Exact CNOT count of the two native range preparations. -/
theorem exponentPreparationCircuit_cnot_count
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (exponentPreparationCircuit P oracles).eventCost =
      2 * OrderPreparation.cnotCount (OrderExpansion.canonical P.order P.order_pos) := by
  simp only [exponentPreparationCircuit, pairConsecutiveCircuit_eventCost, ResourcePool.count_add,
    OrderPreparation.Native.circuit_cnot_count]
  omega

/-- Range preparation introduces no Toffoli instruction. -/
theorem exponentPreparationCircuit_toffoli_count
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (exponentPreparationCircuit P oracles).eventCost = 0 := by
  simp [exponentPreparationCircuit, pairConsecutiveCircuit_eventCost,
    ResourcePool.count_add, OrderPreparation.Native.circuit_toffoli_count]

/-- The preparation makes no declared oracle query. -/
theorem exponentPreparationCircuit_oracle_count
    (P : KnownOrderProblem G) (oracles : OracleModel) (query : oracles.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.oracle query)
        (exponentPreparationCircuit P oracles).eventCost = 0 := by
  simp [exponentPreparationCircuit, pairConsecutiveCircuit_eventCost,
    ResourcePool.count_add, OrderPreparation.Native.circuit_oracle_count]

/-- Both preparations share the actual single-branch unit-duration depth. -/
theorem exponentPreparationCircuit_unit_depth
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    (exponentPreparationCircuit P oracles).evaluatedEventDepth (fun _ => 1) =
      OrderPreparation.unitDepth (OrderExpansion.canonical P.order P.order_pos) := by
  rw [exponentPreparationCircuit, pairConsecutiveCircuit_evaluatedEventDepth,
    OrderPreparation.Native.circuit_unit_depth]

/-- The two actual range-preparation words obey symbolic width-only costs. -/
public theorem exponentPreparationCircuit_widthBounds
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (exponentPreparationCircuit P oracles).eventCost ≤ 22 * orderWidth P ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (exponentPreparationCircuit P oracles).eventCost ≤ 6 * orderWidth P ∧
      (exponentPreparationCircuit P oracles).evaluatedEventDepth (fun _ => 1) ≤
        10 * orderWidth P + 1 := by
  rcases OrderPreparation.orderPreparation_scalarBounds P
      (OrderExpansion.canonical P.order P.order_pos) with ⟨one, cnot, depth⟩
  change OrderPreparation.singleQubitCount (OrderExpansion.canonical P.order P.order_pos) ≤
    11 * orderWidth P at one
  change OrderPreparation.cnotCount (OrderExpansion.canonical P.order P.order_pos) ≤
    3 * orderWidth P at cnot
  change OrderPreparation.unitDepth (OrderExpansion.canonical P.order P.order_pos) ≤
    10 * orderWidth P + 1 at depth
  constructor
  · rw [exponentPreparationCircuit_singleQubit_count P oracles]
    omega
  constructor
  · rw [exponentPreparationCircuit_cnot_count P oracles]
    omega
  · rw [exponentPreparationCircuit_unit_depth P oracles]
    exact depth

/-- Two actual inverse QFT words on the exponent registers. -/
def exponentReadoutCircuit (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (orderWidth P + orderWidth P)).canonicalPlacement.layout :=
  pairConsecutiveCircuit (QuantumFourierTransform.Native.inverseCircuit oracles (orderWidth P))

/-- The readout implements exactly the tensor of the two negative-phase Fourier transforms. -/
theorem exponentReadoutCircuit_binaryMatrix
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    (exponentReadoutCircuit P oracles).binaryMatrix =
      (star (QFTOperator (orderWidth P))).tensor
        (star (QFTOperator (orderWidth P))) := by
  rw [exponentReadoutCircuit, pairConsecutiveCircuit_binaryMatrix]
  have fourier := QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
    oracles (orderWidth P)
  change (QuantumFourierTransform.Native.onBinaryLabels
      (QuantumFourierTransform.Native.inverseCircuit oracles (orderWidth P))).tensor
      (QuantumFourierTransform.Native.onBinaryLabels
        (QuantumFourierTransform.Native.inverseCircuit oracles (orderWidth P))) = _
  rw [fourier]

/-- Exact native-coordinate counts of both inverse QFT words. -/
theorem exponentReadoutCircuit_event_count
    (P : KnownOrderProblem G) (oracles : OracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model oracles)) :
    ResourcePool.count event (exponentReadoutCircuit P oracles).eventCost =
      2 * ((orderWidth P + 3 * (orderWidth P).choose 2) *
          (if .gate .singleQubit = event then 1 else 0) +
        (2 * (orderWidth P).choose 2 + 3 * (orderWidth P / 2)) *
          (if .gate .cnot = event then 1 else 0)) := by
  rw [exponentReadoutCircuit, pairConsecutiveCircuit_eventCost, ResourcePool.count_add]
  exact (congrArg (fun count : Nat => count + count)
    (QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count
      oracles event (orderWidth P))).trans (by omega)

/-- Neither inverse QFT word introduces a Toffoli gate. -/
theorem exponentReadoutCircuit_toffoli_count
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (exponentReadoutCircuit P oracles).eventCost = 0 := by
  rw [exponentReadoutCircuit_event_count]
  simp

/-- Parallel inverse readout has one generated inverse QFT word's depth. -/
theorem exponentReadoutCircuit_unit_depth
    (P : KnownOrderProblem G) (oracles : OracleModel := .empty) :
    (exponentReadoutCircuit P oracles).evaluatedEventDepth (fun _ => 1) =
      orderWidth P + 5 * (orderWidth P).choose 2 + 3 * (orderWidth P / 2) := by
  rw [exponentReadoutCircuit, pairConsecutiveCircuit_evaluatedEventDepth]
  exact QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth
    oracles (orderWidth P)

end

end QuantumAlg.FiniteCyclicDLP.ConcreteCircuitAccess
