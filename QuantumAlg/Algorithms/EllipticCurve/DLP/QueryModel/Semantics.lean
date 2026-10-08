/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Circuit
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Circuit
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Specification
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel.Matrix
public import QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact intrinsic semantics of the declared ECDLP sampling word

The query obeys the unchanged basis-action contract on every point, including
the identity. Native peripheral semantics retain the full state and phase.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

-- These pure data projections are the dependent parameter identities used below.
attribute [local implicit_reducible] problem Layout.pointEncoding

private theorem apply_mul {R : Register} (first second : UnitaryOperator R)
    (state : NormalizedVector R) :
    (first * second).apply state = first.apply (second.apply state) := by
  apply NormalizedVector.ext
  intro index
  change (first * second).applyVec (state : HilbertVector R) index =
    first.applyVec (second.applyVec (state : HilbertVector R)) index
  rw [UnitaryOperator.mul_applyVec]

/-- Binary coordinates expose the original granted group-action operator. -/
public theorem oracleLayer_binaryMatrix (I : ECDLPInstance E) (A : Access I) :
    (oracleLayer I A).binaryMatrix = A.operator := by
  have physical : (oracleLayer I A).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm
        A.operator := by
    rw [oracleLayer, UnitaryCircuit.query_matrix,
      OracleModel.Application.queryApplication_onPlacement_operator]
    apply Subtype.ext
    rfl
  rw [UnitaryCircuit.binaryMatrix, physical]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm A.operator

/-- Every encoded point obeys the original group action under the actual query. -/
public theorem oracleLayer_apply_ket (I : ECDLPInstance E) (A : Access I)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (workspace : GroupPoint E) :
    (oracleLayer I A).binaryMatrix.apply
        (NormalizedVector.ket (basisIndex I left right workspace)) =
      NormalizedVector.ket (basisIndex I left right
        (workspace * (problem I).toSourceScope.oracleMultiplier left.val right.val)) := by
  rw [oracleLayer_binaryMatrix]
  exact A.basisAction left right workspace

/-- Initial physical input contains zero exponents and the actual encoded curve identity. -/
public def inputState (I : ECDLPInstance E) : NormalizedVector (Qubits (Layout.totalQubits I)) :=
  ((NormalizedVector.ket (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0).tensor
    (NormalizedVector.ket (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0)).tensor
      (NormalizedVector.ket ((Layout.pointEncoding E).encode 1))

/-- The state prepared by the independent source range preparations. -/
public def preparedState (I : ECDLPInstance E) :
    NormalizedVector (Qubits (Layout.totalQubits I)) :=
  ((FiniteCyclicDLP.OrderPreparation.state (problem I)).tensor
    (FiniteCyclicDLP.OrderPreparation.state (problem I))).tensor
      (NormalizedVector.ket ((Layout.pointEncoding E).encode 1))

/-- The tensor input is exactly the original intrinsic identity basis label. -/
public theorem inputState_eq_ket (I : ECDLPInstance E) :
    inputState I = NormalizedVector.ket (basisIndex I 0 0 1) := by
  rw [inputState, NormalizedVector.tensor_ket, NormalizedVector.tensor_ket]
  rfl

/-- The actual two native preparations produce the exact source range state. -/
public theorem preparations_apply_input (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (preparations I A expansion).binaryMatrix.apply (inputState I) = preparedState I := by
  rw [preparations, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    UnitaryCircuit.parallelBinary_binaryMatrix, inputState,
    UnitaryOperator.tensor_apply_tensor, UnitaryOperator.tensor_apply_tensor,
    UnitaryOperator.one_apply,
    FiniteCyclicDLP.OrderPreparation.Native.circuit_apply_zero]
  rfl

/-- Both generated inverse QFTs realize the exact source inverse Fourier operator. -/
public theorem inverseQFTs_binaryMatrix (I : ECDLPInstance E) (A : Access I) :
    (inverseQFTs I A).binaryMatrix =
      ((star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I)))).tensor
        (star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I))))).tensor
          (1 : UnitaryOperator (Qubits (Layout.pointWidth E))) := by
  rw [inverseQFTs, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    UnitaryCircuit.parallelBinary_binaryMatrix]
  have Fourier := QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
    (model I A) (FiniteCyclicDLP.orderWidth (problem I))
  change (QuantumFourierTransform.Native.inverseCircuit (model I A)
    (FiniteCyclicDLP.orderWidth (problem I))).binaryMatrix =
      star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I))) at Fourier
  rw [Fourier]

/-- The complete actual sampling word has the original prepared-query-Fourier state. -/
public theorem circuit_apply_input (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (circuit I A expansion).binaryMatrix.apply (inputState I) =
      (((star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I)))).tensor
        (star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I))))).tensor
          (1 : UnitaryOperator (Qubits (Layout.pointWidth E)))).apply
            (A.operator.apply (preparedState I)) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, apply_mul,
    apply_mul, preparations_apply_input, oracleLayer_binaryMatrix,
    inverseQFTs_binaryMatrix]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
