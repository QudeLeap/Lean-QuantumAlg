/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Initialization
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Semantics
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero

/-!
# Independent prepared-query-Fourier state of intrinsic ECDLP sampling

The source state depends only on the original exact range state, granted
group-action operator and inverse Fourier matrices. It is independent of the
chosen binary expansion and of the runtime interpreter.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original source's exact prepared-query-inverse-Fourier state. -/
public def sourceState (I : ECDLPInstance E) (A : Access I) :
    NormalizedVector (Qubits (Layout.totalQubits I)) :=
  (((star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I)))).tensor
    (star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I))))).tensor
      (1 : UnitaryOperator (Qubits (Layout.pointWidth E)))).apply
        (A.operator.apply (preparedState I))

/-- The actual initializer and sampling word produce that same source state from zero. -/
public theorem initializedCircuit_apply_zero (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    ((initializer I A).seq (circuit I A expansion)).binaryMatrix.apply
        (NormalizedVector.ket (R := Qubits (Layout.totalQubits I)) 0) = sourceState I A := by
  rw [UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, apply_mul,
    initializer_apply_zero, circuit_apply_input]
  rfl

/-- The source's physical zero label is exactly binary zero. -/
public theorem binary_zero (I : ECDLPInstance E) :
    (QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)) (layout I).zeroLabel = 0 := by
  exact BinaryBasis.bigEndianEquiv_zero (Layout.totalQubits I)

/-- Each physical zero column is the exact source amplitude, with its phase retained. -/
public theorem initializedCircuit_zero_amplitude (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) (row : (layout I).Basis) :
    ((initializer I A).seq (circuit I A expansion)).matrix row (layout I).zeroLabel =
      sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)) row) := by
  have column := congrArg (fun state => state
    ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)) row))
      (initializedCircuit_apply_zero I A expansion)
  change ((initializer I A).seq (circuit I A expansion)).binaryMatrix.applyVec
      (NormalizedVector.ket (R := Qubits (Layout.totalQubits I)) 0 :
        HilbertVector (Qubits (Layout.totalQubits I)))
        ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)) row) = _ at column
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at column
  change ((initializer I A).seq (circuit I A expansion)).matrix
      ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm
        ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)) row))
      ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm 0) = _ at column
  rw [Equiv.symm_apply_apply,
    ← binary_zero I, Equiv.symm_apply_apply] at column
  exact column

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
