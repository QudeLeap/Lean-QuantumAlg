/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Attempt.Unitary
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Concrete
import all QuantumAlg.Algorithms.EllipticCurve.DLP.OrderPreparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.BornBridge.State

/-!
# Literal ECDLP preparation and the original Born vector

Both literal order-expansion branches produce the same exact final vector
as the analytical range preparation. The intrinsic point bank, counted
group action and both inverse Fourier transforms are unchanged. These
equalities concern states and do not replace the literal circuit's cost.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.GateLevelAttempt

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The explicit preparation produces the exact range-uniform pair consumed
by the established concrete Born analysis. -/
theorem preparation_apply_input (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    (preparationCircuit I B).applyVec
        ((inputPreparation I).normalized :
          HilbertVector (Qubits (Layout.totalQubits I))) =
      FiniteCyclicDLP.Concrete.BornBridge.preparedVec (circuitAccess I A) := by
  change (preparationCircuit I B).applyVec
      (NormalizedVector.ket
        (R := Qubits (Layout.totalQubits I))
        (basisIndex I 0 0 1) : HilbertVector (Qubits (Layout.totalQubits I))) = _
  let tailIndex : Fin (2 ^ Layout.pointWidth E) :=
    ⟨((Layout.pointEncoding E).encode 1).val, by
      simpa only [Layout.pointEncoding_width] using
        ((Layout.pointEncoding E).encode 1).isLt⟩
  have basisIndex_eq :
      basisIndex I 0 0 1 =
        prodEquiv
          (prodEquiv
            ((0 : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I))),
              (0 : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))),
            tailIndex) := by
    apply Fin.ext
    rfl
  rw [basisIndex_eq]
  rw [← NormalizedVector.tensor_ket, ← NormalizedVector.tensor_ket]
  change (preparationCircuit I B).matrix.applyVec
      (HilbertVector.tensor
        (HilbertVector.tensor
          (NormalizedVector.ket
            (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0 :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I))))
          (NormalizedVector.ket
            (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0 :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I)))))
        (NormalizedVector.ket
          (R := Qubits (Layout.pointWidth E))
          tailIndex :
          HilbertVector (Qubits (Layout.pointWidth E)))) =
      HilbertVector.tensor
        (HilbertVector.tensor
          (FiniteCyclicDLP.Concrete.BornBridge.exponentState (problem I) :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I))))
          (FiniteCyclicDLP.Concrete.BornBridge.exponentState (problem I) :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I)))))
        (NormalizedVector.ket
          (R := Qubits (Layout.pointWidth E)) tailIndex :
          HilbertVector (Qubits (Layout.pointWidth E)))
  rw [preparationCircuit, extendWithPoint, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((exponentPreparationCircuit I B).applyVec
        (HilbertVector.tensor
          (NormalizedVector.ket
            (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0 :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I))))
          (NormalizedVector.ket
            (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0 :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I))))))
      ((UnitaryCircuit.identity (Qubits (Layout.pointWidth E))
        (List.range'
          (FiniteCyclicDLP.orderWidth (problem I) +
            FiniteCyclicDLP.orderWidth (problem I))
          (Layout.pointWidth E)) List.nodup_range').applyVec
        (NormalizedVector.ket
          (R := Qubits (Layout.pointWidth E)) tailIndex :
          HilbertVector (Qubits (Layout.pointWidth E)))) = _
  rw [UnitaryCircuit.applyVec_identity]
  congr 1
  rw [exponentPreparationCircuit]
  rw [FiniteCyclicDLP.Canonical.pairConsecutiveCircuit,
    UnitaryCircuit.applyVec, UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((B.paddedPreparation (problem I)).applyVec
          (NormalizedVector.ket
            (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0 :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I)))))
      ((B.paddedPreparation (problem I)).applyVec
          (NormalizedVector.ket
            (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0 :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I))))) = _
  have leftPreparation := congrArg
    (fun state : NormalizedVector
        (Qubits (FiniteCyclicDLP.orderWidth (problem I))) =>
      (state : HilbertVector
        (Qubits (FiniteCyclicDLP.orderWidth (problem I)))))
    (B.paddedPreparation_apply_zero (problem I))
  have leftPreparationVec :
      (B.paddedPreparation (problem I)).applyVec
          (NormalizedVector.ket
            (R := Qubits (FiniteCyclicDLP.orderWidth (problem I))) 0 :
            HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I)))) =
        (FiniteCyclicDLP.Concrete.BornBridge.exponentState (problem I) :
          HilbertVector (Qubits (FiniteCyclicDLP.orderWidth (problem I))) ) := by
    simpa only [UnitaryCircuit.applyNormalized_coe,
      FiniteCyclicDLP.Concrete.BornBridge.exponentState,
      FiniteCyclicDLP.Canonical.BornBridge.exponentState] using leftPreparation
  rw [leftPreparationVec]

/-- On the sealed input, replacing the analytical range leaves by the literal
preparation changes no final normalized state. -/
theorem quantumCircuit_applyNormalized_eq_analytical
    (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    (quantumCircuit I B A).applyNormalized (inputPreparation I).normalized =
      (circuitAccess I A).fullCircuit.applyNormalized
        (circuitAccess I A).preparation.normalized := by
  apply NormalizedVector.ext
  intro index
  have gatePreparation := preparation_apply_input I B A
  have analyticalPreparation :=
    FiniteCyclicDLP.Concrete.BornBridge.preparation_apply_input
      (circuitAccess I A)
  have preparationEquality := gatePreparation.trans analyticalPreparation.symm
  have finalEqualityOld :
      (quantumCircuit I B A).applyVec
          ((inputPreparation I).normalized :
            HilbertVector (Qubits (Layout.totalQubits I))) =
        (circuitAccess I A).fullCircuit.applyVec
          ((circuitAccess I A).preparation.normalized :
            HilbertVector (Qubits (circuitAccess I A).totalQubits)) := by
    rw [quantumCircuit, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq,
      FiniteCyclicDLP.ConcreteCircuitAccess.fullCircuit,
      UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq]
    exact congrArg (circuitAccess I A).readoutCircuit.applyVec
      (congrArg (circuitAccess I A).oracleCircuit.applyVec preparationEquality)
  change
    (quantumCircuit I B A).applyVec
        ((inputPreparation I).normalized :
          HilbertVector (Qubits (Layout.totalQubits I))) index =
      (circuitAccess I A).fullCircuit.applyVec
        ((circuitAccess I A).preparation.normalized :
          HilbertVector (Qubits (circuitAccess I A).totalQubits)) index
  exact congrArg (fun state => state index) finalEqualityOld

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.GateLevelAttempt
