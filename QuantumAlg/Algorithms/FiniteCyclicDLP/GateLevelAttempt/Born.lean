/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Access.Concrete
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.BornBridge.State

/-!
# Literal finite-cyclic preparation and the concrete Born state

The two original Algorithm-1 preparations produce the range-uniform pair
used by the concrete Born analysis. The original encoded group query and
both inverse Fourier transforms then give the same final normalized state.
These state equalities leave all resource accounting on the literal circuit.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The literal preparation produces the concrete range-uniform pair and
retains the original encoded group identity in the third register. -/
theorem preparation_apply_input_eq_concrete (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (preparationCircuit P B).applyVec
        ((inputPreparation P B ux).normalized :
          HilbertVector (Qubits (totalQubits P))) =
      Concrete.BornBridge.preparedVec (circuitAccess P B ux) := by
  change (preparationCircuit P B).applyVec
      (NormalizedVector.ket (R := Qubits (totalQubits P))
        (prodEquiv (prodEquiv ((0 : Fin (2 ^ orderWidth P)),
          (0 : Fin (2 ^ orderWidth P))), ux.encode 1)) :
        HilbertVector (Qubits (totalQubits P))) = _
  rw [← NormalizedVector.tensor_ket, ← NormalizedVector.tensor_ket]
  change (preparationCircuit P B).matrix.applyVec
      (HilbertVector.tensor
        (HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P)))
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P))))
        (NormalizedVector.ket (R := Qubits (orderWidth P)) (ux.encode 1) :
          HilbertVector (Qubits (orderWidth P)))) =
      HilbertVector.tensor
        (HilbertVector.tensor
          (Concrete.BornBridge.exponentState P : HilbertVector (Qubits (orderWidth P)))
          (Concrete.BornBridge.exponentState P : HilbertVector (Qubits (orderWidth P))))
        (NormalizedVector.ket (R := Qubits (orderWidth P)) (ux.encode 1) :
          HilbertVector (Qubits (orderWidth P)))
  rw [preparationCircuit, withGroupWorkspace, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((exponentPreparationCircuit P B).applyVec
        (HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P)))
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P)))))
      ((UnitaryCircuit.identity (Qubits (orderWidth P))
        (List.range' (orderWidth P + orderWidth P) (orderWidth P))
        List.nodup_range').applyVec
          (NormalizedVector.ket (R := Qubits (orderWidth P)) (ux.encode 1) :
            HilbertVector (Qubits (orderWidth P)))) = _
  rw [UnitaryCircuit.applyVec_identity]
  congr 1
  rw [exponentPreparationCircuit, pairConsecutiveCircuit,
    UnitaryCircuit.applyVec, UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((paddedPreparation P B).applyVec
        (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
          HilbertVector (Qubits (orderWidth P))))
      ((paddedPreparation P B).applyVec
        (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
          HilbertVector (Qubits (orderWidth P)))) = _
  have preparationVec := congrArg
    (fun state : NormalizedVector (Qubits (orderWidth P)) =>
      (state : HilbertVector (Qubits (orderWidth P))))
    (paddedPreparation_apply_zero P B)
  have preparationEquality :
      (paddedPreparation P B).applyVec
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P))) =
        (Concrete.BornBridge.exponentState P : HilbertVector (Qubits (orderWidth P))) := by
    simpa only [UnitaryCircuit.applyNormalized_coe, Concrete.BornBridge.exponentState,
      Canonical.BornBridge.exponentState] using preparationVec
  rw [preparationEquality]

/-- On its original basis input, the complete literal circuit gives the
concrete Born state for the same encoded group action. -/
theorem quantumCircuit_applyNormalized_eq_concrete (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (quantumCircuit P B ux).applyNormalized (inputPreparation P B ux).normalized =
      Concrete.BornBridge.evolvedState (circuitAccess P B ux) := by
  apply NormalizedVector.ext
  intro index
  have literalPreparation := preparation_apply_input_eq_concrete P B ux
  have concretePreparation := Concrete.BornBridge.preparation_apply_input
    (circuitAccess P B ux)
  have preparationEquality := literalPreparation.trans concretePreparation.symm
  have finalEquality :
      (quantumCircuit P B ux).applyVec
          ((inputPreparation P B ux).normalized : HilbertVector (Qubits (totalQubits P))) =
        (circuitAccess P B ux).fullCircuit.applyVec
          ((circuitAccess P B ux).preparation.normalized :
            HilbertVector (Qubits (circuitAccess P B ux).totalQubits)) := by
    rw [quantumCircuit, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq,
      ConcreteCircuitAccess.fullCircuit, UnitaryCircuit.applyVec_seq,
      UnitaryCircuit.applyVec_seq]
    exact congrArg (circuitAccess P B ux).readoutCircuit.applyVec
      (congrArg (circuitAccess P B ux).oracleCircuit.applyVec preparationEquality)
  change (quantumCircuit P B ux).applyVec
      ((inputPreparation P B ux).normalized : HilbertVector (Qubits (totalQubits P))) index =
    (circuitAccess P B ux).fullCircuit.applyVec
      ((circuitAccess P B ux).preparation.normalized :
        HilbertVector (Qubits (circuitAccess P B ux).totalQubits)) index
  exact congrArg (fun state => state index) finalEquality

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt
