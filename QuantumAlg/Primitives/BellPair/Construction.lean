/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
public import QuantumAlg.Components.Kets
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Hadamard.Action
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Bell pair (EPR pair) and its preparation

The Bell state (EPR-pair) `(|00⟩ + |11⟩)/√2` [dW19, qcnotes.tex:622] is
prepared from `|00⟩` by a Hadamard on qubit 0 followed by a CNOT with
control qubit 0:

`CNOT · (H ⊗ I) · |00⟩ = (|00⟩ + |11⟩)/√2`.

This is a `Primitives` module: the Bell pair is a reusable resource state, so
it lives below `Algorithms/` and is shared by the protocols that consume it
(superdense coding, teleportation) without those algorithms importing one
another. The exact normalized-vector equality is `bellPreparation_eq`.

## Main results

- `QuantumAlg.bell` — the Bell state, as a `NormalizedVector (Qubits 2)`.
- `QuantumAlg.BellStatePreparation.bellPreparation_eq` — the preparation-circuit equality.
- `QuantumAlg.bell_eq_tensor` — the Bell state in per-qubit tensor form.
- `QuantumAlg.norm_bell` — the Bell state is normalized.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

/-- The Bell state (EPR-pair) as a metadata-free normalized vector. -/
public def bell : NormalizedVector (Qubits 2) :=
  NormalizedVector.ofVector
    (invSqrt2 •
      (((ket 0 : NormalizedVector (Qubits 2)) +
        (ket 3 : NormalizedVector (Qubits 2)) :
        HilbertVector (Qubits 2))))
    (by
      rw [norm_smul, norm_invSqrt2]
      have h :
          ‖(((ket 0 : NormalizedVector (Qubits 2)) +
            (ket 3 : NormalizedVector (Qubits 2)) :
            HilbertVector (Qubits 2)))‖ = Real.sqrt 2 := by
        rw [EuclideanSpace.norm_eq]
        have hsum :
            ∑ i, ‖(((ket 0 : NormalizedVector (Qubits 2)) +
              (ket 3 : NormalizedVector (Qubits 2)) :
              HilbertVector (Qubits 2)) i)‖ ^ 2 = 2 := by
          refine (Fin.sum_univ_four (f := fun i : Fin (2 ^ 2) =>
            ‖(((ket 0 : NormalizedVector (Qubits 2)) +
              (ket 3 : NormalizedVector (Qubits 2)) :
              HilbertVector (Qubits 2)) i)‖ ^ 2)).trans ?_
          simp +decide [NormalizedVector.ket_apply]
          all_goals norm_num
        rw [hsum]
      rw [h, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))])

/-- The Bell state as its explicit computational-basis superposition. -/
@[simp]
lemma bell_coe :
    (bell : HilbertVector (Qubits 2)) =
      invSqrt2 •
        (((ket 0 : NormalizedVector (Qubits 2)) +
          (ket 3 : NormalizedVector (Qubits 2)) :
          HilbertVector (Qubits 2))) :=
  rfl

/-- The Bell state in per-qubit tensor form: `(|0⟩⊗|0⟩ + |1⟩⊗|1⟩)/√2`. -/
lemma bell_eq_tensor :
    (bell : HilbertVector (Qubits 2))
      = invSqrt2 • ((ket0.tensor ket0 + ket1.tensor ket1 : HilbertVector (Qubits 2))) := by
  rw [bell_coe, ket0, ket1, NormalizedVector.tensor_ket,
    NormalizedVector.tensor_ket]
  change
      invSqrt2 •
        (((ket 0 : NormalizedVector (Qubits 2)) +
          (ket 3 : NormalizedVector (Qubits 2)) :
          HilbertVector (Qubits 2))) =
      invSqrt2 •
        (((ket 0 : NormalizedVector (Qubits 2)) +
          (ket 3 : NormalizedVector (Qubits 2)) :
          HilbertVector (Qubits 2)))
  rfl

namespace BellStatePreparation

/-- The actual two-qubit physical layout, in its original big-endian order. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 2 := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- One native Hadamard on the first physical wire, with the second wire untouched. -/
def hadamardLayer : UnitaryCircuit AlgorithmGate.model .empty layout :=
  Gate.singleQubitAt layout .empty HOp 0 rfl

private def cnot : UnitaryCircuit AlgorithmGate.model .empty layout :=
  .native (GateModel.Application.canonical AlgorithmGate.model .cnot)

private lemma cnot_binaryMatrix
    (environment : OracleModel.empty.Interpretation) : (cnot.binaryMatrix environment)
    = CNOTOp := by
  unfold UnitaryCircuit.binaryMatrix cnot
  rw [UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm CNOTOp) = CNOTOp
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv 2).symm _

/-- Bell preparation executes one actual native Hadamard followed by one actual CNOT. -/
public def circuit : UnitaryCircuit AlgorithmGate.model .empty layout :=
  hadamardLayer.seq cnot

private lemma circuit_binaryMatrix (environment : OracleModel.empty.Interpretation) :
    (circuit.binaryMatrix environment) = CNOTOp * HOp.tensor (1 : UnitaryOperator (Qubits 1)) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, cnot_binaryMatrix,
    hadamardLayer]
  exact congrArg (fun op => CNOTOp * op)
    (Gate.singleQubitAt_first_binaryMatrix .empty 1 HOp environment)

/-- Bell preparation input state `|00⟩`. -/
public def input : NormalizedVector (Qubits 2) :=
  ket0.tensor ket0

/-- Raw-vector calculation underlying the normalized preparation theorem. -/
private lemma bellPreparation_coe (environment : OracleModel.empty.Interpretation) :
    (circuit.binaryMatrix environment).applyVec input = (bell : HilbertVector (Qubits 2)) := by
  rw [circuit_binaryMatrix, UnitaryOperator.mul_applyVec]
  change CNOTOp.applyVec
      ((HOp.tensor (1 : UnitaryOperator (Qubits 1))).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1)))) = _
  rw [UnitaryOperator.tensor_applyVec_tensor]
  have hH : HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) :=
    congrArg (fun ψ : NormalizedVector (Qubits 1) =>
      (ψ : HilbertVector (Qubits 1))) hadamardOperator_apply_ket0
  rw [hH, UnitaryOperator.one_applyVec]
  change CNOTOp.applyVec
      (HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1))) = (bell : HilbertVector (Qubits 2))
  have hC00 : CNOTOp.applyVec
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1)) :=
    by
      have h := congrArg (fun ψ : NormalizedVector (Qubits 2) =>
        (ψ : HilbertVector (Qubits 2))) (show CNOTOp.apply (ket0.tensor ket0) = ket0.tensor ket0 by
          simp only [CNOTOp, ket0, NormalizedVector.tensor_ket,
            UnitaryOperator.ofPerm_apply_ket]
          rfl)
      simpa only [UnitaryOperator.apply_coe, NormalizedVector.coe_tensor] using h
  have hC10 : CNOTOp.applyVec
      (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket1 : HilbertVector (Qubits 1)) :=
    by
      have h := congrArg (fun ψ : NormalizedVector (Qubits 2) =>
        (ψ : HilbertVector (Qubits 2))) (show CNOTOp.apply (ket1.tensor ket0) = ket1.tensor ket1 by
          simp only [CNOTOp, ket0, ket1, NormalizedVector.tensor_ket,
            UnitaryOperator.ofPerm_apply_ket]
          rfl)
      simpa only [UnitaryOperator.apply_coe, NormalizedVector.coe_tensor] using h
  rw [bell_eq_tensor, ketPlus_coe, HilbertVector.smul_tensor,
    HilbertVector.add_tensor, UnitaryOperator.applyVec_smul,
    UnitaryOperator.applyVec_add,
    hC00, hC10]
  rfl

/-- Bell-state preparation: the typed circuit turns `|00⟩` into the Bell state. -/
public lemma bellPreparation_eq (environment : OracleModel.empty.Interpretation) :
    (circuit.binaryMatrix environment).apply input = bell := by
  apply NormalizedVector.ext
  intro i
  change (circuit.binaryMatrix environment).applyVec input i = (bell : HilbertVector (Qubits 2)) i
  exact congrArg (fun ψ : HilbertVector (Qubits 2) => ψ i) (bellPreparation_coe environment)


/-- The actual native pool contains one single-qubit instruction and one CNOT. -/
@[simp] lemma circuit_eventCost :
    circuit.eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) := rfl

/-- The two actual gates share the first wire and have two sequential unit-duration layers. -/
@[simp] lemma circuit_evaluatedEventDepth_of_one :
    circuit.evaluatedEventDepth (fun _ => 1) = 2 := by rfl

end BellStatePreparation

/-- The Bell state is normalized by construction. -/
lemma norm_bell : ‖bell‖ = 1 := bell.norm_eq_one

end

end QuantumAlg

end
