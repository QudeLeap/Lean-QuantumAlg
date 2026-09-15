/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Gates
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

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
theorem bell_coe :
    (bell : HilbertVector (Qubits 2)) =
      invSqrt2 •
        (((ket 0 : NormalizedVector (Qubits 2)) +
          (ket 3 : NormalizedVector (Qubits 2)) :
          HilbertVector (Qubits 2))) :=
  rfl

/-- The Bell state in per-qubit tensor form: `(|0⟩⊗|0⟩ + |1⟩⊗|1⟩)/√2`. -/
theorem bell_eq_tensor :
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

/-- The first Bell layer applies `H` on physical qubit zero and identity on
physical qubit one. -/
def hadamardLayer : UnitaryCircuit (Qubits 2) :=
  let rest := UnitaryCircuit.identity (Qubits 1) [] (by simp)
  UnitaryCircuit.tensorQubits H rest
    { left_nodup := H.physical_idx_nodup
      right_nodup := rest.physical_idx_nodup
      disjoint := by
        change List.Disjoint [0] []
        simp }

/-- Bell preparation as two typed circuit atoms over one certified layout. -/
public def circuit : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.seq hadamardLayer CNOT

/-- Bell preparation input state `|00⟩`. -/
public def input : NormalizedVector (Qubits 2) :=
  ket0.tensor ket0

/-- Raw-vector calculation underlying the normalized preparation theorem. -/
private theorem bellPreparation_coe :
    UnitaryCircuit.applyVec circuit input = (bell : HilbertVector (Qubits 2)) := by
  rw [circuit, UnitaryCircuit.applyVec_seq]
  have hLayer : hadamardLayer.matrix =
      UnitaryOperator.tensor HOp (1 : UnitaryOperator (Qubits 1)) := by
    unfold hadamardLayer
    rw [UnitaryCircuit.tensorQubits_matrix]
    rw [H_matrix]
    congr 1
  simp only [UnitaryCircuit.applyVec]
  rw [CNOT_matrix, hLayer]
  change CNOTOp.applyVec
      ((HOp.tensor (1 : UnitaryOperator (Qubits 1))).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1)))) = _
  rw [UnitaryOperator.tensor_applyVec_tensor]
  have hH : HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) :=
    congrArg (fun ψ : NormalizedVector (Qubits 1) =>
      (ψ : HilbertVector (Qubits 1))) H_apply_ket0
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
        (ψ : HilbertVector (Qubits 2))) CNOT_apply_ket0_tensor_ket0
      simpa only [UnitaryCircuit.applyNormalized_coe, UnitaryCircuit.applyVec, CNOT_matrix,
        NormalizedVector.coe_tensor] using h
  have hC10 : CNOTOp.applyVec
      (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket1 : HilbertVector (Qubits 1)) :=
    by
      have h := congrArg (fun ψ : NormalizedVector (Qubits 2) =>
        (ψ : HilbertVector (Qubits 2))) CNOT_apply_ket1_tensor_ket0
      simpa only [UnitaryCircuit.applyNormalized_coe, UnitaryCircuit.applyVec, CNOT_matrix,
        NormalizedVector.coe_tensor] using h
  rw [bell_eq_tensor, ketPlus_coe, HilbertVector.smul_tensor,
    HilbertVector.add_tensor, UnitaryOperator.applyVec_smul,
    UnitaryOperator.applyVec_add,
    hC00, hC10]
  rfl

/-- Bell-state preparation: the typed circuit turns `|00⟩` into the Bell state. -/
public theorem bellPreparation_eq :
    UnitaryCircuit.applyNormalized circuit input = bell := by
  apply NormalizedVector.ext
  intro i
  change UnitaryCircuit.applyVec circuit input i = (bell : HilbertVector (Qubits 2)) i
  exact congrArg (fun ψ : HilbertVector (Qubits 2) => ψ i) bellPreparation_coe


/-- Bell preparation exposes one literal Hadamard and one literal CNOT event. -/
@[simp] theorem circuit_eventCost :
    circuit.eventCost =
      ResourcePool.singleton (Gate.atomicEvent (.builtin "hadamard")) +
        ResourcePool.singleton (Gate.atomicEvent (.builtin "cnot")) := by
  simp [circuit, hadamardLayer, Gate.atomicEventCost]

/-- Unit duration per strict event gives the two sequential Bell layers. -/
@[simp] theorem circuit_evaluatedEventDepth_of_one :
    circuit.evaluatedEventDepth (fun _event => 1) = 2 := by
  simp [circuit, hadamardLayer, UnitaryCircuit.evaluatedEventDepth,
    Gate.H_eventDepth, Gate.CNOT_eventDepth, Gate.atomicEventDepth]

end BellStatePreparation

/-- The Bell state is normalized by construction. -/
theorem norm_bell : ‖bell‖ = 1 := bell.norm_eq_one

end

end QuantumAlg

end
