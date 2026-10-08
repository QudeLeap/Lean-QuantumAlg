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
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# GHZ state preparation

The three-qubit GHZ state `(|000⟩ + |111⟩)/√2`, prepared from `|000⟩` by a
Hadamard on qubit 0 followed by a CNOT cascade:

`(I ⊗ CNOT) · (CNOT ⊗ I) · (H ⊗ I ⊗ I) · |000⟩ = (|000⟩ + |111⟩)/√2`.

States of this multipartite family are due to Greenberger, Horne and
Zeilinger (1989), whose original argument uses a four-particle spin state
(reprinted as arXiv:0712.0921). The three-qubit form and the name "GHZ
state" are standard textbook material (e.g. Nielsen and Chuang 2000). The
unnormalized states `|000⟩ ± |111⟩` appear as
the code blocks of Shor's 9-qubit code [dW19, qcnotes.tex:7456-7459], and a
locally-equivalent three-qubit state powers Mermin's game
[dW19, qcnotes.tex:6667].

## Conventions

- Big-endian basis labelling as in `Core/Base/State/`: `|000⟩ = ket 0` and
  `|111⟩ = ket 7`.
- Qubit 0 carries the Hadamard and controls the first CNOT (target
  qubit 1); qubit 1 controls the second CNOT (target qubit 2).
- The native CNOT is placed on the first or last adjacent pair of the
  original three physical qubits, without changing their binary order.

## Main results

- `QuantumAlg.ghz` — the three-qubit GHZ state, as a `NormalizedVector (Qubits 3)`.
- `QuantumAlg.GHZStatePreparation.circuit` — the typed preparation circuit.
- `QuantumAlg.GHZStatePreparation.ghzPreparation_eq` — the preparation-circuit equality.
- `QuantumAlg.norm_ghz` — the GHZ state is normalized.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

/-- The metadata-free normalized GHZ state. -/
public def ghz : NormalizedVector (Qubits 3) :=
  NormalizedVector.ofVector
    (invSqrt2 •
      (((ket 0 : NormalizedVector (Qubits 3)) +
        (ket 7 : NormalizedVector (Qubits 3)) :
        HilbertVector (Qubits 3))))
    (by
      rw [norm_smul, norm_invSqrt2]
      have h :
          ‖(((ket 0 : NormalizedVector (Qubits 3)) +
            (ket 7 : NormalizedVector (Qubits 3)) :
            HilbertVector (Qubits 3)))‖ = Real.sqrt 2 := by
        rw [EuclideanSpace.norm_eq]
        have hsum : ∑ i,
            ‖(((ket 0 : NormalizedVector (Qubits 3)) +
              (ket 7 : NormalizedVector (Qubits 3)) :
              HilbertVector (Qubits 3)) i)‖ ^ 2 = 2 := by
          refine (Fin.sum_univ_eight (f := fun i : Fin (2 ^ 3) =>
            ‖(((ket 0 : NormalizedVector (Qubits 3)) +
              (ket 7 : NormalizedVector (Qubits 3)) :
              HilbertVector (Qubits 3)) i)‖ ^ 2)).trans ?_
          simp +decide [NormalizedVector.ket_apply]
          all_goals norm_num
        rw [hsum]
      rw [h, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))])

/-- The GHZ state as its explicit computational-basis superposition. -/
@[simp]
theorem ghz_coe :
    (ghz : HilbertVector (Qubits 3)) =
      invSqrt2 •
        (((ket 0 : NormalizedVector (Qubits 3)) +
          (ket 7 : NormalizedVector (Qubits 3)) :
          HilbertVector (Qubits 3))) :=
  rfl

namespace GHZStatePreparation

/-- The original three physical qubits in big-endian binary order. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 3 :=
  (QuantumSignature.qubits 3).canonicalPlacement.layout

/-- The first GHZ layer applies one native `H` on physical qubit zero. -/
def hadamardLayer : UnitaryCircuit AlgorithmGate.model .empty layout :=
  Gate.singleQubitAt layout .empty HOp 0 rfl

private def localCnot : UnitaryCircuit AlgorithmGate.model .empty
    (QuantumSignature.qubits 2).canonicalPlacement.layout :=
  .native (GateModel.Application.canonical AlgorithmGate.model .cnot)

private theorem localCnot_binaryMatrix : localCnot.binaryMatrix = CNOTOp := by
  unfold UnitaryCircuit.binaryMatrix localCnot
  rw [UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm CNOTOp) = CNOTOp
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv 2).symm _

/-- The second GHZ layer applies CNOT from physical qubit zero to one. -/
def firstCnotLayer : UnitaryCircuit AlgorithmGate.model .empty layout :=
  UnitaryCircuit.onBinaryPrefix 1 localCnot

/-- The final GHZ layer applies CNOT from physical qubit one to two. -/
def secondCnotLayer : UnitaryCircuit AlgorithmGate.model .empty layout :=
  UnitaryCircuit.onBinarySuffix 1 localCnot

@[simp]
theorem hadamardLayer_matrix :
    hadamardLayer.binaryMatrix =
      UnitaryOperator.tensor HOp (1 : UnitaryOperator (Qubits 2)) := by
  exact Gate.singleQubitAt_first_binaryMatrix .empty 2 HOp

@[simp]
theorem firstCnotLayer_matrix :
    firstCnotLayer.binaryMatrix =
      UnitaryOperator.tensor CNOTOp (1 : UnitaryOperator (Qubits 1)) := by
  rw [firstCnotLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    localCnot_binaryMatrix]

@[simp]
theorem secondCnotLayer_matrix :
    secondCnotLayer.binaryMatrix =
      UnitaryOperator.tensor (1 : UnitaryOperator (Qubits 1)) CNOTOp := by
  rw [secondCnotLayer, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    localCnot_binaryMatrix]

/-- Typed three-layer GHZ preparation circuit. -/
public def circuit : UnitaryCircuit AlgorithmGate.model .empty layout :=
  (hadamardLayer.seq firstCnotLayer).seq secondCnotLayer

private theorem circuit_binaryMatrix :
    circuit.binaryMatrix =
      ((1 : UnitaryOperator (Qubits 1)).tensor CNOTOp) *
        (CNOTOp.tensor (1 : UnitaryOperator (Qubits 1))) *
          (HOp.tensor (1 : UnitaryOperator (Qubits 2))) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    hadamardLayer_matrix, firstCnotLayer_matrix, secondCnotLayer_matrix]
  simp only [mul_assoc]

/-- GHZ preparation input state. -/
public def input : NormalizedVector (Qubits 3) :=
  ket0.tensor (ket0.tensor ket0)

/-- Raw-vector calculation underlying the normalized preparation theorem. -/
private theorem ghzPreparation_coe :
    circuit.binaryMatrix.applyVec input = (ghz : HilbertVector (Qubits 3)) := by
  rw [circuit_binaryMatrix, input, UnitaryOperator.mul_applyVec,
    UnitaryOperator.mul_applyVec]
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp +decide [ghz_coe, HOp, CNOTOp,
      UnitaryOperator.ofPerm, UnitaryOperator.ofMatrix,
      ket0, NormalizedVector.ket, HilbertVector.tensor, prodEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.one_apply, Fin.sum_univ_eight]

/-- **GHZ state preparation**: the typed cascade circuit turns `|000⟩` into
the GHZ state. -/
public theorem ghzPreparation_eq :
    circuit.binaryMatrix.apply input = ghz := by
  apply NormalizedVector.ext
  intro i
  change circuit.binaryMatrix.applyVec input i = (ghz : HilbertVector (Qubits 3)) i
  exact congrArg (fun ψ : HilbertVector (Qubits 3) => ψ i) ghzPreparation_coe


/-- The strict event pool is derived from the same three atoms used by `ghzPreparation_eq`. -/
@[simp] theorem circuit_eventCost :
    circuit.eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) +
          ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) := by
  simp only [circuit, UnitaryCircuit.seq_eventCost,
    firstCnotLayer, secondCnotLayer,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost,
    hadamardLayer, Gate.singleQubitAt_eventCost]
  rfl

/-- Unit duration per strict event gives the three sequential GHZ layers. -/
@[simp] theorem circuit_evaluatedEventDepth_of_one :
    circuit.evaluatedEventDepth (fun _event => 1) = 3 := by
  simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq,
    firstCnotLayer, secondCnotLayer,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth]
  rfl

end GHZStatePreparation

/-- The GHZ state is normalized. -/
theorem norm_ghz : ‖ghz‖ = 1 := ghz.norm_eq_one

end

end QuantumAlg

end
