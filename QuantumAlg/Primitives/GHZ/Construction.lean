/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

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
- The circuit factors use the qubit groupings `1+2`, `2+1`, `1+2`; the
  index types all reduce to `Fin (2^3)` definitionally.

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

/-- The first GHZ layer applies `H` on physical qubit zero. -/
def hadamardLayer : UnitaryCircuit (Qubits 3) :=
  let rest := UnitaryCircuit.identity (Qubits 2) [1, 2] (by simp)
  UnitaryCircuit.tensorQubits H rest
    { left_nodup := H.physical_idx_nodup
      right_nodup := rest.physical_idx_nodup
      disjoint := by
        change List.Disjoint [0] [1, 2]
        simp }

/-- The second GHZ layer applies CNOT from physical qubit zero to one. -/
def firstCnotLayer : UnitaryCircuit (Qubits 3) :=
  let rest := UnitaryCircuit.identity (Qubits 1) [2] (by simp)
  UnitaryCircuit.tensorQubits CNOT rest
    { left_nodup := CNOT.physical_idx_nodup
      right_nodup := rest.physical_idx_nodup
      disjoint := by
        change List.Disjoint [0, 1] [2]
        simp }

/-- The final GHZ layer applies CNOT from physical qubit one to two. -/
def secondCnotLayer : UnitaryCircuit (Qubits 3) :=
  let leading := UnitaryCircuit.identity (Qubits 1) [0] (by simp)
  let shifted := UnitaryCircuit.shiftPhysicalIdx 1 CNOT
  UnitaryCircuit.tensorQubits leading shifted
    { left_nodup := leading.physical_idx_nodup
      right_nodup := shifted.physical_idx_nodup
      disjoint := by
        change List.Disjoint [0] [1, 2]
        simp }

@[simp]
theorem hadamardLayer_matrix :
    hadamardLayer.matrix =
      UnitaryOperator.tensor HOp (1 : UnitaryOperator (Qubits 2)) := by
  unfold hadamardLayer
  rw [UnitaryCircuit.tensorQubits_matrix, H_matrix]
  congr 1

@[simp]
theorem firstCnotLayer_matrix :
    firstCnotLayer.matrix =
      UnitaryOperator.tensor CNOTOp (1 : UnitaryOperator (Qubits 1)) := by
  unfold firstCnotLayer
  rw [UnitaryCircuit.tensorQubits_matrix, CNOT_matrix]
  congr 1

@[simp]
theorem secondCnotLayer_matrix :
    secondCnotLayer.matrix =
      UnitaryOperator.tensor (1 : UnitaryOperator (Qubits 1)) CNOTOp := by
  unfold secondCnotLayer
  rw [UnitaryCircuit.tensorQubits_matrix, UnitaryCircuit.shiftPhysicalIdx_matrix, CNOT_matrix]
  congr 1

/-- Typed three-layer GHZ preparation circuit. -/
public def circuit : UnitaryCircuit (Qubits 3) :=
  UnitaryCircuit.seq
    (UnitaryCircuit.seq hadamardLayer firstCnotLayer)
    secondCnotLayer

/-- GHZ preparation input state. -/
public def input : NormalizedVector (Qubits 3) :=
  ket0.tensor (ket0.tensor ket0)

/-- Raw-vector calculation underlying the normalized preparation theorem. -/
private theorem ghzPreparation_coe :
    UnitaryCircuit.applyVec circuit input = (ghz : HilbertVector (Qubits 3)) := by
  rw [circuit, input, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq]
  simp only [UnitaryCircuit.applyVec]
  rw [hadamardLayer_matrix, firstCnotLayer_matrix, secondCnotLayer_matrix]
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
    UnitaryCircuit.applyNormalized circuit input = ghz := by
  apply NormalizedVector.ext
  intro i
  change UnitaryCircuit.applyVec circuit input i = (ghz : HilbertVector (Qubits 3)) i
  exact congrArg (fun ψ : HilbertVector (Qubits 3) => ψ i) ghzPreparation_coe


/-- The strict event pool is derived from the same three atoms used by `ghzPreparation_eq`. -/
@[simp] theorem circuit_eventCost :
    circuit.eventCost =
      ResourcePool.singleton (Gate.atomicEvent (.builtin "hadamard")) +
        ResourcePool.singleton (Gate.atomicEvent (.builtin "cnot")) +
          ResourcePool.singleton (Gate.atomicEvent (.builtin "cnot")) := by
  simp [circuit, hadamardLayer, firstCnotLayer, secondCnotLayer,
    Gate.atomicEventCost]

/-- Unit duration per strict event gives the three sequential GHZ layers. -/
@[simp] theorem circuit_evaluatedEventDepth_of_one :
    circuit.evaluatedEventDepth (fun _event => 1) = 3 := by
  rfl

end GHZStatePreparation

/-- The GHZ state is normalized. -/
theorem norm_ghz : ‖ghz‖ = 1 := ghz.norm_eq_one

end

end QuantumAlg

end
