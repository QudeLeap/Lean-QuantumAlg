/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Elementary.Laws
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Reindex

/-!
# Grover's actual owned input register

The input contains only a borrowed unit cell. A charged basis preparation
creates every owned search and required work qubit in zero. The executable
unitary contains the initial Hadamards and the k elementary Grover iterates
[dW19, qcnotes.tex:2783-2792]. Every physical identity and wire value is
preserved by the explicit preparation and binary-coordinate equivalences.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- The original zero-bit borrowed input, with no supplied quantum systems. -/
@[reducible] public def pre : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput ⟨0⟩ .unit (by decide)

theorem pre_systemCount : pre.systemCount = 0 := rfl

/-- The original n search positions, each of dimension two. -/
@[implicit_reducible]
def runtimeLayout (n : Nat) : QuantumLayout n :=
  (layout n).toQuantumLayout

theorem preparationFresh : (⟨1⟩ : StorageKey) ∉ pre.keys := by decide

theorem preparationDisjoint (n : Nat) :
    List.Disjoint (runtimeLayout n).identities pre.physicalIdx := by
  exact List.disjoint_nil_right _

/-- The complete context after allocating and preparing the owned search wires. -/
@[implicit_reducible]
def preparedContext (n : Nat) : RuntimeCtx .quantum :=
  pre.addOwnedLayout ⟨1⟩ (runtimeLayout n) preparationFresh (preparationDisjoint n)

theorem preparedContext_quantumWires (n : Nat) :
    (preparedContext n).quantumWires = (runtimeLayout n).wires := by
  change (runtimeLayout n).wires ++ [] = _
  exact List.append_nil _

theorem preparedContext_physicalIdx (n : Nat) :
    (preparedContext n).physicalIdx = List.range n := by
  rw [RuntimeCtx.physicalIdx, preparedContext_quantumWires]
  change (List.ofFn fun index : Fin n =>
    (runtimeLayout n).wire index).map QuantumWire.identity = _
  rw [List.map_ofFn]
  exact layout_systemIdx n

/-- The actual preparation identifies the new physical register with its own wire values. -/
def preparedLayoutEquiv (n : Nat) :
    (runtimeLayout n).register.Index ≃ (preparedContext n).register.Index :=
  Execution.preparedEmptyBasisEquiv pre ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) pre_systemCount

/-- The original binary label of those same prepared physical wire values. -/
def preparedBasisEquiv (n : Nat) :
    (preparedContext n).register.Index ≃ (Qubits n).Index :=
  (preparedLayoutEquiv n).symm.trans (layout n).binaryIndexEquiv

/-- Prepare zero on every owned search wire. -/
def inputPreparation (n : Nat) : BasisPreparation (runtimeLayout n) :=
  ⟨(layout n).binaryIndexEquiv.symm (0 : Fin (2 ^ n))⟩

/-- The prescribed preparation is exactly the original pure input in its physical coordinates. -/
theorem inputPreparation_density (n : Nat) :
    (DensityOperator.ofPure (inputPreparation n).normalized).reindex
      (S := (preparedContext n).register) (preparedLayoutEquiv n) =
        (DensityOperator.ofPure ((inputState n).normalized)).reindex
          (S := (preparedContext n).register) (preparedBasisEquiv n).symm := by
  have preparedEntry (basis : (runtimeLayout n).register.Index) :
      (inputPreparation n).normalized basis =
        (inputState n).normalized ((layout n).binaryIndexEquiv basis) := by
    change NormalizedVector.ket ((layout n).binaryIndexEquiv.symm
      (0 : Fin (2 ^ n))) basis =
        NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) _
    rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
    simp only [Equiv.eq_symm_apply]
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix, preparedEntry, preparedEntry]
  rfl

/-- The internally prepared zero source and work vector is the actual all-zero basis. -/
theorem elementaryInput_eq_zero (n k : Nat) :
    Elementary.inputVector n k = (inputState (totalQubits n k)).normalized := by
  change (NormalizedVector.ket (R := Qubits n) 0).tensor
    (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0) =
      NormalizedVector.ket (R := Qubits (totalQubits n k)) 0
  rw [NormalizedVector.tensor_ket]
  rfl

/-- The executable elementary sequence, transported through the actual complete wire assembly. -/
def program {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    UnitaryCircuit (preparedContext (totalQubits n k)).register :=
  UnitaryCircuit.reindex (preparedBasisEquiv (totalQubits n k)).symm
    (Elementary.circuit marked k)

theorem program_placement {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (program marked k).physical_idx =
      (preparedContext (totalQubits n k)).physicalIdx := by
  change (Elementary.circuit marked k).physical_idx = _
  rw [Elementary.circuit_physical_idx, preparedContext_physicalIdx]

end

end QuantumAlg.GroverSearch
