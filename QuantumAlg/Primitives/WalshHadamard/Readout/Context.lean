/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.WalshHadamard

/-!
# The actual Walsh-Hadamard query readout input and prepared physical register

The classical input remains a borrowed unit cell. The execution prepares its
own n query qubits and one target qubit in `|0^n>|1>`, then applies the original
Hadamard, XOR-query, Hadamard circuit [dW19, qcnotes.tex:1193,1245]. The target
wire is part of the complete live register at every later step.

The basis equivalence below is the actual preparation assembly with the
unique empty old quantum basis, followed by explicit big-endian binary
encoding of the same wire values. It does not identify registers solely by
their cardinalities.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

/-- The original zero-bit borrowed input, with no supplied quantum systems. -/
@[reducible] public def pre : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput ⟨0⟩ .unit (by decide)

theorem pre_systemCount : pre.systemCount = 0 := rfl

/-- The same n query positions and target position, each of dimension two. -/
@[implicit_reducible]
def runtimeLayout (n : Nat) : QuantumLayout (n + 1) :=
  (layout n).toQuantumLayout

theorem preparationFresh : (⟨1⟩ : StorageKey) ∉ pre.keys := by decide

theorem preparationDisjoint (n : Nat) :
    List.Disjoint (runtimeLayout n).identities pre.physicalIdx := by
  exact List.disjoint_nil_right _

/-- The complete context after allocating and preparing the owned query and target wires. -/
@[implicit_reducible]
def preparedContext (n : Nat) : RuntimeCtx .quantum :=
  pre.addOwnedLayout ⟨1⟩ (runtimeLayout n) preparationFresh (preparationDisjoint n)

theorem preparedContext_quantumWires (n : Nat) :
    (preparedContext n).quantumWires = (runtimeLayout n).wires := by
  change (runtimeLayout n).wires ++ [] = _
  exact List.append_nil _

theorem preparedContext_physicalIdx (n : Nat) :
    (preparedContext n).physicalIdx = List.range (n + 1) := by
  rw [RuntimeCtx.physicalIdx, preparedContext_quantumWires]
  change (List.ofFn fun index : Fin (n + 1) =>
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
    (preparedContext n).register.Index ≃ (Qubits (n + 1)).Index :=
  (preparedLayoutEquiv n).symm.trans (layout n).binaryIndexEquiv

/-- Prepare zero on every query wire and one on the target wire. -/
def inputPreparation (n : Nat) : BasisPreparation (runtimeLayout n) :=
  ⟨(layout n).binaryIndexEquiv.symm
    (prodEquiv ((0 : Fin (2 ^ n)), (1 : Fin (2 ^ 1))))⟩

/-- The prescribed preparation is exactly the original pure input in its physical coordinates. -/
theorem inputPreparation_density (n : Nat) :
    (DensityOperator.ofPure (inputPreparation n).normalized).reindex
      (S := (preparedContext n).register) (preparedLayoutEquiv n) =
        (DensityOperator.ofPure (WalshHadamard.input n)).reindex
          (S := (preparedContext n).register) (preparedBasisEquiv n).symm := by
  have originalInput : WalshHadamard.input n =
      NormalizedVector.ket (prodEquiv ((0 : Fin (2 ^ n)), (1 : Fin (2 ^ 1)))) := by
    exact NormalizedVector.tensor_ket (0 : Fin (2 ^ n)) (1 : Fin (2 ^ 1))
  have preparedEntry (basis : (runtimeLayout n).register.Index) :
      (inputPreparation n).normalized basis =
        WalshHadamard.input n ((layout n).binaryIndexEquiv basis) := by
    rw [originalInput]
    change NormalizedVector.ket ((layout n).binaryIndexEquiv.symm
      (prodEquiv ((0 : Fin (2 ^ n)), (1 : Fin (2 ^ 1))))) basis = _
    rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
    simp only [Equiv.eq_symm_apply]
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix, preparedEntry, preparedEntry]
  rfl

/-- The original executable query circuit, transported through the actual wire assembly. -/
def program {n : Nat} (f : WalshHadamard.Oracle n) :
    UnitaryCircuit (preparedContext n).register :=
  UnitaryCircuit.reindex (preparedBasisEquiv n).symm (WalshHadamard.circuit f)

theorem program_placement {n : Nat} (f : WalshHadamard.Oracle n) :
    (program f).physical_idx = (preparedContext n).physicalIdx := by
  change (WalshHadamard.circuit f).physical_idx = _
  rw [WalshHadamard.circuit_physical_idx, preparedContext_physicalIdx]

end

end QuantumAlg.WalshHadamard.Readout
