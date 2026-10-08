/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Pipeline

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
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Primitives.WalshHadamard.Initialization
import all QuantumAlg.Primitives.WalshHadamard.Initialization
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero

/-!
# The actual Walsh-Hadamard query readout input and prepared physical register

The classical input remains a borrowed unit cell. The execution prepares its
own n query qubits and one target qubit in zero, then executes a native target
X and the original Hadamard, XOR-query, Hadamard circuit [dW19, qcnotes.tex:1193,1245]. The target
wire is part of the complete live register at every later step.

The basis equivalence below is the actual preparation assembly with the
unique empty old quantum basis, followed by explicit big-endian binary
encoding of the same wire values. It does not identify registers solely by
their cardinalities.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

/-- Default native gates, explicitly granted XOR access, and the selected bit/word operations. -/
public abbrev model {n : Nat} (function : Fin (2 ^ n) → Bool) : ExecutionModel :=
  .quantum AlgorithmGate.model (XorOracle.model function) BitWord.model .empty

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

/-- The fixed preparation supplies zero on every query wire and on the target wire. -/
def inputPreparation (n : Nat) : BasisPreparation (runtimeLayout n) :=
  BasisPreparation.zero (runtimeLayout n)

/-- Fixed zero preparation is the original zero binary label on the same physical systems. -/
theorem inputPreparation_density (n : Nat) :
    (DensityOperator.ofPure (inputPreparation n).normalized).reindex
      (S := (preparedContext n).register) (preparedLayoutEquiv n) =
        (DensityOperator.ofPure (NormalizedVector.ket (R := Qubits (n + 1)) 0)).reindex
          (S := (preparedContext n).register) (preparedBasisEquiv n).symm := by
  have physicalZero : (layout n).binaryIndexEquiv.symm (0 : Fin (2 ^ (n + 1))) =
      (inputPreparation n).value :=
    BinaryBasis.bigEndianEquiv_symm_zero (n + 1)
  have preparedEntry (basis : (runtimeLayout n).register.Index) :
      (inputPreparation n).normalized basis =
        NormalizedVector.ket (R := Qubits (n + 1)) 0 ((layout n).binaryIndexEquiv basis) := by
    change NormalizedVector.ket (inputPreparation n).value basis = _
    rw [← physicalZero, NormalizedVector.ket_apply, NormalizedVector.ket_apply]
    simp only [Equiv.eq_symm_apply]
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix, preparedEntry, preparedEntry]
  rfl

/-- Allocating these wires retains their exact canonical order in the prepared context. -/
theorem runtime_wires (n : Nat) :
    (runtimeLayout n).wires = (preparedContext n).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, preparedContext_quantumWires]

/-- The actual X-and-query native word on exactly the complete live prepared register. -/
def program {n : Nat} (function : WalshHadamard.Oracle n) :
    UnitaryCircuit AlgorithmGate.model (XorOracle.model function)
      (preparedContext n).quantumLayout :=
  Execution.unitaryOfEqualWires (runtimeLayout n) (preparedContext n).quantumLayout
    (runtime_wires n) (WalshHadamard.Native.zeroInputProgram function)

end

end QuantumAlg.WalshHadamard.Readout
