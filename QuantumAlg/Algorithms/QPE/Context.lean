/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
public import QuantumAlg.Algorithms.QPE.Basic
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Algorithms.QPE.Circuit
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Owned.Borrowed.Positions
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Algorithms.QPE.Construction

/-!
# The actual borrowed-eigenstate and owned-phase QPE frame

The supplied eigenstate occupies the borrowed suffix of the physical frame.
The algorithm prepares only the disjoint phase prefix. Both remain live in
the same joint register; its explicit coordinates preserve every physical
identity and binary value. The input's pure-state promise is stated separately.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

/-- Default native gates, granted controlled source queries, and finite bit/word operations. -/
public abbrev model (n : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model (UnitarySource.model n true) BitWord.model .empty

/-- Source semantics used only to interpret the fixed-width execution in correctness proofs. -/
@[expose] public def sourceEnvironment {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (model n).Environment where
  quantum := UnitarySource.interpretation U true
  classical := ()

/-- With no classical service, the admitted quantum interpretation determines the environment. -/
public lemma sourceEnvironment_eq {n : Nat} (U : UnitaryOperator (Qubits n))
    (environment : (model n).Environment)
    (same : environment.quantum = UnitarySource.interpretation U true) :
    environment = sourceEnvironment U := by
  cases environment with
  | mk quantum classical =>
      cases classical
      cases same
      rfl

/-- The original source eigenstate is supplied in the borrowed physical suffix. -/
@[reducible] public def pre (t n : Nat) : RuntimeCtx .quantum :=
  OwnedBorrowedQubits.borrowedContext t n

/-- Only the phase prefix is allocated and initialized by the algorithm. -/
@[implicit_reducible]
def phaseRuntimeLayout (t : Nat) : QuantumLayout t :=
  (OwnedBorrowedQubits.wordLayout t).toQuantumLayout

lemma preparationFresh (t n : Nat) : (⟨0⟩ : StorageKey) ∉ (pre t n).keys := by
  change (⟨0⟩ : StorageKey) ∉ [⟨1⟩]
  decide

lemma preparationDisjoint (t n : Nat) :
    List.Disjoint (phaseRuntimeLayout t).identities (pre t n).physicalIdx :=
  OwnedBorrowedQubits.disjointWords t n

/-- The owned prefix and the still-borrowed source form the complete live quantum register. -/
@[implicit_reducible]
def preparedContext (t n : Nat) : RuntimeCtx .quantum := OwnedBorrowedQubits.context t n

lemma pre_systemCount (t n : Nat) : (pre t n).systemCount = n := by
  change (List.ofFn (OwnedBorrowedQubits.borrowedLayout t n).toQuantumLayout.wire ++ []).length = n
  simp only [List.length_append, List.length_ofFn, List.length_nil, Nat.add_zero]

private lemma input_wires (t n : Nat) :
    (OwnedBorrowedQubits.borrowedLayout t n).toQuantumLayout.wires =
      (pre t n).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change _ = (OwnedBorrowedQubits.borrowedLayout t n).toQuantumLayout.wires ++ []
  exact (List.append_nil _).symm

/-- Public binary coordinates of the same supplied borrowed source systems. -/
public def inputBasisEquiv (t n : Nat) : (pre t n).register.Index ≃ (Qubits n).Index :=
  (Execution.basisOfEqualWires (OwnedBorrowedQubits.borrowedLayout t n).toQuantumLayout
    (pre t n).quantumLayout (input_wires t n)).symm.trans
      (OwnedBorrowedQubits.borrowedLayout t n).binaryIndexEquiv

/-- The full actual phase-first, source-second layout used by the source circuit. -/
@[implicit_reducible]
def runtimeLayout (t n : Nat) : QuantumLayout (t + n) := (qpeLayout t n).toQuantumLayout

lemma runtime_wires (t n : Nat) :
    (runtimeLayout t n).wires = (preparedContext t n).quantumLayout.wires :=
  OwnedBorrowedQubits.context_wires t n

def preparedLayoutEquiv (t n : Nat) :
    (runtimeLayout t n).register.Index ≃ (preparedContext t n).register.Index :=
  Execution.basisOfEqualWires (runtimeLayout t n) (preparedContext t n).quantumLayout
    (runtime_wires t n)

def preparedBasisEquiv (t n : Nat) :
    (preparedContext t n).register.Index ≃ (Qubits (t + n)).Index :=
  (preparedLayoutEquiv t n).symm.trans (qpeLayout t n).binaryIndexEquiv

lemma preparedContext_physicalIdx (t n : Nat) :
    (preparedContext t n).physicalIdx = List.range (t + n) :=
  OwnedBorrowedQubits.context_physicalIdx t n

/-- Fixed zero preparation of each phase qubit; the borrowed source is untouched. -/
def inputPreparation (t : Nat) : BasisPreparation (phaseRuntimeLayout t) :=
  BasisPreparation.zero (phaseRuntimeLayout t)

/-- The actual native QPE word on the complete prepared physical register. -/
def nativeProgram (n : Nat) (t : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model n true)
      (preparedContext t n).quantumLayout :=
  Execution.unitaryOfEqualWires (runtimeLayout t n) (preparedContext t n).quantumLayout
    (runtime_wires t n) (Native.circuit t n)

end

end QuantumAlg.QuantumPhaseEstimation
