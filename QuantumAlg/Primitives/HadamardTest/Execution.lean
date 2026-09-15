/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Construction
public import QuantumAlg.Core.Algorithm
import all QuantumAlg.Primitives.HadamardTest.Construction
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Preparation.Borrowed.Positions
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Borrowed

/-!
# The complete native Hadamard-test execution

The circuit prepares its own leading control, executes the actual H/query/H
sequence, and measures that control into one retained finite classical cell.
Output keeps that cell and both owned quantum words. The measurement result
is read directly from its real cell [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

open Execution

theorem resultFresh (width : Nat) : (⟨2⟩ : StorageKey) ∉ (prepared width).keys := by
  change (⟨2⟩ : StorageKey) ∉ [⟨0⟩, ⟨1⟩]
  decide

/-- The control, the complete supplied input, and the actual measured result remain live. -/
@[reducible] public def post (width : Nat) : RuntimeCtx .quantum :=
  (prepared width).addRetained ⟨2⟩ (.finite 2) (resultFresh width)

/-- The actual writable binary classical result cell. -/
def resultRef (width : Nat) : CWriteRef (post width) (.finite 2) :=
  CWriteRef.retainedHead (prepared width) ⟨2⟩ (.finite 2) (resultFresh width)

/-- The full binary coordinates survive retaining a purely classical cell. -/
def outputBasisEquiv (width : Nat) : (post width).register.Index ≃ (Qubits (1 + width)).Index :=
  OwnedQubitPrefix.basisEquiv 1 width

/-- The physical leading control is the first live quantum system. -/
def controlWire (width : Nat) : Fin (post width).systemCount :=
  PreparationBorrowed.fullPositionEquiv (pre width) ⟨0⟩
    (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
    (OwnedQubitPrefix.prefix_fresh 1 width) (OwnedQubitPrefix.prefix_disjoint 1 width)
    (.inl 0)

theorem controlWire_dimension (width : Nat) :
    ((post width).quantumLayout.wire (controlWire width)).dimension = 2 := by
  exact congrArg QuantumWire.dimension
    (PreparationBorrowed.fullPositionEquiv_new_wire (pre width) ⟨0⟩
      (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
      (OwnedQubitPrefix.prefix_fresh 1 width) (OwnedQubitPrefix.prefix_disjoint 1 width) 0)

/-- One actual Z write to the binary cell; no quantum system is released. -/
def readout (width : Nat) : ZReadout (post width) where
  wire := controlWire width
  output := by
    rw [controlWire_dimension]
    exact resultRef width

def beforeMeasurement {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    Circuit (pre width) (post width) :=
  .seq (OwnedQubitPrefix.prepareCode 1 width)
    (.seq (.unitary (nativeProgram unitary) (nativeProgram_placement unitary))
      (.retain (prepared width) ⟨2⟩ (.finite 2) (resultFresh width)))

def readoutCode (width : Nat) : Circuit (post width) (post width) :=
  Circuit.measurementSequence [readout width]

/-- Every preparation, gate and stored measurement belongs to this one circuit. -/
def code {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    Circuit (pre width) (post width) :=
  .seq (beforeMeasurement unitary) (readoutCode width)

def run {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    AlgorithmRun (pre width) (post width) (.finite 2) where
  code := code unitary
  output := Output.all (post width) (.read (.storage (resultRef width).toCStorageRef))

/-- The algorithm contains only the same complete native run. -/
public def algorithm {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    Algorithm .quantum (pre width) (post width) (.finite 2) := ⟨run unitary⟩

theorem run_output_listing {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (run unitary).output.listing = (post width).keys := rfl

public theorem algorithm_output_listing {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (algorithm unitary).run.output.listing = (post width).keys := run_output_listing unitary

theorem post_noBorrowedQuantum (width : Nat) : (post width).borrowedQuantumWires = [] := rfl

end

end QuantumAlg.HadamardTest
