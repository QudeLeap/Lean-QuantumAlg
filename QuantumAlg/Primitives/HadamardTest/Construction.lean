/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Native
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Primitives.HadamardTest.Native
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix.Coordinates
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction

/-!
# The actual Hadamard-test source circuit and physical runtime frame

Two actual Hadamards surround one controlled source query. The input is owned
because this general test may change it; the fresh control is prepared by a
separate counted instruction. The runtime frame retains the control and the
entire input word [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

open Execution

/-- Default native gates with explicitly granted controlled source access. -/
public abbrev model (width : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model (UnitarySource.model width true)

/-- The source unitary is supplied only when interpreting the fixed native program. -/
@[expose]
public def environment {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (model width).Environment where
  quantum := UnitarySource.interpretation unitary true
  classical := ClassicalOracleModel.emptyInterpretation

lemma environment_eq_of_quantum {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (actual : (model width).Environment)
    (same : actual.quantum = UnitarySource.interpretation unitary true) :
    actual = environment unitary := by
  cases actual with
  | mk quantum classical =>
    cases same
    cases classical
    rfl

/-- The complete actual H/query/H word on the canonical physical register. -/
def sourceCircuit (width : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model width true)
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  Native.circuit width

/-- The actual source circuit has the registered binary Hadamard-test operator. -/
lemma sourceCircuit_matrix {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (sourceCircuit width).binaryMatrix
      (UnitarySource.interpretation unitary true) = hadamardTest unitary :=
  Native.hadamardTestNative_binaryMatrix unitary

/-- The source word is supplied without a clean control or borrowed-restoration promise. -/
@[reducible] public def pre (width : Nat) : RuntimeCtx .quantum := OwnedQubitPrefix.pre 1 width

/-- The supplied input's actual ordered physical wires have their original binary labels. -/
public def inputBasisEquiv (width : Nat) :
    (pre width).register.Index ≃ (Qubits width).Index :=
  OwnedQubitPrefix.inputBasisEquiv 1 width

/-- The fresh actual control precedes the still-live owned input. -/
@[reducible] public def prepared (width : Nat) : RuntimeCtx .quantum :=
  OwnedQubitPrefix.post 1 width

/-- Actual native execution on the full prepared register, preserving its ordered physical wires. -/
def nativeProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model width true)
      (prepared width).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
    (prepared width).quantumLayout (OwnedQubitPrefix.post_canonical_wires 1 width)
    (sourceCircuit width)

/-- The native program acts in the exact tensor frame used by real prefix preparation. -/
lemma nativeProgram_matrix {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (nativeProgram width).matrix (UnitarySource.interpretation unitary true) =
      UnitaryOperator.reindex (OwnedQubitPrefix.basisEquiv 1 width).symm
        (hadamardTest unitary) := by
  have physical : (sourceCircuit width).matrix (UnitarySource.interpretation unitary true) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
        (hadamardTest unitary) := by
    rw [← sourceCircuit_matrix]
    exact (UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv (1 + width)) ((sourceCircuit width).matrix
        (UnitarySource.interpretation unitary true))).symm
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix, physical,
    ← OwnedQubitPrefix.canonicalBasisEquiv_eq_basisEquiv]
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

end

end QuantumAlg.HadamardTest
