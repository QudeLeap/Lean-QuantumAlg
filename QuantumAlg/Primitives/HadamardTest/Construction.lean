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
public abbrev model {width : Nat} (unitary : UnitaryOperator (Qubits width)) : ExecutionModel :=
  .quantum AlgorithmGate.model (UnitarySource.model unitary true)

/-- The complete actual H/query/H word on the canonical physical register. -/
def sourceCircuit {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model unitary true)
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  Native.circuit unitary

/-- The actual source circuit has the registered binary Hadamard-test operator. -/
theorem sourceCircuit_matrix {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (sourceCircuit unitary).binaryMatrix = hadamardTest unitary :=
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
def nativeProgram {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model unitary true)
      (prepared width).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
    (prepared width).quantumLayout (OwnedQubitPrefix.post_canonical_wires 1 width)
    (sourceCircuit unitary)

/-- The native program acts in the exact tensor frame used by real prefix preparation. -/
theorem nativeProgram_matrix {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (nativeProgram unitary).matrix =
      UnitaryOperator.reindex (OwnedQubitPrefix.basisEquiv 1 width).symm
        (hadamardTest unitary) := by
  have physical : (sourceCircuit unitary).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
        (hadamardTest unitary) := by
    rw [← sourceCircuit_matrix]
    exact (UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv (1 + width)) (sourceCircuit unitary).matrix).symm
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix, physical,
    ← OwnedQubitPrefix.canonicalBasisEquiv_eq_basisEquiv]
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

end

end QuantumAlg.HadamardTest
