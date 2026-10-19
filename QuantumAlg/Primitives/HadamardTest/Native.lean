/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Basic
public import QuantumAlg.Components.Oracle.UnitarySource.Controlled
public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Components.Oracle.UnitarySource.Controlled
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Hadamard.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Actual native Hadamard-test word

The two leading Hadamards surround one explicitly granted controlled query.
The complete matrix is the original source operator, with the input suffix
retained on its actual wires [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest.Native

noncomputable section

/-- One native Hadamard on the control, with every input system untouched. -/
public def boundary (width : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model width true)
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  Gate.singleQubitAt (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
    (UnitarySource.model width true) Gate.HOp (0 : Fin (1 + width)) rfl

/-- Two actual single-qubit operations surround the granted controlled source call. -/
public def circuit (width : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model width true)
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  ((boundary width).seq (UnitarySource.controlledProgram AlgorithmGate.model width)).seq
    (boundary width)

private lemma query_binaryMatrix {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (UnitarySource.controlledProgram AlgorithmGate.model width).binaryMatrix
      (UnitarySource.interpretation unitary true) =
      UnitaryOperator.controlledQubits unitary := by
  unfold UnitaryCircuit.binaryMatrix
  rw [UnitarySource.controlledProgram_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (1 + width)).symm _

/-- Exact binary matrix of the actual native three-instruction word. -/
public lemma hadamardTestNative_binaryMatrix {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (circuit width).binaryMatrix
      (UnitarySource.interpretation unitary true) = hadamardTest unitary := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, query_binaryMatrix]
  rw [boundary, Gate.singleQubitAt_first_binaryMatrix]
  rfl

/-- The event ledger records both actual native gates and the one granted source query. -/
public lemma hadamardTestNative_eventCost (width : Nat) :
    (circuit width).eventCost =
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (UnitarySource.model width true))
        (.gate AlgorithmGate.Coordinate.singleQubit) +
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (UnitarySource.model width true))
        (.oracle UnitarySource.Coordinate.controlled) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    boundary, Gate.singleQubitAt_eventCost, UnitarySource.controlledProgram_events]
  rw [two_nsmul]
  ac_rfl

/-- The three instructions share the control wire and have unit-event depth three. -/
public lemma hadamardTestNative_unit_depth (width : Nat) :
    (circuit width).evaluatedEventDepth (fun _ => 1) = 3 := by
  rw [circuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, UnitarySource.controlledProgram_depth]
  change (1 + 1) + 1 = 3
  rfl

end

end QuantumAlg.HadamardTest.Native
