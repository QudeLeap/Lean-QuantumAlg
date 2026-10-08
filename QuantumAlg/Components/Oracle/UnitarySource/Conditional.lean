/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.UnitarySource.Binary
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix

/-!
# Conditional source access from separately granted capabilities

The model grants U, its ordinary inverse, and controlled-U. It does not grant
controlled-inverse access. Conditional inverse execution uses an actual
ordinary inverse query and an actual controlled-U query, with two native X
gates selecting the complementary branch. Every occurrence remains charged.
-/

namespace QuantumAlg.UnitarySource.Conditional
noncomputable section

variable {width : Nat} (U : UnitaryOperator (Qubits width))

/-- Original leading selector and complete source register. -/
abbrev layout (width : Nat) :=
  (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout

/-- One explicitly granted controlled-U query, with ordinary inverse also available. -/
def controlled : UnitaryCircuit AlgorithmGate.model (model U true true false) (layout width) :=
  .query (OracleModel.Application.onPlacement (model U true true false) (.controlled rfl)
    (QuantumSignature.qubits (1 + width)).canonicalPlacement)

/-- The controlled source matrix is fixed by its grant, not by caller-supplied semantics. -/
theorem controlled_matrix : (controlled U).binaryMatrix = UnitaryOperator.controlledQubits U := by
  rw [controlled, UnitaryCircuit.binaryMatrix, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width))
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
      (UnitaryOperator.controlledQubits U)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (1 + width)).symm _

/-- An actual X changes only the selector and is charged as a default one-qubit gate. -/
def selectorX : UnitaryCircuit AlgorithmGate.model (model U true true false) (layout width) :=
  Gate.singleQubitAt (layout width) (model U true true false) Gate.XOp (0 : Fin (1 + width)) rfl

/-- An ordinary inverse acts on the entire source suffix without controlling it. -/
def sourceInverse : UnitaryCircuit AlgorithmGate.model (model U true true false) (layout width) :=
  UnitaryCircuit.onBinarySuffix 1 (Binary.circuit AlgorithmGate.model U true true)

/-- Actual conditional inverse: complementary controlled-U followed by an ordinary inverse. -/
def inverse : UnitaryCircuit AlgorithmGate.model (model U true true false) (layout width) :=
  (((selectorX U).seq (controlled U)).seq (selectorX U)).seq (sourceInverse U)

/-- The conditional inverse retains both granted queries and both native selector flips. -/
theorem inverse_events :
    (inverse U).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model (model U true true false))
        (.oracle Coordinate.controlled) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model (model U true true false))
        (.oracle Coordinate.inverse) +
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model (model U true true false))
        (.gate .singleQubit) := by
  rw [inverse, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, sourceInverse,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost, Binary.circuit_events]
  change (((selectorX U).eventCost + ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (model U true true false))
      (.oracle Coordinate.controlled)) + (selectorX U).eventCost) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model (model U true true false))
      (.oracle Coordinate.inverse) = _
  simp only [selectorX, Gate.singleQubitAt_eventCost, two_nsmul]
  ac_rfl

/-- Both queries and both selector gates are included in the same dependency chain. -/
theorem inverse_depth : (inverse U).evaluatedEventDepth (fun _ => 1) = 4 := by
  rw [inverse, UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, sourceInverse,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth, Binary.circuit_depth]
  rfl

end
end QuantumAlg.UnitarySource.Conditional
