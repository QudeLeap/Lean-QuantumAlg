/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Algorithm.Unitary.Owned
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Owned qubit execution with an independent binary operator

A source theorem may specify its unitary in big-endian binary coordinates.
Transporting that mathematical target to physical coordinates lets the same
complete-execution contract use the actual placed circuit unchanged.
-/

namespace QuantumAlg.UnitaryExecution.Owned.Binary
noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {width : Nat}

/-- The canonical physical interface for an independently specified qubit width. -/
public abbrev layout (width : Nat) :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

/-- The specified binary operator expressed on the same physical systems. -/
public def physicalTarget (operator : UnitaryOperator (Qubits width)) :
    UnitaryOperator (layout width).register :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm operator

/-- **Input.** The owned canonical qubit register in any normalized joint state.
**Output.** The same register after the independently specified binary unitary.
**Resource budget.** Supplied native event and depth limits, and the declared register width.
**Success.** Exact joint-state action, retaining correlations with any external reference.
**Source.** The canonical binary view of physical qubit execution. -/
public def problem (operator : oracles.Interpretation → UnitaryOperator (Qubits width))
    (events : ResourcePool (.quantum gates oracles)) (limit : Nat) :
    Problem (.quantum gates oracles) (Owned.context (layout width))
      (Owned.context (layout width)) .unit :=
  Owned.problem (fun environment => physicalTarget (operator environment)) events limit

/-- The same actual circuit run on its complete owned physical interface. -/
public def algorithm (word : UnitaryCircuit gates oracles (layout width)) :
    Algorithm (.quantum gates oracles) (Owned.context (layout width))
      (Owned.context (layout width)) .unit :=
  Owned.algorithm word

/-- A binary-matrix construction theorem certifies the complete owned execution. -/
public theorem main (operator : oracles.Interpretation → UnitaryOperator (Qubits width))
    (events : ResourcePool (.quantum gates oracles)) (limit : Nat)
    (word : UnitaryCircuit gates oracles (layout width))
    (same : ∀ environment, word.binaryMatrix environment
      = operator environment) (cost : word.eventCost ≤ events)
    (depth : word.evaluatedEventDepth (fun _ => 1) ≤ limit) :
    Algorithm.Solves (algorithm word) (problem operator events limit) := by
  apply Owned.main _ _ _ word _ cost depth
  intro environment
  rw [← same environment]
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv width) (word.matrix environment)).symm

end
end QuantumAlg.UnitaryExecution.Owned.Binary
