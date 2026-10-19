/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.PhaseKickback.Construction
import all QuantumAlg.Primitives.PhaseKickback.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

/-!
# Complete eigenvalue phase kickback

The actual query has an independent full-operator target and a complete
supplied register. The original exact phase identity is retained alongside
the common execution contract.
-/

namespace QuantumAlg.GeneralizedPhaseKickback

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits NormalizedVector

variable {n : Nat}

/-- Independent source action in the complete supplied-register coordinates. -/
public def semanticOperator (U : UnitaryOperator (Qubits n)) :
    UnitaryOperator (context (1 + n)).register :=
  UnitaryOperator.reindex (basisEquiv (1 + n)).symm (UnitaryOperator.controlledQubits U)

/-- The native model explicitly grants the one source query used here. -/
public abbrev model (n : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model (UnitarySource.model n true)

private def program (n : Nat) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model n true)
      (context (1 + n)).quantumLayout :=
  Execution.unitaryOfEqualWires (layout (1 + n)) (context (1 + n)).quantumLayout
    (layout_wires (1 + n)) (circuit n)

private lemma program_matrix (U : UnitaryOperator (Qubits n)) :
    (program n).matrix (UnitarySource.interpretation U true) = semanticOperator U := by
  refine (Execution.unitaryOfEqualWires_matrix (layout (1 + n))
    (context (1 + n)).quantumLayout (layout_wires (1 + n))
      (UnitarySource.interpretation U true) (circuit n)).trans ?_
  refine (congrArg
    (UnitaryOperator.reindex (R := (layout (1 + n)).register)
      (S := (context (1 + n)).register)
      (Execution.basisOfEqualWires (layout (1 + n)) (context (1 + n)).quantumLayout
        (layout_wires (1 + n)))) (circuit_matrix U)).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private def code (n : Nat) :
    Circuit (model n) (context (1 + n)) (context (1 + n)) :=
  .unitary (program n)

/-- Execute the actual query and retain the complete supplied joint register. -/
public def algorithm (n : Nat) :
    Algorithm (model n) (context (1 + n)) (context (1 + n)) .unit where
  run := { code := code n, output := Output.all (context (1 + n)) .unit }

/-- Complete Output lists the same original owned systems. -/
private lemma output_listing (n : Nat) :
    (algorithm n).run.output.listing = (context (1 + n)).keys := rfl

private lemma actual_events (n : Nat) (path : (code n).Path) :
    (code n).resourcePool path =
      ResourcePool.singleton (model := model n) (.oracle UnitarySource.Coordinate.controlled) := by
  change ResourcePool.ofList (program n).eventTrace = _
  refine (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program n)).trans ?_
  refine (Execution.unitaryOfEqualWires_cost (layout (1 + n))
    (context (1 + n)).quantumLayout (layout_wires (1 + n))
    (circuit n) .empty .empty).trans ?_
  exact circuit_events n

private lemma actual_resident (n : Nat) (path : (code n).Path) :
    (code n).peakResidentSpace path ≤ space (1 + n) := by
  intro axis
  change Nat.max ((context (1 + n)).residentSpace axis) 0 ≤ space (1 + n) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (n : Nat) (path : (code n).Path) :
    (code n).peakAuxiliarySpace path ≤ space (1 + n) := by
  intro axis
  change Nat.max ((context (1 + n)).auxiliarySpace axis) 0 ≤ space (1 + n) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

end

end QuantumAlg.GeneralizedPhaseKickback
