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
# Complete XOR-oracle phase kickback

The actual query has an independent full-operator target and a complete
supplied register. The original exact phase identity is retained alongside
the common execution contract.
-/

namespace QuantumAlg.PhaseKickback

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits NormalizedVector

variable {n : Nat}

/-- Independent source action in the complete supplied-register coordinates. -/
public def semanticOperator (f : Fin (2 ^ n) → Bool) :
    UnitaryOperator (context (n + 1)).register :=
  UnitaryOperator.reindex (basisEquiv (n + 1)).symm (xorOracleOp f)

/-- The native model explicitly grants the one source query used here. -/
public abbrev model (n : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model (XorOracle.model n)

private def program (n : Nat) :
    UnitaryCircuit AlgorithmGate.model (XorOracle.model n) (context (n + 1)).quantumLayout :=
  Execution.unitaryOfEqualWires (layout (n + 1)) (context (n + 1)).quantumLayout
    (layout_wires (n + 1)) (circuit n)

private lemma program_matrix (f : Fin (2 ^ n) → Bool) :
    (program n).matrix (XorOracle.interpretation f) = semanticOperator f := by
  refine (Execution.unitaryOfEqualWires_matrix (layout (n + 1))
    (context (n + 1)).quantumLayout (layout_wires (n + 1)) (XorOracle.interpretation f) (circuit
      n)).trans ?_
  refine (congrArg
    (UnitaryOperator.reindex (R := (layout (n + 1)).register)
      (S := (context (n + 1)).register)
      (Execution.basisOfEqualWires (layout (n + 1)) (context (n + 1)).quantumLayout
        (layout_wires (n + 1)))) (circuit_matrix f)).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private def code (n : Nat) :
    Circuit (model n) (context (n + 1)) (context (n + 1)) :=
  .unitary (program n)

/-- Execute the actual query and retain the complete supplied joint register. -/
public def algorithm (n : Nat) :
    Algorithm (model n) (context (n + 1)) (context (n + 1)) .unit where
  run := { code := code n, output := Output.all (context (n + 1)) .unit }

/-- Complete Output lists the same original owned systems. -/
private lemma output_listing (n : Nat) :
    (algorithm n).run.output.listing = (context (n + 1)).keys := rfl

private lemma actual_events (n : Nat) (path : (code n).Path) :
    (code n).resourcePool path =
      ResourcePool.singleton (model := model n) (.oracle XorOracle.Coordinate.xor) := by
  change ResourcePool.ofList (program n).eventTrace = _
  refine (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program n)).trans ?_
  refine (Execution.unitaryOfEqualWires_cost (layout (n + 1))
    (context (n + 1)).quantumLayout (layout_wires (n + 1))
    (circuit n) .empty .empty).trans ?_
  exact circuit_events n

private lemma actual_resident (n : Nat) (path : (code n).Path) :
    (code n).peakResidentSpace path ≤ space (n + 1) := by
  intro axis
  change Nat.max ((context (n + 1)).residentSpace axis) 0 ≤ space (n + 1) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (n : Nat) (path : (code n).Path) :
    (code n).peakAuxiliarySpace path ≤ space (n + 1) := by
  intro axis
  change Nat.max ((context (n + 1)).auxiliarySpace axis) 0 ≤ space (n + 1) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

end

end QuantumAlg.PhaseKickback
