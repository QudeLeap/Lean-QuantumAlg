/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.LCU.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.LCU.Construction
import all QuantumAlg.Primitives.LCU.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Oracle.LCU
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

/-!
# Complete LCU execution and the original exact projected block

The same placed three-query circuit implements the source LCU operator,
retains the complete supplied input and obeys independent native budgets
[Lin22, hermfunc.tex:531-554]. Its exact projected block keeps the original
nonnegative-coefficient domain, including zero coefficients with positive sum.
-/

namespace QuantumAlg.LinearCombinationOfUnitaries

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

variable {a n : Nat}

/-- Independent source action in the complete supplied-register coordinates. -/
public def semanticOperator (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    UnitaryOperator (context (a + n)).register :=
  UnitaryOperator.reindex (basisEquiv (a + n)).symm (lcuWalk V U)

/-- Default native gates and the three explicitly granted LCU accesses. -/
public abbrev model (a n : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model (LCUOracle.model a n)

private def program (a n : Nat) :
    UnitaryCircuit AlgorithmGate.model (LCUOracle.model a n)
      (context (a + n)).quantumLayout :=
  Execution.unitaryOfEqualWires (layout (a + n)) (context (a + n)).quantumLayout
    (layout_wires (a + n)) (circuit a n)

private lemma program_matrix (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    ((program a n).matrix (LCUOracle.interpretation V U)) = semanticOperator V U := by
  have physical : ((circuit a n).matrix (LCUOracle.interpretation V U)) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (a + n)).symm
        (lcuWalk V U) := by
    rw [← circuit_matrix V U]
    exact (UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv (a + n)) ((circuit a n).matrix (LCUOracle.interpretation
        V U))).symm
  refine (Execution.unitaryOfEqualWires_matrix (layout (a + n))
    (context (a + n)).quantumLayout (layout_wires (a + n)) (LCUOracle.interpretation V U) (circuit
      a n)).trans ?_
  refine (congrArg
    (UnitaryOperator.reindex (R := (layout (a + n)).register)
      (S := (context (a + n)).register)
      (Execution.basisOfEqualWires (layout (a + n)) (context (a + n)).quantumLayout
        (layout_wires (a + n)))) physical).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private def code (a n : Nat) :
    Circuit (model a n) (context (a + n)) (context (a + n)) :=
  .unitary (program a n)

/-- Execute the actual LCU queries and retain the complete supplied joint register. -/
public def algorithm (a n : Nat) :
    Algorithm (model a n) (context (a + n)) (context (a + n)) .unit where
  run := { code := code a n, output := Output.all (context (a + n)) .unit }

/-- Complete Output lists the same original owned systems. -/
private lemma output_listing (a n : Nat) :
    (algorithm a n).run.output.listing = (context (a + n)).keys := rfl

private lemma actual_events (a n : Nat) (path : (code a n).Path) :
    (code a n).resourcePool path = ResourcePool.singleton (model := model a n) (.oracle .prepare) +
      ResourcePool.singleton (model := model a n) (.oracle .select) +
      ResourcePool.singleton (model := model a n) (.oracle .unprepare) := by
  change ResourcePool.ofList (program a n).eventTrace = _
  refine (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program a n)).trans ?_
  refine (Execution.unitaryOfEqualWires_cost (layout (a + n))
    (context (a + n)).quantumLayout (layout_wires (a + n)) (circuit a n) .empty .empty).trans ?_
  exact circuit_events a n

private lemma actual_resident (a n : Nat) (path : (code a n).Path) :
    (code a n).peakResidentSpace path ≤ space (a + n) := by
  intro axis
  change Nat.max ((context (a + n)).residentSpace axis) 0 ≤ space (a + n) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (a n : Nat) (path : (code a n).Path) :
    (code a n).peakAuxiliarySpace path ≤ space (a + n) := by
  intro axis
  change Nat.max ((context (a + n)).auxiliarySpace axis) 0 ≤ space (a + n) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

end

end QuantumAlg.LinearCombinationOfUnitaries
