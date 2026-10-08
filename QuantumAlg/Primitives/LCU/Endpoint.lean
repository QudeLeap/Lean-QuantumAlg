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

private def semanticOperator (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    UnitaryOperator (context (a + n)).register :=
  UnitaryOperator.reindex (basisEquiv (a + n)).symm (lcuWalk V U)

/-- Default native gates and the three explicitly granted LCU accesses. -/
public abbrev model (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) : ExecutionModel :=
  .quantum AlgorithmGate.model (LCUOracle.model V U)

private def program (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    UnitaryCircuit AlgorithmGate.model (LCUOracle.model V U)
      (context (a + n)).quantumLayout :=
  Execution.unitaryOfEqualWires (layout (a + n)) (context (a + n)).quantumLayout
    (layout_wires (a + n)) (circuit V U)

private theorem program_matrix (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (program V U).matrix = semanticOperator V U := by
  have physical : (circuit V U).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (a + n)).symm
        (lcuWalk V U) := by
    rw [← circuit_matrix V U]
    exact (UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv (a + n)) (circuit V U).matrix).symm
  refine (Execution.unitaryOfEqualWires_matrix (layout (a + n))
    (context (a + n)).quantumLayout (layout_wires (a + n)) (circuit V U)).trans ?_
  refine (congrArg
    (UnitaryOperator.reindex (R := (layout (a + n)).register)
      (S := (context (a + n)).register)
      (Execution.basisOfEqualWires (layout (a + n)) (context (a + n)).quantumLayout
        (layout_wires (a + n)))) physical).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private def code (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    Circuit (model V U) (context (a + n)) (context (a + n)) :=
  .unitary (program V U)

/-- Independent complete LCU execution contract.

**Input.** A supplied owned a+n-qubit register in any normalized joint state,
with every external reference extension admitted. Query access supplies the
a-qubit preparation unitary V, its inverse, and the controlled SELECT family.
**Output.** The entire register remains live after the exact unitary
W=(V dagger tensor I) SELECT (V tensor I). The joint-state target includes
the identity on every reference. The classical result is unit.
**Resource budget.** One forward preparation query, one inverse preparation query
and one SELECT query suffice, each at its own coordinate. Unit-query depth is at most three.
Resident and
owned auxiliary space are both a+n qubits, describing the same supplied
systems. No new qubits, classical cells or other dimensions are allocated.
**Success.** Probability one with the exact full operator action. When V
prepares the normalized square-root coefficients, the zero-control block is
the coefficient-weighted unitary sum divided by the coefficient sum.
**Source.** The LCU lemma and its preparation/SELECT access model are
[Lin22, hermfunc.tex:531-554]. The statement does not assert a gate synthesis
cost or a successful postselection probability for arbitrary input states.
-/
public def problem (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    Problem (model V U) (context (a + n)) (context (a + n)) .unit where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (semanticOperator V U)]
  resources :=
    { events := ResourcePool.singleton (model := model V U) (.oracle .prepare) +
        ResourcePool.singleton (model := model V U) (.oracle .select) +
        ResourcePool.singleton (model := model V U) (.oracle .unprepare)
      resident := space (a + n)
      auxiliary := space (a + n) }
  depth :=
    { duration := fun _ => 1
      limit := 3
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- Execute the actual LCU queries and retain the complete supplied joint register. -/
public def algorithm (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    Algorithm (model V U) (context (a + n)) (context (a + n)) .unit where
  run := { code := code V U, output := Output.all (context (a + n)) .unit }

/-- Complete Output lists the same original owned systems. -/
private theorem output_listing (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (algorithm V U).run.output.listing = (context (a + n)).keys := rfl

/-- Complete Output keeps every supplied system. -/
public theorem algorithm_output_listing (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (algorithm V U).run.output.listing = (context (a + n)).keys := output_listing V U

private theorem actual_events (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) (path : (code V U).Path) :
    (code V U).resourcePool path = (problem V U).resources.events := by
  change ResourcePool.ofList (program V U).eventTrace = _
  refine (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program V U)).trans ?_
  refine (Execution.unitaryOfEqualWires_cost (layout (a + n))
    (context (a + n)).quantumLayout (layout_wires (a + n)) (circuit V U) .empty .empty).trans ?_
  exact circuit_events V U


private theorem actual_resident (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) (path : (code V U).Path) :
    (code V U).peakResidentSpace path ≤ space (a + n) := by
  intro axis
  change Nat.max ((context (a + n)).residentSpace axis) 0 ≤ space (a + n) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) (path : (code V U).Path) :
    (code V U).peakAuxiliarySpace path ≤ space (a + n) := by
  intro axis
  change Nat.max ((context (a + n)).auxiliarySpace axis) 0 ≤ space (a + n) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private theorem algorithm_solves (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    Algorithm.Solves (algorithm V U) (problem V U) := by
  constructor
  · intro Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid _initialization requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator V U) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (semanticOperator V U)
      (program V U) (program_matrix V U)
      (Output.all (context (a + n)) .unit) input
  · intro Reference input _valid _initialization
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed rfl rfl
      (program V U) (Output.all (context (a + n)) .unit) input
  · intro _Reference _input _valid _initialization path _supported
    exact le_of_eq (actual_events V U path)
  · intro _Reference _input _valid _initialization path _supported
    exact actual_resident V U path
  · intro _Reference _input _valid _initialization path _supported
    exact actual_auxiliary V U path
  · intro _Reference _input _valid _initialization _path _supported
    exact le_of_eq (circuit_depth V U)

/-- The complete native circuit solves its independent execution problem and
has the original exact normalized linear-combination block. -/
public theorem main (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))
    (α : Fin (2 ^ a) → ℝ) (halpha : ∀ i, 0 ≤ α i) (hlam : 0 < lcuNorm α)
    (hV : ∀ i, V i 0 = ((Real.sqrt (α i / lcuNorm α) : ℝ) : ℂ)) :
    ∃ candidate, Algorithm.Solves candidate (problem V U) ∧
      ExactBlockEncoding a n (circuit V U).binaryMatrix
        (((lcuNorm α : ℂ))⁻¹ • lcuCombination α U) := by
  refine ⟨algorithm V U, algorithm_solves V U, ?_⟩
  rw [circuit_matrix]
  exact lcuWalk_exactBlockEncoding V U α halpha hlam hV

end

end QuantumAlg.LinearCombinationOfUnitaries
