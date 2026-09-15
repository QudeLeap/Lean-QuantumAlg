/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Construction
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Complete reflection-convention quantum signal processing

The source characterization is realized by complete one-qubit executions.
The full operator, native budget and original polynomial conditions remain
independent of the candidate run [Lin22, hermfunc.tex:1118-1138].
-/

namespace QuantumAlg.ReflectionBasedQuantumSignalProcessing

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits Polynomial

variable (φ₀ : Real) (φs : List Real) (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1)

private def semanticOperator : UnitaryOperator (context 1).register :=
  UnitaryOperator.reindex (basisEquiv 1).symm (operator φ₀ φs x hx)

private def program : UnitaryCircuit (context 1).register :=
  UnitaryCircuit.reindex (basisEquiv 1).symm (circuit φ₀ φs x hx)

private theorem program_matrix :
    (program φ₀ φs x hx).matrix = semanticOperator φ₀ φs x hx := by
  exact (UnitaryCircuit.reindex_matrix (basisEquiv 1).symm (circuit φ₀ φs x hx)).trans
    (congrArg (UnitaryOperator.reindex (basisEquiv 1).symm) (circuit_matrix φ₀ φs x hx))

private theorem placement :
    (program φ₀ φs x hx).physical_idx = (context 1).physicalIdx := by
  change (circuit φ₀ φs x hx).physical_idx = (context 1).physicalIdx
  rw [circuit_physicalIdx, ownedQubits_physicalIdx]

private def code : Circuit (context 1) (context 1) :=
  .unitary (program φ₀ φs x hx) (placement φ₀ φs x hx)

/-- Complete execution of a reflection-convention QSP word.

**Input.** One supplied owned qubit in any normalized joint state, arbitrary
external references, arbitrary real processing phases and x in [-1,1].
**Output.** The same qubit and the classical unit result. The exact algebraic
QSP product acts on the qubit, tensor the identity on every external reference.
**Resource budget.** With d = φs.length, exactly d declared signal operations
and d + 1 exact Z processing rotations. Unit-event depth is at most 2d + 1.
Resident and owned auxiliary space each count the same supplied qubit. No
new quantum systems or classical cells are allocated.
**Success.** Probability one and exact full-operator action.
**Source.** The product and characterization are [Lin22, hermfunc.tex:1103-1138].
-/
public def problem : Problem .quantum (context 1) (context 1) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (semanticOperator φ₀ φs x hx)]
  resources := { events := eventBudget φs.length, resident := space 1, auxiliary := space 1 }
  depth := .quantum (fun _ => 1) (2 * φs.length + 1)

/-- Execute the actual processing word and retain its entire supplied register. -/
public def algorithm : Algorithm .quantum (context 1) (context 1) .unit where
  run := { code := code φ₀ φs x hx, output := Output.all (context 1) .unit }

private theorem output_listing :
    (algorithm φ₀ φs x hx).run.output.listing = (context 1).keys := rfl

/-- The complete Output keeps the original qubit. -/
public theorem algorithm_output_listing :
    (algorithm φ₀ φs x hx).run.output.listing = (context 1).keys :=
  output_listing φ₀ φs x hx

private theorem actual_events (path : (code φ₀ φs x hx).Path) :
    (code φ₀ φs x hx).resourcePool path = eventBudget φs.length := by
  change ResourcePool.ofList (program φ₀ φs x hx).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    UnitaryCircuit.reindex_eventCost, circuit_events]

/-- Exact native signal and rotation multiplicities of every actual execution path. -/
public theorem algorithm_eventPool (path : (algorithm φ₀ φs x hx).run.code.Path) :
    (algorithm φ₀ φs x hx).run.code.resourcePool path = eventBudget φs.length :=
  actual_events φ₀ φs x hx path

private theorem actual_resident (path : (code φ₀ φs x hx).Path) :
    (code φ₀ φs x hx).peakResidentSpace path ≤ space 1 := by
  intro axis
  change Nat.max ((context 1).residentSpace axis) 0 ≤ space 1 axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (path : (code φ₀ φs x hx).Path) :
    (code φ₀ φs x hx).peakAuxiliarySpace path ≤ space 1 := by
  intro axis
  change Nat.max ((context 1).auxiliarySpace axis) 0 ≤ space 1 axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

theorem algorithm_solves : Algorithm.Solves (algorithm φ₀ φs x hx) (problem φ₀ φs x hx) := by
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator φ₀ φs x hx) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (semanticOperator φ₀ φs x hx)
      (program φ₀ φs x hx) (placement φ₀ φs x hx) (program_matrix φ₀ φs x hx)
      (Output.all (context 1) .unit) input
  · intro Reference input _valid
    exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (program φ₀ φs x hx) (placement φ₀ φs x hx)
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact le_of_eq (actual_events φ₀ φs x hx path)
  · intro _Reference _input _valid path _supported
    exact actual_resident φ₀ φs x hx path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary φ₀ φs x hx path
  · intro _Reference _input _valid _path _supported
    exact le_of_eq (circuit_depth φ₀ φs x hx)

/-- The original degree/parity/normalization characterization holds exactly,
and each synthesizing source word has a complete execution satisfying its
independent native contract [Lin22, hermfunc.tex:1118-1138]. -/
public theorem main (d : Nat) (P Q : ℂ[X]) :
    IsQSPPair d P Q ↔
      ∃ (φ₀ : Real) (φs : List Real), φs.length = d ∧
        ∀ (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1),
          qspO φ₀ φs x = qspMat P Q x ∧
            ∃ candidate, Algorithm.Solves candidate (problem φ₀ φs x hx) := by
  constructor
  · intro admissible
    obtain ⟨φ₀, φs, length, realizes⟩ := (characterization d P Q).mp admissible
    exact ⟨φ₀, φs, length, fun x hx =>
      ⟨realizes x hx, algorithm φ₀ φs x hx, algorithm_solves φ₀ φs x hx⟩⟩
  · rintro ⟨φ₀, φs, length, realizes⟩
    exact (characterization d P Q).mpr ⟨φ₀, φs, length, fun x hx => (realizes x hx).1⟩

end

end QuantumAlg.ReflectionBasedQuantumSignalProcessing
