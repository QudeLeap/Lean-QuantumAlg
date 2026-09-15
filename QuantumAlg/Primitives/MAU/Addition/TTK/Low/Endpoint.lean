/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Primitives.MAU.Addition.TTK.Low.Semantics
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Primitives.MAU.Addition.TTK.Low.Semantics
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources

/-!
# Complete native TTK low-word addition

The actual ancilla-free ripple circuit preserves the first supplied operand
and replaces the second by their sum modulo its capacity. The full operator
claim admits every joint operand state and external reference
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK.Low

open QuantumAlg.MAU.Addition.TTK

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

private def semanticOperator (width : Nat) : UnitaryOperator (context (width + width)).register :=
  UnitaryOperator.reindex (basisEquiv (width + width)).symm (lowOperator width)

private def program (width : Nat) : UnitaryCircuit (context (width + width)).register :=
  UnitaryCircuit.reindex (basisEquiv (width + width)).symm (completeLowProgram width)

private theorem program_matrix (width : Nat) :
    (program width).matrix = semanticOperator width := by
  exact (UnitaryCircuit.reindex_matrix (basisEquiv (width + width)).symm
    (completeLowProgram width)).trans
      (congrArg (UnitaryOperator.reindex (basisEquiv (width + width)).symm)
        (ttkCompleteLow_matrix width))

private theorem placement (width : Nat) :
    (program width).physical_idx = (context (width + width)).physicalIdx := by
  change (completeLowProgram width).physical_idx = (context (width + width)).physicalIdx
  rw [ttkCompleteLow_physical, ownedQubits_physicalIdx]

private def code (width : Nat) : Circuit (context (width + width)) (context (width + width)) :=
  .unitary (program width) (placement width)

/-- Independent complete two-word addition contract.

**Input.** Two supplied owned width-qubit words in an arbitrary normalized
joint state, including mixtures and correlations with an external reference.
**Output.** Both words remain live. The addend is preserved and the other word
holds their sum modulo 2^width. The independent unitary target preserves exact
phase on every joint input; the classical result is unit.
**Resource budget.** The native bounds are width+2*(width-1)+2*(width-2) CNOTs
and 2*(width-1) Toffolis, with truncated natural subtraction. Resident and owned
auxiliary coordinates are both 2*width qubits, describing the same supplied
operands. No extra qubits, other dimensions or classical cells are allocated.
Unit-duration serial depth is at most width+4*(width-1)+2*(width-2).
**Success.** Probability one with exact joint-state action. The zero-width
circuit has no events; the width-one circuit is one CNOT.
**Source.** The ancilla-free ripple construction is
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352]. The actual serialized gate
schedule and its boundary-width counts are proved for this implementation;
the source's parallel schedule is not used for this depth bound.
-/
public def problem (width : Nat) :
    Problem .quantum (context (width + width)) (context (width + width)) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (semanticOperator width)]
  resources :=
    { events := (width + 2 * (width - 1) + 2 * (width - 2)) •
        ResourcePool.singleton (.gate (.builtin "cnot")) +
        (2 * (width - 1)) • ResourcePool.singleton (.gate (.builtin "toffoli"))
      resident := space (width + width)
      auxiliary := space (width + width) }
  depth := .quantum (fun _ => 1) (width + 4 * (width - 1) + 2 * (width - 2))

/-- Execute the literal low-word ripple and retain both supplied operands. -/
public def algorithm (width : Nat) :
    Algorithm .quantum (context (width + width)) (context (width + width)) .unit where
  run := { code := code width, output := Output.all (context (width + width)) .unit }

private theorem actual_events (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path = (problem width).resources.events := by
  change ResourcePool.ofList (program width).eventTrace = _
  have cost : (program width).eventCost = (lowRippleProgram width).eventCost :=
    (UnitaryCircuit.reindex_eventCost (basisEquiv (width + width)).symm
      (completeLowProgram width)).trans (ttkCompleteLow_eventCost width)
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, cost]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (lowRippleProgram width).eventCost = _
  rw [ttkLowRipple_native_count]
  simp only [problem, Multiset.count_add, Multiset.count_nsmul,
    ResourcePool.singleton, Multiset.count_replicate]

private theorem actual_resident (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ space (width + width) := by
  intro axis
  change Nat.max ((context (width + width)).residentSpace axis) 0 ≤ space (width + width) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (width : Nat) (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤ space (width + width) := by
  intro axis
  change Nat.max ((context (width + width)).auxiliarySpace axis) 0 ≤ space (width + width) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

/-- The actual ancilla-free ripple solves the independent all-state addition problem. -/
public theorem main (width : Nat) :
    ∃ candidate, Algorithm.Solves candidate (problem width) := by
  refine ⟨algorithm width, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator width) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (semanticOperator width)
      (program width) (placement width) (program_matrix width)
      (Output.all (context (width + width)) .unit) input
  · intro Reference input _valid
    exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (program width) (placement width)
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact le_of_eq (actual_events width path)
  · intro _Reference _input _valid path _supported
    exact actual_resident width path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary width path
  · intro _Reference _input _valid path _supported
    exact le_of_eq (ttkCompleteLow_depth width)

end

end QuantumAlg.MAU.Addition.TTK.Low
