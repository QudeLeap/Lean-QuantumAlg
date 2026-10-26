/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.MAU.Addition.TTK.Low.Semantics
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Primitives.MAU.Addition.TTK.Low.Semantics
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources
import all QuantumAlg.Primitives.MAU.Addition.TTK.Parallel

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

variable {interpretation : OracleModel.empty.Interpretation}

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

private def semanticOperator (width : Nat) : UnitaryOperator (context (width + width)).register :=
  UnitaryOperator.reindex (basisEquiv (width + width)).symm (lowOperator width)

private lemma supplied_wires (width : Nat) :
    (QubitLayout.canonical (encoding width).width).toQuantum.wires =
      (context (width + width)).quantumLayout.wires := by
  rw [ttkEncoding_width, two_mul]
  exact Execution.OwnedQubits.canonical_wires (width + width)

private def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (context (width + width)).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QubitLayout.canonical (encoding width).width).toQuantum
    (context (width + width)).quantumLayout (supplied_wires width)
      (parallelLowRippleProgram width)

private lemma program_matrix (width : Nat) :
    ((program width).matrix interpretation) = semanticOperator width := by
  unfold semanticOperator
  have sourceMatrix : ((lowRippleProgram width).matrix interpretation) =
      UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          (lowOperator width) := by
    have binary := congrArg
      (UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm)
      (ttkLowRipple_matrix (environment := interpretation) width)
    change UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          (UnitaryOperator.reindex
            (QubitLayout.canonical (encoding width).width).basisEquiv
            ((lowRippleProgram width).matrix interpretation)) = _ at binary
    rw [UnitaryOperator.unitaryOperator_reindex_cancel] at binary
    exact binary
  rw [program, Execution.unitaryOfEqualWires_matrix,
    ttkParallelLowRipple_matrix, sourceMatrix]
  apply Subtype.ext
  ext row column
  rfl

private def code (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context (width + width)) (context (width + width)) :=
  .unitary (program width)

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
Unit-duration depth is `5*width-5` for width at least two. The independent
first and final CNOT stages execute as actual parallel layers.
**Success.** Probability one with exact joint-state action. The zero-width
circuit has no events; the width-one circuit is one CNOT.
**Source.** The ancilla-free ripple construction is
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352]. The actual parallel
schedule retains every physical gate, operand and dependency. Its low-word
depth and boundary-width counts are proved for this implementation.
-/
public def problem (width : Nat) :
    Problem (.quantum AlgorithmGate.model .empty)
      (context (width + width)) (context (width + width)) .unit where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [StateRequirement.unitary (semanticOperator width)]
  resources :=
    { events := (width + 2 * (width - 1) + 2 * (width - 2)) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .cnot) +
        (2 * (width - 1)) •
          ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
            (.gate .toffoli)
      resident := space (width + width)
      auxiliary := space (width + width) }
  quantumTimeLimit := (if width - 1 = 0 then 0 else 1) +
    (3 * (width - 1) + 2 * (width - 2)) + (if width = 0 then 0 else 1)

/-- Execute the physically rescheduled low-word ripple and retain both supplied operands. -/
public def algorithm (width : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (context (width + width)) (context (width + width)) .unit where
  run := { code := code width, output := Output.all (context (width + width)) .unit }

private lemma actual_events (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path = (problem width).resources.events := by
  change ResourcePool.ofList (program width).eventTrace = _
  have cost : (program width).eventCost = (parallelLowRippleProgram width).eventCost :=
    Execution.unitaryOfEqualWires_cost
      (QubitLayout.canonical (encoding width).width).toQuantum
      (context (width + width)).quantumLayout (supplied_wires width)
      (parallelLowRippleProgram width) .empty .empty
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, cost, ttkParallelLowRipple_eventCost]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (lowRippleProgram width).eventCost = _
  rw [ttkLowRipple_native_count]
  simp only [problem, Multiset.count_add, Multiset.count_nsmul,
    ResourcePool.singleton, Multiset.count_replicate]

private lemma actual_resident (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ space (width + width) := by
  intro axis
  change Nat.max ((context (width + width)).residentSpace axis) 0 ≤ space (width + width) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (width : Nat) (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤ space (width + width) := by
  intro axis
  change Nat.max ((context (width + width)).auxiliarySpace axis) 0 ≤ space (width + width) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_depth (width : Nat) (path : (code width).Path) :
    (code width).depth (fun _ => 1) path =
      (if width - 1 = 0 then 0 else 1) + (3 * (width - 1) + 2 * (width - 2)) +
        (if width = 0 then 0 else 1) := by
  change DepthExpr.depthEval (fun _ => 1) ((program width).eventDepth .empty .empty) = _
  rw [program, Execution.unitaryOfEqualWires_depth]
  exact ttkParallelLowRipple_unitDepth width

/-- The actual ancilla-free ripple solves the independent all-state addition problem. -/
public theorem main (width : Nat) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem width) := by
  refine ⟨algorithm width, ?_⟩
  constructor
  · intro _environment _witness Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialized requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator width) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds environment (semanticOperator width)
      (program width) (program_matrix (interpretation := environment.quantum) width)
      (Output.all (context (width + width)) .unit) input
  · intro environment _witness Reference input _valid _initialized
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment rfl rfl
      (program width) (Output.all (context (width + width)) .unit) input
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact le_of_eq (actual_events width path)
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_resident width path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_auxiliary width path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact le_of_eq (actual_depth width path)

end

end QuantumAlg.MAU.Addition.TTK.Low
