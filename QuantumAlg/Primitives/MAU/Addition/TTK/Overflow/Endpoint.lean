/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Primitives.MAU.Addition.TTK.Overflow.Semantics
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
import all QuantumAlg.Primitives.MAU.Addition.TTK.Overflow.Semantics
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources

/-!
# Complete native TTK addition with an explicit XOR carry output

The ripple acts on exactly two operands and one supplied output bit. It
preserves the addend, writes the low sum and xors the carry into either initial
output value, with exact phase on arbitrary joint states
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK.Overflow

open QuantumAlg.MAU.Addition.TTK

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

private def semanticOperator (width : Nat) :
    UnitaryOperator (context (width + width + 1)).register :=
  UnitaryOperator.reindex (basisEquiv (width + width + 1)).symm (overflowOperator width)

private def program (width : Nat) : UnitaryCircuit (context (width + width + 1)).register :=
  UnitaryCircuit.reindex (basisEquiv (width + width + 1)).symm (completeOverflowProgram width)

private theorem program_matrix (width : Nat) :
    (program width).matrix = semanticOperator width := by
  exact (UnitaryCircuit.reindex_matrix (basisEquiv (width + width + 1)).symm
    (completeOverflowProgram width)).trans
      (congrArg (UnitaryOperator.reindex (basisEquiv (width + width + 1)).symm)
        (ttkCompleteOverflow_matrix width))

private theorem placement (width : Nat) :
    (program width).physical_idx = (context (width + width + 1)).physicalIdx := by
  change (completeOverflowProgram width).physical_idx = (context (width + width + 1)).physicalIdx
  rw [ttkCompleteOverflow_physical, ownedQubits_physicalIdx]

private def code (width : Nat) :
    Circuit (context (width + width + 1)) (context (width + width + 1)) :=
  .unitary (program width) (placement width)

/-- Independent complete addition-with-carry contract.

**Input.** Two supplied owned width-qubit words and one explicit output bit,
in any normalized joint state and with every external reference allowed.
The output bit can start in either value or a superposition; it need not be zero.
**Output.** Both words and the output bit remain live. The first word is
preserved, the second becomes the sum modulo 2^width, and the final carry is
xored into the initial output bit. The target is an independent exact unitary
on the full frame; the classical result is unit.
**Resource budget.** The native CNOT bound is width+2*(width-1)+2*(width-2)
plus one for width at least two. The Toffoli bound is 2*(width-1) plus one
for positive width. Subtraction is truncated in these all-width formulas.
Unit-duration serial depth is their sum. Resident and owned auxiliary bounds
are each 2*width+1 qubits, describing the same supplied operands and output.
There are no additional work qubits, other dimensions or classical cells.
**Success.** Probability one with the exact joint-state action. Width zero
retains the output bit and executes no gate. Width one executes one CNOT and
one Toffoli on its three supplied systems.
**Source.** The exact no-workspace ripple and carry gates are
[TTK09, qic-loglogaddition-quant.tex:285-318,330-352]. Actual serial counts and
boundary-width behavior are proved for this circuit, without using the source's
different parallel scheduling as the implemented depth.
-/
public def problem (width : Nat) :
    Problem .quantum (context (width + width + 1)) (context (width + width + 1)) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (semanticOperator width)]
  resources :=
    { events := (width + 2 * (width - 1) + 2 * (width - 2) + (if 2 ≤ width then 1 else 0)) •
        ResourcePool.singleton (.gate (.builtin "cnot")) +
        (2 * (width - 1) + (if width = 0 then 0 else 1)) •
          ResourcePool.singleton (.gate (.builtin "toffoli"))
      resident := space (width + width + 1)
      auxiliary := space (width + width + 1) }
  depth := .quantum (fun _ => 1)
    (width + 4 * (width - 1) + 2 * (width - 2) +
      (if 2 ≤ width then 1 else 0) + (if width = 0 then 0 else 1))

/-- Execute the literal overflow ripple and retain both operands and the XOR output. -/
public def algorithm (width : Nat) :
    Algorithm .quantum (context (width + width + 1)) (context (width + width + 1)) .unit where
  run := { code := code width, output := Output.all (context (width + width + 1)) .unit }

private theorem actual_events (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path = (problem width).resources.events := by
  change ResourcePool.ofList (program width).eventTrace = _
  have cost : (program width).eventCost = (overflowProgram width).eventCost :=
    (UnitaryCircuit.reindex_eventCost (basisEquiv (width + width + 1)).symm
      (completeOverflowProgram width)).trans (ttkCompleteOverflow_eventCost width)
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, cost]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (overflowProgram width).eventCost = _
  rw [ttkOverflow_native_count]
  simp only [problem, Multiset.count_add, Multiset.count_nsmul,
    ResourcePool.singleton, Multiset.count_replicate]

private theorem actual_resident (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ space (width + width + 1) := by
  intro axis
  change Nat.max ((context (width + width + 1)).residentSpace axis) 0 ≤
    space (width + width + 1) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (width : Nat) (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤ space (width + width + 1) := by
  intro axis
  change Nat.max ((context (width + width + 1)).auxiliarySpace axis) 0 ≤
    space (width + width + 1) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

/-- Exact native addition with arbitrary initial carry output and no extra workspace. -/
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
      (Output.all (context (width + width + 1)) .unit) input
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
    exact le_of_eq (ttkCompleteOverflow_depth width)

end

end QuantumAlg.MAU.Addition.TTK.Overflow
