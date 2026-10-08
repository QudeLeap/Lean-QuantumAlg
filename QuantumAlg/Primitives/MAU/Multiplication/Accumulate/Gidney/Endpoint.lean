/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Semantics
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Semantics
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.NativeResources

/-!
# Complete native modular multiply-accumulate on two words

The actual selected pivot-flip offsets operate on the supplied source and
target words. Each stage borrows only source coordinates distinct from its
selector and restores those borrowed coordinates before the next stage.
The complete output retains both words and satisfies the independent exact
joint-state permutation, including an arbitrary external reference.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

private theorem supplied_wires (width : Nat) :
    (QubitLayout.canonical (encoding width).width).toQuantum.wires =
      (context (2 * width)).quantumLayout.wires := by
  rw [(gidneyAccumulate_interface width).1]
  exact Execution.OwnedQubits.canonical_wires (2 * width)

private def nativeOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) : UnitaryOperator (context (2 * width)).register :=
  UnitaryOperator.reindex
    (Execution.basisOfEqualWires
      (QubitLayout.canonical (encoding width).width).toQuantum
      (context (2 * width)).quantumLayout (supplied_wires width))
    (UnitaryOperator.reindex
      (QubitLayout.canonical (encoding width).width).basisEquiv.symm
      (wordAccumulateOperator width modulus coefficient))

private def nativeProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (context (2 * width)).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QubitLayout.canonical (encoding width).width).toQuantum
    (context (2 * width)).quantumLayout (supplied_wires width)
      (program width modulus coefficient)

private theorem nativeProgram_matrix (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (nativeProgram width modulus coefficient).matrix =
      nativeOperator width modulus coefficient := by
  unfold nativeOperator
  have sourceMatrix : (program width modulus coefficient).matrix =
      UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          (wordAccumulateOperator width modulus coefficient) := by
    have binary := congrArg
      (UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm)
      (gidneyAccumulate_matrix width modulus coefficient)
    change UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          (UnitaryOperator.reindex
            (QubitLayout.canonical (encoding width).width).basisEquiv
            (program width modulus coefficient).matrix) = _ at binary
    rw [UnitaryOperator.unitaryOperator_reindex_cancel] at binary
    exact binary
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix, sourceMatrix]

private def code (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context (2 * width)) (context (2 * width)) :=
  .unitary (nativeProgram width modulus coefficient)

/-- Independent exact modular multiply-accumulate execution contract.

**Input.**

- Two supplied owned width-qubit words in any joint normalized state,
including mixed states and correlations with an arbitrary external reference.
The fitted modulus N and natural coefficient a are compilation parameters.
No source or target initialization, coefficient inverse, or odd modulus is required.

**Output.**

- Both complete words remain in Output. On basis labels, the source x
is unchanged and a target y<N becomes (y+a*x) mod N; noncanonical target labels
are fixed. The full joint-state target is the independent arithmetic permutation
tensored with the reference identity, with exact phase.

**Resource budget.**

- The actual default-model X, CNOT, and Toffoli coordinates each have cap
width*stageEventBound(width). The stage bound is 9 at widths at most two and
4*modularOffsetEventBound(width) otherwise. Its recursive offset bound is
independent of the emitted gate list.
Resident and owned auxiliary coordinates both contain the same 2*width supplied
dimension-two systems; no extra quantum or classical system is allocated.
Unit-duration depth is at most width*stageEventBound(width).

**Success.**

- The unit result has probability one and the exact joint-state
target holds for every input. Width zero has no events and an empty live carrier.

**Source.**

- Actual pivot-flip modular offsets [G17, paper.tex:266-293,319-334],
internally borrowed constant offsets [HRS16, paper.tex:219-226,232-260], and
the selected binary-add recurrence [VBE95, 9511018.tex:333-367].
-/
public def problem (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    Problem (.quantum AlgorithmGate.model .empty)
      (context (2 * width)) (context (2 * width)) .unit where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (nativeOperator width modulus coefficient)]
  resources :=
    { events := nativeBudget width
      resident := space (2 * width)
      auxiliary := space (2 * width) }
  depth :=
    { duration := fun _ => 1
      limit := width * stageEventBound width
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- Execute the actual two-word circuit and explicitly retain its complete live output. -/
public def algorithm (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (context (2 * width)) (context (2 * width)) .unit where
  run :=
    { code := code width modulus coefficient
      output := Output.all (context (2 * width)) .unit }

/-- The public run retains the complete supplied two-word context. -/
public theorem gidneyAccumulate_output_listing (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (algorithm width modulus coefficient).run.output.listing = (context (2 * width)).keys := (rfl)

/-- The independent resident budget contains exactly the two supplied words. -/
public theorem gidneyAccumulate_resident_budget (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (problem width modulus coefficient).resources.resident = space (2 * width) := (rfl)

private theorem actual_events (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (path : (code width modulus coefficient).Path) :
    (code width modulus coefficient).resourcePool path ≤
      (problem width modulus coefficient).resources.events := by
  change ResourcePool.ofList (nativeProgram width modulus coefficient).eventTrace ≤
    nativeBudget width
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  have cost : (nativeProgram width modulus coefficient).eventCost =
      (program width modulus coefficient).eventCost :=
    Execution.unitaryOfEqualWires_cost
      (QubitLayout.canonical (encoding width).width).toQuantum
      (context (2 * width)).quantumLayout (supplied_wires width)
      (program width modulus coefficient) .empty .empty
  rw [cost]
  exact gidneyAccumulate_native_bound width modulus coefficient

private theorem actual_resident (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (path : (code width modulus coefficient).Path) :
    (code width modulus coefficient).peakResidentSpace path ≤ space (2 * width) := by
  intro axis
  change Nat.max ((context (2 * width)).residentSpace axis) 0 ≤ space (2 * width) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (path : (code width modulus coefficient).Path) :
    (code width modulus coefficient).peakAuxiliarySpace path ≤ space (2 * width) := by
  intro axis
  change Nat.max ((context (2 * width)).auxiliarySpace axis) 0 ≤ space (2 * width) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (path : (code width modulus coefficient).Path) :
    (code width modulus coefficient).depth (fun _ => 1) path ≤
      width * stageEventBound width := by
  change DepthExpr.depthEval (fun _ => 1)
    ((nativeProgram width modulus coefficient).eventDepth .empty .empty) ≤ _
  rw [nativeProgram, Execution.unitaryOfEqualWires_depth]
  exact gidneyAccumulate_depth_bound width modulus coefficient

/-- The native algorithm meets the independent arithmetic and coordinatewise resource contract. -/
public theorem main (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    ∃ candidate, Algorithm.Solves candidate (problem width modulus coefficient) := by
  refine ⟨algorithm width modulus coefficient, ?_⟩
  constructor
  · intro Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid _initialized requirement present
    have same : requirement = StateRequirement.unitary (nativeOperator width modulus coefficient) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (nativeOperator width modulus coefficient)
      (nativeProgram width modulus coefficient) (nativeProgram_matrix width modulus coefficient)
      (Output.all (context (2 * width)) .unit) input
  · intro Reference input _valid _initialized
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed rfl rfl
      (nativeProgram width modulus coefficient)
      (Output.all (context (2 * width)) .unit) input
  · intro _Reference _input _valid _initialized path _supported
    exact actual_events width modulus coefficient path
  · intro _Reference _input _valid _initialized path _supported
    exact actual_resident width modulus coefficient path
  · intro _Reference _input _valid _initialized path _supported
    exact actual_auxiliary width modulus coefficient path
  · intro _Reference _input _valid _initialized path _supported
    exact actual_depth width modulus coefficient path

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
