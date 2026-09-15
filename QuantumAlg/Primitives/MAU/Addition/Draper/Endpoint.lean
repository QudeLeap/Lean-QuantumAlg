/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Primitives.MAU.Addition.Draper.Semantics
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
import all QuantumAlg.Primitives.MAU.Addition.Draper.Semantics
import all QuantumAlg.Primitives.MAU.Addition.Draper.Resources

/-!
# Complete native Draper constant addition

The exact Fourier adder executes on the supplied target word and retains that
whole word in Output. Its independently defined modular translation acts on
every incoming state and preserves its full relation to an arbitrary external
reference. No carry register or measured classical result is allocated
[D00, paper.tex:216-233,302,352-365].
-/

namespace QuantumAlg.MAU.Addition.Draper

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

private def semanticOperator (width constant : Nat) : UnitaryOperator (context width).register :=
  UnitaryOperator.reindex (basisEquiv width).symm (wordTranslation width constant)

private def program (width constant : Nat) : UnitaryCircuit (context width).register :=
  UnitaryCircuit.reindex (basisEquiv width).symm (additionProgram width constant)

private theorem program_matrix (width constant : Nat) :
    (program width constant).matrix = semanticOperator width constant := by
  simp only [program, UnitaryCircuit.reindex_matrix, draperAddition_matrix, semanticOperator]

private theorem placement (width constant : Nat) :
    (program width constant).physical_idx = (context width).physicalIdx := by
  change (additionProgram width constant).physical_idx = (context width).physicalIdx
  rw [draperAddition_physical_idx, ownedQubits_physicalIdx]

private def code (width constant : Nat) : Circuit (context width) (context width) :=
  .unitary (program width constant) (placement width constant)

/-- Independent exact constant-addition execution contract.

**Input.** One supplied owned width-qubit word in any normalized state, including
mixed states and correlations with an arbitrary external reference. The natural
constant is a compilation parameter and allocates no runtime register.
**Output.** The same complete live word, transformed by addition of the constant
modulo 2^width. The joint target is the independent translation operator tensored
with the reference identity, with exact phase and no input factorization premise.
**Resource budget.** Exactly 2*width Hadamards, 2*(width choose 2) native controlled
QFT phases and width native single-qubit phases suffice. Both resident and owned
auxiliary coordinates are width dimension-two systems; they describe the same
word. There are no classical bits, other dimensions or extra carry systems.
Unit-duration depth is at most width*(width+1) plus one when width is positive.
**Success.** The unit result has probability one and the full joint-state target
holds for every input. Width zero is the zero-event identity on the empty word.
**Source.** Exact Fourier addition and known-constant rotations in
[D00, paper.tex:216-233,302,352-365]; counts and depth describe this actual exact
construction, including retained zero-angle phases.
-/
public def problem (width constant : Nat) :
    Problem .quantum (context width) (context width) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (semanticOperator width constant)]
  resources :=
    { events := (2 * width) • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        (2 * width.choose 2) • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
        width • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "phase"))
      resident := space width
      auxiliary := space width }
  depth := .quantum (fun _ => 1) (width * (width + 1) + (if width = 0 then 0 else 1))

/-- Execute the exact placed adder and explicitly retain the complete supplied word. -/
public def algorithm (width constant : Nat) :
    Algorithm .quantum (context width) (context width) .unit where
  run := { code := code width constant, output := Output.all (context width) .unit }

private theorem actual_events (width constant : Nat) (path : (code width constant).Path) :
    (code width constant).resourcePool path = (problem width constant).resources.events := by
  change ResourcePool.ofList (program width constant).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    UnitaryCircuit.reindex_eventCost, draperAddition_eventCost]
  rfl

private theorem actual_resident (width constant : Nat) (path : (code width constant).Path) :
    (code width constant).peakResidentSpace path ≤ space width := by
  intro axis
  change Nat.max ((context width).residentSpace axis) 0 ≤ space width axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (width constant : Nat) (path : (code width constant).Path) :
    (code width constant).peakAuxiliarySpace path ≤ space width := by
  intro axis
  change Nat.max ((context width).auxiliarySpace axis) 0 ≤ space width axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

/-- The complete native exact adder meets its independent all-state and resource contract. -/
public theorem main (width constant : Nat) :
    ∃ candidate, Algorithm.Solves candidate (problem width constant) := by
  refine ⟨algorithm width constant, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator width constant) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (semanticOperator width constant)
      (program width constant) (placement width constant) (program_matrix width constant)
      (Output.all (context width) .unit) input
  · intro Reference input _valid
    exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (program width constant) (placement width constant)
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact le_of_eq (actual_events width constant path)
  · intro _Reference _input _valid path _supported
    exact actual_resident width constant path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary width constant path
  · intro _Reference _input _valid path _supported
    exact le_of_eq (draperAddition_unit_depth width constant)

end

end QuantumAlg.MAU.Addition.Draper
