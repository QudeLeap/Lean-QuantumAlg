/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Semantics
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

private def wordBasisEquiv (width : Nat) :
    (context (2 * width)).register.Index ≃ (Qubits (encoding width).width).Index :=
  (basisEquiv (2 * width)).trans
    (finCongr (congrArg (fun size : Nat => 2 ^ size) (Nat.two_mul width)))

private def nativeOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) : UnitaryOperator (context (2 * width)).register :=
  UnitaryOperator.reindex (wordBasisEquiv width).symm
    (wordAccumulateOperator width modulus coefficient)

private def nativeProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) : UnitaryCircuit (context (2 * width)).register :=
  UnitaryCircuit.reindex (wordBasisEquiv width).symm (program width modulus coefficient)

private theorem nativeProgram_matrix (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (nativeProgram width modulus coefficient).matrix =
      nativeOperator width modulus coefficient := by
  exact (UnitaryCircuit.reindex_matrix (R := Qubits (encoding width).width)
    (S := (context (2 * width)).register) (wordBasisEquiv width).symm
    (program width modulus coefficient)).trans
      (congrArg (fun operator : UnitaryOperator (Qubits (encoding width).width) =>
        UnitaryOperator.reindex (wordBasisEquiv width).symm operator)
        (gidneyAccumulate_matrix width modulus coefficient))

private theorem placement (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (nativeProgram width modulus coefficient).physical_idx = (context (2 * width)).physicalIdx := by
  change (program width modulus coefficient).physical_idx = (context (2 * width)).physicalIdx
  rw [gidneyAccumulate_physical, ownedQubits_physicalIdx]

private def code (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    Circuit (context (2 * width)) (context (2 * width)) :=
  .unitary (nativeProgram width modulus coefficient) (placement width modulus coefficient)

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

- Six explicit native coordinates are permitted: X, CNOT,
and Toffoli with one or two additional dimension-two controls. Each has cap
width*stageEventBound(width), where the stage bound is 9 at widths at most two
and 6*F(width+1)+12*F(width)+6*width+6 otherwise, with F(w)=w*(39*clog(2,w)+1).
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
    Problem .quantum (context (2 * width)) (context (2 * width)) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (nativeOperator width modulus coefficient)]
  resources :=
    { events := nativeBudget width
      resident := space (2 * width)
      auxiliary := space (2 * width) }
  depth := .quantum (fun _ => 1) (width * stageEventBound width)

/-- Execute the actual two-word circuit and explicitly retain its complete live output. -/
public def algorithm (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    Algorithm .quantum (context (2 * width)) (context (2 * width)) .unit where
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
  exact (UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (nativeProgram width modulus coefficient)).le.trans
      ((UnitaryCircuit.reindex_eventCost (R := Qubits (encoding width).width)
        (S := (context (2 * width)).register) (wordBasisEquiv width).symm
        (program width modulus coefficient)).le.trans
          (gidneyAccumulate_native_bound width modulus coefficient))

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

/-- The native algorithm meets the independent arithmetic and coordinatewise resource contract. -/
public theorem main (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    ∃ candidate, Algorithm.Solves candidate (problem width modulus coefficient) := by
  refine ⟨algorithm width modulus coefficient, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = StateRequirement.unitary (nativeOperator width modulus coefficient) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (nativeOperator width modulus coefficient)
      (nativeProgram width modulus coefficient) (placement width modulus coefficient)
      (nativeProgram_matrix width modulus coefficient)
      (Output.all (context (2 * width)) .unit) input
  · intro Reference input _valid
    exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (nativeProgram width modulus coefficient) (placement width modulus coefficient)
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact actual_events width modulus coefficient path
  · intro _Reference _input _valid path _supported
    exact actual_resident width modulus coefficient path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary width modulus coefficient path
  · intro _Reference _input _valid path _supported
    exact gidneyAccumulate_depth_bound width modulus coefficient

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
