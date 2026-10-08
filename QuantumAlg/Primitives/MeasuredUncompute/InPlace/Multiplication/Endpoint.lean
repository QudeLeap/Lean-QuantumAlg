/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Components.GateModel.Algorithm
public import Mathlib.Data.Nat.Prime.Defs
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Requirement
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Restoration
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication.Resources
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete measured in-place modular multiplication

The actual fixed preparation, native arithmetic, Z writes, stored-value
correction and final swap belong to one execution. The independent target
prescribes the complete original two-word arithmetic beside every restored
auxiliary bit and arbitrary external reference. Retained outcomes remain
actual finite classical cells in the complete Output.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceMultiplication

noncomputable section

open Execution MAU.Inversion.SharedEEA

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original two owned words retain their actual physical identities. -/
@[reducible] public def inputContext (width : Nat) : RuntimeCtx .quantum :=
  InversePreparation.before width

/-- Every original word, shared-frame auxiliary and finite measurement cell remains live. -/
@[reducible] public def outputContext (width : Nat) : RuntimeCtx .quantum :=
  NumeratorMeasurement.context width

/-- Independent complete-state contract for measured in-place multiplication.

**Input.**

A prime modulus p is a compilation parameter and n=size(p).
The two owned n-qubit words X,Y have any normalized coherent or mixed
joint state supported on 0<X<p and 0<=Y<p. All external-reference
extensions are admitted, including Y=0 and p=2. No auxiliary preparation,
measurement outcome or computed inverse is supplied by the caller.

**Output.**

Preserve X and replace Y by X*Y modulo p. The
full independent target restores the actually prepared A=0 and fixed
shared-EEA auxiliary state, retaining every reference matrix entry. Output
lists all live systems and reads the n actual finite Z-result cells.
The state promise aggregates these outcomes without dropping any quantum
system or claiming that listing resources proves their restoration.

**Resource budget.**

The independent native allowance is
InPlaceMultiplicationResources.events(p): one fixed preparation followed by
the proved EEA, product, measured-reset, selected product-correction and
swap component bounds in actual execution order. Resident and owned
auxiliary capacity are each 3*n+4*size(n)+11 qubits plus n retained
classical bits. Unit-event depth is at most
InPlaceMultiplicationResources.depthBound(n), including preparation and
measurement-to-correction dependencies. These are upper bounds for the
actual finite implementation; no asymptotic leading constant is claimed.

**Success.**

The complete independent state requirement holds with
probability one. Every actual stored result is accepted and remains
available to subsequent classical reads.

**Source.**

The measured arithmetic sequence and shared frame are
[LYL+26, sec_point_add/sec_point_add.tex:119-122], with the original
arithmetic domain in [LYL+26, sec_point_add/sec_point_add.tex:24-36].
The joint density interpretation uses [dW19, qcnotes.tex:5381,5394,5405].
-/
public def problem (modulus : Nat) (prime : Nat.Prime modulus) :
    Problem (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size)
      (.fixedVector modulus.size (.finite 2)) where
  valid := InPlaceDomain.valid modulus
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [InPlaceRequirement.requirement .multiplication modulus prime]
  resources :=
    { events := InPlaceMultiplicationResources.events modulus
      resident := InPlaceDivisionResources.space modulus.size
      auxiliary := InPlaceDivisionResources.space modulus.size }
  depth :=
    { duration := fun _ => 1
      limit := InPlaceMultiplicationResources.depthBound modulus.size
      classicalQuery_unit := fun coordinate => nomatch coordinate
      quantumQuery_unit := fun coordinate => nomatch coordinate }

/-- The single actual circuit exposes all live storage and reads its real measurement results. -/
public def algorithm (modulus : Nat) (prime : Nat.Prime modulus) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size)
      (.fixedVector modulus.size (.finite 2)) where
  run := { code := code modulus prime, output := output modulus.size }

/-- The same actual run meets the independent full-state, restoration and resource contract. -/
public theorem main (modulus : Nat) (prime : Nat.Prime modulus) :
    ∃ candidate, Algorithm.Solves candidate (problem modulus prime) := by
  refine ⟨algorithm modulus prime, ?_⟩
  constructor
  · intro Reference input _valid _initial
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input valid _initial requirement present
    have same : requirement = InPlaceRequirement.requirement .multiplication modulus prime :=
      List.mem_singleton.mp present
    subst requirement
    exact InPlaceRequirement.multiplication_holds modulus prime (output modulus.size) input valid
  · intro Reference input _valid _initial
    change Execution.observeBorrowedAfter (code modulus prime) Reference
      ((code modulus prime).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
      Execution.observeBorrowed Reference input.state
    refine (InPlaceRestoration.multiplication_restored modulus prime
      (input.state.mapClassical fun value => (value.1, (value.2, value.1)))).trans ?_
    refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _Reference _input _valid _initial path _supported
    exact InPlaceMultiplicationResources.event_budget modulus prime path
  · intro _Reference _input _valid _initial path _supported
    exact InPlaceMultiplicationResources.resident modulus prime path
  · intro _Reference _input _valid _initial path _supported
    exact InPlaceMultiplicationResources.auxiliary modulus prime path
  · intro _Reference _input _valid _initial path _supported
    exact InPlaceMultiplicationResources.depth modulus prime path

end

end QuantumAlg.MeasuredUncompute.InPlaceMultiplication
