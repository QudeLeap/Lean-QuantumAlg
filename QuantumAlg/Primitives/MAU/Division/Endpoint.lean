/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.State
import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.Resources

/-!
# Complete modular-add division for every positive modulus and unit denominator

The original modular-add Data action is implemented by actual fixed auxiliary
preparation and complete shared-EEA compute, variable product accumulation,
and the identical full uncomputation. The supplied numerator, arbitrary target,
and original flag remain physical owned systems. Every valid mixed or coherent
input and arbitrary external-reference extension is covered. The source's prime
inversion construction is extended here to general positive unit domains;
this endpoint is a project composition, with independent conservative bounds.
-/

namespace QuantumAlg.MAU.Division

noncomputable section

open SharedEEA

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual supplied denominator, numerator, arbitrary modular target, and original live flag. -/
@[reducible] public def inputContext (width : Nat) : RuntimeCtx .quantum :=
  ExecutionLayout.before width

/-- All supplied systems and every actually prepared EEA auxiliary remain owned and live. -/
@[reducible] public def outputContext (width : Nat) : RuntimeCtx .quantum :=
  ExecutionLayout.after width

/-- Read every original data field through its exact actual physical basis correspondence. -/
public def inputFields (width : Nat) (basis : (inputContext width).register.Index) :
    Fin (2 ^ width) × ((Fin (2 ^ width) × Fin (2 ^ width)) × Bool) :=
  ExecutionLayout.inputBasisEquiv width basis

/-- Independently specified complete unit-denominator modular-add division.

**Input.** A positive modulus N is a compilation parameter and n=size(N).
Three owned n-qubit words encode denominator x, numerator y, and target z;
one owned qubit is the original flag f. Any normalized mixed or coherent
joint state is permitted whose local density support has x<N, gcd(x,N)=1,
y<N, and z<N. The numerator may be zero or a nonunit, the target may be any
modular value, and the flag is arbitrary. Every external-reference extension
is admitted. Even/composite moduli and N=1 require no extra width, parity,
clean-work, positive-residue, history, or input/reference separation promise.

**Output.** The independent complete joint action is
(x,y,z,f) -> (x,y,z+y*x^(-1) mod N,f), exactly the original
Data.addQuotientIntoTarget action on every unit denominator. The actual fixed
EEA auxiliary preparation is retained and restored to the same complete values.
Every denominator, numerator, target, flag, and auxiliary system is listed in
Output.all. All relative phases and joint-reference coherences are retained.
For N=1, the same actual preparation precedes full-frame identity, and every
supplied and prepared field remains unchanged.

**Resource budget.** Zero allocation and fixed-seed X gates precede arithmetic. The independent
coordinatewise native envelope is SharedEEA.nativeBudget(n), containing both
corrected EEA passes and all actual VariableGidney product-accumulation stages.
Resident and owned auxiliary space each contain 4*n+4*size(n)+12 qubits and
zero classical bits, including the supplied flag. Unit-event depth is at most
1+auxiliaryWidth(n)+SharedEEA.eventBound(n). Here eventBound(n) covers both
corrected EEA passes and n controlled MAC stages, each charged from its
literal gate list. These are conservative bounds for this composition, not
the source's measured-division space count or leading gate constant. The
N=1 branch still pays the same zero allocation and seed loading and retains
the complete physical frame.

**Success.** The unit classical observation is accepted with probability one;
a nonempty state requirement specifies the entire independent joint density.
Borrowed/reference restoration is separately proved for this same actual run.

**Source.** Shared EEA storage and the four-phase inversion construction are
[LYL+26, sec_EEA/sub_regshare.tex:16-26; sec_EEA/sub_4phase.tex:104-128].
The source's fixed schedule is [LYL+26, app_proof/sub_stepnum.tex:4-16].
That source assumes a prime modulus and nonzero input. General positive unit
domains, the actual modulus-one branch, and modular-add division into an
arbitrary target with the original flag are project proof extensions and
composition results; they are not attributed to the source's measured route.
Mixed density and local-unitary interpretation use [dW19, qcnotes.tex:5381,5394,5405].
-/
public def problem (modulus : Nat) (modulusPositive : 0 < modulus) :
    Problem (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size) .unit where
  Witness := Unit
  valid := fun _ _ => ExecutionLayout.valid modulus
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [ExecutionTarget.requirement modulus modulusPositive]
  resources :=
    { events := ExecutionResources.events modulus
      resident := ExecutionResources.space modulus.size
      auxiliary := ExecutionResources.space modulus.size }
  quantumTimeLimit := ExecutionResources.depthBound modulus.size

/-- Execute one fixed preparation and the complete modulus-selected native body, retaining all
  keys. -/
public def algorithm (modulus : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size) .unit where
  run :=
    { code := ExecutionRuntime.code modulus
      output := Output.all (outputContext modulus.size) .unit }

/-- This same actual run meets the independent original-data action and complete resource
  contract. -/
public theorem main (modulus : Nat) (modulusPositive : 0 < modulus) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate
      (problem modulus modulusPositive) := by
  refine ⟨algorithm modulus, ?_⟩
  constructor
  · intro environment _witness Reference input _valid _initial
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input valid _initial requirement present
    have same : requirement = ExecutionTarget.requirement modulus modulusPositive :=
      List.mem_singleton.mp present
    subst requirement
    exact ExecutionStateProof.divisionState_requirement_holds
      (runtimeEnvironment := environment) modulus modulusPositive
      (Output.all (outputContext modulus.size) .unit) input valid
  · intro environment _witness Reference input _valid _initial
    change Execution.observeBorrowedAfter (ExecutionRuntime.code modulus) Reference
      ((ExecutionRuntime.code modulus).execute environment Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
      Execution.observeBorrowed Reference input.state
    refine (ExecutionStateProof.divisionState_borrowedRestored
      (runtimeEnvironment := environment) modulus
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
    refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact ExecutionResources.divisionResources_events modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact ExecutionResources.divisionResources_resident modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact ExecutionResources.divisionResources_auxiliary modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact ExecutionResources.divisionResources_depth modulus path

end

end QuantumAlg.MAU.Division
