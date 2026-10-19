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
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.Basic
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Agreement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Target
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.State
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Runtime.Resources

/-!
# Complete native modular-add inversion on the original unit domain

The actual fixed preparation and shared-EEA compute, modular accumulation,
and complete inverse realize the original arbitrary-target data action.
The supplied flag and every auxiliary remain physically live and counted.
Complete supported mixed states and arbitrary external references are
covered, including the modulus-one branch after actual preparation.
-/

namespace QuantumAlg.MAU.Inversion

noncomputable section

open SharedEEA

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Original input, arbitrary target, and supplied flag on their actual wire identities. -/
@[reducible] public def inputContext (width : Nat) : RuntimeCtx .quantum :=
  AccumulateRuntime.before width

/-- Every original data bit and every fixed source auxiliary remain in the complete output. -/
@[reducible] public def outputContext (width : Nat) : RuntimeCtx .quantum :=
  AccumulateRuntime.after width

/-- Canonical binary encoding of every original modular-inversion datum, including either flag. -/
def inputData (modulus : Nat) (modulusPositive : 0 < modulus) (value : Data modulus) :
    (inputContext modulus.size).register.Index :=
  (AccumulateRuntime.inputBasisEquiv modulus.size).symm
    (Accumulate.residueWord modulus modulusPositive value.input,
      Accumulate.residueWord modulus modulusPositive value.target, value.flag)

/-- Original data internally satisfy the complete local input domain, including modulus one. -/
lemma modularInversion_inputData_admissible (modulus : Nat)
    (modulusPositive : 0 < modulus) (value : Data modulus) :
    AccumulateSpecification.admissible modulus
      (AccumulateRuntime.inputBasisEquiv modulus.size
        (inputData modulus modulusPositive value)) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  rw [inputData, Equiv.apply_symm_apply]
  exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime value.input, ZMod.val_lt _⟩

/-- The independent target is exactly the original modular-add data operation for every datum. -/
lemma modularInversion_inputData_target (modulus : Nat)
    (modulusPositive : 0 < modulus) (value : Data modulus) :
    AccumulateTarget.inputPermutation modulus modulusPositive
        (inputData modulus modulusPositive value) =
      inputData modulus modulusPositive value.addInverseIntoTarget := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  have fields := AccumulateSpecification.accumulateSpecification_valid modulus modulusPositive
    (Accumulate.residueWord modulus modulusPositive value.input,
      Accumulate.residueWord modulus modulusPositive value.target, value.flag) (ZMod.val_lt _)
  apply (AccumulateRuntime.inputBasisEquiv modulus.size).injective
  rw [AccumulateTarget.accumulateTarget_input_read]
  simp only [inputData, Equiv.apply_symm_apply]
  apply Prod.ext
  · exact fields.1
  · apply Prod.ext
    · apply Fin.ext
      exact fields.2.1.trans (congrArg Fin.val
        (Accumulate.accumulateOutput_unit modulus modulusPositive value.input value.target))
    · exact fields.2.2

/-- Independent complete modular-add inversion.

**Input.** A positive modulus N is fixed and n=size(N). The supplied
owned quantum data consists of an n-bit unit residue x, an arbitrary
canonical n-bit target t, and one flag qubit. The local density support
requires x<N, gcd(x,N)=1 and t<N. All normalized coherent or mixed states
on that support and all external-reference extensions are admitted.
Even and composite moduli and N=1 are included. Fixed auxiliary values
are produced by actual preparation, without a caller clean-work premise.

**Output.** The complete joint arithmetic action is
(x,t,flag) -> (x,t+x^{-1} mod N,flag). This is the original
Data.addInverseIntoTarget operation, as proved by its binary encoding.
All prepared auxiliaries are restored to their prescribed fixed basis;
all data, auxiliaries and reference coherences remain in the full state
requirement. Modulus one performs full-frame identity after preparation.
Every live storage key is listed exactly once in the complete Output.

**Resource budget.** Actual zero allocation and every fixed-seed X are charged. The independent
native envelope is two complete corrected EEA envelopes plus the
coefficient-one Gidney accumulation envelope. The strict unit-event depth
is at most 1+auxiliaryWidth(n)+2*C(n)+n*B(n), where C is correctedBound and B is
Gidney.stageEventBound. Resident and owned auxiliary space each contain
3*n+4*size(n)+12 qubits and zero classical bits, including the original
flag. These conservative bounds concern this actual implementation.

**Success.** The classical unit observation has probability one. The
complete independently specified joint state and mandatory borrowed
restoration are proved separately for the same actual run.

**Source.** The shared-register EEA and retained forward state come from
[LYL+26, sec_EEA/sub_regshare.tex:16-26; sec_EEA/sub_4phase.tex:99-128].
Modular addition uses [G17, paper.tex:319-334]. The actual compute-add-dagger
composition and extension from the source prime domain to all positive
moduli and unit residues are project results. Mixed-state interpretation
uses [dW19, qcnotes.tex:5381,5394,5405].
-/
public def problem (modulus : Nat) (modulusPositive : 0 < modulus) :
    Problem (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size) .unit where
  Witness := Unit
  valid := fun _ _ => AccumulateTarget.valid modulus
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [AccumulateTarget.requirement modulus modulusPositive]
  resources :=
    { events := AccumulateResources.events modulus
      resident := AccumulateResources.space modulus.size
      auxiliary := AccumulateResources.space modulus.size }
  quantumTimeLimit := AccumulateResources.depthBound modulus.size

/-- Execute the one actual prepared modular-add inverse and manifest every surviving system. -/
public def algorithm (modulus : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size) .unit where
  run :=
    { code := AccumulateRuntime.code modulus
      output := Output.all (outputContext modulus.size) .unit }

/-- The actual prepared native program meets the complete original modular-add inverse contract. -/
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
    have same : requirement = AccumulateTarget.requirement modulus modulusPositive :=
      List.mem_singleton.mp present
    subst requirement
    exact AccumulateState.accumulateState_requirement_holds
      (runtimeEnvironment := environment) modulus modulusPositive
      (Output.all (outputContext modulus.size) .unit) input valid
  · intro environment _witness Reference input _valid _initial
    change Execution.observeBorrowedAfter (AccumulateRuntime.code modulus) Reference
      ((AccumulateRuntime.code modulus).execute environment Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
      Execution.observeBorrowed Reference input.state
    refine (AccumulateState.accumulateState_borrowedRestored
      (runtimeEnvironment := environment) modulus
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
    refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact AccumulateResources.accumulateResources_events modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact AccumulateResources.accumulateResources_resident modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact AccumulateResources.accumulateResources_auxiliary modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact AccumulateResources.accumulateResources_depth modulus path

end

end QuantumAlg.MAU.Inversion
