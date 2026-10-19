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
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.State
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Resources

/-!
# Complete native shared-EEA XOR inversion

The unit domain of every positive modulus is a local quantum support
condition, including even and composite moduli and modulus one. Arbitrary
coherent or mixed inputs, arbitrary XOR targets, and
every external-reference extension are covered. The independent full-state
target uses the canonical ZMod inverse, while the actual run executes fixed
preparation and, for moduli greater than one, the verified finite native
compute, copy, and dagger lists. Modulus one executes identity on the same
complete prepared frame. This is a project proof extension of the source
prime domain.

All actual systems remain listed in Output. The separate in-place interface
for measured division retains its own smaller physical interface and budgets.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Two supplied owned n-qubit words: the input residue and the arbitrary XOR target. -/
@[reducible] public def inputContext (width : Nat) : RuntimeCtx .quantum :=
  InversePreparation.before width

/-- Both supplied words and every actually prepared shared-frame auxiliary remain live. -/
@[reducible] public def outputContext (width : Nat) : RuntimeCtx .quantum :=
  InversePreparation.after width

/-- The two words are read through their exact actual wire basis correspondence. -/
public def inputWords (width : Nat) (basis : (inputContext width).register.Index) :
    Fin (2 ^ width) × Fin (2 ^ width) :=
  InversePreparation.inputBasisEquiv width basis

/-- Independently specified complete native shared-EEA inversion.

**Input.** A positive modulus N is a compilation parameter and n=size(N).
Two owned n-qubit words may have any normalized mixed or coherent joint
state. The first word has local density support on x<N with gcd(x,N)=1;
the second word is arbitrary. All external-reference extensions are admitted.
This includes even and composite moduli and N=1, without extra fit,
clean-work, history, or positive-residue hypotheses.

**Output.** The complete joint action preserves x and XORs the canonical
ZMod inverse of x modulo N into the target. The original shared-frame
auxiliaries are actually prepared in fixed values and restored to precisely
those values. All input, target, and auxiliary systems are retained in Output;
the full state requirement preserves every relative phase and reference entry.
For N=1, the canonical inverse is zero and the actual full-frame identity
preserves both supplied words and every actually prepared auxiliary. This
XOR contract is distinct from modular-add inversion and division contracts.

**Resource budget.** Actual zero allocation and every fixed-seed X are charged.
Each of the six native X/CNOT/Toffoli and once-controlled coordinates has the
independent cap ForwardResources.xorBound(n), including actual finite
selectors, terminal counter repair, decoder, copy, and complete inverse.
Resident and owned auxiliary space each contain 3*n+4*size(n)+11 qubits and
zero classical bits. Unit-event depth is at most
1+auxiliaryWidth(n)+xorBound(n). These are
conservative bounds for this actual implementation, not a claim of the
paper's leading gate constant or the in-place division space count.

**Success.** The unit classical observation has probability one, and its
nonempty state requirement specifies the complete independent joint state.

**Source.** Shared registers and four phases are
[LYL+26, sec_EEA/sub_regshare.tex:16-26; sec_EEA/sub_4phase.tex:104-128].
The fixed schedule uses [LYL+26, app_proof/sub_stepnum.tex:4-16], with the
proved internal boundary corrections in the actual native construction.
The source assumes a prime modulus. Extension to all positive moduli and
unit residues, including the actual modulus-one branch, is a project proof
extension. Full density/reference interpretation uses [dW19, qcnotes.tex:5381,5394,5405].
-/
public def problem (modulus : Nat) (modulusPositive : 0 < modulus) :
    Problem (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size) .unit where
  Witness := Unit
  valid := fun _ _ => InverseSpecification.valid modulus
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [InverseTarget.requirement modulus modulusPositive]
  resources :=
    { events := InverseResources.events modulus
      resident := InverseResources.space modulus.size
      auxiliary := InverseResources.space modulus.size }
  quantumTimeLimit := InverseResources.depthBound modulus.size

/-- Execute fixed preparation and the modulus-selected unitary, exposing every live system. -/
public def algorithm (modulus : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (inputContext modulus.size) (outputContext modulus.size) .unit where
  run :=
    { code := InverseRuntime.code modulus
      output := Output.all (outputContext modulus.size) .unit }

/-- The same actual run meets the independent arithmetic, restoration, and resource contract. -/
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
    have same : requirement = InverseTarget.requirement modulus modulusPositive :=
      List.mem_singleton.mp present
    subst requirement
    exact InverseState.requirement_holds (runtimeEnvironment := environment) modulus modulusPositive
      (Output.all (outputContext modulus.size) .unit) input valid
  · intro environment _witness Reference input _valid _initial
    change Execution.observeBorrowedAfter (InverseRuntime.code modulus) Reference
      ((InverseRuntime.code modulus).execute environment Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
      Execution.observeBorrowed Reference input.state
    refine (InverseState.borrowedRestored (runtimeEnvironment := environment) modulus
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
    refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact InverseResources.resourcePool modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact InverseResources.resident modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    exact InverseResources.auxiliary modulus path
  · intro _environment _witness _Reference _input _valid _initial path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact InverseResources.depth modulus path

end

end QuantumAlg.MAU.Inversion.SharedEEA
