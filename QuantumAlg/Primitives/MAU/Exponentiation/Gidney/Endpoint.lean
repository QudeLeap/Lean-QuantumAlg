/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Endpoint.Execution
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Endpoint.Execution

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Context
public import QuantumAlg.Primitives.MAU.Exponentiation.WordAction
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Problem

import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Requirement
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Resources
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Counts
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Examples
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Native arbitrary-target XOR exponentiation with internal work preparation

The incoming exponent and target may be in any normalized joint state.
The actual program prepares the missing identity-power and zero auxiliary
words, executes the literal selected-power gate list, and retains every live system.
Its independent complete state target includes every external reference.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.SuppliedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent XOR exponentiation with internally allocated work words.

**Input.**

- One caller-supplied interface containing an exponentWidth-qubit exponent and a width-qubit
arbitrary XOR target, in any normalized mixed state and with any external
reference. A positive fitted modulus N and a unit base in ZMod N are compilation
parameters. Even N, N=1, exponentWidth=0, and width=0 are included. The caller
supplies no initialized work word and no canonical-target premise.

**Output.**

- The complete output retains the exponent, transformed target, and both internally
prepared words. On a basis input (x,t), the target becomes t XOR (base^x mod N),
the exponent remains x, and the work words return to (0,0). The full
joint-state target tensors the incoming state with that declared work basis
and applies the independent exact finite exponentiation operator, preserving
all relative phases and external reference correlations.

**Resource budget.**

- Every fresh work qubit contributes its actual zero-preparation event. The
independent native budget covers identity loading and unloading, selected-power
compute and uncompute, and the literal CNOT copy. Each native gate coordinate
is bounded by `8*exponentWidth*M(width)+3*width`, where `M` is the registered
multiplier envelope. Resident space is exponentWidth+3*width qubits, and
auxiliary space is the two prepared width-qubit words. The unit-duration depth
bound includes the preparation layer and the complete arithmetic gate schedule.

**Success.**

- The unit result has probability one. The complete reference-aware state
promise holds for every admitted input. Empty work layouts retain their actual
preparation event while allocating zero work systems. Every live entry appears
in the output, and borrowed-restoration obligations follow from the execution.

**Source.**

- The modular-power target and reversible XOR form follow the selected-power
construction [VBE95, 9511018.tex:372-416]. The implementation composes the
registered arithmetic components with literal selected-power controls, copying,
and inverse computation; its budgets follow the actual elementary event trace.
-/
public def problem (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Problem model (context (exponentWidth + width)) (preparedContext exponentWidth width)
      .unit where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [preparedRequirement exponentWidth width modulus positive base]
  resources :=
    { events := arithmeticPreparedNativeBudget exponentWidth width
      resident := space (exponentWidth + 3 * width)
      auxiliary := space (2 * width) }
  quantumTimeLimit := arithmeticPreparedNativeDepth exponentWidth width

set_option maxHeartbeats 800000 in
-- The endpoint proof expands both the native execution trace and the borrowed-register
-- observation; the larger budget is confined to this theorem.
/-- Actual preparation and XOR exponentiation satisfy the complete independent native problem. -/
private lemma complete_correct
    (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Algorithm.Solves (algorithm exponentWidth width modulus positive base)
      (problem exponentWidth width modulus positive base) := by
  constructor
  · intro environment _witness Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialization requirement present
    have same : requirement = preparedRequirement exponentWidth width modulus positive base :=
      List.mem_singleton.mp present
    subst requirement
    exact gidneyExponentPreparedRequirement_holds exponentWidth width modulus positive base
      (Output.all (preparedContext exponentWidth width) .unit)
      (environment := environment) input
  · intro environment _witness Reference input _valid _initialization
    change Execution.observeBorrowedAfter
      (arithmeticNativeCode exponentWidth width modulus positive base) Reference
        ((arithmeticNativeCode exponentWidth width modulus positive base).execute
          environment Reference
          (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
      Execution.observeBorrowed Reference input.state
    refine (actual_borrowed exponentWidth width modulus positive base (environment := environment)
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
    refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact arithmeticNativeCode_native_bound exponentWidth width modulus positive base path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact arithmeticNativeCode_resident_bound exponentWidth width modulus positive base path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact arithmeticNativeCode_auxiliary_bound exponentWidth width modulus positive base path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact arithmeticNativeCode_depth_bound exponentWidth width modulus positive base path

/-- The actual native algorithm realizes the independently stated unit-base problem. -/
lemma mainOfUnit (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate
      (problem exponentWidth width modulus positive base) :=
  ⟨algorithm exponentWidth width modulus positive base,
    complete_correct exponentWidth width modulus positive base⟩

/-- **Modular exponentiation.** A positive fitted modulus and a bounded
coprime natural base determine the complete reversible XOR implementation.
The finite base representation is converted to a unit only from the stated
coprimality witness. -/
public theorem main (exponentWidth width N a : Nat) (positive : 0 < N)
    (fitted : N ≤ 2 ^ width) (_baseBound : a < N) (coprime : Nat.Coprime a N) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate
      (problem exponentWidth width
        (⟨N, Nat.lt_succ_of_le fitted⟩ : Fin (2 ^ width + 1)) positive
        (ZMod.unitOfCoprime a coprime)) :=
  mainOfUnit exponentWidth width
    (⟨N, Nat.lt_succ_of_le fitted⟩ : Fin (2 ^ width + 1)) positive
    (ZMod.unitOfCoprime a coprime)

end

end QuantumAlg.MAU.Exponentiation.Gidney
