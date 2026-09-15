/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Context
public import QuantumAlg.Primitives.MAU.Exponentiation.WordAction
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Requirement
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Resources

/-!
# Native arbitrary-target XOR exponentiation with internal work preparation

The incoming exponent and target may be in any normalized joint state.
The actual program prepares the missing identity-power and zero auxiliary
words, executes the selected-power oracle, and retains every live system.
Its independent complete state target includes every external reference.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.OwnedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent XOR exponentiation with internally allocated work words.

**Input.**

- One owned bank containing an exponentWidth-qubit exponent and a width-qubit
arbitrary XOR target, in any normalized mixed state and with any external
reference. A positive fitted modulus N and a unit base in ZMod N are compilation
parameters. Even N, N=1, exponentWidth=0, and width=0 are included. The caller
supplies no initialized work word and no canonical-target premise.

**Output.**

- The complete output retains the exponent, original target, and both internally
prepared words. On a basis input (x,t), the target becomes t XOR (base^x mod N),
the exponent remains x, and the work words return to (1 mod N,0). The full
joint-state target tensors the incoming state with that declared work basis
and applies the independent exact finite exponentiation operator, preserving
all relative phases and external reference correlations.

**Resource budget.**

- One declared two-word preparation event and the independent native oracle pool:
twice exponentWidth copies of the controlled unit-multiplier pool, plus width
native CNOT events for the literal XOR copy. Every controlled label is retained.
The unit multiplier has bound M(width)=2*width*B(width)+3*width, where B(w) is 9
for w at most two and 6*F(w+1)+12*F(w)+6*w+6 otherwise, with
F(w)=w*(39*clog(2,w)+1). Resident and owned auxiliary peaks are the same
exponentWidth+3*width dimension-two systems. Unit-duration depth is at most
1+2*exponentWidth*M(width)+width.

**Success.**

- The unit result has probability one. The complete reference-aware state
promise holds for every admitted input. Empty work layouts retain their actual
preparation event while allocating zero work systems. Every live entry appears
in the output, and borrowed-restoration obligations follow from the execution.

**Source.**

- Selected binary powers, initialized identity, reversible multiplication and
cleanup [VBE95, 9511018.tex:372-416], implemented using unit-inverse arithmetic
[G17, paper.tex:186-211], actual pivot-flip modular offsets
[G17, paper.tex:266-293,319-334], and the internally borrowed HRS adder
[HRS16, paper.tex:219-226,232-260].
-/
public def problem (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Problem .quantum (context (exponentWidth + width)) (preparedContext exponentWidth width)
      .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [preparedRequirement exponentWidth width modulus positive base]
  resources :=
    { events := preparedNativeBudget exponentWidth width modulus positive
      resident := space (exponentWidth + 3 * width)
      auxiliary := space (exponentWidth + 3 * width) }
  depth := .quantum (fun _ => 1) (1 + oracleEventBound exponentWidth width)

/-- Prepare the two work words, execute the actual XOR oracle, and retain every live entry. -/
public def algorithm (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Algorithm .quantum (context (exponentWidth + width)) (preparedContext exponentWidth width)
      .unit where
  run :=
    { code := nativeCode exponentWidth width modulus positive base
      output := Output.all (preparedContext exponentWidth width) .unit }

/-- Both input fields and both internally prepared work words remain in the complete output. -/
public theorem gidneyExponentiation_output_listing (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (algorithm exponentWidth width modulus positive base).run.output.listing =
      (preparedContext exponentWidth width).keys := (rfl)

/-- The public problem includes its complete joint-state requirement. -/
public theorem gidneyExponentiation_stateRequirement_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (problem exponentWidth width modulus positive base).states.length = 1 := (rfl)

/-- The resident budget counts the supplied exponent and target plus exactly two prepared words. -/
public theorem gidneyExponentiation_resident_budget (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (problem exponentWidth width modulus positive base).resources.resident =
      space (exponentWidth + 3 * width) := (rfl)

private theorem actual_borrowed (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) {Reference : Register}
    {H : Type} [Fintype H]
    (state : Execution.State (context (exponentWidth + width)) Reference H) :
    (nativeCode exponentWidth width modulus positive base).BorrowedRestored Reference state
      ((nativeCode exponentWidth width modulus positive base).execute Reference state) := by
  let : Subsingleton (context (exponentWidth + width)).borrowedClassicalShape.Value := by
    change Subsingleton (CShape.Value .unit)
    exact ⟨fun left right => by cases left; cases right; rfl⟩
  let preparation := Circuit.prepare (context (exponentWidth + width)) workKey
    (workLayout exponentWidth width) (gidneyExponentWork_fresh exponentWidth width)
    (gidneyExponentWork_disjoint exponentWidth width)
    (workPreparation exponentWidth width modulus positive)
  exact Circuit.borrowedRestored_seq preparation
    (Circuit.unitary (nativeUnitary exponentWidth width modulus base)
      (gidneyExponentNativeUnitary_physical exponentWidth width modulus base)) state
    (Circuit.borrowedRestored_prepare_noBorrowedQuantum rfl state workKey
      (workLayout exponentWidth width) (gidneyExponentWork_fresh exponentWidth width)
      (gidneyExponentWork_disjoint exponentWidth width)
      (workPreparation exponentWidth width modulus positive))
    (Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (nativeUnitary exponentWidth width modulus base)
      (gidneyExponentNativeUnitary_physical exponentWidth width modulus base)
      (preparation.execute Reference state))

/-- Actual preparation and XOR exponentiation satisfy the complete independent native problem. -/
public theorem main (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    ∃ candidate, Algorithm.Solves candidate
      (problem exponentWidth width modulus positive base) := by
  refine ⟨algorithm exponentWidth width modulus positive base, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = preparedRequirement exponentWidth width modulus positive base :=
      List.mem_singleton.mp present
    subst requirement
    exact gidneyExponentPreparedRequirement_holds exponentWidth width modulus positive base
      (Output.all (preparedContext exponentWidth width) .unit) input
  · intro Reference input _valid
    exact actual_borrowed exponentWidth width modulus positive base
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact gidneyExponentNativeCode_native_bound exponentWidth width modulus positive base path
  · intro _Reference _input _valid path _supported
    exact gidneyExponentNativeCode_resident_bound exponentWidth width modulus positive base path
  · intro _Reference _input _valid path _supported
    exact gidneyExponentNativeCode_auxiliary_bound exponentWidth width modulus positive base path
  · intro _Reference _input _valid path _supported
    exact gidneyExponentNativeCode_depth_bound exponentWidth width modulus positive base path

end

end QuantumAlg.MAU.Exponentiation.Gidney
