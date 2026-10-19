/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Endpoint.Execution
public import QuantumAlg.Primitives.QFT.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.QFT.Endpoint.Execution
import all QuantumAlg.Primitives.QFT.Endpoint.Specification
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Time

/-!
# Complete native quantum Fourier transform

The public contract uses the independent mathematical Fourier operator,
tensored with the identity on every external reference, and independent
resource budgets. The supporting implementation executes the same source
circuit on the complete supplied register and retains every live system.
-/

namespace QuantumAlg.QuantumFourierTransform

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent exact QFT execution contract.

**Input.** A supplied owned n-qubit register in any normalized mixed state,
including every joint state with an arbitrary finite external reference. The
public width n allocates no classical runtime cells.
**Output.** The same live register, transformed by the forward Fourier
operator with phase exp(2*pi*i/2^n). Its complete joint state with the reference
is specified by that operator tensored with the reference identity.
**Resource budget.** Exactly n native Hadamard gates, n choose 2 native
controlled-phase gates, and n/2 native SWAP gates suffice, with no oracle queries.
Both resident and auxiliary coordinates are bounded by n
dimension-two systems, since the supplied register has the owned role. These
bounds describe the same live systems. There are no classical bits or other
quantum dimensions. Unit-event depth is at most n+(n choose 2)+(n/2).
**Success.** The unit classical result has probability one, the independent
joint-state requirement holds, and the untouched reference is restored.
**Source.** Exact Fourier definition and circuit in [dW19, qcnotes.tex:1692]
and [Lin22, phaseestimation.tex:351]; the all-n construction theorem also
covers width zero and preserves its exact native gate counts.
-/
@[expose] public def problem (n : Nat) :
    Problem model (inputContext n) (inputContext n) .unit where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [stateRequirement n]
  resources :=
    { events := n •
        ResourcePool.singleton (model := model) (.gate FourierGate.Coordinate.hadamard) +
        (n.choose 2) • ResourcePool.singleton (model := model)
          (.gate FourierGate.Coordinate.controlledPhase) +
        (n / 2) • ResourcePool.singleton (model := model) (.gate FourierGate.Coordinate.swap)
      resident := spaceBudget n
      auxiliary := spaceBudget n }
  quantumTimeLimit := n + n.choose 2 + n / 2

/-- The complete native QFT execution solves its independent Fourier-state and resource contract. -/
public theorem main (n : Nat) :
    ∃ candidate : Algorithm model (inputContext n) (inputContext n) .unit,
      Algorithm.Solves candidate (problem n) := by
  refine ⟨algorithm n, ?_⟩
  constructor
  · intro environment _witness Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialization requirement present
    have same : requirement = stateRequirement n := List.mem_singleton.mp present
    subst requirement
    exact actual_state n environment input
  · intro environment _witness Reference input _valid _initialization
    exact restores_borrowed n environment input
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact le_of_eq (actual_events n path)
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_resident n path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_auxiliary n path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact actual_depth n path

end

end QuantumAlg.QuantumFourierTransform
