/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.State
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Resources
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Restoration
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Complete native semiclassical Fourier measurement

The output is the actual vector of retained measurement bits. Its mathematical
frequency interpretation reverses the physical binary label without allocating
storage or executing a conversion. The two independent state requirements
specify the complete measured bank and arbitrary external reference.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Endpoint

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent complete semiclassical Fourier measurement contract.

**Input.** Any normalized mixed state of a supplied n-qubit register, with
every external-reference extension admitted. The Boolean parameter selects
the forward transform or negative Fourier phases. Width zero is included.
**Output.** The same retained physical register and a structural vector of
n actual binary measurement cells. Its physical label is the bit reversal
of the Fourier frequency. The complete bank-reference state is the ideal
Fourier output dephased in the physical bank basis; conditioning on each
actual stored vector gives exactly its physical bank ket at its actual mass.
**Resource budget.** At most n native Hadamards, n choose 2 native single-qubit
phase gates and n binary measurements. At most n supplied qubits and n retained
classical bits are resident; only those n bits are auxiliary. No auxiliary
qubits, other quantum dimensions or oracle queries are required. The actual
quantum computation time is at most n+n choose 2.
**Success.** The stored output event has probability one. Both independent
state requirements and complete borrowed restoration hold on the same run.
**Source.** The Fourier definition, earlier measurement and single-qubit
feedback construction are [GN96, 9511007.tex:100-114,214-266].
-/
@[expose] public def problem (inverse : Bool) (n : Nat) :
    Problem model (inputContext n) (outputContext n) (.fixedVector n (.finite 2)) where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [instrumentRequirement inverse n, storedResultRequirement n]
  resources :=
    { events := eventBudget n
      resident := residentBudget n
      auxiliary := auxiliaryBudget n }
  quantumTimeLimit := n + n.choose 2

/-- The genuine adaptive native execution solves the independent complete Fourier contract. -/
public theorem main (inverse : Bool) (n : Nat) :
    ∃ candidate : Algorithm model (inputContext n) (outputContext n)
      (.fixedVector n (.finite 2)), candidate.Solves (problem inverse n) := by
  refine ⟨algorithm inverse n, ?_⟩
  constructor
  · intro environment _witness Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialization requirement present
    rcases List.mem_cons.mp present with equal | remaining
    · subst requirement
      exact algorithm_instrumentRequirement (environment := environment) inverse n input
    · have equal := List.mem_singleton.mp remaining
      subst requirement
      exact algorithm_storedResultRequirement (environment := environment) inverse n input
  · intro environment _witness Reference input _valid _initialization
    exact qftSemiclassical_algorithm_restoresBorrowed (environment := environment) inverse n input
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact qftSemiclassical_complete_events inverse n path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact qftSemiclassical_complete_resident inverse n path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact qftSemiclassical_complete_auxiliary inverse n path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact qftSemiclassical_complete_time inverse n path

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
