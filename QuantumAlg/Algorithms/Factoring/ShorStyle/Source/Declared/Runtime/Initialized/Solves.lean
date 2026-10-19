/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Protocol
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Basis.Seeded.ReadoutPromise

/-!
# Complete first-round correctness from the original input

All seven obligations concern the same actual initializer and complete round.
The source success threshold is obtained on its real prefix output. Physical
zero holds for every result including zero-mass fibers; the full borrowed
frame is restored and every actual path is included in all resource bounds.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized

open Execution

noncomputable section

/-- An empty incoming quantum carrier has no borrowed quantum subsystem. -/
lemma base_noBorrowedQuantum (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) : base.borrowedQuantumWires = [] := by
  have sublist := base.borrowedQuantumWires_sublist
  rw [noQuantum] at sublist
  exact List.sublist_nil.mp sublist

/-- Every actual first-round result has its full predetermined zero bank. -/
lemma output_state (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N)
    (actual : (executionModel N).Environment) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles base Reference) :
    (stateRequirement base noQuantum N).Holds original.caller
      ((algorithm base noQuantum N input).run.finalState actual Reference original.state) := by
  intro value
  apply AlgorithmRun.pure_fullSelection_of_executionReadout
    (algorithm base noQuantum N input).run actual
    (Iteration.context (bank base noQuantum N) N).quantumLayout.zeroLabel _ original value
  intro reference history _ state selected
  exact BasisSeeded.readout_pure_fullSelection
    ((code base noQuantum N input).execute actual reference state)
    (Iteration.context (bank base noQuantum N) N).quantumLayout.zeroLabel
    (code_seeded (environment := actual) base noQuantum N input state)
    (fun store => (algorithm base noQuantum N input).run.output.eval store) selected

/-- Initialization and the first complete round satisfy every independent protocol obligation. -/
lemma shorDeclared_first_solves (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) :
    (algorithm base noQuantum N input).Solves
      (problem base noQuantum N input) := by
  constructor
  · intro actual witness Reference original valid _admitted
    have same := environment_eq_of_quantum input actual valid
    subst actual
    exact relational_success base noQuantum witness original
  · intro actual _witness Reference original _valid _admitted requirement present
    have same : requirement = stateRequirement base noQuantum N := List.mem_singleton.mp present
    subst requirement
    exact output_state base noQuantum N input actual original
  · intro actual _witness Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (code base noQuantum N input) actual
      (base_noBorrowedQuantum base noQuantum) reference state
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact code_pool_le base noQuantum N input path
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact code_resident_le base noQuantum N input path
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact code_auxiliary_le base noQuantum N input path
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact code_depth_le base noQuantum N input
      Resource.Event.quantumDuration path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
