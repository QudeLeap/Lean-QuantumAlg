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
theorem base_noBorrowedQuantum (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) : base.borrowedQuantumWires = [] := by
  have sublist := base.borrowedQuantumWires_sublist
  rw [noQuantum] at sublist
  exact List.sublist_nil.mp sublist

/-- Every actual first-round result has its full predetermined zero bank. -/
theorem output_state (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : OracleInput
      (executionModel (Probability.Input.ofSemiprimeModel model)).classicalOracles base Reference) :
    (stateRequirement base noQuantum N).Holds original.caller
      ((algorithm base noQuantum model).run.finalState Reference original.state) := by
  intro value
  apply AlgorithmRun.pure_fullSelection_of_executionReadout
    (algorithm base noQuantum model).run
    (Iteration.context (bank base noQuantum N) N).quantumLayout.zeroLabel _ original value
  intro reference history _ state selected
  exact BasisSeeded.readout_pure_fullSelection
    ((code base noQuantum N (Probability.Input.ofSemiprimeModel model)).execute reference state)
    (Iteration.context (bank base noQuantum N) N).quantumLayout.zeroLabel
    (code_seeded base noQuantum N (Probability.Input.ofSemiprimeModel model) state)
    (fun store => (algorithm base noQuantum model).run.output.eval store) selected

/-- Initialization and the first complete round satisfy every independent protocol obligation. -/
theorem shorDeclared_first_solves (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (algorithm base noQuantum model).Solves
      (problem base noQuantum model duration unitQueries) := by
  constructor
  · intro Reference original _valid _admitted
    exact relational_success base noQuantum model original
  · intro Reference original _valid _admitted requirement present
    have same : requirement = stateRequirement base noQuantum N := List.mem_singleton.mp present
    subst requirement
    exact output_state base noQuantum model original
  · intro Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (code base noQuantum N (Probability.Input.ofSemiprimeModel model))
      (base_noBorrowedQuantum base noQuantum) reference state
  · intro _Reference _original _valid _admitted path _supported
    exact code_pool_le base noQuantum N (Probability.Input.ofSemiprimeModel model) path
  · intro _Reference _original _valid _admitted path _supported
    exact code_resident_le base noQuantum N (Probability.Input.ofSemiprimeModel model) path
  · intro _Reference _original _valid _admitted path _supported
    exact code_auxiliary_le base noQuantum N (Probability.Input.ofSemiprimeModel model) path
  · intro _Reference _original _valid _admitted path _supported
    exact code_depth_le base noQuantum N (Probability.Input.ofSemiprimeModel model) duration path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
