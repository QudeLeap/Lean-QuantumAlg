/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Cleanup
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Suffix
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.CycleSchedule.Bounds

/-!
# Every positive actual Shor run has complete first and reused quantum cycles

The first complete cycle includes actual initialization and preparation.
Every further requested attempt is complete and physically admitted. The
sole certain classical pack ends the same original run. Reassociation changes
sequence parentheses alone, retaining all weighted states, actual paths,
native events, chronological depth and both live-space peaks.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
  (model : NumberTheory.Factoring.SemiprimeFactorModel N) (further : Nat)

/-- The caller prescribes one full initialized cycle, further complete rounds and one paid pack. -/
def positivePlan
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CyclePlan (executionModel (Probability.Input.ofSemiprimeModel model)) base
      (context base noQuantum N (further + 1)) (.option (.unsignedWord (modulusBits N))) :=
  .seq (.cycle (Initialized.problem base noQuantum model duration unitQueries))
    (Finite.completionPlan (Iteration.context (Initialized.bank base noQuantum N) N) model
      (Completion.cells (Initialized.bank base noQuantum N) N
        (Initialized.cells base noQuantum N)) further duration unitQueries)

private def positiveAssociation :
    Circuit.Reassociation
      (code base noQuantum N (Probability.Input.ofSemiprimeModel model) (further + 1))
      ((Initialized.code base noQuantum N (Probability.Input.ofSemiprimeModel model)).seq
        (Finite.code (Iteration.context (Initialized.bank base noQuantum N) N) N
          (Probability.Input.ofSemiprimeModel model)
          ((Iteration.quantumWires (Initialized.bank base noQuantum N) N).trans
            (Initialized.bank_wires base noQuantum N)) further
          (Completion.cells (Initialized.bank base noQuantum N) N
            (Initialized.cells base noQuantum N))
          (Completion.liftWrite (Initialized.bank base noQuantum N) N
            (Initialized.result base noQuantum N)))) := by
  let input := Probability.Input.ofSemiprimeModel model
  let ctx := Initialized.bank base noQuantum N
  let cells := Initialized.cells base noQuantum N
  let result := Initialized.result base noQuantum N
  let first := Completion.code ctx N input (Initialized.bank_wires base noQuantum N) cells result
  let rest := Finite.body (Iteration.context ctx N) N input
    ((Iteration.quantumWires ctx N).trans (Initialized.bank_wires base noQuantum N))
    (Completion.cells ctx N cells) (Completion.liftWrite ctx N result) further
  let packed := Finite.pack ctx N input (further + 1) cells result
  exact (Circuit.Reassociation.seq (.refl (Initialized.ready base noQuantum N input))
    (.seqAssoc first rest packed)).trans
      (Circuit.Reassociation.seqAssoc (Initialized.ready base noQuantum N input)
        first (rest.seq packed)).symm

private def groupedPositiveSchedule
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (positivePlan base noQuantum model further duration unitQueries)
      ((Initialized.code base noQuantum N (Probability.Input.ofSemiprimeModel model)).seq
        (Finite.code (Iteration.context (Initialized.bank base noQuantum N) N) N
          (Probability.Input.ofSemiprimeModel model)
          ((Iteration.quantumWires (Initialized.bank base noQuantum N) N).trans
            (Initialized.bank_wires base noQuantum N)) further
          (Completion.cells (Initialized.bank base noQuantum N) N
            (Initialized.cells base noQuantum N))
          (Completion.liftWrite (Initialized.bank base noQuantum N) N
            (Initialized.result base noQuantum N)))) :=
  .seq _ _ (.complete _ (Initialized.completeCycle base noQuantum model duration unitQueries))
    (Finite.completionSchedule (Iteration.context (Initialized.bank base noQuantum N) N) model
      ((Iteration.quantumWires (Initialized.bank base noQuantum N) N).trans
        (Initialized.bank_wires base noQuantum N))
      (Completion.cells (Initialized.bank base noQuantum N) N
        (Initialized.cells base noQuantum N))
      (Completion.liftWrite (Initialized.bank base noQuantum N) N
        (Initialized.result base noQuantum N))
      (Completion.separated (Initialized.bank base noQuantum N) N
        (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)
        (Initialized.separated base noQuantum N))
      ((Initialized.code base noQuantum N
        (Probability.Input.ofSemiprimeModel model)).borrowedQuantumWires_preserved.trans
          (Initialized.base_noBorrowedQuantum base noQuantum))
      further duration unitQueries)
    (by
      intro Reference original _admitted
      exact Finite.completionPlan_admits_of_domain
        (Iteration.context (Initialized.bank base noQuantum N) N) model
        (Completion.cells (Initialized.bank base noQuantum N) N
          (Initialized.cells base noQuantum N)) further duration unitQueries
        ((Initialized.code base noQuantum N
          (Probability.Input.ofSemiprimeModel model)).nextInput original)
        (Initialized.nextInput_admitted base noQuantum model original))
    (Or.inr ⟨Initialized.restartCleanup base noQuantum N
      (Probability.Input.ofSemiprimeModel model)⟩)

/-- The original positive initialized circuit carries the caller's complete physical schedule. -/
def positiveSchedule
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (positivePlan base noQuantum model further duration unitQueries)
      (code base noQuantum N (Probability.Input.ofSemiprimeModel model) (further + 1)) :=
  .reassociate (positiveAssociation base noQuantum model further)
    (groupedPositiveSchedule base noQuantum model further duration unitQueries)

/-- Maximum cycle depth includes one actual initializer and one complete Shor computation. -/
theorem positive_maximumCycleDepth_le
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (code base noQuantum N (Probability.Input.ofSemiprimeModel model) (further + 1)).Path) :
    (positiveSchedule base noQuantum model further duration unitQueries).maximumCycleDepth
      duration path ≤ ResourcePool.weightedCount duration
        (Initialized.firstEnvelope (Probability.Input.ofSemiprimeModel model)) := by
  apply Circuit.CycleSchedule.maximumCycleDepth_reassociate_le
  intro groupedPath
  change max ((Initialized.code base noQuantum N
    (Probability.Input.ofSemiprimeModel model)).depth duration groupedPath.1) _ ≤ _
  apply max_le
  · exact Initialized.code_depth_le base noQuantum N (Probability.Input.ofSemiprimeModel model)
      duration groupedPath.1
  · have later := Finite.completion_maximumCycleDepth_le
      (Iteration.context (Initialized.bank base noQuantum N) N) model
      ((Iteration.quantumWires (Initialized.bank base noQuantum N) N).trans
        (Initialized.bank_wires base noQuantum N))
      (Completion.cells (Initialized.bank base noQuantum N) N
        (Initialized.cells base noQuantum N))
      (Completion.liftWrite (Initialized.bank base noQuantum N) N
        (Initialized.result base noQuantum N))
      (Completion.separated (Initialized.bank base noQuantum N) N
        (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)
        (Initialized.separated base noQuantum N))
      ((Initialized.code base noQuantum N
        (Probability.Input.ofSemiprimeModel model)).borrowedQuantumWires_preserved.trans
          (Initialized.base_noBorrowedQuantum base noQuantum))
      further duration unitQueries groupedPath.2
    refine later.trans ?_
    rw [Initialized.firstEnvelope, ResourcePool.weightedCount_add]
    exact Nat.le_add_left _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
