/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# Independent physical restart facts for the completed reused EH batch

The concrete next segment measures, restores borrowed roles and resets every
owned selected-bank block for arbitrary store, service history and reference.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

noncomputable section

open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

private theorem restartCleanup_of_code_eq {execution : ExecutionModel}
    {pre post : RuntimeCtx execution.kind}
    (first second : Circuit execution pre post) (same : first = second)
    (certificate : Circuit.RestartCleanup second) :
    Circuit.RestartCleanup first := by
  cases same
  exact certificate

private theorem nextExplicit_restartCleanup (input : Input N) :
    Circuit.RestartCleanup
      (((Retry.next base noQuantum N input).seq
        (Retry.pack base noQuantum N input)).seq
          (Cleanup.reset base noQuantum N input)) where
  measured := by
    intro path
    obtain ⟨dimension, present⟩ :=
      Cleanup.reset_measured base noQuantum N input path.2
    exact ⟨dimension, List.mem_append.mpr (Or.inr present)⟩
  restores := by
    intro Reference History _ state
    have emptyBase : base.borrowedQuantumWires = [] := by
      have subset := base.borrowedQuantumWires_sublist
      rw [noQuantum] at subset
      exact List.sublist_nil.mp subset
    have empty : (Retry.context base noQuantum N).borrowedQuantumWires = [] :=
      (Retry.first base noQuantum N input).borrowedQuantumWires_preserved.trans emptyBase
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (((Retry.next base noQuantum N input).seq
        (Retry.pack base noQuantum N input)).seq
          (Cleanup.reset base noQuantum N input)) empty Reference state
  reinitialized := by
    refine ⟨(Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis
      (Retry.context base noQuantum N).borrowedSelectionᶜ
      (Retry.context base noQuantum N).quantumLayout.zeroLabel, ?_⟩
    intro Reference History _ state label
    let earlier := (Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N input)
    have seeded : BasisSeeded.Holds
        (Retry.context base noQuantum N).quantumLayout.zeroLabel
        ((earlier.seq (Cleanup.reset base noQuantum N input)).execute Reference state) := by
      apply BasisSeeded.seq earlier (Cleanup.reset base noQuantum N input)
      exact Cleanup.reset_seeded base noQuantum N input _
    exact Cleanup.seeded_recordSeed _ _ seeded label
      (Retry.context base noQuantum N).borrowedSelectionᶜ

/-- The actual further-batch segment is physically restartable for arbitrary
incoming store, service state and reference, without a good-key restriction. -/
theorem nextCompleted_restartCleanup (input : Input N) :
    Circuit.RestartCleanup (Cleanup.nextCompletedCode base noQuantum N input) :=
  restartCleanup_of_code_eq _ _ (by rfl)
    (nextExplicit_restartCleanup base noQuantum input)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
