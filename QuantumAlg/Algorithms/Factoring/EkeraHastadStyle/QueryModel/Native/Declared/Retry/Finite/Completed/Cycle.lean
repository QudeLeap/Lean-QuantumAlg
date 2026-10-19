/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.First

/-!
# The first independently completed EH batch as one certified cycle

The first actual sampled, recovered, packed and reset batch solves its own
all-input source problem. Its physical restart certificate supplies the
measured and reinitialized boundary needed before any subsequent cycle.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
variable {environment : (model N).Environment}

/-- The first completed batch ends with an actual measured, borrowed-restored
and fixed-seed boundary for every original input and external reference. -/
lemma completedOne_restartCleanup (input : Input N) :
    Circuit.RestartCleanup
      (Cleanup.completedCode base noQuantum N input 0) environment where
  measured := by
    intro path
    have first := firstCompleted_restartCleanup (environment := environment) base noQuantum input
    obtain ⟨dimension, present⟩ := first.measured path.1
    exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩
  restores := by
    intro Reference History _ state
    have empty : base.borrowedQuantumWires = [] := by
      have subset := base.borrowedQuantumWires_sublist
      rw [noQuantum] at subset
      exact List.sublist_nil.mp subset
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (Cleanup.completedCode base noQuantum N input 0) environment empty Reference state
  reinitialized := by
    refine ⟨(Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis
      (Retry.context base noQuantum N).borrowedSelectionᶜ
      (Retry.context base noQuantum N).quantumLayout.zeroLabel, ?_⟩
    intro Reference History _ state label
    exact Cleanup.seeded_recordSeed _ _
      (Cleanup.completed_seeded base noQuantum N input 0 state) label
      (Retry.context base noQuantum N).borrowedSelectionᶜ

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
