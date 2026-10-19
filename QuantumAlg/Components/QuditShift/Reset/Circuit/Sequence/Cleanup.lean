/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Pure
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Resources
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Physical restart certificate for an actual complete reset

For a nonempty fully owned layout, the original reset circuit measures a real
system on every path and leaves the same predetermined quantum seed in every
complete record. Borrowed classical data and its reference correlations remain
restored. This physical certificate does not specify a completed computation.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
  {environment : (ExecutionModel.quantum gates oracles).Environment} {ctx : RuntimeCtx .quantum}
  (implementations : ∀ wire, Realizations gates oracles ctx.quantumLayout wire)

/-- The physical reset prepares the prescribed basis label, fixed before any
input or measurement outcome, on the actual owned output. -/
lemma resetToBasis_reinitializedAt {allowAllocation : Bool}
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (resetToBasis (allowAllocation := allowAllocation) implementations
        outputs label) environment
      (ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ label) := by
  have empty : ctx.borrowedSelection = ∅ := by
    ext wire
    simp [RuntimeCtx.mem_borrowedSelection, noBorrowed]
  have all : ctx.borrowedSelectionᶜ = Finset.univ := by
    simp [empty]
  unfold Circuit.ReinitializedAt
  rw [all]
  intro Reference History _ state record
  exact resetToBasis_pure_fullSelection (allowAllocation := allowAllocation) implementations outputs
      label state record

/-- A nonempty all-owned reset is physically restartable without discarding any record. -/
lemma resetToBasis_restartCleanup {allowAllocation : Bool}
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) (positive : 0 < ctx.systemCount)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (resetToBasis (allowAllocation := allowAllocation) implementations
        outputs label) environment where
  measured := resetToBasis_measured (allowAllocation := allowAllocation) implementations outputs
      label positive
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (resetToBasis
        (allowAllocation := allowAllocation) implementations outputs label) environment noBorrowed
          Reference state
  reinitialized := by
    refine ⟨ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ label, ?_⟩
    exact resetToBasis_reinitializedAt (allowAllocation := allowAllocation) implementations outputs
        label noBorrowed

end

end QuantumAlg.QuditShift
