/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Readout
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Observation
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation
import all QuantumAlg.Core.Measure.RealWeights

/-!
# Complete actual state of each retained finite-cyclic sample

The literal source circuit determines the normalized vector and its original
terminal Born law. Finite cells are read in precisely that original order.
Each actual complete store block retains its full reference matrix after the
unitary, and actual reset supplies the required seed internally. These are
observations of the one interpreter and its existing state.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat) (ux : UxAccess P)

/-- Reading all actual measured cells yields the original terminal readout exactly. -/
theorem nativeFiniteCyclicBatch_observed_outcome (slot : Fin count)
    (store : Store (context base noQuantum P count))
    (basis : (context base noQuantum P count).register.Index) :
    observedOutcome P ((Circuit.writeMeasurementPath (readouts base noQuantum P count slot) store
      (Circuit.measurementBasisPath (readouts base noQuantum P count slot) basis)).read
        (samples base noQuantum P count slot)) =
      (terminalMeasurement P).readout
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) basis) := by
  funext index
  exact nativeFiniteCyclicBatch_measured_bit base noQuantum P count slot store basis index

/-- Summing actual histories keeps the same reset seed in every complete classical store. -/
theorem nativeFiniteCyclicBatch_reset_seeded (slot : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History) :
    BasisSeeded.Holds (resetLabel base noQuantum P count ux)
      ((reset base noQuantum P count ux slot).execute Reference state) := by
  intro original left right leftRef rightRef
  by_cases supported :
      left = resetLabel base noQuantum P count ux ∧ right = resetLabel base noQuantum P count ux
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    rw [← BasisSeeded.store_matrix]
    rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
    simp only [Matrix.ite_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro record _
    split
    · rw [nativeFiniteCyclicBatch_reset_block_entry, if_neg supported]
    · rfl

/-- The real unitary acts on the original seed and each store's complete reference coefficient. -/
theorem nativeFiniteCyclicBatch_unitary_seed_entry
    (B : UniformSuperposition.BinaryExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History)
    (seeded : BasisSeeded.Holds (resetLabel base noQuantum P count ux) state)
    (original : Store (context base noQuantum P count))
    (left right : (context base noQuantum P count).register.Index) (leftRef rightRef :
      Reference.Index) :
    (((Circuit.unitary (member base noQuantum P count B ux)
      (nativeFiniteCyclicBatch_member_physicalIdx base noQuantum P count B ux)).execute Reference
        state
        ).filterClassical
        (fun entry => entry.1 = original)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
      (evolvedState P B ux).normalized
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) left) *
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (resetLabel base noQuantum P count ux, leftRef) (resetLabel base noQuantum P count ux,
          rightRef) *
      star ((evolvedState P B ux).normalized
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) right)) := by
  have filtered := Circuit.unitary_store_filter (member base noQuantum P count B ux)
    (nativeFiniteCyclicBatch_member_physicalIdx base noQuantum P count B ux) state
    (fun store => store = original)
  have entries := congrArg
    (fun density : DensityOperator (Register.prod (context base noQuantum P count).register
      Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) filtered
  refine entries.trans ((BasisSeeded.unitary_entry _ state seeded
    (member base noQuantum P count B ux).matrix original left right leftRef rightRef).trans ?_)
  rw [nativeFiniteCyclicBatch_member_seed_amplitude, nativeFiniteCyclicBatch_member_seed_amplitude]
  rfl

end

end GateLevelAttempt.Native.Batch
end QuantumAlg.FiniteCyclicDLP.Canonical
