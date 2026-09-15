/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Readout
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation
import all QuantumAlg.Core.Measure.RealWeights

/-!
# Original finite-cyclic Born vector and complete observed store blocks

The literal source circuit determines the normalized vector and its original
terminal Born law. Finite cells are read in precisely that original order.
Each actual complete store block retains its full reference matrix after the
unitary, and actual reset supplies the required seed internally. These are
observations of the one interpreter and its existing state.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

/-- The exact original literal preparation, opaque group query and two inverse QFTs. -/
def evolvedState (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    QubitLayout.State (layout P) where
  state := PureState.ofNormalized
    ((GateLevelAttempt.quantumCircuit P B ux).applyNormalized
      (GateLevelAttempt.inputPreparation P B ux).normalized)
    (layout P).systemIdx
  system_idx_eq := rfl

/-- The original terminal Born law of this same literal source circuit. -/
def outcomePMF (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    PMF (Fin (sampleWidth P) → Bool) :=
  (terminalMeasurement P).outcomePMF (evolvedState P B ux)

/-- Interpret the real two-valued cells as the original ordered bit string. -/
def observedOutcome (P : KnownOrderProblem G)
    (value : (CShape.fixedVector (sampleWidth P) (.finite 2)).Value) :
    Fin (sampleWidth P) → Bool :=
  fun index => decide ((value.get index).toFin.val = 1)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (ux : UxAccess P)

/-- Reading all actual measured cells yields the original terminal readout exactly. -/
theorem nativeFiniteCyclic_observed_outcome (store : Store (context base noQuantum P))
    (basis : (context base noQuantum P).register.Index) :
    observedOutcome P ((Circuit.writeMeasurementPath (readouts base noQuantum P) store
      (Circuit.measurementBasisPath (readouts base noQuantum P) basis)).read
        (sampleInput base noQuantum P)) =
      (terminalMeasurement P).readout
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) basis) := by
  funext index
  exact nativeFiniteCyclic_measured_bit base noQuantum P store basis index

/-- Summing actual histories keeps the same reset seed in every complete classical store. -/
theorem nativeFiniteCyclic_reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P) Reference History) :
    BasisSeeded.Holds (resetLabel base noQuantum P ux)
      ((reset base noQuantum P ux).execute Reference state) := by
  intro original left right leftRef rightRef
  by_cases supported :
      left = resetLabel base noQuantum P ux ∧ right = resetLabel base noQuantum P ux
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    rw [← BasisSeeded.store_matrix]
    rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
    simp only [Matrix.ite_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro record _
    split
    · rw [nativeFiniteCyclic_reset_block_entry, if_neg supported]
    · rfl

/-- The real unitary acts on the original seed and each store's complete reference coefficient. -/
theorem nativeFiniteCyclic_unitary_seed_entry
    (B : UniformSuperposition.BinaryExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P) Reference History)
    (seeded : BasisSeeded.Holds (resetLabel base noQuantum P ux) state)
    (original : Store (context base noQuantum P))
    (left right : (context base noQuantum P).register.Index) (leftRef rightRef : Reference.Index) :
    (((Circuit.unitary (member base noQuantum P B ux)
      (nativeFiniteCyclic_member_physicalIdx base noQuantum P B ux)).execute Reference state
        ).filterClassical
        (fun entry => entry.1 = original)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
      (evolvedState P B ux).normalized
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) left) *
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (resetLabel base noQuantum P ux, leftRef) (resetLabel base noQuantum P ux, rightRef) *
      star ((evolvedState P B ux).normalized
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) right)) := by
  have filtered := Circuit.unitary_store_filter (member base noQuantum P B ux)
    (nativeFiniteCyclic_member_physicalIdx base noQuantum P B ux) state
    (fun store => store = original)
  have entries := congrArg
    (fun density : DensityOperator (Register.prod (context base noQuantum P).register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) filtered
  refine entries.trans ((BasisSeeded.unitary_entry _ state seeded
    (member base noQuantum P B ux).matrix original left right leftRef rightRef).trans ?_)
  rw [nativeFiniteCyclic_member_seed_amplitude, nativeFiniteCyclic_member_seed_amplitude]
  rfl

end

end GateLevelAttempt.Native
end QuantumAlg.FiniteCyclicDLP.Canonical
