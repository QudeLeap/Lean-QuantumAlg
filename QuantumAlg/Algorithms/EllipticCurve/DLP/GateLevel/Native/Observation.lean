/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.State
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Readout
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation
import all QuantumAlg.Core.Measure.RealWeights

/-!
# Original ECDLP Born vector and complete observed store blocks

The literal source circuit determines the normalized vector and its original
terminal Born law. Finite cells are read in precisely that original order.
Each actual complete store block retains its full reference matrix after the
unitary, and actual reset supplies the required seed internally. These are
observations of the one interpreter and its existing state.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The exact original literal preparation, opaque group query and two inverse QFTs. -/
def evolvedState (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) :
    QubitLayout.State (qubitLayout I) where
  state := PureState.ofNormalized
    ((GateLevelAttempt.quantumCircuit I B A).applyNormalized (inputPreparation I).normalized)
    (qubitLayout I).systemIdx
  system_idx_eq := rfl

/-- The original terminal Born law of this same literal source circuit. -/
def outcomePMF (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) :
    PMF (Fin (sampleWidth I) → Bool) :=
  (terminalMeasurement I).outcomePMF (evolvedState I B A)

/-- Interpret the real two-valued cells as the original ordered bit string. -/
def observedOutcome (I : ECDLPInstance E)
    (value : (CShape.fixedVector (sampleWidth I) (.finite 2)).Value) :
    Fin (sampleWidth I) → Bool :=
  fun index => decide ((value.get index).toFin.val = 1)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

/-- Reading all actual measured cells yields the original terminal readout exactly. -/
theorem nativeECDLP_observed_outcome (store : Store (context base noQuantum I))
    (basis : (context base noQuantum I).register.Index) :
    observedOutcome I ((Circuit.writeMeasurementPath (readouts base noQuantum I) store
      (Circuit.measurementBasisPath (readouts base noQuantum I) basis)).read
        (sampleInput base noQuantum I)) =
      (terminalMeasurement I).readout
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) basis) := by
  funext index
  exact nativeECDLP_measured_bit base noQuantum I store basis index

/-- Summing actual histories keeps the same reset seed in every complete classical store. -/
theorem nativeECDLP_reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History) :
    BasisSeeded.Holds (resetLabel base noQuantum I)
      ((reset base noQuantum I).execute Reference state) := by
  intro original left right leftRef rightRef
  by_cases supported : left = resetLabel base noQuantum I ∧ right = resetLabel base noQuantum I
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    rw [← BasisSeeded.store_matrix]
    rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
    simp only [Matrix.ite_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro record _
    split
    · rw [nativeECDLP_reset_block_entry, if_neg supported]
    · rfl

/-- The real unitary acts on the original seed and each store's complete reference coefficient. -/
theorem nativeECDLP_unitary_seed_entry (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History)
    (seeded : BasisSeeded.Holds (resetLabel base noQuantum I) state)
    (original : Store (context base noQuantum I))
    (left right : (context base noQuantum I).register.Index) (leftRef rightRef : Reference.Index) :
    (((Circuit.unitary (member base noQuantum I B A)
      (nativeECDLP_member_physicalIdx base noQuantum I B A)).execute Reference state
        ).filterClassical
        (fun entry => entry.1 = original)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
      (evolvedState I B A).normalized
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) left) *
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (resetLabel base noQuantum I, leftRef) (resetLabel base noQuantum I, rightRef) *
      star ((evolvedState I B A).normalized
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) right)) := by
  have filtered := Circuit.unitary_store_filter (member base noQuantum I B A)
    (nativeECDLP_member_physicalIdx base noQuantum I B A) state (fun store => store = original)
  have entries := congrArg
    (fun density : DensityOperator (Register.prod (context base noQuantum I).register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) filtered
  refine entries.trans ((BasisSeeded.unitary_entry _ state seeded
    (member base noQuantum I B A).matrix original left right leftRef rightRef).trans ?_)
  rw [nativeECDLP_member_seed_amplitude, nativeECDLP_member_seed_amplitude]
  rfl

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
