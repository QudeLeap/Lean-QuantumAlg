/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Round
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# Actual seeded support for a reused ECC section

The independent seeded initialization refers to every local store and service
block. Positivity transfers its pure basis support to every complete block
with an arbitrary external reference, then to the actual input marginal.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ)
  (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)

/-- The independently specified local joint initialization has zero weight
on every sampling basis other than the prescribed reset seed. -/
theorem checkedSectionSeededInitialization_localSupport
    (state : ExecutionState
      (Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
        ClassicalOracleModel.empty.HiddenState)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).register)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed state)
    (entry)
    (basis : (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.Index)
    (outside : basis ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed) :
    (state.block entry).matrix basis basis = 0 := by
  let layout := (persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)).quantumLayout
  let selected := layout.allSelectedBasisEquiv basis
  have sameSeed : checkedSectionAllSeed E fieldTail sameWidth fits problem seed =
      layout.allSelectedBasisEquiv
        (samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed) := rfl
  have different : selected ≠
      checkedSectionAllSeed E fieldTail sameWidth fits problem seed := by
    intro same
    apply outside
    apply layout.allSelectedBasisEquiv.injective
    rw [sameSeed] at same
    exact same
  have pure := checkedSectionSeededInitialization_fullSeed E fieldTail sameWidth fits
    problem seed state seeded entry
  have diagonal :
      ((state.block entry).reindex (S := layout.selectedRegister Finset.univ)
        layout.allSelectedBasisEquiv).matrix selected selected = 0 := by
    change _ = _ at pure
    rw [pure]
    simp [DensityOperator.ofPure_matrix, NormalizedVector.ket_apply, different]
  simpa only [DensityOperator.reindex_entry, selected, Equiv.symm_apply_apply]
    using diagonal

/-- Every actual joint input admitted by the reused protocol has the same
sampling-basis support, even with an arbitrary external reference. -/
theorem checkedSectionSeededInitialization_jointSupport
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      input.localState)
    (basis : ((persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference).Index)
    (outside : basis.1 ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed) :
    input.state.quantumMarginal.matrix basis basis = 0 := by
  change (∑ entry, (input.state.block entry).matrix) basis basis = 0
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro entry _
  apply DensityOperator.joint_diagonal_zero_of_marginal_diagonal_zero
    (input.state.block entry) basis.1
  · rw [← input.oracleInput_localState_block]
    exact checkedSectionSeededInitialization_localSupport E fieldTail sameWidth fits
      problem seed input.localState seeded entry basis.1 outside

/-- The same seeded support reaches the original sampling context after all
seven existing persistent classical cells become reference/history coordinates. -/
theorem checkedSectionSeededInitialization_splitSupport
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      input.localState)
    (basis : ((PublicInput.terminal E (orderWidth problem)).register.prod
      (persistentLocalReference (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem) Reference)).Index)
    (outside : basis.1 ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed) :
    (underPersistentSplitState (Canonical.Layout.fieldWidth E) (orderWidth problem)
      (State.skip input.state)).quantumMarginal.matrix basis basis = 0 := by
  apply underPersistentSplitState_basisSupport
    (Canonical.Layout.fieldWidth E) (orderWidth problem) (State.skip input.state)
    (samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed)
  · intro original different
    rw [State.skip_quantumMarginal]
    exact checkedSectionSeededInitialization_jointSupport E fieldTail sameWidth fits
      problem seed input seeded original different
  · exact outside

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
