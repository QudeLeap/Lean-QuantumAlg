/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout.Density

/-!
# Original mass in the complete sampling coordinates

Splitting the existing frame and result cells uses only the exact classical
and quantum coordinate maps. It preserves the original mass, including every
subnormalized posterior branch. No outcome is discarded or renormalized.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem cellsSplit_mass (ctx : RuntimeCtx .quantum) (count : Nat)
    {Reference : Register} {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State (MeasurementCells.context ctx 2 count) Reference (Hidden × History)) :
    (Circuit.underMeasurementCellsSplitState ctx 2 count state).mass = state.mass := by
  induction count generalizing Reference History with
  | zero =>
      simp only [Circuit.underMeasurementCellsSplitState]
      exact State.mapHistory_mass state _
  | succ count ih =>
      simp only [Circuit.underMeasurementCellsSplitState]
      erw [State.mapHistory_mass, ih, Circuit.underRetainedSplitState_mass]

/-- Complete scalar proof coordinates retain the mass of the same actual terminal state. -/
theorem samplingReadoutSplitState_mass {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (exponentWidth : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E exponentWidth) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (samplingReadoutSplitState E exponentWidth state).mass = state.mass :=
  (cellsSplit_mass (Allocation.after p.size (2 * exponentWidth)) (2 * exponentWidth)
    (splitServiceState (exponentMeasurementContext p exponentWidth)
      (PublicInput.frame E exponentWidth)
      (PublicInput.terminal_disjoint E exponentWidth) state)).trans
    (contextUnion_splitServiceState_mass (exponentMeasurementContext p exponentWidth)
      (PublicInput.frame E exponentWidth) (PublicInput.terminal_disjoint E exponentWidth) state)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
