/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Validity
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent

/-!
# Public points across the actual reused ECC readout

The unchanged readout preserves the two borrowed public-point
interpretations in every supported output block, independently of recovery.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E)

/-- The actual reset-free readout retains admitted public points on every
positive block, with arbitrary persistent cells and reference history. -/
theorem persistentSamplingReadout_points_of_validity
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H))
    (valid : ∀ entry, 0 < (state.block entry).mass →
      CheckedSelectionValid E problem entry.1)
    (entry)
    (positive : 0 < (((persistentSamplingReadout E fieldTail odd problem points).execute
      Reference state).block entry).mass) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
        (orderWidth problem) (PublicInput.terminalBaseRef E (orderWidth problem))))
        problem.generator.toMathlib ∧
    PointRepresents (Canonical.Layout.curveSpec E)
      (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
        (orderWidth problem) (PublicInput.terminalTargetRef E (orderWidth problem))))
        problem.target.toMathlib := by
  have noQuantum :
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  exact PublicInput.persistentProgram_preserves_represents E (orderWidth problem)
    problem (persistentSamplingReadout E fieldTail odd problem points) noQuantum state
    (fun previous present => ⟨(valid previous present).1, (valid previous present).2.1⟩)
    entry positive

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
