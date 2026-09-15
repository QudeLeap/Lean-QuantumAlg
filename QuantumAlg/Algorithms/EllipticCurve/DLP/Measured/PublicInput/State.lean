/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Store
import all QuantumAlg.Core.Execution.Context.Union.Preparation.State
import all QuantumAlg.Core.Execution.Local.Framing.State

/-!
# Complete execution blocks with the original public inputs resident

Each actual instruction is compared in exact union coordinates. The public
store remains part of the complete history label, and the reference includes
all resident frame coordinates. No public value, initial workspace value or
product-state assumption is needed for these stage identities.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open MAU.Inversion.SharedEEA FiniteCyclicDLP GenericPointAddition.InPlace

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

/-- The same charged arithmetic preparation preserves every public classical block. -/
theorem prepareAuxiliary_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (before E exponentWidth) Reference History) :
    splitState
      ((InversePreparation.after p.size).disjointUnion
        (Allocation.exponents p.size (2 * exponentWidth))
        (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
      (frame E exponentWidth) (auxiliary_disjoint E exponentWidth)
      ((prepareAuxiliary E exponentWidth).execute Reference state) =
        ((Allocation.prepareAuxiliary p (2 * exponentWidth)).execute
          (Register.prod (frame E exponentWidth).register Reference)
          (splitState (Allocation.before p.size (2 * exponentWidth))
            (frame E exponentWidth) (before_disjoint E exponentWidth) state)).mapHistory
              (fun record => (record.1.1, (record.1.2, record.2))) := by
  exact prepareFramed_execute InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout p.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh p.size) (InversePreparation.auxiliary_disjoint p.size)
      (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
    (preparation_wires_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh p.size) (InversePreparation.auxiliary_disjoint p.size)
      (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
    (auxiliary_disjoint E exponentWidth) (InPlacePreparation.preparation p) state

/-- The same charged selector preparation retains every old quantum and public input block. -/
theorem prepareSelector_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (withCells E exponentWidth) Reference History) :
    splitState (Allocation.after p.size (2 * exponentWidth))
      (frame E exponentWidth) (after_disjoint E exponentWidth)
      ((prepareSelector E exponentWidth).execute Reference state) =
        ((Allocation.prepareSelector p.size (2 * exponentWidth)).execute
          (Register.prod (frame E exponentWidth).register Reference)
          (splitState (Allocation.withCells p.size (2 * exponentWidth))
            (frame E exponentWidth) (cells_disjoint E exponentWidth) state)).mapHistory
              (fun record => (record.1.1, (record.1.2, record.2))) := by
  exact prepareFramed_execute (indexedKey p.size (2 * exponentWidth))
    (indexedLayout p.size (2 * exponentWidth))
    (Allocation.selector_fresh p.size (2 * exponentWidth))
    (Allocation.selector_disjoint p.size (2 * exponentWidth))
    (after_disjoint E exponentWidth)
    (BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))) state

/-- Actual terminal Z measurements retain the public store and every original outcome. -/
theorem measurements_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (terminal E exponentWidth) Reference History) :
    splitState (exponentMeasurementContext p exponentWidth)
      (frame E exponentWidth) (terminal_disjoint E exponentWidth)
      ((measurements E exponentWidth).execute Reference state) =
        ((exponentMeasurements p exponentWidth).execute
          (Register.prod (frame E exponentWidth).register Reference)
          (splitState (exponentMeasurementContext p exponentWidth)
            (frame E exponentWidth) (terminal_disjoint E exponentWidth) state)).mapHistory
              (fun record => (record.1.1, (record.1.2,
                frameLocalPathEquiv (exponentMeasurements p exponentWidth)
                  (Circuit.measurementSequence_isLocal _) (frame E exponentWidth)
                  (terminal_disjoint E exponentWidth) record.2))) :=
  frameLocal_execute (exponentMeasurements p exponentWidth)
    (Circuit.measurementSequence_isLocal _) (frame E exponentWidth)
    (terminal_disjoint E exponentWidth) Reference state

variable [Fact p.Prime]

omit [Fact p.Prime] in
/-- The original exponent preparation keeps the initially present public input store. -/
theorem beforePreparation_execute (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before E (orderWidth problem)) Reference History) :
    splitState (Allocation.before p.size (2 * orderWidth problem))
      (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem))
      ((frameLocal (beforeExponentPreparation p problem) trivial
        (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem))).execute
          Reference state) =
      ((beforeExponentPreparation p problem).execute
        (Register.prod (frame E (orderWidth problem)).register Reference)
        (splitState (Allocation.before p.size (2 * orderWidth problem))
          (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem)) state)).mapHistory
            (fun record => (record.1.1, (record.1.2,
              frameLocalPathEquiv (beforeExponentPreparation p problem) trivial
                (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem))
                record.2))) :=
  frameLocal_execute (beforeExponentPreparation p problem) trivial
    (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem)) Reference state

/-- The actual converted measured cascade retains full coherences with the public inputs. -/
theorem convertedCascade_execute (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (after E (orderWidth problem)) Reference History) :
    let code := Encoding.placedConvertedCascade E points
      (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)
    let supported := Encoding.placedConvertedCascade_isLocal E points _ _
    splitState (Allocation.after p.size (2 * orderWidth problem))
      (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))
      ((frameLocal code supported (frame E (orderWidth problem))
        (after_disjoint E (orderWidth problem))).execute Reference state) =
      (code.execute (Register.prod (frame E (orderWidth problem)).register Reference)
        (splitState (Allocation.after p.size (2 * orderWidth problem))
          (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem)) state)).mapHistory
            (fun record => (record.1.1, (record.1.2,
              frameLocalPathEquiv code supported (frame E (orderWidth problem))
                (after_disjoint E (orderWidth problem)) record.2))) :=
  frameLocal_execute _ (Encoding.placedConvertedCascade_isLocal E points _ _)
    (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem)) Reference state

omit [Fact p.Prime] in
/-- The original inverse QFT preserves the same complete public and external reference blocks. -/
theorem afterReadout_execute (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (after E (orderWidth problem)) Reference History) :
    splitState (Allocation.after p.size (2 * orderWidth problem))
      (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))
      ((frameLocal (afterExponentReadout p problem) trivial
        (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))).execute
          Reference state) =
      ((afterExponentReadout p problem).execute
        (Register.prod (frame E (orderWidth problem)).register Reference)
        (splitState (Allocation.after p.size (2 * orderWidth problem))
          (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem)) state)).mapHistory
            (fun record => (record.1.1, (record.1.2,
              frameLocalPathEquiv (afterExponentReadout p problem) trivial
                (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))
                record.2))) :=
  frameLocal_execute (afterExponentReadout p problem) trivial
    (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem)) Reference state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
