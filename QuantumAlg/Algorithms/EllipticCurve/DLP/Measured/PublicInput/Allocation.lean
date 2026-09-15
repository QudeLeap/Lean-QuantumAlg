/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.State
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Execution

/-!
# Original retained allocations with both public inputs resident

The original terminal and arithmetic result cells keep their keys, initial
encodings and literal retain instructions. Context equalities only associate
the already resident exponent and public-input entry lists. Actual recursive
execution records retain every original Unit-valued allocation step.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open MAU.Inversion.SharedEEA

private def pathTransportInput {pre next post : RuntimeCtx .quantum}
    (same : pre = next) (code : Circuit next post) :
    code.Path ≃ (Eq.mpr (congrArg (fun ctx => Circuit ctx post) same) code).Path := by
  cases same
  exact Equiv.refl _

private def pathTransportOutput {pre post next : RuntimeCtx .quantum}
    (same : post = next) (code : Circuit pre next) :
    code.Path ≃ (Eq.mpr (congrArg (fun ctx => Circuit pre ctx) same) code).Path := by
  cases same
  exact Equiv.refl _

private theorem inputCast_heq {pre next post : RuntimeCtx .quantum}
    (same : pre = next) (code : Circuit next post) :
    HEq (Eq.mpr (congrArg (fun ctx => Circuit ctx post) same) code) code := by
  cases same
  rfl

private theorem outputCast_heq {pre post next : RuntimeCtx .quantum}
    (same : post = next) (code : Circuit pre next) :
    HEq (Eq.mpr (congrArg (fun ctx => Circuit pre ctx) same) code) code := by
  cases same
  rfl

private theorem seq_heq {pre mid post nextPre nextMid nextPost : RuntimeCtx .quantum}
    (first : pre = nextPre) (middle : mid = nextMid) (last : post = nextPost)
    (earlier : Circuit pre mid) (later : Circuit mid post)
    (nextEarlier : Circuit nextPre nextMid) (nextLater : Circuit nextMid nextPost)
    (sameEarlier : HEq earlier nextEarlier) (sameLater : HEq later nextLater) :
    HEq (earlier.seq later) (nextEarlier.seq nextLater) := by
  cases first
  cases middle
  cases last
  cases sameEarlier
  cases sameLater
  rfl

private theorem retain_heq {ctx next : RuntimeCtx .quantum} (same : ctx = next)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) (nextFresh : key ∉ next.keys) :
    HEq (Circuit.retain ctx key shape fresh) (Circuit.retain next key shape nextFresh) := by
  cases same
  rfl

private theorem id_heq {ctx next : RuntimeCtx .quantum} (same : ctx = next) :
    HEq (Circuit.id ctx) (Circuit.id next) := by
  cases same
  rfl

private theorem allocateFramed_outer_execute
    (ctx resident framed : RuntimeCtx .quantum) (dimension : ℕ+) :
    ∀ (count : Nat)
      (original : RuntimeCtx.StorageDisjoint
        (MeasurementCells.context ctx dimension count) resident)
      (outside : RuntimeCtx.StorageDisjoint
        ((MeasurementCells.context ctx dimension count).disjointUnion resident original) framed)
      (rightOutside : RuntimeCtx.StorageDisjoint resident framed)
      (combined : RuntimeCtx.StorageDisjoint (MeasurementCells.context ctx dimension count)
        (resident.disjointUnion framed rightOutside))
      (initial : RuntimeCtx.StorageDisjoint
        (ctx.disjointUnion resident
          (MeasurementCells.original_disjoint ctx resident dimension count original)) framed)
      (actual : Circuit
        ((ctx.disjointUnion resident
          (MeasurementCells.original_disjoint ctx resident dimension count original)).disjointUnion
            framed initial)
        (RuntimeCtx.disjointUnion
          ((MeasurementCells.context ctx dimension count).disjointUnion resident original)
          framed outside))
      (_same : HEq actual (MeasurementCells.allocateFramed ctx
        (resident.disjointUnion framed rightOutside) dimension count combined))
      (paths : (MeasurementCells.allocateFramed ctx resident dimension count original).Path →
        actual.Path) (Reference : Register) {History : Type} [Fintype History]
      (state : State
        ((ctx.disjointUnion resident
          (MeasurementCells.original_disjoint ctx resident dimension count original)).disjointUnion
            framed initial) Reference History),
      splitState ((MeasurementCells.context ctx dimension count).disjointUnion resident original)
        framed outside (actual.execute Reference state) =
        ((MeasurementCells.allocateFramed ctx resident dimension count original).execute
          (Register.prod framed.register Reference)
          (splitState (ctx.disjointUnion resident
            (MeasurementCells.original_disjoint ctx resident dimension count original))
            framed initial state)).mapHistory
              (fun record => (record.1.1, (record.1.2, paths record.2))) := by
  intro count
  induction count with
  | zero =>
      intro original outside rightOutside combined initial actual same paths Reference
        History _ state
      have entries := union_assoc ctx resident framed original outside rightOutside combined
      have actualId : actual = .id ((ctx.disjointUnion resident original).disjointUnion
          framed outside) :=
        eq_of_heq (same.trans (id_heq entries).symm)
      subst actual
      have skipped := contextUnion_splitState_skip (ctx.disjointUnion resident original)
        framed outside state
      exact skipped.trans (by congr 1)
  | succ count ih =>
      intro original outside rightOutside combined initial actual same paths Reference
        History _ state
      let middle := MeasurementCells.context ctx dimension count
      let key := middle.canonicalFreshKey
      let shape : CShape := .finite dimension
      let fresh := middle.canonicalFreshKey_fresh
      let originalPrefix := MeasurementCells.retained_disjoint key shape fresh original
      let originalFresh := MeasurementCells.retained_fresh_union key shape fresh original
      let outsidePrefix := MeasurementCells.retained_disjoint key shape originalFresh outside
      let combinedPrefix := MeasurementCells.retained_disjoint key shape fresh combined
      let expandedPrefix := MeasurementCells.allocateFramed ctx
        (resident.disjointUnion framed rightOutside) dimension count combinedPrefix
      have first := union_assoc ctx resident framed
        (MeasurementCells.original_disjoint ctx resident dimension count originalPrefix)
        initial rightOutside
        (MeasurementCells.original_disjoint ctx
          (resident.disjointUnion framed rightOutside) dimension count combinedPrefix)
      have mid := union_assoc middle resident framed originalPrefix outsidePrefix
        rightOutside combinedPrefix
      have last := union_assoc (MeasurementCells.context ctx dimension (count + 1))
        resident framed original outside rightOutside combined
      let earlierCode : Circuit
          (RuntimeCtx.disjointUnion
            (ctx.disjointUnion resident
              (MeasurementCells.original_disjoint ctx resident dimension count originalPrefix))
            framed initial)
          ((middle.disjointUnion resident originalPrefix).disjointUnion framed outsidePrefix) :=
        Eq.mpr (congrArg (fun pre => Circuit pre
          ((middle.disjointUnion resident originalPrefix).disjointUnion framed outsidePrefix))
            first)
          (Eq.mpr (congrArg (fun post => Circuit
            (ctx.disjointUnion (resident.disjointUnion framed rightOutside)
              (MeasurementCells.original_disjoint ctx
                (resident.disjointUnion framed rightOutside) dimension count combinedPrefix)) post)
                  mid) expandedPrefix)
      have samePrefix : HEq earlierCode expandedPrefix :=
        (inputCast_heq first _).trans (outputCast_heq mid expandedPrefix)
      let actualFresh := MeasurementCells.retained_fresh_union key shape originalFresh outside
      let retained := Circuit.retain
        ((middle.disjointUnion resident originalPrefix).disjointUnion framed outsidePrefix)
        key shape actualFresh
      have sameRetain := retain_heq mid key shape actualFresh
        (MeasurementCells.retained_fresh_union key shape fresh combined)
      have decomposed : actual = earlierCode.seq retained := by
        apply eq_of_heq
        exact same.trans (seq_heq first mid last earlierCode retained expandedPrefix
          (Circuit.retain (middle.disjointUnion (resident.disjointUnion framed rightOutside)
            combinedPrefix) key shape
              (MeasurementCells.retained_fresh_union key shape fresh combined))
          samePrefix sameRetain).symm
      subst actual
      let prefixPaths :
          (MeasurementCells.allocateFramed ctx resident dimension count originalPrefix).Path →
            earlierCode.Path := fun path => (paths (path, ())).1
      have prior := ih originalPrefix outsidePrefix rightOutside combinedPrefix initial
        earlierCode samePrefix prefixPaths Reference state
      change splitState
          ((middle.addRetained key shape fresh).disjointUnion resident original) framed outside
          ((((earlierCode.execute Reference state).retain key shape actualFresh)).mapHistory
            (fun record => (record.1.1, (record.1.2, record.2)))) = _
      erw [contextUnion_splitState_mapHistory, MeasurementCells.retain_splitState, prior,
        State.mapHistory_retain]
      · change _ =
          ((((MeasurementCells.allocateFramed ctx resident dimension count originalPrefix).execute
            (Register.prod framed.register Reference)
            (splitState (ctx.disjointUnion resident
              (MeasurementCells.original_disjoint ctx resident dimension count originalPrefix))
              framed initial state)).retain key shape originalFresh).mapHistory
                (fun record => (record.1.1, (record.1.2, record.2)))).mapHistory _
        simp only [State.mapHistory_comp, Function.comp_def]
        erw [State.mapHistory_comp]
        conv_rhs => erw [State.mapHistory_comp]
        congr 1
      · exact originalFresh

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

/-- Reassociating the actual resident frames retains the original arithmetic allocation path. -/
def allocateCellsPathEquiv :
    (Allocation.allocateCells p.size (2 * exponentWidth)).Path ≃
      (allocateCells E exponentWidth).Path := by
  let expandedFrame := (Allocation.exponents p.size (2 * exponentWidth)).disjointUnion
    (frame E exponentWidth) (exponents_disjoint E exponentWidth)
  let complete := union_right_separate
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (numerator_disjoint E exponentWidth) (exponents_disjoint E exponentWidth)
  let original := MeasurementCells.original_disjoint (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  have first := union_assoc (InversePreparation.after p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))
    (auxiliary_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) original
  have last := union_assoc (NumeratorMeasurement.context p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) complete
  let originalPaths := MeasurementCells.allocateFramedPathEquiv
    (InversePreparation.after p.size) (Allocation.exponents p.size (2 * exponentWidth))
    2 p.size (Allocation.complete_disjoint p.size (2 * exponentWidth))
  let expanded := MeasurementCells.allocateFramed (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  let expandedPaths := MeasurementCells.allocateFramedPathEquiv
    (InversePreparation.after p.size) expandedFrame 2 p.size complete
  exact ((originalPaths.symm.trans expandedPaths).trans (pathTransportOutput last expanded)).trans
    (pathTransportInput first _)

/-- The actual original arithmetic retains preserve the full public store and reference state. -/
theorem allocateCells_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (withAuxiliary E exponentWidth) Reference History) :
    splitState (Allocation.withCells p.size (2 * exponentWidth))
      (frame E exponentWidth) (cells_disjoint E exponentWidth)
      ((allocateCells E exponentWidth).execute Reference state) =
      ((Allocation.allocateCells p.size (2 * exponentWidth)).execute
        (Register.prod (frame E exponentWidth).register Reference)
        (splitState
          ((InversePreparation.after p.size).disjointUnion
            (Allocation.exponents p.size (2 * exponentWidth))
            (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
          (frame E exponentWidth) (auxiliary_disjoint E exponentWidth) state)).mapHistory
            (fun record => (record.1.1,
              (record.1.2, allocateCellsPathEquiv E exponentWidth record.2))) := by
  let expandedFrame := (Allocation.exponents p.size (2 * exponentWidth)).disjointUnion
    (frame E exponentWidth) (exponents_disjoint E exponentWidth)
  let complete := union_right_separate
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (numerator_disjoint E exponentWidth) (exponents_disjoint E exponentWidth)
  let original := MeasurementCells.original_disjoint (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  have first := union_assoc (InversePreparation.after p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))
    (auxiliary_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) original
  have last := union_assoc (NumeratorMeasurement.context p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) complete
  let expanded := MeasurementCells.allocateFramed (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  have same : HEq (allocateCells E exponentWidth) expanded :=
    (inputCast_heq first _).trans (outputCast_heq last expanded)
  exact allocateFramed_outer_execute (InversePreparation.after p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth) 2 p.size
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) complete
    (auxiliary_disjoint E exponentWidth) (allocateCells E exponentWidth) same
    (allocateCellsPathEquiv E exponentWidth) Reference state

/-- Terminal cell allocation preserves all public blocks, quantum-reference entries and paths. -/
theorem allocateTerminal_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (after E exponentWidth) Reference History) :
    splitState (exponentMeasurementContext p exponentWidth)
      (frame E exponentWidth) (terminal_disjoint E exponentWidth)
      ((allocateTerminal E exponentWidth).execute Reference state) =
      ((exponentMeasurementAllocate p exponentWidth).execute
        (Register.prod (frame E exponentWidth).register Reference)
        (splitState (Allocation.after p.size (2 * exponentWidth))
          (frame E exponentWidth) (after_disjoint E exponentWidth) state)).mapHistory
            (fun record => (record.1.1, (record.1.2,
              MeasurementCells.allocateFramedPathEquiv
                (Allocation.after p.size (2 * exponentWidth)) (frame E exponentWidth)
                2 (2 * exponentWidth) (terminal_disjoint E exponentWidth) record.2))) :=
  MeasurementCells.allocateFramed_execute (Allocation.after p.size (2 * exponentWidth))
    (frame E exponentWidth) 2 (2 * exponentWidth) (terminal_disjoint E exponentWidth) state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
