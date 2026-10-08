/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Point.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Bounds.Operand
import all QuantumAlg.Util.RSA.ShortLog.Widths

/-!
# Actual short-log candidate from the stored nearest-plane center

The three actual rounded-division outputs supply the coefficient center.
One original offset and the retained reduced basis feed the native candidate
constructor, with the original source point and width bounds unchanged.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeShortLogCandidatePoint

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The nearest-plane state and caller-owned storage for one candidate point. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The common reduced basis and the three phase-local division outputs. -/
  nearest : LatticeNearestPlaneThree.Refs ctx width
  /-- One caller-supplied coefficient offset. -/
  offset : LatticeState.PointRefs ctx width
  /-- Workspace for the center-plus-offset coefficient. -/
  coefficient : LatticeState.PointRefs ctx width
  /-- Caller-owned destination for the corresponding lattice point. -/
  point : LatticeState.PointRefs ctx width
  /-- Shared low-word product scratch for the three point coordinates. -/
  product : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  productRole : product.toCStorageRef.role = .workspace
  /-- The first nearest-plane coefficient output is usable as a point word. -/
  firstOutputRole : nearest.first.division.output.toCStorageRef.role = .workspace
  /-- The second nearest-plane coefficient output is usable as a point word. -/
  secondOutputRole : nearest.second.division.output.toCStorageRef.role = .workspace
  /-- The third nearest-plane coefficient output is usable as a point word. -/
  thirdOutputRole : nearest.third.division.output.toCStorageRef.role = .workspace

/-- The three phase outputs, ordered as the short-log coefficient center. -/
def centerRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeState.PointRefs ctx width where
  first := refs.nearest.first.division.output
  firstRole := refs.firstOutputRole
  second := refs.nearest.second.division.output
  secondRole := refs.secondOutputRole
  third := refs.nearest.third.division.output
  thirdRole := refs.thirdOutputRole

/-- The literal candidate adapter view shares the actual reduced basis and
nearest-plane coefficient output cells. -/
def candidateRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeCandidatePointMachine.Refs ctx width where
  basis := refs.nearest.basis
  center := centerRefs refs
  offset := refs.offset
  coefficient := refs.coefficient
  point := refs.point
  product := refs.product
  productRole := refs.productRole

/-- Separation required only by the candidate-point suffix. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  candidate : LatticeCandidatePointMachine.Separation (candidateRefs refs)

/-- Caller-owned raw representations at the candidate-point suffix entry. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (before : Store ctx) : Prop where
  basis : LatticeCandidatePointMachine.BasisRawRepresents before refs.nearest.basis
    (LatticeNearestPlaneShortLog.basis m ell samples)
  center : LatticeArithmetic.PointRawRepresents before (centerRefs refs)
    (LatticeNearestPlaneShortLog.trace m ell samples).center
  offset : LatticeArithmetic.PointRawRepresents before refs.offset offset

/-- The candidate adapter's suffix caller frame. -/
def CallerFrame {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {width : Nat}
    (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  LatticeCandidatePointMachine.CallerFrame (model := model) (candidateRefs refs) before after

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual candidate constructor uses the original nearest-plane coefficient cells. -/
def candidatePointInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  LatticeCandidatePointMachine.candidatePointInto (candidateRefs refs)

/-- Complete actual candidate store and chronological native instruction path. -/
def candidateStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidatePointInto refs).Path :=
  LatticeCandidatePointMachine.candidateStep (candidateRefs refs) store

/-- The complete actual source adapter preserves every incoming history and reference block. -/
theorem candidatePointInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePointInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := candidateStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  LatticeCandidatePointMachine.candidatePointInto_execute (candidateRefs refs) Reference state

/-- Exact original short-log outputs and all retained caller reads of the actual suffix. -/
structure Outcome (m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (before after : Store ctx) : Prop where
  coefficient : LatticeArithmetic.PointRawRepresents after refs.coefficient
    ((LatticeNearestPlaneShortLog.trace m ell samples).center.add offset)
  point : LatticeArithmetic.PointRawRepresents after refs.point
    (RSA.shortLogPointAtOffset m ell samples offset)
  callerFrame : CallerFrame refs before after

/-- The actual suffix preserves every read outside the original candidate footprint. -/
theorem candidatePointInto_callerFrame (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (candidateStep refs store).1 :=
  LatticeCandidatePointMachine.candidatePointInto_callerFrame (candidateRefs refs) store

/-- The actual native suffix realizes the original pure short-log point at the caller offset. -/
theorem candidatePointInto_correct (m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions m ell samples offset refs store) :
    Outcome m ell samples offset refs store (candidateStep refs store).1 := by
  have result := LatticeCandidatePointMachine.candidatePointInto_correct (candidateRefs refs)
    separation.candidate store (LatticeNearestPlaneShortLog.basis m ell samples)
    (LatticeNearestPlaneShortLog.trace m ell samples).center offset
    ⟨initial.basis, initial.center, initial.offset⟩
  refine ⟨result.coefficient, ?_, result.callerFrame⟩
  rw [RSA.shortLogPointAtOffset_eq]
  simpa only [candidateStep, candidateRefs, LatticeNearestPlaneShortLog.basis,
    LatticeNearestPlaneShortLog.target, LatticeNearestPlaneShortLog.trace,
    NumberTheory.nearestPlaneTrace3_center] using result.point

/-- Every point visited by the canonical offset scan is exactly representable
in the common signed coordinate word. -/
theorem pointSignedRepresentable (N m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    let point := RSA.shortLogPointAtOffset m ell samples offset
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
        (RSA.ShortLogWidths.coordinateWidth N m ell) point.1 ∧
      ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (RSA.ShortLogWidths.coordinateWidth N m ell) point.2.1 ∧
        ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (RSA.ShortLogWidths.coordinateWidth N m ell) point.2.2 := by
  have coordinateWidths :=
    RSA.shortLogPointAtOffset_coordinate_sizes_le N m ell samples hoffset
  have ledger : 512 * RSA.shortLogRecoveryInputBits N m ell ≤
      RSA.ShortLogWidths.operandWidthBound N m ell := by
    dsimp only [RSA.ShortLogWidths.operandWidthBound, RSA.ShortLogWidths.inputBitWidth]
    omega
  exact
    ⟨LatticeOperandBounds.signedRepresentable_of_size_le_operandWidthBound
        (coordinateWidths.1.trans ledger),
      LatticeOperandBounds.signedRepresentable_of_size_le_operandWidthBound
        (coordinateWidths.2.1.trans ledger),
      LatticeOperandBounds.signedRepresentable_of_size_le_operandWidthBound
        (coordinateWidths.2.2.trans ledger)⟩

/-- The distance, range, and both scaled comparison operands of one canonical
offset slot fit the common unsigned coordinate word. -/
theorem nearTargetOperandsFit (N m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    let point := RSA.shortLogPointAtOffset m ell samples offset
    let target := RSA.shortLogLatticeTarget m ell samples
    let distance := NumberTheory.squaredDistance point.toVector target.toVector
    let upperBound := 2 ^ m
    distance < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
      upperBound < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
        8 * distance < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
          upperBound * upperBound <
              CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
            9 * (upperBound * upperBound) <
              CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) := by
  let point := RSA.shortLogPointAtOffset m ell samples offset
  let target := RSA.shortLogLatticeTarget m ell samples
  let distance := NumberTheory.squaredDistance point.toVector target.toVector
  let upperBound := 2 ^ m
  have operandSizes :=
    RSA.shortLogNearTarget_operand_sizes_le N m ell samples hoffset
  have scaledDistanceSize : Nat.size (8 * distance) ≤
      RSA.ShortLogWidths.operandWidthBound N m ell := by
    simpa only [point, target, distance, RSA.ShortLogWidths.operandWidthBound,
      RSA.ShortLogWidths.inputBitWidth] using operandSizes.1
  have scaledRangeSize : Nat.size (9 * (upperBound * upperBound)) ≤
      RSA.ShortLogWidths.operandWidthBound N m ell := by
    simpa only [point, target, upperBound, pow_two,
      RSA.ShortLogWidths.operandWidthBound, RSA.ShortLogWidths.inputBitWidth] using operandSizes.2
  have scaledDistanceFits :=
    LatticeOperandBounds.nat_lt_wordModulus_of_size_le_operandWidthBound
      scaledDistanceSize
  have scaledRangeFits :=
    LatticeOperandBounds.nat_lt_wordModulus_of_size_le_operandWidthBound
      scaledRangeSize
  have upperBoundSize : Nat.size upperBound ≤
      RSA.ShortLogWidths.operandWidthBound N m ell := by
    dsimp only [upperBound, RSA.ShortLogWidths.operandWidthBound,
      RSA.ShortLogWidths.inputBitWidth, RSA.shortLogRecoveryInputBits]
    rw [Nat.size_pow]
    omega
  have upperBoundFits :=
    LatticeOperandBounds.nat_lt_wordModulus_of_size_le_operandWidthBound
      upperBoundSize
  have distanceFits : distance <
      CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) := by
    exact (show distance ≤ 8 * distance by omega).trans_lt scaledDistanceFits
  have rangeSquareFits : upperBound * upperBound <
      CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) := by
    exact (show upperBound * upperBound ≤
      9 * (upperBound * upperBound) by omega).trans_lt scaledRangeFits
  exact ⟨distanceFits, upperBoundFits, scaledDistanceFits,
    rangeSquareFits, scaledRangeFits⟩

/-- The machine's squared-distance word is exactly the arithmetic operand in
the source near-target predicate. -/
theorem shortLogNearTarget_iff_scaledSquaredDistance (m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (point : NumberTheory.IntegerPoint3) :
    RSA.ShortLogNearTarget m ell samples point ↔
      8 * NumberTheory.integerPointSquaredNorm
          (point.sub (RSA.shortLogLatticeTarget m ell samples)) <
        9 * ((2 ^ m) * (2 ^ m)) := by
  simp only [RSA.ShortLogNearTarget, NumberTheory.squaredDistance_point3,
    NumberTheory.integerPointSquaredNorm, NumberTheory.IntegerPoint3.sub, pow_two]

/-- Actual native multiplicities equal the independent eighteen-instruction candidate formula. -/
theorem candidatePointInto_resourcePool (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).resourcePool path =
      ResourcePool.ofList (LatticeCandidatePointMachine.candidateTrace width) :=
  LatticeCandidatePointMachine.candidatePointInto_resourcePool (candidateRefs refs) path

/-- Actual short-log candidate depth includes all eighteen original native instructions. -/
theorem candidatePointInto_depth (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).depth (fun _ => 1) path = 18 :=
  LatticeCandidatePointMachine.candidatePointInto_depth (candidateRefs refs) path

/-- The actual source adapter restores every borrowed-reference joint state. -/
theorem candidatePointInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePointInto refs).BorrowedRestored Reference state
      ((candidatePointInto refs).execute Reference state) :=
  LatticeCandidatePointMachine.candidatePointInto_borrowedRestored (candidateRefs refs)
    Reference state

/-- Actual resident accounting includes the entire original caller context. -/
theorem candidatePointInto_resident_le (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).peakResidentSpace path ≤ ctx.residentSpace :=
  LatticeCandidatePointMachine.candidatePointInto_resident_le (candidateRefs refs) path

/-- Actual auxiliary accounting retains the original cell roles without extra storage. -/
theorem candidatePointInto_auxiliary_le (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  LatticeCandidatePointMachine.candidatePointInto_auxiliary_le (candidateRefs refs) path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeShortLogCandidatePoint
