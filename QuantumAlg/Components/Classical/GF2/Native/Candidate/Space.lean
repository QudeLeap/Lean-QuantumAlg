/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Candidate
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Resources

/-!
# Actual live space of pivot-record candidate construction

The selected row keeps its masked word and equality bit while the original
column mask may be live. Both nested traversals reuse these same lexical
scopes. Bounds retain all original context roles and apply to every path.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem coefficient_resident (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit)
    (path : (candidateCoefficientChoice candidate column value).Path) :
    (candidateCoefficientChoice candidate column value).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace := by
  cases value with
  | bit value =>
      cases value
      · exact gf2MaterializePivotColumn_resident_le candidate column path
      · exact (SpacePool.max_zero _).le.trans (fun _axis => Nat.le_add_left _ _)

private theorem rowBody_resident
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width)
    (path : (candidateRowBody matrix free candidate zero work flag row column).Path) :
    (candidateRowBody matrix free candidate zero work flag row column).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace := by
  have entry : ctx.residentSpace ≤ SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace :=
    fun _axis => Nat.le_add_left _ _
  refine (Circuit.peakResidentSpace_seq (.classical (candidateMaskOp matrix free work row))
    (.seq (.classical (decisionEqualityOp work zero flag))
      (.branch (.storage flag.toCStorageRef) (candidateCoefficientChoice candidate column)))
    path).le.trans ?_
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_classical]
  exact SpacePool.max_le entry (SpacePool.max_le entry
    (coefficient_resident candidate column path.2.2.1 path.2.2.2))

/-- A selected row charges both original outer cells and the possible inner column mask. -/
theorem gf2CandidateRowSelected_resident_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width)
    (path : (candidateRowSelected matrix free candidate zero row column).Path) :
    (candidateRowSelected matrix free candidate zero row column).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace))
      := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (scopedCandidateRow matrix free candidate zero row column)
    path).le.trans ?_
  refine SpacePool.max_le ?_ ?_
  · intro axis
    change ctx.residentSpace axis ≤ SpacePool.ofShape (.unsignedWord width) axis +
      (SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis))
    omega
  · refine (Circuit.peakResidentSpace_workspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
      (placedCandidateRow matrix free candidate zero row column) path).le.trans ?_
    refine SpacePool.max_le ?_ (rowBody_resident _ _ _ _ _ _ row column path)
    intro axis
    change SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis ≤
      SpacePool.ofShape (.unsignedWord width) axis +
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis))
    omega

/-- The actual pivot-record branch adds no workspace outside the original selected-row scopes. -/
theorem gf2CandidatePivotRow_resident_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width)
    (path : (candidatePivotRow matrix rows free candidate zero row column).Path) :
    (candidatePivotRow matrix rows free candidate zero row column).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace))
      := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · refine (SpacePool.max_zero _).le.trans ?_
        intro axis
        change ctx.residentSpace axis ≤ SpacePool.ofShape (.unsignedWord width) axis +
          (SpacePool.ofShape .bit axis +
            (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis))
        omega
      · exact gf2CandidateRowSelected_resident_le matrix free candidate zero row column path

/-- Both actual traversals reuse the original scopes without multiplying live workspace. -/
theorem gf2BuildCandidate_resident_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (path : (buildCandidate matrix rows free candidate zero).Path) :
    (buildCandidate matrix rows free candidate zero).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace))
      := by
  have entry : ctx.residentSpace ≤ SpacePool.ofShape (.unsignedWord width) +
      (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace))
      := by
    intro axis
    change ctx.residentSpace axis ≤ SpacePool.ofShape (.unsignedWord width) axis +
      (SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis))
    omega
  refine (Circuit.peakResidentSpace_seq (.classical (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column))) path).le.trans ?_
  rw [Circuit.peakResidentSpace_classical]
  refine SpacePool.max_le entry (Circuit.forRange_resident_le width _ _ entry ?_ path.2)
  intro column current
  exact Circuit.forRange_resident_le rowCount _ _ entry
    (fun row => gf2CandidatePivotRow_resident_le matrix rows free candidate zero row column) current

private theorem coefficient_auxiliary (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit)
    (path : (candidateCoefficientChoice candidate column value).Path) :
    (candidateCoefficientChoice candidate column value).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace := by
  cases value with
  | bit value =>
      cases value
      · exact gf2MaterializePivotColumn_auxiliary_le candidate column path
      · exact (SpacePool.max_zero _).le.trans (fun _axis => Nat.le_add_left _ _)

private theorem rowBody_auxiliary
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width)
    (path : (candidateRowBody matrix free candidate zero work flag row column).Path) :
    (candidateRowBody matrix free candidate zero work flag row column).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace := by
  have entry : ctx.auxiliarySpace ≤ SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace :=
    fun _axis => Nat.le_add_left _ _
  refine (Circuit.peakAuxiliarySpace_seq (.classical (candidateMaskOp matrix free work row))
    (.seq (.classical (decisionEqualityOp work zero flag))
      (.branch (.storage flag.toCStorageRef) (candidateCoefficientChoice candidate column)))
    path).le.trans ?_
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_classical]
  exact SpacePool.max_le entry (SpacePool.max_le entry
    (coefficient_auxiliary candidate column path.2.2.1 path.2.2.2))

/-- A selected row charges both original outer cells and the possible inner column mask. -/
theorem gf2CandidateRowSelected_auxiliary_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width)
    (path : (candidateRowSelected matrix free candidate zero row column).Path) :
    (candidateRowSelected matrix free candidate zero row column).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace))
      := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (scopedCandidateRow matrix free candidate zero row column)
    path).le.trans ?_
  refine SpacePool.max_le ?_ ?_
  · intro axis
    change ctx.auxiliarySpace axis ≤ SpacePool.ofShape (.unsignedWord width) axis +
      (SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis))
    omega
  · refine (Circuit.peakAuxiliarySpace_workspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
      (placedCandidateRow matrix free candidate zero row column) path).le.trans ?_
    refine SpacePool.max_le ?_ (rowBody_auxiliary _ _ _ _ _ _ row column path)
    intro axis
    change SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis ≤
      SpacePool.ofShape (.unsignedWord width) axis +
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis))
    omega

/-- The actual pivot-record branch adds no workspace outside the original selected-row scopes. -/
theorem gf2CandidatePivotRow_auxiliary_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width)
    (path : (candidatePivotRow matrix rows free candidate zero row column).Path) :
    (candidatePivotRow matrix rows free candidate zero row column).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace))
      := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · refine (SpacePool.max_zero _).le.trans ?_
        intro axis
        change ctx.auxiliarySpace axis ≤ SpacePool.ofShape (.unsignedWord width) axis +
          (SpacePool.ofShape .bit axis +
            (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis))
        omega
      · exact gf2CandidateRowSelected_auxiliary_le matrix free candidate zero row column path

/-- Both actual traversals reuse the original scopes without multiplying live workspace. -/
theorem gf2BuildCandidate_auxiliary_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (path : (buildCandidate matrix rows free candidate zero).Path) :
    (buildCandidate matrix rows free candidate zero).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace))
      := by
  have entry : ctx.auxiliarySpace ≤ SpacePool.ofShape (.unsignedWord width) +
      (SpacePool.ofShape .bit + (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace))
      := by
    intro axis
    change ctx.auxiliarySpace axis ≤ SpacePool.ofShape (.unsignedWord width) axis +
      (SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis))
    omega
  refine (Circuit.peakAuxiliarySpace_seq (.classical (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column))) path).le.trans ?_
  rw [Circuit.peakAuxiliarySpace_classical]
  refine SpacePool.max_le entry (Circuit.forRange_auxiliary_le width _ _ entry ?_ path.2)
  intro column current
  exact Circuit.forRange_auxiliary_le rowCount _ _ entry
    (fun row => gf2CandidatePivotRow_auxiliary_le matrix rows free candidate zero row column)
    current

end QuantumAlg.ClassicalRoutines.GF2.Native
