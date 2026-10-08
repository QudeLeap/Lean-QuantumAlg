/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program

/-!
# Basis preservation across actual nearest-plane phases

The phase-local injective layouts already separate basis cells from every
actual write. These consequences require no extra cross-phase basis premises.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private theorem third_namedFrame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape)
    (source : LatticeNearestPlaneThird.PhaseCell)
    (sourceKey : other.key = LatticeNearestPlaneThird.phaseCellKey (thirdRefs refs) source)
    (outside : source ∉ LatticeNearestPlaneThird.mutableCells) :
    (LatticeNearestPlaneThird.thirdStep (thirdRefs refs) store).1.read
      (.storage other.toCStorageRef) = store.read (.storage other.toCStorageRef) := by
  apply thirdInto_callerFrame
  intro cell present
  change LatticeNearestPlaneThird.phaseCellKey (thirdRefs refs) cell ∉ [other.key]
  simpa only [List.mem_singleton, sourceKey] using
    separation.third.phase.phaseCellKey_ne cell source
      (fun equal => outside (equal ▸ present))

private def secondMutableCells : List LatticeNearestPlaneSecond.PhaseCell :=
  [.crossFirst, .crossSecond, .crossThird, .crossProductLeft, .crossProductRight,
    .dotProduct, .g11, .g21, .targetDotSecond, .targetDotFirst, .denominator,
    .numerator, .numeratorProduct, .divisionMagnitude, .divisionNegative,
    .divisionWideNumerator, .divisionWideDenominator, .divisionQuotientRemainder,
    .divisionOutput, .reduceProduct, .targetFirst, .targetSecond, .targetThird]

private theorem second_namedFrame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape)
    (source : LatticeNearestPlaneSecond.PhaseCell)
    (sourceKey : other.key = LatticeNearestPlaneSecond.phaseCellKey (secondRefs refs) source)
    (outside : source ∉ secondMutableCells) :
    (LatticeNearestPlaneSecond.secondStep (secondRefs refs) store).1.read
      (.storage other.toCStorageRef) = store.read (.storage other.toCStorageRef) := by
  apply secondInto_callerFrame
  intro key present
  have keys : LatticeNearestPlaneSecond.mutableKeys (secondRefs refs) =
      secondMutableCells.map (LatticeNearestPlaneSecond.phaseCellKey (secondRefs refs)) := rfl
  rw [keys] at present
  obtain ⟨cell, cellMember, keyEq⟩ := List.mem_map.mp present
  subst key
  change LatticeNearestPlaneSecond.phaseCellKey (secondRefs refs) cell ∉ [other.key]
  simpa only [List.mem_singleton, sourceKey] using
    separation.second.phase.phaseCellKey_ne cell source
      (fun equal => outside (equal ▸ cellMember))

omit [BitWord.Selected model] in
private theorem point_of_frames {before after : Store ctx}
    (refs : LatticeState.PointRefs ctx width) (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents before refs value)
    (first : after.read (writeInput refs.first) = before.read (writeInput refs.first))
    (second : after.read (writeInput refs.second) = before.read (writeInput refs.second))
    (third : after.read (writeInput refs.third) = before.read (writeInput refs.third)) :
    LatticeArithmetic.PointRawRepresents after refs value := by
  refine ⟨?_, ?_, ?_⟩
  · rw [first]; exact rep.1
  · rw [second]; exact rep.2.1
  · rw [third]; exact rep.2.2

/-- The actual third phase retains the original first basis row by local separation. -/
theorem thirdInto_preserves_basis_first (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store refs.basis.first value) :
    LatticeArithmetic.PointRawRepresents
      (LatticeNearestPlaneThird.thirdStep (thirdRefs refs) store).1 refs.basis.first value := by
  apply point_of_frames refs.basis.first value rep
  · exact third_namedFrame refs separation store refs.basis.first.first
      .basisFirstFirst rfl (by decide)
  · exact third_namedFrame refs separation store refs.basis.first.second
      .basisFirstSecond rfl (by decide)
  · exact third_namedFrame refs separation store refs.basis.first.third
      .basisFirstThird rfl (by decide)

/-- The actual third phase retains the original second basis row by local separation. -/
theorem thirdInto_preserves_basis_second (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store refs.basis.second value) :
    LatticeArithmetic.PointRawRepresents
      (LatticeNearestPlaneThird.thirdStep (thirdRefs refs) store).1 refs.basis.second value := by
  apply point_of_frames refs.basis.second value rep
  · exact third_namedFrame refs separation store refs.basis.second.first
      .basisSecondFirst rfl (by decide)
  · exact third_namedFrame refs separation store refs.basis.second.second
      .basisSecondSecond rfl (by decide)
  · exact third_namedFrame refs separation store refs.basis.second.third
      .basisSecondThird rfl (by decide)

/-- The actual second phase retains the original first basis row by local separation. -/
theorem secondInto_preserves_basis_first (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store refs.basis.first value) :
    LatticeArithmetic.PointRawRepresents
      (LatticeNearestPlaneSecond.secondStep (secondRefs refs) store).1 refs.basis.first value := by
  apply point_of_frames refs.basis.first value rep
  · exact second_namedFrame refs separation store refs.basis.first.first
      .basisFirstFirst rfl (by decide)
  · exact second_namedFrame refs separation store refs.basis.first.second
      .basisFirstSecond rfl (by decide)
  · exact second_namedFrame refs separation store refs.basis.first.third
      .basisFirstThird rfl (by decide)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree
