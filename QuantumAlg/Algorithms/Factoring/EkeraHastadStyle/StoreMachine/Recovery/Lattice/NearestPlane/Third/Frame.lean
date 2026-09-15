/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Normalization

/-!
# Actual third-phase caller frames

All sign, magnitude, numerator, division and target writes belong to the same
actual footprint. The frame applies to arbitrary structural caller reads.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The six actual rounded-division output cells in the third-phase naming scheme. -/
def divisionCells : List PhaseCell :=
  [.divisionMagnitude, .divisionNegative, .divisionWideNumerator,
    .divisionWideDenominator, .divisionQuotientRemainder, .divisionOutput]

/-- Actual mutable cells before the target reduction starts. -/
def beforeReductionCells : List PhaseCell :=
  [.denominatorMagnitude, .numerator] ++ divisionCells

/-- Actual mutable cells of sign normalization, division and target reduction. -/
def suffixCells : List PhaseCell :=
  beforeReductionCells ++ [.reduceProduct, .targetFirst, .targetSecond, .targetThird]

/-- The complete third-phase written footprint. -/
def mutableCells : List PhaseCell := prefixCells ++ suffixCells

/-- Named division cells match the actual stored output keys. -/
theorem division_mutableKeys (refs : Refs ctx width) :
    RoundedDiv.mutableKeys refs.division = divisionCells.map (phaseCellKey refs) := rfl

/-- Reads outside normalization and division writes survive to the actual reduction input. -/
theorem beforeReduction_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell ∈ beforeReductionCells, phaseCellKey refs cell ∉ other.storageKeys) :
    (RoundedDiv.bodyStep refs.division (signedInputsStore refs store)).1.read other =
      store.read other := by
  rw [RoundedDiv.body_callerFrame _ _ other (by
    intro key present
    rw [division_mutableKeys] at present
    obtain ⟨cell, cellMember, keyEq⟩ := List.mem_map.mp present
    subst key
    exact avoids cell (by simp [beforeReductionCells, cellMember]))]
  exact signedInputsStore_callerFrame refs store other
    (avoids .divisionNegative (by simp [beforeReductionCells, divisionCells]))
    (avoids .denominatorMagnitude (by simp [beforeReductionCells]))
    (avoids .numerator (by simp [beforeReductionCells]))

/-- The complete actual normalization suffix frames every read outside all its writes. -/
theorem thirdNormalizeInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell ∈ suffixCells, phaseCellKey refs cell ∉ other.storageKeys) :
    (thirdNormalizeStep refs store).1.read other = store.read other := by
  change (LatticeArithmetic.pointStore (writeInput refs.division.output)
    refs.basis.third refs.target refs.reduceProduct
    (RoundedDiv.bodyStep refs.division (signedInputsStore refs store)).1).read other = _
  rw [LatticeArithmetic.pointReduce_callerFrame _ _ _ _ _ other
    (avoids .reduceProduct (by simp [suffixCells]))
    (avoids .targetFirst (by simp [suffixCells]))
    (avoids .targetSecond (by simp [suffixCells]))
    (avoids .targetThird (by simp [suffixCells]))]
  exact beforeReduction_callerFrame refs store other
    (fun cell present => avoids cell (by simp [suffixCells, present]))

/-- Every caller read outside the full actual third-phase footprint is unchanged. -/
theorem thirdInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell ∈ mutableCells, phaseCellKey refs cell ∉ other.storageKeys) :
    (thirdStep refs store).1.read other = store.read other := by
  unfold thirdStep
  rw [thirdNormalizeInto_callerFrame _ _ other
    (fun cell present => avoids cell (by simp [mutableCells, present]))]
  exact thirdMetricPrefixInto_callerFrame refs store other
    (fun cell present => avoids cell (by simp [mutableCells, present]))

/-- Any named cell outside the actual pre-reduction footprint retains its original stored value. -/
theorem beforeReduction_namedFrame (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape) (source : PhaseCell)
    (sourceKey : other.key = phaseCellKey refs source) (outside : source ∉ beforeReductionCells) :
    (RoundedDiv.bodyStep refs.division (signedInputsStore refs store)).1.read
      (.storage other.toCStorageRef) = store.read (.storage other.toCStorageRef) := by
  apply beforeReduction_callerFrame
  intro cell present
  change phaseCellKey refs cell ∉ [other.key]
  simpa only [List.mem_singleton, sourceKey] using
    separation.phaseCellKey_ne cell source (fun equal => outside (equal ▸ present))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
