/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Sign
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Prefix
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Arithmetic

/-!
# Actual normalized third-coordinate division inputs

The real denominator sign writes its magnitude and controls numerator negation.
No initial value is required of the magnitude cell or the sign flag.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual chronological normalization and numerator-sign writes before division. -/
def signedInputsStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  (numeratorSignStep refs (normalizationStep (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude store).1).1

/-- Actual normalization changes only the flag, magnitude and numerator words. -/
theorem signedInputsStore_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (notFlag : refs.division.negative.key ∉ other.storageKeys)
    (notMagnitude : refs.denominatorMagnitude.key ∉ other.storageKeys)
    (notNumerator : refs.numerator.key ∉ other.storageKeys) :
    (signedInputsStore refs store).read other = store.read other := by
  unfold signedInputsStore
  rw [numeratorSignInto_callerFrame _ _ other notNumerator,
    normalizeMagnitude_callerFrame _ _ _ _ other notFlag notMagnitude]

/-- Actual inputs represent the corrected numerator and positive denominator magnitude. -/
theorem signedInputsStore_correct (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) (numerator denominator : Int)
    (fits : NormalizeFits width numerator denominator)
    (numeratorRep : RawSignedRepresents (store.read (writeInput refs.numerator)) numerator)
    (denominatorRep : RawSignedRepresents (store.read (writeInput refs.denominator)) denominator) :
    RawSignedRepresents ((signedInputsStore refs store).read refs.division.numerator)
        (if denominator < 0 then -numerator else numerator) ∧
      RawSignedRepresents ((signedInputsStore refs store).read refs.division.denominator)
        (denominator.natAbs : Int) := by
  let normalized := (normalizationStep (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude store).1
  have magnitude := normalizeMagnitude_correct (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude store
    (named_avoids refs separation refs.denominator .denominator .divisionNegative rfl (by decide))
  rw [raw_magnitude_of_represents _ denominator fits.widthPositive denominatorRep
    fits.denominatorSignedFits] at magnitude
  have flag := normalizeMagnitude_sign (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude store
    (separation.phaseCellKey_ne .denominatorMagnitude .divisionNegative (by decide))
  rw [raw_sign_of_represents _ denominator fits.widthPositive denominatorRep
    fits.denominatorSignedFits] at flag
  have retained : RawSignedRepresents (normalized.read (writeInput refs.numerator)) numerator := by
    rw [normalizeMagnitude_callerFrame _ _ _ store (writeInput refs.numerator)
      (named_avoids refs separation refs.numerator .numerator .divisionNegative rfl (by decide))
      (named_avoids refs separation refs.numerator .numerator
        .denominatorMagnitude rfl (by decide))]
    exact numeratorRep
  have corrected := numeratorSignInto_correct refs normalized numerator retained
  change (normalized.read (writeInput refs.division.negative)).toBool = decide (denominator < 0)
    at flag
  rw [flag] at corrected
  have magnitudeAfter : ((signedInputsStore refs store).read
      (writeInput refs.denominatorMagnitude)).toNat = denominator.natAbs := by
    unfold signedInputsStore
    rw [numeratorSignInto_callerFrame _ _ (writeInput refs.denominatorMagnitude)
      (named_avoids refs separation refs.denominatorMagnitude .denominatorMagnitude
        .numerator rfl (by decide))]
    exact magnitude
  refine ⟨?_, ?_⟩
  · rw [refs.divisionNumerator]
    simpa only [signedInputsStore, normalized, decide_eq_true_eq] using corrected
  · rw [refs.divisionDenominator]
    unfold RawSignedRepresents Int.ModEq
    rw [magnitudeAfter]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
