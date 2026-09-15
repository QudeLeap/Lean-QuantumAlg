/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Centering.Arithmetic

/-!
# Original centered-target semantics of actual stored-bit selection

The proved actual comparison values select the original centered-value formula.
All original scratch and flag outputs and the complete caller frame survive the
selected arithmetic. No incoming-scratch or modulus-range premise is required.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- An actual correct stored half comparison selects its exact original raw integer expression. -/
theorem half_represents (refs : Refs ctx width) (store : Store ctx)
    (correct : (store.read (writeInput refs.belowHalf)).toBool =
      decide ((store.read refs.a).toNat < (store.read refs.modulus).toNat / 2)) :
    RawSignedRepresents ((halfStep refs store).1.read (writeInput refs.output))
      (if (store.read refs.a).toNat < (store.read refs.modulus).toNat / 2 then
        -(store.read refs.a).toNat else (store.read refs.modulus).toNat -
          (store.read refs.a).toNat : Int) := by
  change RawSignedRepresents
    ((halfArmStep refs (store.read (writeInput refs.belowHalf)) store).1.read
      (writeInput refs.output)) _
  cases value : store.read (writeInput refs.belowHalf) with
  | bit flag =>
    have selected : flag = decide ((store.read refs.a).toNat <
        (store.read refs.modulus).toNat / 2) := by
      simpa only [value, CShape.Value.toBool] using correct
    cases flag
    · have failed := of_decide_eq_false selected.symm
      simp only [halfArmStep, if_neg failed]
      exact sub_represents refs refs.modulus refs.a store
    · have passed := of_decide_eq_true selected.symm
      simp only [halfArmStep, if_pos passed]
      exact negate_represents refs store

/-- Actual correct zero and half bits select precisely the original centered integer formula. -/
theorem finish_represents (refs : Refs ctx width) (store : Store ctx)
    (zero : (store.read (writeInput refs.isZero)).toBool = decide ((store.read refs.a).toNat = 0))
    (half : (store.read (writeInput refs.belowHalf)).toBool =
      decide ((store.read refs.a).toNat < (store.read refs.modulus).toNat / 2)) :
    RawSignedRepresents ((finishStep refs store).1.read (writeInput refs.output))
      (RSA.ShortLogTarget.centeredValue (store.read refs.a).toNat
        (store.read refs.modulus).toNat) := by
  change RawSignedRepresents
    ((finishArmStep refs (store.read (writeInput refs.isZero)) store).1.read
      (writeInput refs.output)) _
  cases value : store.read (writeInput refs.isZero) with
  | bit flag =>
    have selected : flag = decide ((store.read refs.a).toNat = 0) := by
      simpa only [value, CShape.Value.toBool] using zero
    cases flag
    · have nonzero := of_decide_eq_false selected.symm
      simp only [finishArmStep, RSA.ShortLogTarget.centeredValue, if_neg nonzero]
      exact half_represents refs store half
    · have isZero := of_decide_eq_true selected.symm
      simp only [finishArmStep, RSA.ShortLogTarget.centeredValue, if_pos isZero]
      have subtracted := sub_represents refs refs.a refs.a store
      simp only [sub_self] at subtracted
      exact subtracted

/-- The complete actual output represents the centered value of the original source and modulus. -/
theorem centeredTargetInto_output (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    RawSignedRepresents ((centeredTargetStep refs store).1.read (writeInput refs.output))
      (RSA.ShortLogTarget.centeredValue (store.read refs.a).toNat
        (store.read refs.modulus).toNat) := by
  have sourceFrame := prepare_callerFrame refs store refs.a separation.aAvoidsScratch
    separation.aAvoidsIsZero separation.aAvoidsBelowHalf
  have modulusFrame := prepare_callerFrame refs store refs.modulus separation.modulusAvoidsScratch
    separation.modulusAvoidsIsZero separation.modulusAvoidsBelowHalf
  have zero : ((prepareStore refs store).read (writeInput refs.isZero)).toBool =
      decide (((prepareStore refs store).read refs.a).toNat = 0) := by
    rw [sourceFrame]
    exact prepare_isZero refs separation store
  have half : ((prepareStore refs store).read (writeInput refs.belowHalf)).toBool =
      decide (((prepareStore refs store).read refs.a).toNat <
        ((prepareStore refs store).read refs.modulus).toNat / 2) := by
    rw [sourceFrame, modulusFrame]
    exact prepare_belowHalf refs separation store
  have selected := finish_represents refs (prepareStore refs store) zero half
  rw [sourceFrame, modulusFrame] at selected
  exact selected

/-- All original centered-target outputs and the complete actual four-write caller frame. -/
structure CenteredTargetOutcome (refs : Refs ctx width) (before after : Store ctx) : Prop where
  scratch : (after.read (writeInput refs.scratch)).toNat = (before.read refs.modulus).toNat / 2
  isZero : (after.read (writeInput refs.isZero)).toBool = decide ((before.read refs.a).toNat = 0)
  belowHalf : (after.read (writeInput refs.belowHalf)).toBool =
    decide ((before.read refs.a).toNat < (before.read refs.modulus).toNat / 2)
  output : RawSignedRepresents (after.read (writeInput refs.output))
    (RSA.ShortLogTarget.centeredValue (before.read refs.a).toNat (before.read refs.modulus).toNat)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.scratch.key ∉ other.storageKeys → refs.isZero.key ∉ other.storageKeys →
      refs.belowHalf.key ∉ other.storageKeys → refs.output.key ∉ other.storageKeys →
        after.read other = before.read other

/-- Actual comparison and selection realize the original centered target without initial zeros. -/
theorem centeredTargetInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) : CenteredTargetOutcome refs store (centeredTargetStep refs store).1 := by
  refine ⟨?_, ?_, ?_, centeredTargetInto_output refs separation store,
    centeredTargetInto_callerFrame refs store⟩
  · change ((finishStep refs (prepareStore refs store)).1.read (writeInput refs.scratch)).toNat = _
    rw [finish_callerFrame refs _ _ separation.scratchAvoidsOutput,
      prepare_scratch refs separation store]
  · change ((finishStep refs (prepareStore refs store)).1.read (writeInput refs.isZero)).toBool = _
    rw [finish_callerFrame refs _ _ separation.isZeroAvoidsOutput,
      prepare_isZero refs separation store]
  · change ((finishStep refs (prepareStore refs store)).1.read
      (writeInput refs.belowHalf)).toBool = _
    rw [finish_callerFrame refs _ _ separation.belowHalfAvoidsOutput,
      prepare_belowHalf refs separation store]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
