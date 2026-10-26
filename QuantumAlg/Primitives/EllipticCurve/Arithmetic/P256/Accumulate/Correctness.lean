/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Arithmetic

/-!
# Actual arbitrary-accumulator multiplication and complete source restoration

The original target ranges over all canonical residues, including nonzero
accumulators. Every forward prefix retains the original multiplier, outer
selector, caller complement and clean flags. The actual complete inverse
then restores the source for both outer-selector branches.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

/-- The complete actual next add uses the unchanged original multiplier bit. -/
lemma forwardRound_canonical (source target : Word) (sourceCanonical : Canonical source)
    (retained : Saved) (index : Fin width) :
    forwardRoundStep saved multiplier outer outerMultiplier index
        ((((sourceWord source (index.val - 1),
          accumulatorWord source (multiplier.value retained) target
            (outer.get retained) index.val), false), (false, false)), retained) =
      ((((sourceWord source index.val,
        accumulatorWord source (multiplier.value retained) target
          (outer.get retained) (index.val + 1)), false), (false, false)), retained) := by
  let word := multiplier.value retained
  let selected := outer.get retained
  let previous := sourceWord source (index.val - 1)
  let current := sourceWord source index.val
  let accumulator := accumulatorWord source word target selected index.val
  let stage := stepList (stageGates saved (.retained (multiplier.bits index)) outer
    (outerMultiplier index))
  have accumulatorCanonical : Canonical accumulator :=
    accumulatorWord_canonical source word target selected index.val
  have body := stage_clean_canonical saved (.retained (multiplier.bits index)) outer
    (outerMultiplier index) current accumulator
    (sourceWord_canonical source sourceCanonical index.val) accumulatorCanonical retained
  have bitRead : operandMultiplierValue saved (.retained (multiplier.bits index)) current
      retained = word.val.testBit index.val := multiplier.reads retained index
  have targetOutput :
      (if selected && operandMultiplierValue saved (.retained (multiplier.bits index))
          current retained then modularSumWord current accumulator else accumulator) =
      accumulatorWord source word target selected (index.val + 1) := by
    rw [bitRead]
    exact (accumulatorWord_succ source word target selected sourceCanonical index.val).symm
  have afterBody : stage ((((current, accumulator), false), (false, false)), retained) =
      ((((current, accumulatorWord source word target selected (index.val + 1)), false),
        (false, false)), retained) :=
    body.trans (congrArg (fun result : Word =>
      ((((current, result), false), (false, false)), retained)) targetOutput)
  by_cases first : index.val = 0
  · have unchanged : previous = current := by dsimp only [previous, current]; rw [first]
    have shifted := congrArg (fun value : Word =>
      stage ((((value, accumulator), false), (false, false)), retained)) unchanged
    exact (show forwardRoundStep saved multiplier outer outerMultiplier index
        ((((previous, accumulator), false), (false, false)), retained) =
          stage ((((previous, accumulator), false), (false, false)), retained) from
      if_pos first).trans (shifted.trans afterBody)
  · have indexNext : index.val - 1 + 1 = index.val := by omega
    have currentEq : Doubling.doubledWord previous = current :=
      congrArg (sourceWord source) indexNext
    have doubled := sourceDoubling_canonical saved previous accumulator
      (sourceWord_canonical source sourceCanonical _) false false retained
    have prepared := doubled.trans (congrArg (fun value : Word =>
      ((((value, accumulator), false), (false, false)), retained)) currentEq)
    exact (show forwardRoundStep saved multiplier outer outerMultiplier index
        ((((previous, accumulator), false), (false, false)), retained) =
          stage (sourceDoublingStep saved
            ((((previous, accumulator), false), (false, false)), retained)) from
      if_neg first).trans ((congrArg stage prepared).trans afterBody)

/-- Every executed low-bit prefix has the complete original-frame invariant. -/
lemma forwardPrefix_canonical (source target : Word) (sourceCanonical : Canonical source)
    (targetCanonical : Canonical target) (retained : Saved)
    (processed : Nat) (within : processed ≤ width) :
    UnitaryCircuit.Realizes.stepList
        ((List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier)).take processed)
        ((((source, target), false), (false, false)), retained) =
      ((((sourceWord source (processed - 1),
        accumulatorWord source (multiplier.value retained) target (outer.get retained) processed),
          false), (false, false)), retained) := by
  induction processed with
  | zero =>
      exact (congrArg (fun result : Word =>
        ((((source, result), false), (false, false)), retained))
          (accumulatorWord_zero source (multiplier.value retained) target
            (outer.get retained) targetCanonical)).symm
  | succ processed ih =>
      let steps := List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier)
      have inBounds : processed < width := by omega
      have listBound : processed < steps.length := by
        simpa only [steps, List.length_ofFn] using inBounds
      have previous := ih (by omega)
      have selected : steps.get ⟨processed, listBound⟩ =
          forwardRoundStep saved multiplier outer outerMultiplier ⟨processed, inBounds⟩ := by
        simp only [steps, List.get_ofFn, Fin.cast_mk]
      have actual := UnitaryCircuit.Realizes.stepList_take_succ steps processed listBound
        ((((source, target), false), (false, false)), retained)
      exact actual.trans ((congrArg (steps.get ⟨processed, listBound⟩) previous).trans
        ((congrFun selected _).trans
          (forwardRound_canonical saved multiplier outer outerMultiplier source target
            sourceCanonical retained ⟨processed, inBounds⟩)))

lemma forward_canonical (source target : Word) (sourceCanonical : Canonical source)
    (targetCanonical : Canonical target) (retained : Saved) :
    forwardStep saved multiplier outer outerMultiplier
        ((((source, target), false), (false, false)), retained) =
      ((((sourceWord source (width - 1),
        accumulatorWord source (multiplier.value retained) target (outer.get retained) width),
          false), (false, false)), retained) := by
  have actual := forwardPrefix_canonical saved multiplier outer outerMultiplier source target
    sourceCanonical targetCanonical retained width le_rfl
  have complete :
      (List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier)).take width =
        List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier) :=
    List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
  exact (congrArg (fun steps => UnitaryCircuit.Realizes.stepList steps
      ((((source, target), false), (false, false)), retained)) complete).symm.trans actual

/-- Every actual source inverse is executed; the current accumulator may be any word. -/
lemma restoration_canonical (source target : Word) (canonical : Canonical source)
    (retained : Saved) (count : Nat) :
    (inverseSourceDoublingStep saved)^[count]
        ((((sourceWord source count, target), false), (false, false)), retained) =
      ((((source, target), false), (false, false)), retained) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have first := inverseSourceDoubling_restore saved (sourceWord source count) target
        (sourceWord_canonical source canonical count) false false retained
      have actual := Function.iterate_succ_apply (inverseSourceDoublingStep saved) count
        ((((sourceWord source (count + 1), target), false), (false, false)), retained)
      exact actual.trans
        ((congrArg ((inverseSourceDoublingStep saved)^[count]) first).trans ih)

/-- The arbitrary original canonical accumulator receives the selected product;
all original source, multiplier, caller and work fields are restored. -/
lemma fullStep_canonical (source target : Word) (sourceCanonical : Canonical source)
    (targetCanonical : Canonical target) (retained : Saved) :
    fullStep saved multiplier outer outerMultiplier
        ((((source, target), false), (false, false)), retained) =
      ((((source, accumulatedWord source (multiplier.value retained) target
        (outer.get retained)), false), (false, false)), retained) :=
  (congrArg ((inverseSourceDoublingStep saved)^[width - 1])
    (forward_canonical saved multiplier outer outerMultiplier source target sourceCanonical
      targetCanonical retained)).trans
    ((restoration_canonical saved source _ sourceCanonical retained (width - 1)).trans
      (congrArg (fun result : Word => ((((source, result), false), (false, false)), retained))
        (accumulatorWord_full source (multiplier.value retained) target (outer.get retained)
          targetCanonical)))

/-- Literal actual native execution implements arbitrary-accumulator MAC without phase loss. -/
lemma program_canonical (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target) (retained : Saved) :
    (program saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, target), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, accumulatedWord source (multiplier.value retained) target
            (outer.get retained)), false), (false, false)), retained))) :=
  ((realizes saved multiplier outer outerMultiplier environment).apply_encoded_ket _).trans
    (congrArg (fun state => NormalizedVector.ket
      ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode state)))
        (fullStep_canonical saved multiplier outer outerMultiplier source target sourceCanonical
          targetCanonical retained))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
