/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Arithmetic

/-!
# Complete quantum-operand Horner multiplication with a clean target

Every prefix retains the original source, complete caller frame and all
three original clean work bits. Both outer-selector branches are proved on
the entire label before applying the phase-exact actual circuit theorem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : QuantumMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (multiplier.ports index)).wire)

private lemma highIndex_value (index : Fin width) :
    (highIndex index).val = width - index.val - 1 := by
  change width - (index.val + 1) = width - index.val - 1
  omega

private lemma first_prefix_double (source word : Word) (selected : Bool)
    (index : Fin width) (first : index.val = 0) :
    prefixWord source word selected index.val =
      Doubling.doubledWord (prefixWord source word selected index.val) := by
  rw [first, prefixWord_zero, doubledWord_zero]

/-- A complete actual round advances the prefix and restores every other original field. -/
lemma cleanRound_canonical (source : Word) (sourceCanonical : Canonical source)
    (retained : Saved) (index : Fin width) :
    cleanRoundStep saved multiplier outer outerMultiplier index
        ((((source, prefixWord source (multiplier.value source retained)
          (outer.get retained) index.val), false), (false, false)), retained) =
      ((((source, prefixWord source (multiplier.value source retained)
        (outer.get retained) (index.val + 1)), false), (false, false)), retained) := by
  let word := multiplier.value source retained
  let selected := outer.get retained
  let target := prefixWord source word selected index.val
  let stage := stepList (stageGates saved (multiplier.ports (highIndex index)) outer
    (outerMultiplier (highIndex index)))
  have targetCanonical : Canonical target := prefixWord_canonical source word selected _
  have bitRead : operandMultiplierValue saved (multiplier.ports (highIndex index))
      source retained = word.val.testBit (width - index.val - 1) :=
    (multiplier.reads source retained (highIndex index)).trans
      (congrArg (fun position => word.val.testBit position) (highIndex_value index))
  have body := stage_clean_canonical saved (multiplier.ports (highIndex index)) outer
    (outerMultiplier (highIndex index)) source (Doubling.doubledWord target) sourceCanonical
    (Doubling.doubledWord_canonical target) retained
  have targetOutput :
      (if selected && operandMultiplierValue saved (multiplier.ports (highIndex index))
          source retained then modularSumWord source (Doubling.doubledWord target)
        else Doubling.doubledWord target) =
      prefixWord source word selected (index.val + 1) := by
    rw [bitRead]
    exact (prefixWord_succ source word selected index.val).symm
  have afterBody : stage ((((source, Doubling.doubledWord target), false),
      (false, false)), retained) =
      ((((source, prefixWord source word selected (index.val + 1)), false),
        (false, false)), retained) :=
    body.trans (congrArg (fun result : Word =>
      ((((source, result), false), (false, false)), retained)) targetOutput)
  by_cases first : index.val = 0
  · have before : target = Doubling.doubledWord target :=
      first_prefix_double source word selected index first
    have shifted := congrArg (fun result : Word =>
      stage ((((source, result), false), (false, false)), retained)) before
    exact (show cleanRoundStep saved multiplier outer outerMultiplier index
        ((((source, target), false), (false, false)), retained) =
          stage ((((source, target), false), (false, false)), retained) from
      if_pos first).trans (shifted.trans afterBody)
  · have doubled := operandDoubling_clean_canonical saved source target targetCanonical
      false false retained
    exact (show cleanRoundStep saved multiplier outer outerMultiplier index
        ((((source, target), false), (false, false)), retained) =
          stage (stepList (operandDoublingGates saved)
            ((((source, target), false), (false, false)), retained)) from
      if_neg first).trans ((congrArg stage doubled).trans afterBody)

/-- Every actual schedule prefix has the original complete clean-frame invariant. -/
lemma cleanPrefix_canonical (source : Word) (sourceCanonical : Canonical source)
    (retained : Saved) (processed : Nat) (within : processed ≤ width) :
    UnitaryCircuit.Realizes.stepList
        ((List.ofFn (cleanRoundStep saved multiplier outer outerMultiplier)).take processed)
        ((((source, zeroWord), false), (false, false)), retained) =
      ((((source, prefixWord source (multiplier.value source retained)
        (outer.get retained) processed), false), (false, false)), retained) := by
  induction processed with
  | zero =>
      exact (congrArg (fun result : Word =>
        ((((source, result), false), (false, false)), retained))
          (prefixWord_zero source (multiplier.value source retained) (outer.get retained))).symm
  | succ processed ih =>
      let steps := List.ofFn (cleanRoundStep saved multiplier outer outerMultiplier)
      have inBounds : processed < width := by omega
      have listBound : processed < steps.length := by
        simpa only [steps, List.length_ofFn] using inBounds
      have previous := ih (by omega)
      have selected : steps.get ⟨processed, listBound⟩ =
          cleanRoundStep saved multiplier outer outerMultiplier ⟨processed, inBounds⟩ := by
        simp only [steps, List.get_ofFn, Fin.cast_mk]
      have actual := UnitaryCircuit.Realizes.stepList_take_succ steps processed listBound
        ((((source, zeroWord), false), (false, false)), retained)
      exact actual.trans ((congrArg (steps.get ⟨processed, listBound⟩) previous).trans
        ((congrFun selected _).trans
          (cleanRound_canonical saved multiplier outer outerMultiplier source sourceCanonical
            retained ⟨processed, inBounds⟩)))

/-- The complete native program multiplies into the original zero target, retaining all else. -/
lemma clean_canonical (source : Word) (sourceCanonical : Canonical source) (retained : Saved) :
    cleanStep saved multiplier outer outerMultiplier
        ((((source, zeroWord), false), (false, false)), retained) =
      ((((source, prefixWord source (multiplier.value source retained)
        (outer.get retained) width), false), (false, false)), retained) := by
  have actual := cleanPrefix_canonical saved multiplier outer outerMultiplier source
    sourceCanonical retained width le_rfl
  have complete : (List.ofFn (cleanRoundStep saved multiplier outer outerMultiplier)).take width =
      List.ofFn (cleanRoundStep saved multiplier outer outerMultiplier) :=
    List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
  exact (congrArg (fun steps => UnitaryCircuit.Realizes.stepList steps
      ((((source, zeroWord), false), (false, false)), retained)) complete).symm.trans actual

/-- The actual complete native tree has the exact clean multiplication action on basis kets. -/
lemma cleanProgram_canonical (environment : OracleModel.empty.Interpretation)
    (source : Word) (sourceCanonical : Canonical source) (retained : Saved) :
    (cleanProgram saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, zeroWord), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, prefixWord source (multiplier.value source retained)
            (outer.get retained) width), false), (false, false)), retained))) :=
  ((clean_realizes saved multiplier outer outerMultiplier environment).apply_encoded_ket _).trans
    (congrArg (fun state => NormalizedVector.ket
      ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode state)))
        (clean_canonical saved multiplier outer outerMultiplier source sourceCanonical retained))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
