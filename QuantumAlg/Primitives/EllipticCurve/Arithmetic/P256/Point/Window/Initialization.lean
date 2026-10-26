/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Unlookup
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Correction
import all QuantumAlg.Util.Nat.FixedWidth
import Batteries.Data.BitVec.Lemmas

/-!
# Native loading of the same fixed affine starting point

The mathematical choice of starting point supplies two constants. Their
actual X gates act on the original numerical X and Y words in one
physically disjoint layer. Every other wire is preserved on arbitrary
input, and all selected native gates remain in the resource ledger.
This is distinct from the small per-call inversion seed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialization

noncomputable section

open EncodedBit

/-- Original X followed by original Y, both in numerical little-endian order. -/
def word : EncodedBit.Word encoding (256 + 256) :=
  ⟨Fin.append (resultWord .work2).bit (resultWord .numerator).bit⟩

private lemma words_separate (first second : Fin 256) :
    ((resultWord .work2).bit first).wire ≠ ((resultWord .numerator).bit second).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, resultWord_wire] at positions
  simp only [WordPort.physicalIndex] at positions
  have firstBound := first.isLt
  have secondBound := second.isLt
  omega

lemma word_distinct : Function.Injective (fun index => (word.bit index).wire) := by
  intro left right
  refine Fin.addCases (fun left => ?_) (fun left => ?_) left
  · refine Fin.addCases (fun right => ?_) (fun right => ?_) right
    · intro same
      simp only [word, Fin.append_left] at same
      exact congrArg (Fin.castAdd 256) (resultWord_distinct .work2 same)
    · intro same
      simp only [word, Fin.append_left, Fin.append_right] at same
      exact False.elim (words_separate left right same)
  · refine Fin.addCases (fun right => ?_) (fun right => ?_) right
    · intro same
      simp only [word, Fin.append_left, Fin.append_right] at same
      exact False.elim (words_separate right left same.symm)
    · intro same
      simp only [word, Fin.append_right] at same
      exact congrArg (Fin.natAdd 256) (resultWord_distinct .numerator same)

/-- A symbolic finite word; no enumeration of the 512-bit basis is performed. -/
private def concatenate {width : Nat} (x y : Fin (2 ^ width)) : Fin (2 ^ (width + width)) :=
  (BitVec.ofFin y ++ BitVec.ofFin x).toFin

def constant (x y : Fin (2 ^ 256)) : Fin (2 ^ (256 + 256)) := concatenate x y

lemma constant_bit_left (x y : Fin (2 ^ 256)) (index : Fin 256) :
    (constant x y).val.testBit (index.castAdd 256).val = x.val.testBit index.val := by
  change (BitVec.ofFin y ++ BitVec.ofFin x).getLsbD index.val = _
  rw [BitVec.getLsbD_append, if_pos index.isLt, BitVec.getLsbD_ofFin]

lemma constant_bit_right (x y : Fin (2 ^ 256)) (index : Fin 256) :
    (constant x y).val.testBit (index.natAdd 256).val = y.val.testBit index.val := by
  change (BitVec.ofFin y ++ BitVec.ofFin x).getLsbD (256 + index.val) = _
  rw [BitVec.getLsbD_append, if_neg (by omega : ¬256 + index.val < 256)]
  simp only [Nat.add_sub_cancel_left, BitVec.getLsbD_ofFin]

def step (x y : Fin (2 ^ 256)) : Raw → Raw :=
  Word.xorConstantStep word (constant x y)

/-- The actual native loader pays all selected X gates in one independent layer. -/
def program (x y : Fin (2 ^ 256)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical encoding.width).toQuantum :=
  EncodedBit.WindowLookup.wordXProgram (QubitLayout.canonical _) .empty word word_distinct
    (constant x y)

lemma program_realizes (x y : Fin (2 ^ 256)) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding (program x y) environment (step x y) :=
  EncodedBit.WindowLookup.wordXProgram_realizes _ _ _ _ _ environment

lemma step_x_bit (x y : Fin (2 ^ 256)) (state : Raw) (index : Fin 256) :
    (Frame.work2 (step x y state).1).val.testBit index.val =
      ((Frame.work2 state.1).val.testBit index.val ^^ x.val.testBit index.val) := by
  have actual := Word.xorConstantStep_get_target word (constant x y) (index.castAdd 256)
    (fun other different same => different (word_distinct same)) state
  rw [constant_bit_left] at actual
  simpa only [step, word, Fin.append_left, resultWord, pointBit_get, WordPort.bit_get,
    WordPort.value] using actual

lemma step_y_bit (x y : Fin (2 ^ 256)) (state : Raw) (index : Fin 256) :
    (Frame.numerator (step x y state).1).val.testBit index.val =
      ((Frame.numerator state.1).val.testBit index.val ^^ y.val.testBit index.val) := by
  have actual := Word.xorConstantStep_get_target word (constant x y) (index.natAdd 256)
    (fun other different same => different (word_distinct same)) state
  rw [constant_bit_right] at actual
  simpa only [step, word, Fin.append_right, resultWord, pointBit_get, WordPort.bit_get,
    WordPort.value] using actual

/-- Loading after real whole-bank reset puts exactly the chosen affine coordinates in X and Y. -/
lemma step_coordinates (x y : Fin (2 ^ 256)) (state : Raw)
    (zeroX : Frame.work2 state.1 = 0) (zeroY : Frame.numerator state.1 = 0) :
    Frame.work2 (step x y state).1 = x ∧ Frame.numerator (step x y state).1 = y := by
  constructor
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    rw [step_x_bit, zeroX]
    simp
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    rw [step_y_bit, zeroY]
    simp

/-- The complete complement, including A, metadata, controls and all address wires, is unchanged. -/
lemma step_other (x y : Fin (2 ^ 256)) (state : Raw) (observed : EncodedBit encoding)
    (outsideX : ∀ index, ((resultWord .work2).bit index).wire ≠ observed.wire)
    (outsideY : ∀ index, ((resultWord .numerator).bit index).wire ≠ observed.wire) :
    observed.get (step x y state) = observed.get state := by
  apply Word.xorConstantStep_get_observed_of_target_ne word (constant x y) observed
  intro index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simpa only [word, Fin.append_left] using outsideX index
  · simpa only [word, Fin.append_right] using outsideY index

lemma program_eventTrace (x y : Fin (2 ^ 256)) :
    (program x y).eventTrace =
      List.replicate (Word.constantOneIndices (constant x y)).length
        (.gate .singleQubit) :=
  EncodedBit.WindowLookup.wordXProgram_eventTrace _ _ _ _ _

lemma program_native_counts (x y : Fin (2 ^ 256)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (program x y).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate .cnot) (program x y).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) (program x y).eventCost ≤ 512 := by
  simp only [← UnitaryCircuit.ofList_eventTrace_eq_eventCost (program x y), program_eventTrace]
  simp only [ResourcePool.ofList_replicate, ResourcePool.count_scale,
    ResourcePool.count_singleton]
  have differentTF : (Resource.Event.gate .singleQubit :
      Resource.Event (.quantum AlgorithmGate.model .empty)) ≠ .gate .toffoli := by decide
  have differentCX : (Resource.Event.gate .singleQubit :
      Resource.Event (.quantum AlgorithmGate.model .empty)) ≠ .gate .cnot := by decide
  simp only [if_neg differentTF, if_neg differentCX, if_true, Nat.mul_zero, Nat.mul_one,
    true_and]
  exact Word.constantOneIndices_length_le (constant x y)

/-- All selected X gates have disjoint physical support on the original bank. -/
lemma program_quantumTime_le (x y : Fin (2 ^ 256)) :
    (program x y).evaluatedEventDepth Resource.Event.quantumDuration ≤ 1 :=
  EncodedBit.WindowLookup.wordXProgram_quantumTime_le _ _ _ _ _

end

end Initialization

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
