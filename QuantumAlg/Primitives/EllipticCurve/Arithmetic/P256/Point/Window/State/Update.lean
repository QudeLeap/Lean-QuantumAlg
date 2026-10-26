/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Selection
import all QuantumAlg.Components.Encoded.BitGates.Word.Product

/-!
# Complete original readouts after a numerical word replacement

The mathematical output labels of real measured queries keep the complete
scan pool, every other numerical word, both source roles, the genuine normal
bit and the complete address. These identities supply the next chronological
operation's premises without adding reset instructions or a new input domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

lemma resultSetConstant_pool (port : WordPort) (value : Word) (state : Raw) :
    (resultSetConstant (resultWord port) value state).1.1.1.2 = state.1.1.1.2 :=
  QueryInsertion.wordXor_pool port _ state

lemma resultSetConstant_cleanPool (port : WordPort) (value : Word) (state : Raw)
    (clean : Frame.CleanPool state.1) :
    Frame.CleanPool (resultSetConstant (resultWord port) value state).1 :=
  (resultSetConstant_pool port value state).trans clean

lemma resultSetConstant_word (port : WordPort) (value : Word) (state : Raw) :
    port.value (resultSetConstant (resultWord port) value state).1 = value := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  simpa only [resultWord, pointBit_get, WordPort.bit_get] using
    resultSetConstant_get (resultWord port) (resultWord_distinct port) value state index

lemma resultSetConstant_word_other (source observed : WordPort) (different : source ≠ observed)
    (value : Word) (state : Raw) :
    observed.value (resultSetConstant (resultWord source) value state).1 =
      observed.value state.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  simpa only [resultWord, pointBit_get, WordPort.bit_get] using
    resultSetConstant_observed (resultWord source) value ((resultWord observed).bit index)
      (fun bit => QueryInsertion.resultWord_ports_disjoint source observed different bit index)
      state

lemma resultSetConstant_digit (port : WordPort) (value : Word) (state : Raw)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (index : Fin (width + 1)) :
    (Enable.digitBit stream width bounded index).get
        (resultSetConstant (resultWord port) value state) =
      (Enable.digitBit stream width bounded index).get state := by
  apply resultSetConstant_observed
  intro bit same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, Enable.digitBit_wire] at positions
  have within := bit.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;>
    split_ifs at positions <;> omega

lemma resultSetConstant_normal (port : WordPort) (value : Word) (state : Raw) :
    normalBit.get (resultSetConstant (resultWord port) value state) = normalBit.get state := by
  apply resultSetConstant_observed
  intro bit same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, normalBit_wire] at positions
  have within := bit.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

lemma resultSetConstant_address (port : WordPort) (value : Word) (state : Raw) :
    (resultSetConstant (resultWord port) value state).2 = state.2 := by
  change (resultSetConstant
    (EncodedBit.Word.onProductLeft addressEncoding
      (⟨port.bit⟩ : EncodedBit.Word Frame.encoding 256))
      value (state.1, state.2)).2 = _
  rw [EncodedBit.Word.resultSetConstant_onProductLeft]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
