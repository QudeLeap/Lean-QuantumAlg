/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Loading
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Coordinates

/-!
# Exact selected table word and retained operands of the real loader

The original stream top and complete address select the numerical word.
Loading into the genuine zero result gives exactly that value and keeps
the other numerical words, original digit and genuine normal bit. These
readouts connect the actual query operands to the chronological field
calculation without imposing a new active or inactive input restriction.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

/-- Independent numerical word at the original complete physical address. -/
def selectedWord (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ 256)) (state : Raw) : Fin (2 ^ 256) :=
  table (((selector stream width bounded).stack ⟨0, by omega⟩).get state)
    ((selector stream width bounded).addressLabelAt width 0 (by omega) 0 (by omega) state)

lemma resultWord_ports_disjoint (left right : WordPort) (different : left ≠ right)
    (first second : Fin 256) :
    ((resultWord left).bit first).wire ≠ ((resultWord right).bit second).wire := by
  intro same
  apply WordPort.bit_ports_disjoint left right different first second
  apply Fin.ext
  exact congrArg (fun wire : Fin encoding.width => wire.val) same

lemma loadedState_get_other (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256))
    (observed : EncodedBit encoding)
    (outside : ∀ index, ((resultWord port).bit index).wire ≠ observed.wire) (state : Raw) :
    observed.get (loadedState stream port highRemaining lowWidth bounded lowBound table state) =
      observed.get state :=
  EncodedBit.Word.xorConstantStep_get_observed_of_target_ne (resultWord port) _ observed
    outside state

/-- The real zero-target load contains precisely the original full-address table value. -/
lemma loadedState_source (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw)
    (zero : ∀ index, ((resultWord port).bit index).get state = false) :
    port.value (loadedState stream port highRemaining lowWidth bounded lowBound table state).1 =
      selectedWord stream (highRemaining + lowWidth) bounded table state := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have actual := EncodedBit.Word.xorConstantStep_get_target (resultWord port)
    (selectedWord stream (highRemaining + lowWidth) bounded table state) index
    (fun other different same => different (resultWord_distinct port same)) state
  change ((resultWord port).bit index).get
      (loadedState stream port highRemaining lowWidth bounded lowBound table state) = _ at actual
  rw [zero index, Bool.false_xor] at actual
  simpa only [resultWord, pointBit_get, WordPort.bit_get] using actual

lemma loadedState_word_other (stream : Fin 2) (source observed : WordPort)
    (different : source ≠ observed) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw) :
    observed.value
        (loadedState stream source highRemaining lowWidth bounded lowBound table state).1 =
      observed.value state.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have actual := loadedState_get_other stream source highRemaining lowWidth bounded lowBound
    table ((resultWord observed).bit index)
    (fun other => resultWord_ports_disjoint source observed different other index) state
  simpa only [resultWord, pointBit_get, WordPort.bit_get] using actual

lemma loadedState_digit (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw)
    (index : Fin (highRemaining + lowWidth + 1)) :
    (Enable.digitBit stream (highRemaining + lowWidth) bounded index).get
        (loadedState stream port highRemaining lowWidth bounded lowBound table state) =
      (Enable.digitBit stream (highRemaining + lowWidth) bounded index).get state := by
  apply loadedState_get_other
  intro bit same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, Enable.digitBit_wire] at positions
  have within := bit.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;>
    split_ifs at positions <;> omega

lemma loadedState_normal (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw) :
    normalBit.get (loadedState stream port highRemaining lowWidth bounded lowBound table state) =
      normalBit.get state := by
  apply loadedState_get_other
  intro bit same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, normalBit_wire] at positions
  have within := bit.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
