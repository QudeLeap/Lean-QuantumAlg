/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Frame

/-!
# Original point word ports and arithmetic flag coordinates

Work1 and Work2 use the numerical little-endian order of their original
shared-EEA wires. The separate numerator uses its original finite-word
encoding. All three word supports and all three borrowed pool flags are
physically disjoint, independently of quantum labels or clean premises.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point

noncomputable section

/-- Static choice among the three original resident payload words. -/
inductive WordPort where
  | work1
  | work2
  | numerator
deriving DecidableEq

namespace WordPort

def bit : WordPort → Fin 256 → EncodedBit Frame.encoding
  | .work1 => Frame.work1Bit
  | .work2 => Frame.work2Bit
  | .numerator => Frame.numeratorBit

def value : WordPort → Frame.Raw → Fin (2 ^ 256)
  | .work1 => Frame.work1
  | .work2 => Frame.work2
  | .numerator => Frame.numerator

def physicalIndex : WordPort → Fin 256 → Nat
  | .work1, index => index.val
  | .work2, index => 259 + index.val
  | .numerator, index => 580 + (255 - index.val)

lemma bit_wire (port : WordPort) (index : Fin 256) :
    (port.bit index).wire.val = port.physicalIndex index := by
  cases port with
  | work1 => exact Frame.work1Bit_wire index
  | work2 => exact Frame.work2Bit_wire index
  | numerator => exact Frame.numeratorBit_wire index

lemma bit_get (port : WordPort) (index : Fin 256) (state : Frame.Raw) :
    (port.bit index).get state = (port.value state).val.testBit index.val := by
  cases port with
  | work1 => exact Frame.work1Bit_get index state
  | work2 => exact Frame.work2Bit_get index state
  | numerator => exact Frame.numeratorBit_get index state

lemma bit_index_injective (port : WordPort) :
    Function.Injective (fun index : Fin 256 => (port.bit index).wire) := by
  intro left right same
  apply Fin.ext
  have positions := congrArg Fin.val same
  rw [bit_wire, bit_wire] at positions
  have leftBound := left.isLt
  have rightBound := right.isLt
  cases port <;> simp only [physicalIndex] at positions <;> omega

lemma bit_ports_disjoint (left right : WordPort) (different : left ≠ right)
    (first second : Fin 256) : (left.bit first).wire ≠ (right.bit second).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [bit_wire, bit_wire] at positions
  have firstBound := first.isLt
  have secondBound := second.isLt
  cases left <;> cases right <;> simp only [physicalIndex] at positions <;>
    first | exact different rfl | omega

/-- Every original word and numerical bit has a distinct actual physical address. -/
lemma bit_port_injective :
    Function.Injective (fun port : WordPort × Fin 256 => (port.1.bit port.2).wire) := by
  rintro ⟨left, first⟩ ⟨right, second⟩ same
  have samePort : left = right := by
    by_contra different
    exact bit_ports_disjoint left right different first second same
  cases samePort
  exact congrArg (fun index => (left, index)) (bit_index_injective left same)

end WordPort

/-- Original pool positions in reduction/latch/native-lowering order. -/
def arithmeticFlag (index : Fin 3) : EncodedBit Frame.encoding :=
  if index.val = 0 then Frame.reductionBit
  else if index.val = 1 then Frame.latchBit else Frame.loweringBit

def arithmeticFlagIndex (index : Fin 3) : Nat :=
  if index.val = 0 then 559 else if index.val = 1 then 569 else 579

lemma arithmeticFlag_wire (index : Fin 3) :
    (arithmeticFlag index).wire.val = arithmeticFlagIndex index := by
  unfold arithmeticFlag arithmeticFlagIndex
  split_ifs
  · exact Frame.reductionBit_wire
  · exact Frame.latchBit_wire
  · exact Frame.loweringBit_wire

lemma arithmeticFlag_injective :
    Function.Injective (fun index : Fin 3 => (arithmeticFlag index).wire) := by
  intro left right same
  apply Fin.ext
  have positions := congrArg Fin.val same
  rw [arithmeticFlag_wire, arithmeticFlag_wire] at positions
  have leftBound := left.isLt
  have rightBound := right.isLt
  unfold arithmeticFlagIndex at positions
  split_ifs at positions <;> omega

lemma word_flag_disjoint (port : WordPort) (index : Fin 256) (flag : Fin 3) :
    (port.bit index).wire ≠ (arithmeticFlag flag).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [WordPort.bit_wire, arithmeticFlag_wire] at positions
  have indexBound := index.isLt
  unfold arithmeticFlagIndex at positions
  split_ifs at positions <;> cases port <;>
    simp only [WordPort.physicalIndex] at positions <;> omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point
