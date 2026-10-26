/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Seed
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Seed

/-!
# The complete fixed affine loader output is the original blank source

The equality retains every original register, including the three Work2
padding bits, metadata, pool, controls and address. Its proof uses symbolic
bit positions and the actual loader's preservation laws.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialization

noncomputable section

open MAU.Inversion MAU.Inversion.SharedEEA MAU.Inversion.SharedEEA.Scanned

private def residentBlank (width : Nat) (x y : Fin (2 ^ width)) :
    ControlledResidentFrame.Data width :=
  ControlledResidentSeed.blank width ((BitVec.ofFin x).setWidth (width + 3))
    (0, (0, false)) (false, (false, false)) y

private lemma ofFin_zero (width : Nat) :
    BitVec.ofFin (0 : Fin (2 ^ width)) = 0#width := rfl

private lemma reverse_zero (width : Nat) : (0#width).reverse = 0#width := by
  apply BitVec.eq_of_getMsbD_eq
  intro index _
  simp only [BitVec.getMsbD_reverse, BitVec.getLsbD_zero, BitVec.getMsbD_zero]

private lemma encoded_product_zero {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (x : Left) (y : Right) (first : (left.encode x).val = 0)
    (second : (right.encode y).val = 0) :
    ((BinaryLabelEncoding.prod left right).encode (x, y)).val = 0 := by
  rw [BinaryLabelEncoding.prod_encode, UnitaryCircuit.prodEquiv_value, first, second]
  simp only [Nat.mul_zero, Nat.add_zero]

private lemma word_zero_encode (width : Nat) :
    ((wordEncoding width).encode 0).val = 0 := BitVec.toNat_zero

private lemma register_zero_encode (width : Nat) :
    ((SharedEEA.encoding width).encode (ResidentSeed.blank width 0)).val = 0 := by
  change ((tupleEncoding width).encode
    ((0, 0), (((0, 0), (0, 0)), (((false, false), (false, false)), false)))).val = 0
  repeat' apply encoded_product_zero
  all_goals exact word_zero_encode _

private lemma residentBlank_zero (width : Nat) :
    residentBlank width 0 0 =
      (((ResidentSeed.blank width 0, (0, (0, false))), 0), (false, (false, false))) := by
  unfold residentBlank
  rw [ofFin_zero, BitVec.setWidth_zero]
  simp only [ControlledResidentSeed.blank, ControlledResidentFrame.reassemble,
    OutputOrientation.grouping, Equiv.coe_fn_symm_mk, ResidentSeed.blank, reverse_zero]
  rfl

private lemma residentBlank_zero_encode (width : Nat) :
    ((ControlledResidentFrame.encoding width).encode (residentBlank width 0 0)).val = 0 := by
  rw [residentBlank_zero]
  apply encoded_product_zero
  · apply encoded_product_zero
    · apply encoded_product_zero
      · exact register_zero_encode width
      · apply encoded_product_zero
        · exact word_zero_encode _
        · exact encoded_product_zero _ _ _ _ (word_zero_encode _) rfl
    · rfl
  · exact encoded_product_zero _ _ _ _ rfl
      (encoded_product_zero _ _ _ _ rfl rfl)

private lemma fullBlank_zero_encode (width : Nat) :
    ((BinaryLabelEncoding.prod (ControlledResidentFrame.encoding width) addressEncoding).encode
      (residentBlank width 0 0, (0 : Address))).val = 0 :=
  encoded_product_zero _ _ _ _ (residentBlank_zero_encode width) rfl

private lemma equal_of_zero_encoding {Data : Type} (labels : BinaryLabelEncoding Data)
    (first last : Data) (initial : (labels.encode first).val = 0)
    (final : (labels.encode last).val = 0) : first = last :=
  labels.encode_injective (Fin.ext (initial.trans final.symm))

attribute [local irreducible] zeroRaw residentBlank

private lemma actual_encoding :
    encoding = .prod (ControlledResidentFrame.encoding 256) addressEncoding := rfl

section

attribute [local irreducible] encoding Frame.encoding ControlledResidentFrame.encoding
  addressEncoding

private lemma zeroRaw_complete : zeroRaw = (residentBlank 256 0 0, 0) := by
  apply equal_of_zero_encoding encoding _ _ (congrArg Fin.val zeroRaw_encode)
  rw [actual_encoding]
  exact fullBlank_zero_encode 256

end

private def withoutAt (width : Nat)
    (state : ControlledResidentFrame.Data width × Address) :
    ControlledResidentFrame.Data width × Address :=
  (((({ state.1.1.1.1 with secondWord := 0 }, state.1.1.1.2), 0), state.1.2), state.2)

private def restoreAt (width : Nat) (state : ControlledResidentFrame.Data width × Address)
    (x : BitVec (width + 3)) (y : Fin (2 ^ width)) :
    ControlledResidentFrame.Data width × Address :=
  (((({ state.1.1.1.1 with secondWord := x }, state.1.1.1.2), y), state.1.2), state.2)

private abbrev withoutCoordinates := withoutAt 256

private abbrev restoreCoordinates := restoreAt 256

private lemma restore_blank (width : Nat) (x y : Fin (2 ^ width)) :
    restoreAt width (withoutAt width (residentBlank width 0 0, 0))
      ((BitVec.ofFin x).setWidth (width + 3)).reverse y = (residentBlank width x y, 0) := by
  unfold residentBlank
  rfl

private lemma restore_withoutCoordinates (state : Raw) :
    restoreCoordinates (withoutCoordinates state) state.1.1.1.1.secondWord state.1.1.2 =
      state := rfl

private lemma step_withoutCoordinates (x y : Fin (2 ^ 256)) (state : Raw) :
    withoutCoordinates (step x y state) = withoutCoordinates state := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate present
  rw [EncodedBit.Word.xorConstantGates] at present
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp present
  change ∀ current, withoutCoordinates ((word.bit index).flip current) = _
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · intro current
    simp only [word, Fin.append_left]
    rfl
  · intro current
    simp only [word, Fin.append_right]
    rfl

private lemma seed_withoutCoordinates (x y : Fin (2 ^ 256)) :
    withoutCoordinates (seed x y) = withoutCoordinates (residentBlank 256 0 0, 0) := by
  rw [seed, step_withoutCoordinates, zeroRaw_complete]

private def work2PhysicalBit (index : Fin 259) : EncodedBit encoding :=
  pointBit (Frame.scanBit (sourceBit 256 (secondWordBit 256 index)))

private lemma work2PhysicalBit_wire (index : Fin 259) :
    (work2PhysicalBit index).wire.val = 259 + index.val := rfl

private lemma work2PhysicalBit_get (index : Fin 259) (state : Raw) :
    (work2PhysicalBit index).get state = state.1.1.1.1.secondWord.getMsbD index.val := by
  rw [work2PhysicalBit, pointBit_get, Frame.scanBit_get, sourceBit_get, secondWordBit_get]

attribute [local irreducible] work2PhysicalBit Frame.encoding encoding

private lemma padding_outside_x (index : Fin 259) (padding : 256 ≤ index.val)
    (position : Fin 256) :
    ((resultWord .work2).bit position).wire ≠ (work2PhysicalBit index).wire := by
  intro same
  have equal := congrArg Fin.val same
  rw [resultWord_wire, work2PhysicalBit_wire] at equal
  simp only [WordPort.physicalIndex] at equal
  have bounded := position.isLt
  omega

private lemma padding_outside_y (index : Fin 259) (position : Fin 256) :
    ((resultWord .numerator).bit position).wire ≠ (work2PhysicalBit index).wire := by
  intro same
  have equal := congrArg Fin.val same
  rw [resultWord_wire, work2PhysicalBit_wire] at equal
  simp only [WordPort.physicalIndex] at equal
  have bounded := position.isLt
  have physical := index.isLt
  omega

attribute [local irreducible] seed

private lemma padded_reverse_bit {width : Nat} (x : Fin (2 ^ width))
    (index : Nat) (within : index < width + 3) :
    ((BitVec.ofFin x).setWidth (width + 3)).reverse.getMsbD index =
      (BitVec.ofFin x).getLsbD index := by
  rw [BitVec.getMsbD_reverse, BitVec.getLsbD_setWidth]
  simp only [within, decide_true, Bool.true_and]

private lemma seed_secondWord (x y : Fin (2 ^ 256)) :
    (seed x y).1.1.1.1.secondWord = ((BitVec.ofFin x).setWidth 259).reverse := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  change index < 259 at within
  rw [padded_reverse_bit x index within]
  by_cases payload : index < 256
  · have actual := Frame.work2Bit_get ⟨index, payload⟩ (seed x y).1
    rw [Frame.work2Bit, Frame.scanBit_get, sourceBit_get, secondWordBit_get] at actual
    rw [BitVec.getLsbD_ofFin]
    exact actual.trans (congrArg (fun value : Fin (2 ^ 256) => value.val.testBit index)
      (seed_coordinates x y).1)
  · have actual := seed_other x y (work2PhysicalBit ⟨index, within⟩)
      (padding_outside_x ⟨index, within⟩ (show 256 ≤ index from Nat.le_of_not_gt payload))
      (padding_outside_y ⟨index, within⟩)
    rw [BitVec.getLsbD_of_ge (BitVec.ofFin x) index (by omega)]
    exact (work2PhysicalBit_get ⟨index, within⟩ (seed x y)).symm.trans actual

private lemma seed_residentBlank (x y : Fin (2 ^ 256)) :
    seed x y = (residentBlank 256 x y, 0) := by
  rw [← restore_withoutCoordinates (seed x y), seed_withoutCoordinates, seed_secondWord]
  rw [show (seed x y).1.1.2 = y from (seed_coordinates x y).2]
  exact restore_blank 256 x y

private lemma inputFrame_word (p : Nat) (x : Fin (2 ^ p.size)) :
    (InitialPortProgram.inputFrame p x).secondWord =
      (BitVec.ofFin x).setWidth (p.size + 3) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  change x.val = x.val % 2 ^ (p.size + 3)
  exact (Nat.mod_eq_of_lt (x.isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))).symm

private lemma transported_residentBlank {width : Nat} (same : width = 256)
    (x y : Fin (2 ^ width)) :
    Inversion.Transport.state same (residentBlank width x y) =
      residentBlank 256 (Fin.cast (congrArg (fun n => 2 ^ n) same) x)
        (Fin.cast (congrArg (fun n => 2 ^ n) same) y) := by
  cases same
  unfold residentBlank
  rfl

private lemma sourceBlank_residentBlank (x y : Fin (2 ^ modulus.size)) :
    sourceBlank x y (false, (false, false)) 0 =
      (Inversion.Transport.state Inversion.modulus_size
        (residentBlank modulus.size x y), 0) := by
  unfold sourceBlank Inversion.Seed.blank residentBlank
  rw [inputFrame_word]

/-- The actual fixed loader produces the complete original arithmetic source boundary. -/
lemma seed_sourceBlank (x y : Fin (2 ^ 256)) :
    seed x y = sourceBlank
      (Fin.cast (congrArg (fun n => 2 ^ n) Inversion.modulus_size).symm x)
      (Fin.cast (congrArg (fun n => 2 ^ n) Inversion.modulus_size).symm y)
      (false, (false, false)) 0 := by
  rw [seed_residentBlank, sourceBlank_residentBlank, transported_residentBlank]
  simp only [Fin.cast_cast, Fin.cast_eq_self]

end

end Initialization

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
