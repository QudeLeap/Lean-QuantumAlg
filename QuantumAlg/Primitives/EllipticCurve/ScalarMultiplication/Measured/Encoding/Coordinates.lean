/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Program

/-!
# Conversion grouping on the actual prepared arithmetic coordinates

The grouping reads the original selected coordinate and the existing A
word. Physical bit equations retain every other field when the selected
coordinate changes. In particular, actual preparation supplies A = 0.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open MeasuredUncompute BinaryLabelEncoding
open MAU.Inversion.SharedEEA

private def coordinateWord (width : Nat) (coordinate : MeasuredPointAddition.Coordinate) :
    EncodedBit.Word (ProductPlacement.frameEncoding width) width :=
  match coordinate with
  | .x => FramePorts.input width
  | .y => FramePorts.numerator width

/-- Read the full existing coordinate word, including every finite padded label. -/
def coordinateValue (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (state : ProductPlacement.Frame width) : Fin (2 ^ width) :=
  match coordinate with
  | .x => ProductReadout.input width state
  | .y => ProductReadout.numerator width state

private lemma coordinate_wire (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (index : Fin width) :
    ((coordinateWord width coordinate).bit index).wire.val =
      coordinateStart width coordinate + index.val := by
  cases coordinate
  · exact FramePorts.input_wire width index
  · exact FramePorts.numerator_wire width index

private lemma coordinate_read (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (state : ProductPlacement.Frame width) (index : Fin width) :
    ((coordinateWord width coordinate).bit index).get state =
      (coordinateValue width coordinate state).val.testBit index.rev.val := by
  cases coordinate
  · exact (ProductReadout.readWord_bit (FramePorts.input width) state index).symm
  · exact (ProductReadout.readWord_bit (FramePorts.numerator width) state index).symm

private def inputBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (MAU.Multiplication.Accumulate.Gidney.encoding width)
    (finIdentity (retainedWidth width))
    (prodLeftBit (finIdentity width) (finIdentity width) (finIdentityBit width index))

private def auxiliaryBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (MAU.Multiplication.Accumulate.Gidney.encoding width)
    (finIdentity (retainedWidth width))
    (prodRightBit (finIdentity width) (finIdentity width) (finIdentityBit width index))

private def retainedBit (width : Nat) (index : Fin (retainedWidth width)) :
    EncodedBit (sourceEncoding width) :=
  prodRightBit (MAU.Multiplication.Accumulate.Gidney.encoding width)
    (finIdentity (retainedWidth width)) (finIdentityBit (retainedWidth width) index)

private lemma placed_read (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (state : ProductPlacement.Frame width) (source : EncodedBit (sourceEncoding width))
    (target : EncodedBit (ProductPlacement.frameEncoding width))
    (same : wires width coordinate source.wire = target.wire) :
    source.get ((placement width coordinate).grouping state) = target.get state := by
  rw [ProductReadout.bit_read, ProductReadout.bit_read]
  exact (grouping_bit width coordinate state source.wire).trans
    (congrArg (fun wire : Fin (ProductPlacement.frameEncoding width).width =>
      ((ProductPlacement.frameEncoding width).encode state).val.testBit wire.rev.val) same)

/-- The first grouped native word is exactly the selected original X or Y word. -/
lemma grouping_coordinate (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (state : ProductPlacement.Frame width) :
    ((placement width coordinate).grouping state).1.1 = coordinateValue width coordinate state := by
  apply ProductReadout.word_ext
  intro index
  have same : wires width coordinate (inputBit width index).wire =
      ((coordinateWord width coordinate).bit index).wire := by
    apply Fin.ext
    exact (wires_coordinate width coordinate index).trans
      (coordinate_wire width coordinate index).symm
  have actual := placed_read width coordinate state (inputBit width index)
    ((coordinateWord width coordinate).bit index) same
  change (finIdentityBit width index).get ((placement width coordinate).grouping state).1.1 = _
    at actual
  exact (ProductReadout.bit_read _ _).symm.trans
    (actual.trans (coordinate_read width coordinate state index))

/-- The second grouped native word is precisely the resident A port. -/
lemma grouping_auxiliary (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (state : ProductPlacement.Frame width) :
    ((placement width coordinate).grouping state).1.2 = ProductReadout.accumulator width state := by
  apply ProductReadout.word_ext
  intro index
  have same : wires width coordinate (auxiliaryBit width index).wire =
      ((FramePorts.accumulator width).bit index).wire := by
    apply Fin.ext
    exact (wires_auxiliary width coordinate index).trans
      (FramePorts.accumulator_wire width index).symm
  have actual := placed_read width coordinate state (auxiliaryBit width index)
    ((FramePorts.accumulator width).bit index) same
  change (finIdentityBit width index).get ((placement width coordinate).grouping state).1.2 = _
    at actual
  exact (ProductReadout.bit_read _ _).symm.trans
    (actual.trans (ProductReadout.readWord_bit (FramePorts.accumulator width) state index).symm)

/-- The original prepared full arithmetic frame has the specified two incoming coordinate words. -/
def preparedFrame (modulus : Nat) (x y : Fin (2 ^ modulus.size)) :
    ProductPlacement.Frame modulus.size :=
  (InitialPortProgram.inputFrame modulus x, y)

/-- Replace only the named coordinate in the independently specified prepared frame. -/
def preparedUpdate (modulus : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (x y next : Fin (2 ^ modulus.size)) : ProductPlacement.Frame modulus.size :=
  match coordinate with
  | .x => preparedFrame modulus next y
  | .y => preparedFrame modulus x next

/-- Actual preparation initializes the same A port to zero for arbitrary original coordinates. -/
lemma grouping_prepared_auxiliary (modulus : Nat)
    (coordinate : MeasuredPointAddition.Coordinate) (x y : Fin (2 ^ modulus.size)) :
    ((placement modulus.size coordinate).grouping (preparedFrame modulus x y)).1.2 = 0 := by
  rw [grouping_auxiliary]
  exact InPlaceArithmetic.initial_accumulator modulus x y

/-- The actual grouped original coordinate is the full supplied input word. -/
lemma grouping_prepared_coordinate (modulus : Nat)
    (coordinate : MeasuredPointAddition.Coordinate) (x y : Fin (2 ^ modulus.size)) :
    ((placement modulus.size coordinate).grouping (preparedFrame modulus x y)).1.1 =
      match coordinate with | .x => x | .y => y := by
  rw [grouping_coordinate]
  cases coordinate
  · exact InPlaceArithmetic.initial_input modulus x y
  · exact ProductReadout.numerator_eq modulus.size _

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
