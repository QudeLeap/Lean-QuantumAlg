/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Native.Control
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Gates
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Frame.Controlled
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Primitives.MAU.Addition.Gidney.ModularOffset
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Program

/-!
# Native arithmetic in the existing affine point-addition frame

Each placed body comes from an existing executable native program. Its
binary grouping and its physical leaf addresses are derived from the same
wire permutation. Only the explicitly emitted control exchanges execute
SWAP operations. The two measured calls reuse the original arithmetic
words and outcome cells [LYL+26, sec_point_add/sec_point_add.tex:24-36,119-123].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open MeasuredUncompute MAU.Inversion EncodedBit GateSpec BinaryLabelEncoding

/-- The complete physical frame, including both actual control coordinates. -/
abbrev NativeCircuit (width : Nat) :=
  UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical (encoding width).width).toQuantum

private def prefixAddress (count index : Nat) : Nat :=
  if index < count then if index = 0 then count - 1 else index - 1 else index

private def prefixInverse (count index : Nat) : Nat :=
  if index < count then if index + 1 < count then index + 1 else 0 else index

/-- Rotate only a finite prefix when placing a leading control or borrowed flag. -/
private def prefixWires (total count : Nat) (fits : count ≤ total) :
    Equiv.Perm (Fin total) where
  toFun index := ⟨prefixAddress count index.val, by
    have bound := index.isLt
    unfold prefixAddress
    split_ifs <;> omega⟩
  invFun index := ⟨prefixInverse count index.val, by
    have bound := index.isLt
    unfold prefixInverse
    split_ifs <;> omega⟩
  left_inv index := by
    apply Fin.ext
    change prefixInverse count (prefixAddress count index.val) = index.val
    unfold prefixAddress prefixInverse
    split_ifs <;> omega
  right_inv index := by
    apply Fin.ext
    change prefixAddress count (prefixInverse count index.val) = index.val
    by_cases inside : index.val < count
    · by_cases next : index.val + 1 < count
      · rw [prefixInverse, if_pos inside, if_pos next, prefixAddress, if_pos next,
          if_neg (by omega)]
        omega
      · have last : count = index.val + 1 := by omega
        rw [last]
        simp [prefixInverse, prefixAddress]
    · simp [prefixInverse, prefixAddress, inside]

private def wordAddress (width start index : Nat) : Nat :=
  if index < width then start + index
  else if start ≤ index ∧ index < start + width then index - start else index

/-- Exchange two word address ranges as placement, retaining every other real wire. -/
private def wordWires (total width start : Nat) (separate : width ≤ start)
    (fits : start + width ≤ total) : Equiv.Perm (Fin total) where
  toFun index := ⟨wordAddress width start index.val, by
    have bound := index.isLt
    unfold wordAddress
    split_ifs <;> omega⟩
  invFun index := ⟨wordAddress width start index.val, by
    have bound := index.isLt
    unfold wordAddress
    split_ifs <;> omega⟩
  left_inv index := by
    apply Fin.ext
    change wordAddress width start (wordAddress width start index.val) = index.val
    unfold wordAddress
    split_ifs <;> omega
  right_inv index := by
    apply Fin.ext
    change wordAddress width start (wordAddress width start index.val) = index.val
    unfold wordAddress
    split_ifs <;> omega

private theorem total_width (width : Nat) :
    (encoding width).width = 3 * width + 4 * width.size + 13 := by
  change ((ProductPlacement.frameEncoding width).width + 1) + 1 = _
  rw [ProductPlacement.frame_width]
  unfold ProductWires.width ProductPlacement.tailWidth
  omega

private def retainedWidth (width : Nat) (control : OffsetControl) : Nat :=
  (encoding width).width - controlWidth control - (width + 2)

@[reducible] private def offsetEncoding (width : Nat) (control : OffsetControl) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity (controlWidth control))
    (BinaryLabelEncoding.prod (MAU.Addition.Gidney.encoding width)
      (BinaryLabelEncoding.finIdentity (retainedWidth width control)))

private theorem offset_width (width : Nat) (control : OffsetControl) :
    (offsetEncoding width control).width = (encoding width).width := by
  change controlWidth control + ((1 + (width + 1)) + retainedWidth width control) = _
  unfold retainedWidth
  rw [total_width]
  cases control <;> simp only [controlWidth] <;> omega

private theorem bool_total : Function.Surjective BinaryLabelEncoding.bool.encode := by
  intro value
  fin_cases value
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

private theorem prod_total {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (leftTotal : Function.Surjective left.encode)
    (rightTotal : Function.Surjective right.encode) :
    Function.Surjective (BinaryLabelEncoding.prod left right).encode := by
  intro value
  obtain ⟨⟨leftValue, rightValue⟩, rfl⟩ :=
    (prodEquiv (m := left.width) (n := right.width)).surjective value
  obtain ⟨leftState, rfl⟩ := leftTotal leftValue
  obtain ⟨rightState, rfl⟩ := rightTotal rightValue
  exact ⟨(leftState, rightState), rfl⟩

private theorem raw_total (width : Nat) : Function.Surjective (encoding width).encode :=
  prod_total _ _ (prod_total _ _ (ProductPlacement.frame_total width) bool_total) bool_total

private theorem offset_total (width : Nat) (control : OffsetControl) :
    Function.Surjective (offsetEncoding width control).encode :=
  prod_total _ _ Function.surjective_id
    (prod_total _ _ (prod_total _ _ bool_total
      (prod_total _ _ Function.surjective_id bool_total)) Function.surjective_id)

private def controlWires (width : Nat) (control : OffsetControl) :
    Equiv.Perm (Fin (encoding width).width) :=
  match control with
  | .supplied => prefixWires _ (InPlaceControlled.frameWidth width + 1) (by
      change _ ≤ (InPlaceControlled.frameWidth width + 1) + 1
      omega)
  | .exceptional => (prefixWires _ (encoding width).width (by omega)).trans
      (prefixWires _ (encoding width).width (by omega))

/-- The arithmetic target is one of the two original caller data words. -/
inductive Coordinate where
  | x
  | y
  deriving DecidableEq

private def coordinateStart (width : Nat) : Coordinate → Nat
  | .x => width + 6
  | .y => 2 * width + 6 + ProductPlacement.tailWidth width

private def coordinateWires (width : Nat) (coordinate : Coordinate) :
    Equiv.Perm (Fin (encoding width).width) :=
  wordWires _ width (coordinateStart width coordinate)
    (by cases coordinate <;> simp only [coordinateStart] <;> omega)
    (by rw [total_width]; cases coordinate <;>
        simp only [coordinateStart, ProductPlacement.tailWidth] <;> omega)

private def arithmeticWires (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) :
    Fin (offsetEncoding width control).width ≃ Fin (encoding width).width :=
  (finCongr (offset_width width control)).trans
    ((controlWires width control).trans
      ((prefixWires _ (width + 1) (by rw [total_width]; omega)).trans
        (coordinateWires width coordinate)))

/-- Actual offset placement borrows two resident history bits and owns every control wire. -/
private def offsetPlacement (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) :
    EncodedBit.FullPlacement (offsetEncoding width control) (encoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (offset_total width control) (raw_total width)
    (arithmeticWires width control coordinate)

private theorem rawBit_wire (width : Nat) (index : Fin (finIdentity width).width) :
    (finIdentityBit width index).wire = index := rfl

private theorem boolBit_wire (index : Fin BinaryLabelEncoding.bool.width) :
    BinaryLabelEncoding.boolBit.wire = index := by
  change (0 : Fin 1) = index
  exact Subsingleton.elim _ _

private def gidneyBits (width : Nat) :
    Fin (MAU.Addition.Gidney.encoding width).width →
      EncodedBit (MAU.Addition.Gidney.encoding width) :=
  productBit (fun _ => boolBit) (productBit (finIdentityBit width) (fun _ => boolBit))

private theorem gidneyBits_wire (width : Nat)
    (index : Fin (MAU.Addition.Gidney.encoding width).width) :
    (gidneyBits width index).wire = index :=
  productBit_wire (left := BinaryLabelEncoding.bool)
    (right := prod (finIdentity width) BinaryLabelEncoding.bool) _ _
    boolBit_wire
    (productBit_wire (left := finIdentity width) (right := BinaryLabelEncoding.bool)
      _ _ (rawBit_wire width) boolBit_wire) index

private def arithmeticBits (width : Nat) (control : OffsetControl) :=
  productBit (left := MAU.Addition.Gidney.encoding width)
    (right := finIdentity (retainedWidth width control))
    (gidneyBits width) (finIdentityBit (retainedWidth width control))

private theorem arithmeticBits_wire (width : Nat) (control : OffsetControl)
    (index : Fin ((MAU.Addition.Gidney.encoding width).prod
      (finIdentity (retainedWidth width control))).width) :
    (arithmeticBits width control index).wire = index :=
  productBit_wire (left := MAU.Addition.Gidney.encoding width)
    (right := finIdentity (retainedWidth width control))
    _ _ (gidneyBits_wire width) (rawBit_wire (retainedWidth width control)) index

private theorem arithmetic_capacity (width : Nat) (control : OffsetControl) :
    4 ≤ (MAU.Addition.Gidney.encoding width).width + retainedWidth width control := by
  change 4 ≤ 1 + (width + 1) + retainedWidth width control
  unfold retainedWidth
  rw [total_width]
  cases control <;> simp only [controlWidth] <;> omega

private def arithmeticControlGates (width : Nat) (control : OffsetControl)
    (source : List (GateSpec (MAU.Addition.Gidney.encoding width))) :
    List (GateSpec (offsetEncoding width control)) :=
  prefixControlGates _ (arithmeticBits width control)
    (arithmeticBits_wire width control)
    (arithmetic_capacity width control) control
    (source.map (GateSpec.prodLeft (finIdentity (retainedWidth width control))))

/-- Expand the real source list, then retain its original complete physical placement. -/
def placedArithmeticGates (width : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (source : List (GateSpec (MAU.Addition.Gidney.encoding width))) :
    List (GateSpec (encoding width)) :=
  (arithmeticControlGates width control source).map
    (offsetPlacement width control coordinate).placeGate

/-- Physical arithmetic is compiled solely from actual native instructions. -/
def placedArithmetic (width : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (source : List (GateSpec (MAU.Addition.Gidney.encoding width))) : NativeCircuit width :=
  programList (QubitLayout.canonical _) .empty
    (placedArithmeticGates width control coordinate source)

/-- Placement preserves the exact expanded instruction order. -/
theorem placedArithmetic_trace (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (source : List (GateSpec (MAU.Addition.Gidney.encoding width))) :
    (placedArithmetic width control coordinate source).eventTrace =
      (arithmeticControlGates width control source).map (event .empty) :=
  FullPlacement.placeGates_eventTrace _ _ _ _

/-- All-label native action follows the complete grouping and restores all retained bits. -/
theorem pointPlacedArithmetic_gates_step (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (source : List (GateSpec (MAU.Addition.Gidney.encoding width)))
    (sourceStep : MAU.Addition.Gidney.Registers width → MAU.Addition.Gidney.Registers width)
    (runs : ∀ state, stepList source state = sourceStep state) (state : Raw width) :
    stepList (placedArithmeticGates width control coordinate source) state =
      (offsetPlacement width control coordinate).step
        (fun grouped => (grouped.1, if grouped.1 = activeValue control then
          (sourceStep grouped.2.1, grouped.2.2) else grouped.2)) state := by
  rw [placedArithmeticGates, FullPlacement.placeGates_step]
  unfold FullPlacement.step
  apply congrArg (offsetPlacement width control coordinate).grouping.symm
  rw [arithmeticControlGates, pointPrefixControlGates_step]
  simp only [stepList_prodLeft, runs]

/-- Exact phase and arbitrary dirty restoration use the original FullPlacement without a premise. -/
theorem pointPlacedArithmetic_realizes (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (source : List (GateSpec (MAU.Addition.Gidney.encoding width)))
    (sourceStep : MAU.Addition.Gidney.Registers width → MAU.Addition.Gidney.Registers width)
    (runs : ∀ state, stepList source state = sourceStep state) :
    UnitaryCircuit.Realizes (encoding width) (placedArithmetic width control coordinate source)
      ((offsetPlacement width control coordinate).step
        (fun grouped => (grouped.1, if grouped.1 = activeValue control then
          (sourceStep grouped.2.1, grouped.2.2) else grouped.2))) :=
  realizesList_congrStep _ _ _
    (pointPlacedArithmetic_gates_step width control coordinate source sourceStep runs)

private def fittedConstant (modulus : Nat) (constant : Fin (modulus + 1)) :
    Fin ((InPlaceArithmetic.modulusWord modulus).val + 1) :=
  ⟨constant.val, constant.isLt⟩

/-- The literal controlled modular-offset word on the original X or Y coordinates. -/
def offsetGates (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) : List (GateSpec (encoding modulus.size)) :=
  placedArithmeticGates modulus.size control coordinate
    (MAU.Addition.Gidney.modularOffsetGates modulus.size
      (InPlaceArithmetic.modulusWord modulus) (fittedConstant modulus constant))

/-- Add the fixed canonical residue under the original quantum controls. -/
def offset (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) : NativeCircuit modulus.size :=
  programList (QubitLayout.canonical _) .empty (offsetGates modulus control coordinate constant)

/-- The literal controlled pivot reflection on the original X word. -/
def reflectGates (modulus : Nat) : List (GateSpec (encoding modulus.size)) :=
  placedArithmeticGates modulus.size .supplied .x
    (MAU.Addition.Gidney.pivotGates modulus.size (InPlaceArithmetic.modulusWord modulus))

/-- The original X word receives the actual canonical pivot reflection. -/
def reflect (modulus : Nat) : NativeCircuit modulus.size :=
  programList (QubitLayout.canonical _) .empty (reflectGates modulus)

private def controlBit (width : Nat) : EncodedBit (encoding width) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodRightBit (ProductPlacement.frameEncoding width)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)

private def selectorBit (width : Nat) : EncodedBit (encoding width) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit

private theorem controls_separate (width : Nat) :
    (controlBit width).wire ≠ (selectorBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  change (ProductPlacement.frameEncoding width).width =
    (ProductPlacement.frameEncoding width).width + 1 at values
  omega

/-- A literal three-CNOT exchange of the two resident control coordinates. -/
def exchangeControlGates (width : Nat) : List (GateSpec (encoding width)) :=
  swapGates (controlBit width) (selectorBit width) (controls_separate width)

/-- The actual control exchange uses no new wire. -/
def exchangeControls (width : Nat) : NativeCircuit width :=
  programList (QubitLayout.canonical _) .empty (exchangeControlGates width)

private def frameWord (width : Nat)
    (word : EncodedBit.Word (ProductPlacement.frameEncoding width) width) :
    EncodedBit.Word (encoding width) width :=
  ⟨fun index => BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodLeftBit (ProductPlacement.frameEncoding width)
      BinaryLabelEncoding.bool (word.bit index))⟩

private theorem copy_separate (width : Nat) (index : Fin width) :
    ((frameWord width (FramePorts.numerator width)).bit index).wire ≠
      ((frameWord width (FramePorts.accumulator width)).bit index).wire := by
  intro same
  have values := congrArg Fin.val same
  change ((FramePorts.numerator width).bit index).wire.val =
    ((FramePorts.accumulator width).bit index).wire.val at values
  exact (FramePorts.accumulator_numerator_ne width index index).symm (Fin.ext values)

/-- XOR Y into the original A word; no clean premise is needed for the literal list. -/
def squareCopyGates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.xorIntoGates (frameWord width (FramePorts.numerator width))
    (frameWord width (FramePorts.accumulator width)) (copy_separate width)

/-- The same XOR word is used on both sides of the product adjoint. -/
def squareCopy (width : Nat) : NativeCircuit width :=
  programList (QubitLayout.canonical _) .empty (squareCopyGates width)

@[reducible] private def squareEncoding (width : Nat) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity 1)
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)

private theorem square_width (width : Nat) :
    (squareEncoding width).width = (encoding width).width := by
  change 1 + ((ProductPlacement.frameEncoding width).width + 1) =
    ((ProductPlacement.frameEncoding width).width + 1) + 1
  omega

private def squarePlacement (width : Nat) :
    EncodedBit.FullPlacement (squareEncoding width) (encoding width) :=
  EncodedBit.FullPlacement.ofWires _ _
    (prod_total _ _ Function.surjective_id
      (prod_total _ _ (ProductPlacement.frame_total width) bool_total))
    (raw_total width)
    ((finCongr (square_width width)).trans
      ((controlWires width .supplied).trans
        ((coordinateWires width .x).trans (coordinateWires width .y))))

private theorem square_capacity (width : Nat) :
    4 ≤ (NativeFrameControl.encoding width).width := by
  change 4 ≤ (ProductPlacement.frameEncoding width).width + 1
  rw [ProductPlacement.frame_width]
  unfold ProductWires.width ProductPlacement.tailWidth
  omega

/-- Control the literal reversed product word at the original full square placement. -/
def squareSubtractGates (modulus : Nat) : List (GateSpec (encoding modulus.size)) :=
  (prefixControlGates _ (NativeFrameControl.bits modulus.size)
    (NativeFrameControl.nativeFrameControl_bits_wire modulus.size)
    (square_capacity modulus.size) .supplied
    ((NativeProductFrame.gates modulus.size (InPlaceArithmetic.modulusWord modulus)).reverse.map
      (GateSpec.prodLeft BinaryLabelEncoding.bool))).map
        (squarePlacement modulus.size).placeGate

/-- The actual product adjoint subtracts Y*A into X while C is true. -/
def squareSubtract (modulus : Nat) : NativeCircuit modulus.size :=
  programList (QubitLayout.canonical _) .empty (squareSubtractGates modulus)

/-- The copied word is uncomputed after the actual controlled product adjoint. -/
def subtractSquareGates (modulus : Nat) : List (GateSpec (encoding modulus.size)) :=
  squareCopyGates modulus.size ++ squareSubtractGates modulus ++ squareCopyGates modulus.size

/-- Literal XOR, controlled inverse multiplication, and XOR execute on the same frame. -/
def subtractSquare (modulus : Nat) : NativeCircuit modulus.size :=
  programList (QubitLayout.canonical _) .empty (subtractSquareGates modulus)

private def comparisonPlacement (width : Nat) :
    EncodedBit.FullPlacement (offsetEncoding width .supplied) (encoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (offset_total width .supplied) (raw_total width)
    ((arithmeticWires width .supplied .x).trans
      (Equiv.swap ⟨width, by rw [total_width]; omega⟩
        (selectorBit width).wire))

private def compareZeroGates (width : Nat) : List (GateSpec (encoding width)) :=
  (arithmeticControlGates width .supplied
    (MAU.Addition.Gidney.comparisonGates width
      ⟨1, by have := Nat.two_pow_pos width; omega⟩)).map (comparisonPlacement width).placeGate

private def compareZero (width : Nat) : NativeCircuit width :=
  programList (QubitLayout.canonical _) .empty (compareZeroGates width)

/-- N receives C xor (C and X=0), using the actual comparison target and resident helper. -/
def selectNormalGates (width : Nat) : List (GateSpec (encoding width)) :=
  [.cnot (controlBit width) (selectorBit width) (controls_separate width)] ++ compareZeroGates width

/-- The selector executes the concrete CNOT and controlled comparison lists. -/
def selectNormal (width : Nat) : NativeCircuit width :=
  programList (QubitLayout.canonical _) .empty (selectNormalGates width)

private def constantWord {p : Nat} [Fact p.Prime] (value : ZMod p) : Fin (p + 1) :=
  ⟨value.val, (ZMod.val_lt value).trans (Nat.lt_succ_self p)⟩

/-- Actual controlled coordinate differences prepare the first measured division. -/
def beforeDivisionGates {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : List (GateSpec (encoding p.size)) :=
  offsetGates p .supplied .x (constantWord (-Q.x)) ++
    offsetGates p .supplied .y (constantWord (-Q.y))

def beforeDivision {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : NativeCircuit p.size :=
  programList (QubitLayout.canonical _) .empty (beforeDivisionGates Q)

/-- Form D, compute its internally reachable selector, and exchange the resident controls. -/
def beforeMultiplicationGates {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : List (GateSpec (encoding p.size)) :=
  offsetGates p .supplied .x (constantWord (3 * Q.x)) ++ subtractSquareGates p ++
    selectNormalGates p.size ++ exchangeControlGates p.size

def beforeMultiplication {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : NativeCircuit p.size :=
  programList (QubitLayout.canonical _) .empty (beforeMultiplicationGates Q)

/-- Restore C, clean the exceptional slope, reverse N's list, and return both coordinates. -/
def afterMultiplicationGates {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : List (GateSpec (encoding p.size)) :=
  exchangeControlGates p.size ++
    offsetGates p .exceptional .y (constantWord (-exceptionalSlope E Q)) ++
      (selectNormalGates p.size).reverse ++ reflectGates p ++
        offsetGates p .supplied .x (constantWord (Q.x + 1)) ++
          offsetGates p .supplied .y (constantWord (-Q.y))

def afterMultiplication {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : NativeCircuit p.size :=
  programList (QubitLayout.canonical _) .empty (afterMultiplicationGates E Q)

/-- The complete pre-division trace is the literal controlled native word. -/
theorem beforeDivision_trace {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) :
    (beforeDivision Q).eventTrace = (beforeDivisionGates Q).map (event .empty) :=
  programList_eventTrace _ _ _

/-- The complete middle trace includes both physical C/N exchange and selector computation. -/
theorem beforeMultiplication_trace {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) :
    (beforeMultiplication Q).eventTrace = (beforeMultiplicationGates Q).map (event .empty) :=
  programList_eventTrace _ _ _

/-- Cleanup preserves the exact reversed selector instruction order. -/
theorem afterMultiplication_trace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) :
    (afterMultiplication E Q).eventTrace = (afterMultiplicationGates E Q).map (event .empty) :=
  programList_eventTrace _ _ _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
