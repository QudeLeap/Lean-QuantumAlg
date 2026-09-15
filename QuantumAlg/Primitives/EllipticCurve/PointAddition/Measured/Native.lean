/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Layout
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.Control
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

open MeasuredUncompute MAU.Inversion

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

/-- The only controlled offset sectors used by the concrete point-addition schedule. -/
inductive OffsetControl where
  | supplied
  | exceptional
  deriving DecidableEq

@[reducible] private def controlWidth : OffsetControl → Nat
  | .supplied => 1
  | .exceptional => 2

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

private def prefixControl {bodyWidth : Nat} (count : Nat) (active : Fin (2 ^ count))
    (body : UnitaryCircuit (Qubits bodyWidth)) :
    UnitaryCircuit (Qubits (count + bodyWidth)) :=
  UnitaryCircuit.reindex prodEquiv
    (UnitaryCircuit.controlAt (Qubits count) (List.range count)
      (UnitaryCircuit.shiftPhysicalIdx count body)
      { left_nodup := List.nodup_range
        right_nodup := (UnitaryCircuit.shiftPhysicalIdx count body).physical_idx_nodup
        disjoint := by
          apply List.disjoint_left.mpr
          intro wire leading shifted
          have bound := List.mem_range.mp leading
          obtain ⟨original, _, same⟩ := List.mem_map.mp shifted
          omega }
      active)

private theorem prefixControl_within {bodyWidth : Nat} (count : Nat)
    (active : Fin (2 ^ count)) (body : UnitaryCircuit (Qubits bodyWidth))
    (within : body.physical_idx ⊆ List.range bodyWidth) :
    (prefixControl count active body).physical_idx ⊆ List.range (count + bodyWidth) := by
  intro wire present
  change wire ∈ List.range count ++ (UnitaryCircuit.shiftPhysicalIdx count body).physical_idx
    at present
  rcases List.mem_append.mp present with leading | shifted
  · exact List.mem_range.mpr (by have bound := List.mem_range.mp leading; omega)
  · exact UnitaryCircuit.shiftPhysicalIdx_physical_idx_subset_range count body within shifted

private def activeValue : (control : OffsetControl) → Fin (2 ^ controlWidth control)
  | .supplied => 1
  | .exceptional => 2

/-- Place an actual Gidney member under C, or jointly under C=true and N=false. -/
def placedArithmetic (width : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (body : UnitaryCircuit (Qubits (MAU.Addition.Gidney.encoding width).width))
    (within : body.physical_idx ⊆ List.range (MAU.Addition.Gidney.encoding width).width) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (offsetPlacement width control coordinate).place
    (prefixControl (controlWidth control) (activeValue control)
      (UnitaryCircuit.prodLeft (n := retainedWidth width control) body))
    (prefixControl_within _ _ _ (UnitaryCircuit.prodLeft_physical_idx_subset_range body within))

theorem placedArithmetic_physical (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate)
    (body : UnitaryCircuit (Qubits (MAU.Addition.Gidney.encoding width).width))
    (within : body.physical_idx ⊆ List.range (MAU.Addition.Gidney.encoding width).width) :
    (placedArithmetic width control coordinate body within).physical_idx =
      List.range (encoding width).width :=
  EncodedBit.FullPlacement.place_physical _ _ _

/-- Every controlled event is derived from the actual supplied native member. -/
theorem placedArithmetic_trace (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate)
    (body : UnitaryCircuit (Qubits (MAU.Addition.Gidney.encoding width).width))
    (within : body.physical_idx ⊆ List.range (MAU.Addition.Gidney.encoding width).width) :
    (placedArithmetic width control coordinate body within).eventTrace =
      body.eventTrace.map (fun event => event.controlForDimension (2 ^ controlWidth control)) := by
  rw [placedArithmetic, EncodedBit.FullPlacement.place_eventTrace]
  simp only [prefixControl, UnitaryCircuit.reindex_eventTrace,
    UnitaryCircuit.controlAt_eventTrace, UnitaryCircuit.shiftPhysicalIdx_eventTrace,
    UnitaryCircuit.prodLeft_eventTrace, Fintype.card_fin]

private def fittedConstant (modulus : Nat) (constant : Fin (modulus + 1)) :
    Fin ((InPlaceArithmetic.modulusWord modulus).val + 1) :=
  ⟨constant.val, constant.isLt⟩

/-- Add the fixed canonical residue on the original X or Y under its actual quantum controls. -/
def offset (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) : UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  placedArithmetic modulus.size control coordinate
    (MAU.Addition.Gidney.modularOffsetProgram modulus.size
      (InPlaceArithmetic.modulusWord modulus) (fittedConstant modulus constant))
    (by rw [MAU.Addition.Gidney.gidneyModularOffset_physical]
        change List.range (modulus.size + 2) ⊆ List.range (1 + (modulus.size + 1))
        have same : modulus.size + 2 = 1 + (modulus.size + 1) := by omega
        rw [same]
        exact List.Subset.refl _)

/-- The original X word receives the actual canonical pivot reflection. -/
def reflect (modulus : Nat) : UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  placedArithmetic modulus.size .supplied .x
    (MAU.Addition.Gidney.pivotProgram modulus.size (InPlaceArithmetic.modulusWord modulus))
    (by rw [MAU.Addition.Gidney.gidneyPivot_physical]
        change List.range (modulus.size + 2) ⊆ List.range (1 + (modulus.size + 1))
        have same : modulus.size + 2 = 1 + (modulus.size + 1) := by omega
        rw [same]
        exact List.Subset.refl _)

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

/-- A literal three-CNOT exchange moves N to the frozen measured body's real control address. -/
def exchangeControls (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  EncodedBit.swapProgram (controlBit width) (selectorBit width) (controls_separate width)

theorem exchangeControls_within (width : Nat) :
    (exchangeControls width).physical_idx ⊆ List.range (encoding width).width :=
  EncodedBit.swapProgram_physical_idx_subset_range _ _ _

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

/-- The existing clean A temporarily copies Y using exactly n actual CNOTs. -/
def squareCopy (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  EncodedBit.Word.xorIntoProgram (frameWord width (FramePorts.numerator width))
    (frameWord width (FramePorts.accumulator width)) (copy_separate width)

theorem squareCopy_within (width : Nat) :
    (squareCopy width).physical_idx ⊆ List.range (encoding width).width :=
  EncodedBit.Word.xorIntoProgram_physical_idx_subset_range _ _ _

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

/-- The same actual VariableGidney adjoint subtracts Y*A into X while C is true. -/
def squareSubtract (modulus : Nat) :
    UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  (squarePlacement modulus.size).place
    (prefixControl 1 1 (UnitaryCircuit.prodLeft (n := 1)
      (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)).dagger))
    (prefixControl_within _ _ _ (UnitaryCircuit.prodLeft_physical_idx_subset_range _
      (by rw [UnitaryCircuit.dagger_physical_idx,
          NativeProductFrame.program, EncodedBit.FullPlacement.place_physical]
          exact List.Subset.refl _)))

theorem squareSubtract_physical (modulus : Nat) :
    (squareSubtract modulus).physical_idx = List.range (encoding modulus.size).width :=
  EncodedBit.FullPlacement.place_physical _ _ _

/-- The copied word is uncomputed after the actual controlled product adjoint. -/
def subtractSquare (modulus : Nat) : UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  (squareCopy modulus.size).seq ((squareSubtract modulus).seq (squareCopy modulus.size))

private def comparisonPlacement (width : Nat) :
    EncodedBit.FullPlacement (offsetEncoding width .supplied) (encoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (offset_total width .supplied) (raw_total width)
    ((arithmeticWires width .supplied .x).trans
      (Equiv.swap ⟨width, by rw [total_width]; omega⟩
        (selectorBit width).wire))

private def compareZero (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (comparisonPlacement width).place
    (prefixControl 1 1 (UnitaryCircuit.prodLeft (n := retainedWidth width .supplied)
      (MAU.Addition.Gidney.comparisonProgram width ⟨1, by have := Nat.two_pow_pos width; omega⟩)))
    (prefixControl_within _ _ _ (UnitaryCircuit.prodLeft_physical_idx_subset_range _
      (by rw [MAU.Addition.Gidney.gidneyComparison_physical]
          change List.range (width + 2) ⊆ List.range (1 + (width + 1))
          have same : width + 2 = 1 + (width + 1) := by omega
          rw [same]
          exact List.Subset.refl _)))

/-- N receives C xor (C and X=0), using its actual comparison target and a resident helper. -/
def selectNormal (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (EncodedBit.GateSpec.cnot (controlBit width) (selectorBit width)
    (controls_separate width)).program |>.seq (compareZero width)

theorem selectNormal_within (width : Nat) :
    (selectNormal width).physical_idx ⊆ List.range (encoding width).width := by
  apply UnitaryCircuit.seq_physical_idx_subset
  · exact EncodedBit.GateSpec.program_physical_idx_subset_range _
  · rw [compareZero, EncodedBit.FullPlacement.place_physical]
    exact List.Subset.refl _

private theorem offset_within (modulus : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (constant : Fin (modulus + 1)) :
    (offset modulus control coordinate constant).physical_idx ⊆
      List.range (encoding modulus.size).width := by
  rw [offset, placedArithmetic_physical]
  exact List.Subset.refl _

private theorem reflect_within (modulus : Nat) :
    (reflect modulus).physical_idx ⊆ List.range (encoding modulus.size).width := by
  rw [reflect, placedArithmetic_physical]
  exact List.Subset.refl _

private theorem subtractSquare_within (modulus : Nat) :
    (subtractSquare modulus).physical_idx ⊆ List.range (encoding modulus.size).width := by
  apply UnitaryCircuit.seq_physical_idx_subset _ _ (squareCopy_within _)
  apply UnitaryCircuit.seq_physical_idx_subset
  · rw [squareSubtract_physical]
    exact List.Subset.refl _
  · exact squareCopy_within _

private def constantWord {p : Nat} [Fact p.Prime] (value : ZMod p) : Fin (p + 1) :=
  ⟨value.val, (ZMod.val_lt value).trans (Nat.lt_succ_self p)⟩

/-- Actual controlled coordinate differences prepare the first measured division. -/
def beforeDivision {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : UnitaryCircuit (Qubits (encoding p.size).width) :=
  (offset p .supplied .x (constantWord (-Q.x))).seq
    (offset p .supplied .y (constantWord (-Q.y)))

theorem beforeDivision_within {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : (beforeDivision Q).physical_idx ⊆ List.range (encoding p.size).width :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (offset_within _ _ _ _) (offset_within _ _ _ _)

/-- Form D, compute its internally reachable selector, and execute the real C/N exchange. -/
def beforeMultiplication {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : UnitaryCircuit (Qubits (encoding p.size).width) :=
  (offset p .supplied .x (constantWord (3 * Q.x))).seq
    ((subtractSquare p).seq ((selectNormal p.size).seq (exchangeControls p.size)))

theorem beforeMultiplication_within {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) :
    (beforeMultiplication Q).physical_idx ⊆ List.range (encoding p.size).width :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (offset_within _ _ _ _)
    (UnitaryCircuit.seq_physical_idx_subset _ _ (subtractSquare_within _)
      (UnitaryCircuit.seq_physical_idx_subset _ _ (selectNormal_within _)
        (exchangeControls_within _)))

/-- Restore C, clean the exceptional slope, uncompute N, and return the two affine coordinates. -/
def afterMultiplication {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : UnitaryCircuit (Qubits (encoding p.size).width) :=
  (exchangeControls p.size).seq
    ((offset p .exceptional .y (constantWord (-exceptionalSlope E Q))).seq
      ((selectNormal p.size).dagger.seq ((reflect p).seq
        ((offset p .supplied .x (constantWord (Q.x + 1))).seq
          (offset p .supplied .y (constantWord (-Q.y)))))))

theorem afterMultiplication_within {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) :
    (afterMultiplication E Q).physical_idx ⊆ List.range (encoding p.size).width :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (exchangeControls_within _)
    (UnitaryCircuit.seq_physical_idx_subset _ _ (offset_within _ _ _ _)
      (UnitaryCircuit.seq_physical_idx_subset _ _
        (UnitaryCircuit.dagger_physical_idx_subset _ (selectNormal_within _))
        (UnitaryCircuit.seq_physical_idx_subset _ _ (reflect_within _)
          (UnitaryCircuit.seq_physical_idx_subset _ _ (offset_within _ _ _ _)
            (offset_within _ _ _ _)))))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
