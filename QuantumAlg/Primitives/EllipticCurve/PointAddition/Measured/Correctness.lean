/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Embedding.Framing
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Domain
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Correctness
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Mathematics
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Equiv
import all QuantumAlg.Core.Execution.Context.Embedding.Sequence
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log

/-!
# Complete affine domain of the measured point-addition body

A zero second multiplier is the original reachable finite exceptional result
-Q. The original input is then 2(-Q), so its slope is a fixed classical value
that can be cleared without a division by zero. This project construction
preserves the original active generic boundary of the measured field interfaces
[LYL+26, sec_point_add/sec_point_add.tex:24-36,119-123].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution ContextUnion MeasuredUncompute
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original prime characteristic above three gives the measured canonical word width. -/
lemma canonical_width {p : Nat} (prime : Nat.Prime p) (characteristic : 3 < p) :
    p.size = Nat.clog 2 p := by
  have bound := Nat.le_pow_clog (by decide : 1 < 2) p
  have different : p ≠ 2 ^ Nat.clog 2 p := by
    intro same
    have dividesPower : p ∣ 2 ^ Nat.clog 2 p := same ▸ dvd_refl p
    have divides := prime.dvd_of_dvd_pow dividesPower
    have small := Nat.le_of_dvd (by decide : 0 < 2) divides
    omega
  apply le_antisymm
  · exact Nat.size_le.mpr (by omega)
  · exact Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_size_self p))

private lemma nativeList_step {width : Nat}
    (gates : List (EncodedBit.GateSpec (encoding width))) (action : Raw width → Raw width)
    (realized : UnitaryCircuit.Realizes (encoding width)
      (EncodedBit.GateSpec.programList (nativeLayout width) .empty gates) environment.quantum
        action)
    (state : Raw width) : EncodedBit.GateSpec.stepList gates state = action state := by
  have literal := EncodedBit.GateSpec.realizesList (environment := environment.quantum)
    (nativeLayout width) .empty gates
  have actual := literal.apply_encoded_ket state
  exact (encoding width).encode_injective ((nativeLayout width).basisEquiv.symm.injective
    (NormalizedVector.ket_injective (actual.symm.trans (realized.apply_encoded_ket state))))

private lemma nativeList_append_realizes {width : Nat}
    (first second : List (EncodedBit.GateSpec (encoding width)))
    (firstStep secondStep : Raw width → Raw width)
    (left : UnitaryCircuit.Realizes (encoding width)
      (EncodedBit.GateSpec.programList (nativeLayout width) .empty first) environment.quantum
        firstStep)
    (right : UnitaryCircuit.Realizes (encoding width)
      (EncodedBit.GateSpec.programList (nativeLayout width) .empty second) environment.quantum
        secondStep) :
    UnitaryCircuit.Realizes (encoding width)
      (EncodedBit.GateSpec.programList (nativeLayout width) .empty (first ++ second))
        environment.quantum
      (secondStep ∘ firstStep) := by
  apply EncodedBit.GateSpec.realizesList_congrStep (environment := environment.quantum)
  intro state
  rw [EncodedBit.GateSpec.stepList_append,
    nativeList_step first firstStep left, nativeList_step second secondStep right]
  rfl

private lemma nativeRealizes_ket {width : Nat}
    (program : NativeCircuit width) (action : Raw width → Raw width)
    (realized : UnitaryCircuit.Realizes (encoding width) program environment.quantum action)
      (state : Raw width) :
    (program.binaryMatrix environment.quantum).apply (NormalizedVector.ket ((encoding
      width).encode state)) =
      NormalizedVector.ket ((encoding width).encode (action state)) :=
  UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
    program _ _ (realized.apply_encoded_ket state)

private lemma nativeList_matrix_append {width : Nat}
    (first second : List (EncodedBit.GateSpec (encoding width))) :
    ((EncodedBit.GateSpec.programList (nativeLayout width) .empty (first ++ second)).matrix
      environment.quantum) =
      ((EncodedBit.GateSpec.programList (nativeLayout width) .empty second).matrix
        environment.quantum) *
        ((EncodedBit.GateSpec.programList (nativeLayout width) .empty first).matrix
          environment.quantum) := by
  induction first with
  | nil => simp only [List.nil_append, EncodedBit.GateSpec.programList,
      UnitaryCircuit.identity_matrix, mul_one]
  | cons gate rest ih =>
      simp only [List.cons_append, EncodedBit.GateSpec.programList, UnitaryCircuit.seq_matrix]
      rw [ih, mul_assoc]

private lemma nativeList_binary_append {width : Nat}
    (first second : List (EncodedBit.GateSpec (encoding width))) :
    ((EncodedBit.GateSpec.programList (nativeLayout width) .empty (first ++ second)).binaryMatrix
      environment.quantum) =
      ((EncodedBit.GateSpec.programList (nativeLayout width) .empty second).binaryMatrix
        environment.quantum) *
        ((EncodedBit.GateSpec.programList (nativeLayout width) .empty first).binaryMatrix
          environment.quantum) := by
  unfold UnitaryCircuit.binaryMatrix
  erw [nativeList_matrix_append, UnitaryOperator.unitaryOperator_reindex_mul]
  rfl

private lemma binary_apply_mul {R : Register} (first second : UnitaryOperator R)
    (state : NormalizedVector R) :
    (second * first).apply state = second.apply (first.apply state) := by
  apply NormalizedVector.ext
  intro row
  exact congrArg (fun vector => vector row) (UnitaryOperator.mul_applyVec second first state.vec)

/-- The actual controlled list retains the complete source step and every borrowed coordinate. -/
private lemma placedArithmetic_realizes (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate)
    (source : List (EncodedBit.GateSpec (MAU.Addition.Gidney.encoding width)))
    (step : MAU.Addition.Gidney.Registers width → MAU.Addition.Gidney.Registers width)
    (runs : ∀ state, EncodedBit.GateSpec.stepList source state = step state) :
    UnitaryCircuit.Realizes (encoding width)
      (placedArithmetic width control coordinate source) environment.quantum
      ((offsetPlacement width control coordinate).step
        (fun state => (state.1, if state.1 = activeValue control then
          (step state.2.1, state.2.2) else state.2))) :=
  pointPlacedArithmetic_realizes width control coordinate source step runs

private lemma frame_count (width : Nat) :
    InPlaceControlled.frameWidth width = 3 * width + 4 * width.size + 11 := by
  change (ProductPlacement.frameEncoding width).width = _
  rw [ProductPlacement.frame_width]
  unfold ProductWires.width ProductPlacement.tailWidth
  omega

private lemma arithmetic_address (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (index : Fin (offsetEncoding width control).width) :
    (arithmeticWires width control coordinate index).val =
      wordAddress width (coordinateStart width coordinate)
        (prefixAddress (width + 1) (match control with
          | .supplied => prefixAddress (InPlaceControlled.frameWidth width + 1) index.val
          | .exceptional => prefixAddress (encoding width).width
              (prefixAddress (encoding width).width index.val))) := by
  cases control <;> rfl

private def sourceWordPosition (width : Nat) (control : OffsetControl) (index : Fin width) :
    Fin (offsetEncoding width control).width :=
  ⟨controlWidth control + 1 + index.val, by
    rw [offset_width, total_width]
    have bound := index.isLt
    cases control <;> simp only [controlWidth] <;> omega⟩

/-- A positive source position advances to its preceding physical prefix position. -/
private lemma prefix_positive (count index : Nat) (positive : 0 < index)
    (within : index < count) :
    prefixAddress count index = index - 1 := by
  rw [prefixAddress, if_pos within, if_neg (Nat.ne_of_gt positive)]

/-- Every placed Gidney word bit has precisely the original selected X or Y wire address. -/
private lemma arithmetic_word_address (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (index : Fin width) :
    (arithmeticWires width control coordinate (sourceWordPosition width control index)).val =
      coordinateStart width coordinate + index.val := by
  rw [arithmetic_address]
  have bound := index.isLt
  cases control
  · change wordAddress width (coordinateStart width coordinate)
      (prefixAddress (width + 1)
        (prefixAddress (InPlaceControlled.frameWidth width + 1) (1 + 1 + index.val))) = _
    rw [prefix_positive (InPlaceControlled.frameWidth width + 1) (1 + 1 + index.val)
      (by omega) (by rw [frame_count]; omega)]
    rw [prefix_positive (width + 1) (1 + 1 + index.val - 1) (by omega) (by omega)]
    have same : 1 + 1 + index.val - 1 - 1 = index.val := by omega
    rw [same, wordAddress, if_pos bound]
  · change wordAddress width (coordinateStart width coordinate)
      (prefixAddress (width + 1) (prefixAddress (encoding width).width
        (prefixAddress (encoding width).width (2 + 1 + index.val)))) = _
    rw [prefix_positive (encoding width).width (2 + 1 + index.val)
      (by omega) (by rw [total_width]; omega)]
    rw [prefix_positive (encoding width).width (2 + 1 + index.val - 1)
      (by omega) (by rw [total_width]; omega)]
    rw [prefix_positive (width + 1) (2 + 1 + index.val - 1 - 1) (by omega) (by omega)]
    have same : 2 + 1 + index.val - 1 - 1 - 1 = index.val := by omega
    rw [same, wordAddress, if_pos bound]

private def coordinateWord (width : Nat) : Coordinate → EncodedBit.Word (encoding width) width
  | .x => frameWord width (FramePorts.input width)
  | .y => frameWord width (FramePorts.numerator width)

private def coordinateValue (width : Nat) (coordinate : Coordinate) (state : Raw width) :
    Fin (2 ^ width) :=
  match coordinate with
  | .x => ProductReadout.input width state.1.1
  | .y => ProductReadout.numerator width state.1.1

private def sourceWordBit (width : Nat) (control : OffsetControl) (index : Fin width) :
    EncodedBit (offsetEncoding width control) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity (controlWidth control))
    (BinaryLabelEncoding.prod (MAU.Addition.Gidney.encoding width)
      (BinaryLabelEncoding.finIdentity (retainedWidth width control)))
    (BinaryLabelEncoding.prodLeftBit (MAU.Addition.Gidney.encoding width)
      (BinaryLabelEncoding.finIdentity (retainedWidth width control))
      (MAU.Addition.Gidney.wordBit width index.rev))

private lemma source_word_wire (width : Nat) (control : OffsetControl) (index : Fin width) :
    (sourceWordBit width control index).wire = sourceWordPosition width control index := by
  apply Fin.ext
  change controlWidth control + (1 + (width - 1 - index.rev.val)) =
    controlWidth control + 1 + index.val
  rw [Fin.val_rev]
  have bound := index.isLt
  omega

private lemma coordinate_wire (width : Nat) (coordinate : Coordinate) (index : Fin width) :
    ((coordinateWord width coordinate).bit index).wire.val =
      coordinateStart width coordinate + index.val := by
  cases coordinate
  · exact FramePorts.input_wire width index
  · exact FramePorts.numerator_wire width index

private lemma coordinate_read (width : Nat) (coordinate : Coordinate) (index : Fin width)
    (state : Raw width) :
    ((coordinateWord width coordinate).bit index).get state =
      (coordinateValue width coordinate state).val.testBit index.rev.val := by
  cases coordinate
  · exact (ProductReadout.readWord_bit (FramePorts.input width) state.1.1 index).symm
  · exact (ProductReadout.readWord_bit (FramePorts.numerator width) state.1.1 index).symm

private lemma wirePlacement_read {Source Target : Type}
    (source : BinaryLabelEncoding Source) (target : BinaryLabelEncoding Target)
    (sourceTotal : Function.Surjective source.encode)
    (targetTotal : Function.Surjective target.encode)
    (wires : Fin source.width ≃ Fin target.width) (sourceBit : EncodedBit source)
    (targetBit : EncodedBit target) (same : wires sourceBit.wire = targetBit.wire)
    (state : Target) :
    sourceBit.get ((EncodedBit.FullPlacement.ofWires source target sourceTotal targetTotal
      wires).grouping state) = targetBit.get state := by
  rw [ProductReadout.bit_read, ProductReadout.bit_read]
  have bits := EncodedBit.FullPlacement.wireBasis_bit source target wires
    (source.encode ((EncodedBit.FullPlacement.ofWires source target sourceTotal targetTotal
      wires).grouping state)) sourceBit.wire
  have encoded := (EncodedBit.FullPlacement.ofWires source target sourceTotal targetTotal
    wires).basis_encode state
  change EncodedBit.FullPlacement.wireBasis source target wires
    (source.encode ((EncodedBit.FullPlacement.ofWires source target sourceTotal targetTotal
      wires).grouping state)) = target.encode state at encoded
  rw [encoded, same] at bits
  exact bits.symm

/-- The actual arithmetic grouping reads the original full target word on every complete frame. -/
private lemma grouping_coordinate (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (state : Raw width) :
    ((offsetPlacement width control coordinate).grouping state).2.1.2.1 =
      coordinateValue width coordinate state := by
  apply ProductReadout.word_ext
  intro index
  have wires : arithmeticWires width control coordinate (sourceWordBit width control index).wire =
      ((coordinateWord width coordinate).bit index).wire := by
    apply Fin.ext
    rw [source_word_wire, arithmetic_word_address, coordinate_wire]
  have actual := wirePlacement_read (offsetEncoding width control) (encoding width)
    (offset_total width control) (raw_total width) (arithmeticWires width control coordinate)
    (sourceWordBit width control index) ((coordinateWord width coordinate).bit index) wires state
  change (MAU.Addition.Gidney.wordBit width index.rev).get
    ((offsetPlacement width control coordinate).grouping state).2.1 = _ at actual
  rw [MAU.Addition.Gidney.gidneyWordBit_get, coordinate_read] at actual
  exact actual

private lemma prefix_zero (count : Nat) (positive : 0 < count) :
    prefixAddress count 0 = count - 1 := by
  rw [prefixAddress, if_pos positive, if_pos rfl]

private lemma prefix_outside (count index : Nat) (outside : count ≤ index) :
    prefixAddress count index = index := if_neg (Nat.not_lt.mpr outside)

private lemma word_outside (width start index : Nat) (afterPrefix : width ≤ index)
    (afterWord : start + width ≤ index) : wordAddress width start index = index := by
  rw [wordAddress, if_neg (Nat.not_lt.mpr afterPrefix), if_neg (by omega)]

private lemma coordinate_end (width : Nat) (coordinate : Coordinate) :
    coordinateStart width coordinate + width ≤ InPlaceControlled.frameWidth width := by
  rw [frame_count]
  cases coordinate <;> simp only [coordinateStart, ProductPlacement.tailWidth] <;> omega

/-- The source's first leading control is exactly the real supplied control address. -/
private lemma arithmetic_control_address (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (index : Fin (offsetEncoding width control).width)
    (zero : index.val = 0) :
    (arithmeticWires width control coordinate index).val = InPlaceControlled.controlWire width := by
  rw [arithmetic_address]
  have frameBound : width + 1 ≤ InPlaceControlled.frameWidth width := by rw [frame_count]; omega
  have ending := coordinate_end width coordinate
  cases control
  · change wordAddress width (coordinateStart width coordinate)
      (prefixAddress (width + 1)
        (prefixAddress (InPlaceControlled.frameWidth width + 1) index.val)) = _
    rw [zero]
    rw [prefix_zero _ (by omega), Nat.add_sub_cancel,
      prefix_outside _ _ frameBound, word_outside _ _ _ (by omega) ending]
    rfl
  · change wordAddress width (coordinateStart width coordinate)
      (prefixAddress (width + 1) (prefixAddress (encoding width).width
        (prefixAddress (encoding width).width index.val))) = _
    rw [zero]
    have whole : (encoding width).width = InPlaceControlled.frameWidth width + 2 := by
      change (InPlaceControlled.frameWidth width + 1) + 1 = _
      omega
    rw [prefix_zero _ (by rw [whole]; omega)]
    rw [prefix_positive (encoding width).width ((encoding width).width - 1)
      (by rw [whole]; omega) (by rw [whole]; omega)]
    have same : (encoding width).width - 1 - 1 = InPlaceControlled.frameWidth width := by omega
    rw [same, prefix_outside _ _ frameBound, word_outside _ _ _ (by omega) ending]
    rfl

/-- The second leading control in the exceptional offset is exactly the owned selector address. -/
private lemma arithmetic_selector_address (width : Nat) (coordinate : Coordinate)
    (index : Fin (offsetEncoding width .exceptional).width) (one : index.val = 1) :
    (arithmeticWires width .exceptional coordinate index).val = selectorWire width := by
  rw [arithmetic_address]
  change wordAddress width (coordinateStart width coordinate)
    (prefixAddress (width + 1) (prefixAddress (encoding width).width
      (prefixAddress (encoding width).width index.val))) = _
  rw [one]
  have whole : (encoding width).width = InPlaceControlled.frameWidth width + 2 := by
    change (InPlaceControlled.frameWidth width + 1) + 1 = _
    omega
  have frameBound : width + 1 ≤ InPlaceControlled.frameWidth width := by rw [frame_count]; omega
  have ending := coordinate_end width coordinate
  rw [prefix_positive (encoding width).width 1 (by omega) (by rw [whole]; omega)]
  change wordAddress width (coordinateStart width coordinate)
    (prefixAddress (width + 1) (prefixAddress (encoding width).width 0)) = _
  rw [prefix_zero _ (by rw [whole]; omega)]
  rw [prefix_outside _ _ (by omega), word_outside _ _ _ (by omega) (by omega)]
  unfold selectorWire
  omega

private def sourceControlBit (width : Nat) (control : OffsetControl)
    (index : Fin (controlWidth control)) : EncodedBit (offsetEncoding width control) :=
  BinaryLabelEncoding.prodLeftBit (BinaryLabelEncoding.finIdentity (controlWidth control))
    (BinaryLabelEncoding.prod (MAU.Addition.Gidney.encoding width)
      (BinaryLabelEncoding.finIdentity (retainedWidth width control)))
    (BinaryLabelEncoding.finIdentityBit (controlWidth control) index)

private lemma grouping_suppliedControl (width : Nat) (coordinate : Coordinate)
    (state : Raw width) :
    ((offsetPlacement width .supplied coordinate).grouping state).1 =
      BinaryLabelEncoding.bool.encode state.1.2 := by
  have wires : arithmeticWires width .supplied coordinate
      (sourceControlBit width .supplied 0).wire =
      (controlBit width).wire := by
    apply Fin.ext
    exact arithmetic_control_address width .supplied coordinate _ rfl
  have actual := wirePlacement_read (offsetEncoding width .supplied) (encoding width)
    (offset_total width .supplied) (raw_total width) (arithmeticWires width .supplied coordinate)
    (sourceControlBit width .supplied 0) (controlBit width) wires state
  change ((offsetPlacement width .supplied coordinate).grouping state).1.val.testBit 0 = state.1.2
    at actual
  apply ProductReadout.word_ext (width := 1)
  intro index
  have same : index = 0 := Subsingleton.elim _ _
  subst index
  change ((offsetPlacement width .supplied coordinate).grouping state).1.val.testBit 0 = _
  rw [actual]
  cases state.1.2 <;> rfl

private lemma grouping_exceptionalControl (width : Nat) (coordinate : Coordinate)
    (state : Raw width) :
    ((offsetPlacement width .exceptional coordinate).grouping state).1 =
      (if state.1.2 then if state.2 then 3 else 2 else if state.2 then 1 else 0) := by
  have controlWire : arithmeticWires width .exceptional coordinate
      (sourceControlBit width .exceptional 0).wire = (controlBit width).wire := by
    apply Fin.ext
    exact arithmetic_control_address width .exceptional coordinate _ rfl
  have selectorWire : arithmeticWires width .exceptional coordinate
      (sourceControlBit width .exceptional 1).wire = (selectorBit width).wire := by
    apply Fin.ext
    exact arithmetic_selector_address width coordinate _ rfl
  have control := wirePlacement_read (offsetEncoding width .exceptional) (encoding width)
    (offset_total width .exceptional) (raw_total width)
    (arithmeticWires width .exceptional coordinate)
    (sourceControlBit width .exceptional 0) (controlBit width) controlWire state
  have selector := wirePlacement_read (offsetEncoding width .exceptional) (encoding width)
    (offset_total width .exceptional) (raw_total width)
    (arithmeticWires width .exceptional coordinate)
    (sourceControlBit width .exceptional 1) (selectorBit width) selectorWire state
  change ((offsetPlacement width .exceptional coordinate).grouping state).1.val.testBit 1 =
    state.1.2 at control
  change ((offsetPlacement width .exceptional coordinate).grouping state).1.val.testBit 0 =
    state.2 at selector
  apply ProductReadout.word_ext (width := 2)
  intro index
  fin_cases index
  · change ((offsetPlacement width .exceptional coordinate).grouping state).1.val.testBit 1 = _
    rw [control]
    cases state.1.2 <;> cases state.2 <;> rfl
  · change ((offsetPlacement width .exceptional coordinate).grouping state).1.val.testBit 0 = _
    rw [selector]
    cases state.1.2 <;> cases state.2 <;> rfl

private def offsetStep (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) (state : Raw modulus.size) : Raw modulus.size :=
  (offsetPlacement modulus.size control coordinate).step (fun grouped =>
    (grouped.1, if grouped.1 = activeValue control then
      (MAU.Addition.Gidney.modularOffsetOutput (InPlaceArithmetic.modulusWord modulus)
        constant grouped.2.1, grouped.2.2) else grouped.2)) state

/-- Each actual offset has complete normalized basis semantics with both borrowed bits restored. -/
private lemma offset_realizes (modulus : Nat) (control : OffsetControl) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) :
    UnitaryCircuit.Realizes (encoding modulus.size) (offset modulus control coordinate constant)
      environment.quantum
      (offsetStep modulus control coordinate constant) :=
  placedArithmetic_realizes modulus.size control coordinate _ _
    (MAU.Addition.Gidney.gidneyModularOffsetGates_step modulus.size
      (InPlaceArithmetic.modulusWord modulus) constant)

/-- The native offset leaves the complete source grouping outside its selected word intact. -/
private lemma offsetStep_grouping (modulus : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (constant : Fin (modulus + 1)) (state : Raw modulus.size) :
    (offsetPlacement modulus.size control coordinate).grouping
      (offsetStep modulus control coordinate constant state) =
      let grouped := (offsetPlacement modulus.size control coordinate).grouping state
      (grouped.1, if grouped.1 = activeValue control then
        (MAU.Addition.Gidney.modularOffsetOutput (InPlaceArithmetic.modulusWord modulus)
          constant grouped.2.1, grouped.2.2) else grouped.2) :=
  (offsetPlacement modulus.size control coordinate).grouping.apply_symm_apply _

/-- Inactive control makes the actual offset the identity on every complete raw frame. -/
private lemma offsetStep_inactive (modulus : Nat) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) (state : Raw modulus.size) (inactive : state.1.2 = false) :
    offsetStep modulus .supplied coordinate constant state = state := by
  apply (offsetPlacement modulus.size .supplied coordinate).grouping.injective
  rw [offsetStep_grouping]
  dsimp only []
  have controlValue := grouping_suppliedControl modulus.size coordinate state
  rw [inactive] at controlValue
  have absent : ((offsetPlacement modulus.size .supplied coordinate).grouping state).1 ≠
      activeValue .supplied := by
    rw [controlValue]
    change (0 : Fin 2) ≠ 1
    exact Fin.zero_ne_one
  rw [if_neg absent]

/-- The supplied quantum control is preserved by the whole actual controlled offset. -/
private lemma offsetStep_control (modulus : Nat) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) (state : Raw modulus.size) :
    (offsetStep modulus .supplied coordinate constant state).1.2 = state.1.2 := by
  apply BinaryLabelEncoding.bool.encode_injective
  rw [← grouping_suppliedControl modulus.size coordinate,
    ← grouping_suppliedControl modulus.size coordinate]
  have actual := congrArg (fun grouped => grouped.1)
    (offsetStep_grouping modulus .supplied coordinate constant state)
  exact actual

/-- The exact selected output word is the independent finite modular addition, including padding. -/
private lemma offsetStep_word (modulus : Nat) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) (state : Raw modulus.size) :
    coordinateValue modulus.size coordinate
      (offsetStep modulus .supplied coordinate constant state) =
      if state.1.2 then Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus)
        constant (coordinateValue modulus.size coordinate state)
      else coordinateValue modulus.size coordinate state := by
  have actual := congrArg (fun grouped => grouped.2.1.2.1)
    (offsetStep_grouping modulus .supplied coordinate constant state)
  dsimp only [] at actual
  rw [grouping_coordinate] at actual
  by_cases active : state.1.2 = true
  · rw [grouping_suppliedControl, active] at actual
    dsimp only [BinaryLabelEncoding.bool, controlWidth, activeValue] at actual
    change coordinateValue modulus.size coordinate
      (offsetStep modulus .supplied coordinate constant state) =
      Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus) constant
        ((offsetPlacement modulus.size .supplied coordinate).grouping state).2.1.2.1 at actual
    rw [grouping_coordinate] at actual
    simpa only [active, if_true] using actual
  · have inactive : state.1.2 = false := Bool.eq_false_iff.mpr active
    rw [offsetStep_inactive modulus coordinate constant state inactive, inactive]
    rfl

private lemma offsetEncoding_outside_word (width : Nat) (control : OffsetControl)
    (state : Fin (2 ^ controlWidth control) ×
      (MAU.Addition.Gidney.Registers width × Fin (2 ^ retainedWidth width control)))
    (word : Fin (2 ^ width)) (index : Fin (offsetEncoding width control).width)
    (outside : index.val < controlWidth control + 1 ∨
      controlWidth control + 1 + width ≤ index.val) :
    ((offsetEncoding width control).encode
      (state.1, ((state.2.1.1, (word, state.2.1.2.2)), state.2.2))).val.testBit index.rev.val =
      ((offsetEncoding width control).encode state).val.testBit index.rev.val := by
  let next := (state.1, ((state.2.1.1, (word, state.2.1.2.2)), state.2.2))
  have fromBit (bit : EncodedBit (offsetEncoding width control))
      (position : bit.wire = index) (same : bit.get next = bit.get state) :
      ((offsetEncoding width control).encode next).val.testBit index.rev.val =
        ((offsetEncoding width control).encode state).val.testBit index.rev.val := by
    rw [ProductReadout.bit_read, ProductReadout.bit_read, position] at same
    exact same
  by_cases leading : index.val < controlWidth control
  · apply fromBit (sourceControlBit width control ⟨index.val, leading⟩)
    · apply Fin.ext
      rfl
    · rfl
  · by_cases flag : index.val = controlWidth control
    · apply fromBit (BinaryLabelEncoding.prodRightBit
        (BinaryLabelEncoding.finIdentity (controlWidth control))
        (BinaryLabelEncoding.prod (MAU.Addition.Gidney.encoding width)
          (BinaryLabelEncoding.finIdentity (retainedWidth width control)))
        (BinaryLabelEncoding.prodLeftBit (MAU.Addition.Gidney.encoding width)
          (BinaryLabelEncoding.finIdentity (retainedWidth width control))
          (MAU.Addition.Gidney.flagBit width)))
      · apply Fin.ext
        change controlWidth control + 0 = index.val
        omega
      · rfl
    · by_cases helper : index.val = controlWidth control + 1 + width
      · apply fromBit (BinaryLabelEncoding.prodRightBit
          (BinaryLabelEncoding.finIdentity (controlWidth control))
          (BinaryLabelEncoding.prod (MAU.Addition.Gidney.encoding width)
            (BinaryLabelEncoding.finIdentity (retainedWidth width control)))
          (BinaryLabelEncoding.prodLeftBit (MAU.Addition.Gidney.encoding width)
            (BinaryLabelEncoding.finIdentity (retainedWidth width control))
            (MAU.Addition.Gidney.helperBit width)))
        · apply Fin.ext
          change controlWidth control + (1 + width) = index.val
          omega
        · rfl
      · have bound := index.isLt
        change index.val < controlWidth control + ((1 + (width + 1)) +
          retainedWidth width control) at bound
        let selected : Fin (retainedWidth width control) :=
          ⟨index.val - (controlWidth control + (1 + (width + 1))), by omega⟩
        apply fromBit (BinaryLabelEncoding.prodRightBit
          (BinaryLabelEncoding.finIdentity (controlWidth control))
          (BinaryLabelEncoding.prod (MAU.Addition.Gidney.encoding width)
            (BinaryLabelEncoding.finIdentity (retainedWidth width control)))
          (BinaryLabelEncoding.prodRightBit (MAU.Addition.Gidney.encoding width)
            (BinaryLabelEncoding.finIdentity (retainedWidth width control))
            (BinaryLabelEncoding.finIdentityBit (retainedWidth width control) selected)))
        · apply Fin.ext
          change controlWidth control + ((1 + (width + 1)) + selected.val) = index.val
          dsimp only [selected]
          omega
        · rfl

/-- Updating only the grouped arithmetic word preserves every other physical bit. -/
private lemma grouping_word_preserves_bit (width : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (state next : Raw width) (word : Fin (2 ^ width))
    (grouping : (offsetPlacement width control coordinate).grouping next =
      let grouped := (offsetPlacement width control coordinate).grouping state
      (grouped.1, ((grouped.2.1.1, (word, grouped.2.1.2.2)), grouped.2.2)))
    (bit : EncodedBit (encoding width))
    (separate : ∀ selected : Fin width,
      bit.wire ≠ ((coordinateWord width coordinate).bit selected).wire) :
    bit.get next = bit.get state := by
  let wires := arithmeticWires width control coordinate
  let index := wires.symm bit.wire
  have outside : index.val < controlWidth control + 1 ∨
      controlWidth control + 1 + width ≤ index.val := by
    by_contra inside
    let selected : Fin width := ⟨index.val - (controlWidth control + 1), by omega⟩
    have source : sourceWordPosition width control selected = index := by
      apply Fin.ext
      change controlWidth control + 1 + (index.val - (controlWidth control + 1)) = index.val
      omega
    have address : wires index = ((coordinateWord width coordinate).bit selected).wire := by
      apply Fin.ext
      rw [← source, arithmetic_word_address, coordinate_wire]
    exact separate selected ((wires.apply_symm_apply bit.wire).symm.trans address)
  have encoded (original : Raw width) :
      ((encoding width).encode original).val.testBit bit.wire.rev.val =
        ((offsetEncoding width control).encode
          ((offsetPlacement width control coordinate).grouping original)).val.testBit
            index.rev.val := by
    have actual := EncodedBit.FullPlacement.wireBasis_bit
      (offsetEncoding width control) (encoding width) wires
      ((offsetEncoding width control).encode
        ((offsetPlacement width control coordinate).grouping original)) index
    have compatible := (offsetPlacement width control coordinate).basis_encode original
    change EncodedBit.FullPlacement.wireBasis (offsetEncoding width control)
      (encoding width) wires ((offsetEncoding width control).encode
        ((offsetPlacement width control coordinate).grouping original)) =
      (encoding width).encode original at compatible
    rw [compatible] at actual
    simpa only [index, Equiv.apply_symm_apply] using actual
  rw [ProductReadout.bit_read, ProductReadout.bit_read, encoded, encoded, grouping]
  exact offsetEncoding_outside_word width control
    ((offsetPlacement width control coordinate).grouping state) word index outside

/-- Every actual physical bit outside the selected word survives the whole native offset. -/
private lemma offsetStep_preserves_bit (modulus : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (constant : Fin (modulus + 1)) (state : Raw modulus.size)
    (bit : EncodedBit (encoding modulus.size))
    (separate : ∀ selected : Fin modulus.size,
      bit.wire ≠ ((coordinateWord modulus.size coordinate).bit selected).wire) :
    bit.get (offsetStep modulus control coordinate constant state) = bit.get state := by
  let wires := arithmeticWires modulus.size control coordinate
  let index := wires.symm bit.wire
  have outside : index.val < controlWidth control + 1 ∨
      controlWidth control + 1 + modulus.size ≤ index.val := by
    by_contra inside
    let selected : Fin modulus.size := ⟨index.val - (controlWidth control + 1), by omega⟩
    have source : sourceWordPosition modulus.size control selected = index := by
      apply Fin.ext
      change controlWidth control + 1 + (index.val - (controlWidth control + 1)) = index.val
      omega
    have address : wires index = ((coordinateWord modulus.size coordinate).bit selected).wire := by
      apply Fin.ext
      rw [← source, arithmetic_word_address, coordinate_wire]
    exact separate selected ((wires.apply_symm_apply bit.wire).symm.trans address)
  have encoded (original : Raw modulus.size) :
      ((encoding modulus.size).encode original).val.testBit bit.wire.rev.val =
        ((offsetEncoding modulus.size control).encode
          ((offsetPlacement modulus.size control coordinate).grouping original)).val.testBit
            index.rev.val := by
    have actual := EncodedBit.FullPlacement.wireBasis_bit
      (offsetEncoding modulus.size control) (encoding modulus.size) wires
      ((offsetEncoding modulus.size control).encode
        ((offsetPlacement modulus.size control coordinate).grouping original)) index
    have compatible := (offsetPlacement modulus.size control coordinate).basis_encode original
    change EncodedBit.FullPlacement.wireBasis (offsetEncoding modulus.size control)
      (encoding modulus.size) wires ((offsetEncoding modulus.size control).encode
        ((offsetPlacement modulus.size control coordinate).grouping original)) =
      (encoding modulus.size).encode original at compatible
    rw [compatible] at actual
    simpa only [index, Equiv.apply_symm_apply] using actual
  rw [ProductReadout.bit_read, ProductReadout.bit_read, encoded, encoded, offsetStep_grouping]
  dsimp only []
  split_ifs with activated
  · exact offsetEncoding_outside_word modulus.size control
      ((offsetPlacement modulus.size control coordinate).grouping state) _ index outside
  · rfl

private def completeBit {Data : Type} (encoded : BinaryLabelEncoding Data)
    (total : Function.Surjective encoded.encode) (index : Fin encoded.width) :
    EncodedBit encoded :=
  BinaryLabelEncoding.ofEquivBit
    (Equiv.ofBijective encoded.encode ⟨encoded.encode_injective, total⟩) index

private def sharedBit (width : Nat)
    (bit : EncodedBit (MAU.Inversion.SharedEEA.encoding width)) : EncodedBit (encoding width) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodLeftBit (ProductPlacement.frameEncoding width)
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prodLeftBit (MAU.Inversion.SharedEEA.encoding width)
        (BinaryLabelEncoding.finIdentity width) bit))

private lemma inputFrame_bit_outside (modulus : Nat) (value : Fin (2 ^ modulus.size))
    (bit : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size))
    (outside : bit.wire.val < modulus.size + 6 ∨
      2 * modulus.size + 6 ≤ bit.wire.val) :
    bit.get (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus value) =
      InPlacePreparation.fixedBit modulus bit.wire.val := by
  have actual := InPlacePreparation.frame_auxiliary modulus
    ((MAU.Inversion.SharedEEA.InputPreparation.inputBasisEquiv modulus.size).symm value) bit
    (by
      change bit.wire.val < modulus.size + 6 ∨
        modulus.size + 6 + modulus.size ≤ bit.wire.val
      omega)
  rw [InPlacePreparation.frame_eq_inputFrame, Equiv.apply_symm_apply] at actual
  exact actual

private def preparedRaw (modulus : Nat) (control selector : Bool)
    (x y : Fin (2 ^ modulus.size)) : Raw modulus.size :=
  (((MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus x, y), control), selector)

private lemma preparedRaw_coordinate (modulus : Nat) (control selector : Bool)
    (x y : Fin (2 ^ modulus.size)) (coordinate : Coordinate) :
    coordinateValue modulus.size coordinate (preparedRaw modulus control selector x y) =
      match coordinate with | .x => x | .y => y := by
  cases coordinate
  · exact InPlaceArithmetic.initial_input modulus x y
  · exact ProductReadout.numerator_eq modulus.size _

private lemma preparedRaw_label (modulus : Nat) (control selector : Bool)
    (x y : Fin (2 ^ modulus.size)) :
    (basis modulus.size).symm ((encoding modulus.size).encode
      (preparedRaw modulus control selector x y)) =
      label modulus.size (BinaryLabelEncoding.bool.encode control)
        (BinaryLabelEncoding.bool.encode selector) (InPlaceTarget.preparedBasis modulus x y) := by
  apply (basis modulus.size).injective
  rw [Equiv.apply_symm_apply]
  have actual := basis_label modulus.size
    (show Fin 2 from BinaryLabelEncoding.bool.encode control)
    (show Fin 2 from BinaryLabelEncoding.bool.encode selector)
    (InPlaceTarget.preparedBasis modulus x y)
  rw [InPlaceTarget.preparedBasis_frame] at actual
  exact actual.symm

private lemma control_outside_coordinate (width : Nat) (coordinate : Coordinate)
    (selected : Fin width) :
    (controlBit width).wire ≠ ((coordinateWord width coordinate).bit selected).wire := by
  intro same
  have values := congrArg Fin.val same
  change InPlaceControlled.frameWidth width = _ at values
  rw [coordinate_wire] at values
  have ending := coordinate_end width coordinate
  have bound := selected.isLt
  omega

private lemma selector_outside_coordinate (width : Nat) (coordinate : Coordinate)
    (selected : Fin width) :
    (selectorBit width).wire ≠ ((coordinateWord width coordinate).bit selected).wire := by
  intro same
  have values := congrArg Fin.val same
  change InPlaceControlled.frameWidth width + 1 = _ at values
  rw [coordinate_wire] at values
  have ending := coordinate_end width coordinate
  have bound := selected.isLt
  omega

/-- The selector is retained by every actual one- or two-control modular offset. -/
private lemma offsetStep_selector (modulus : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (constant : Fin (modulus + 1)) (state : Raw modulus.size) :
    (offsetStep modulus control coordinate constant state).2 = state.2 :=
  offsetStep_preserves_bit modulus control coordinate constant state (selectorBit modulus.size)
    (selector_outside_coordinate modulus.size coordinate)

private lemma bit_get_of_wire_eq {Data : Type} {encoded : BinaryLabelEncoding Data}
    (left right : EncodedBit encoded) (same : left.wire = right.wire) (state : Data) :
    left.get state = right.get state := by
  rw [ProductReadout.bit_read, ProductReadout.bit_read, same]

/-- A physical X-only word update reconstructs the complete prepared frame. -/
private lemma prepared_x_of_words (modulus : Nat) (selector : Bool)
    (x y word : Fin (2 ^ modulus.size)) (next : Raw modulus.size)
    (actualWord : coordinateValue modulus.size .x next = word)
    (preserved : ∀ bit : EncodedBit (encoding modulus.size),
      (∀ selected : Fin modulus.size,
        bit.wire ≠ ((coordinateWord modulus.size .x).bit selected).wire) →
      bit.get next = bit.get (preparedRaw modulus true selector x y)) :
    next = preparedRaw modulus true selector word y := by
  let state := preparedRaw modulus true selector x y
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply (MAU.Inversion.SharedEEA.encoding modulus.size).encode_injective
        apply ProductReadout.word_ext
        intro index
        let bit := completeBit (MAU.Inversion.SharedEEA.encoding modulus.size)
          (MAU.Inversion.SharedEEA.encoding_surjective modulus.size) index
        have values : bit.get next.1.1.1 =
            bit.get (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus word) := by
          by_cases outside : index.val < modulus.size + 6 ∨
              2 * modulus.size + 6 ≤ index.val
          · have separate : ∀ selected : Fin modulus.size,
                (sharedBit modulus.size bit).wire ≠
                  ((coordinateWord modulus.size .x).bit selected).wire := by
              intro selected same
              have positions := congrArg Fin.val same
              change index.val = _ at positions
              rw [coordinate_wire] at positions
              change index.val = modulus.size + 6 + selected.val at positions
              have bound := selected.isLt
              omega
            have preserved := preserved
              (sharedBit modulus.size bit) separate
            change bit.get next.1.1.1 =
              bit.get (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus x) at preserved
            exact preserved.trans ((inputFrame_bit_outside modulus x bit outside).trans
              (inputFrame_bit_outside modulus word bit outside).symm)
          · let selected : Fin modulus.size := ⟨index.val - (modulus.size + 6), by omega⟩
            have wires : (sharedBit modulus.size bit).wire =
                ((coordinateWord modulus.size .x).bit selected).wire := by
              apply Fin.ext
              change index.val = _
              rw [coordinate_wire]
              change index.val = modulus.size + 6 + (index.val - (modulus.size + 6))
              omega
            have actual := (bit_get_of_wire_eq (sharedBit modulus.size bit)
              ((coordinateWord modulus.size .x).bit selected) wires next).trans
                (coordinate_read modulus.size .x selected next)
            have desired := (bit_get_of_wire_eq (sharedBit modulus.size bit)
              ((coordinateWord modulus.size .x).bit selected) wires
                (preparedRaw modulus true selector word y)).trans
                  (coordinate_read modulus.size .x selected
                    (preparedRaw modulus true selector word y))
            rw [actualWord] at actual
            rw [preparedRaw_coordinate] at desired
            exact actual.trans desired.symm
        rw [ProductReadout.bit_read, ProductReadout.bit_read] at values
        exact values
      · apply ProductReadout.word_ext
        intro index
        have preserved := preserved
          ((frameWord modulus.size (FramePorts.numerator modulus.size)).bit index) (by
            intro selected same
            have positions := congrArg Fin.val same
            change ((FramePorts.numerator modulus.size).bit index).wire.val =
              ((FramePorts.input modulus.size).bit selected).wire.val at positions
            exact (FramePorts.input_separate modulus.size selected index).2
              (Fin.ext positions.symm))
        change ((FramePorts.numerator modulus.size).bit index).get next.1.1 =
          ((FramePorts.numerator modulus.size).bit index).get state.1.1 at preserved
        rw [FramePorts.numerator_read, FramePorts.numerator_read] at preserved
        exact preserved
    · exact preserved (controlBit modulus.size) (control_outside_coordinate modulus.size .x)
  · exact preserved (selectorBit modulus.size) (selector_outside_coordinate modulus.size .x)

/-- An active X offset restores the complete arithmetic preparation and both controls. -/
private lemma offsetStep_prepared_x (modulus : Nat) (constant : Fin (modulus + 1))
    (selector : Bool) (x y : Fin (2 ^ modulus.size)) :
    offsetStep modulus .supplied .x constant (preparedRaw modulus true selector x y) =
      preparedRaw modulus true selector
        (Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus)
          constant x) y := by
  apply prepared_x_of_words modulus selector x y
  · have actual := offsetStep_word modulus .x constant (preparedRaw modulus true selector x y)
    rw [preparedRaw_coordinate] at actual
    exact actual
  · exact offsetStep_preserves_bit modulus .supplied .x constant _

private lemma offsetStep_word_active (modulus : Nat) (control : OffsetControl)
    (coordinate : Coordinate) (constant : Fin (modulus + 1)) (state : Raw modulus.size)
    (activated : ((offsetPlacement modulus.size control coordinate).grouping state).1 =
      activeValue control) :
    coordinateValue modulus.size coordinate (offsetStep modulus control coordinate constant state) =
      Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus) constant
        (coordinateValue modulus.size coordinate state) := by
  have complete := offsetStep_grouping modulus control coordinate constant state
  dsimp only [] at complete
  simp only [if_pos activated] at complete
  have actual := congrArg (fun grouped => grouped.2.1.2.1) complete
  change ((offsetPlacement modulus.size control coordinate).grouping
    (offsetStep modulus control coordinate constant state)).2.1.2.1 =
      Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus) constant
        ((offsetPlacement modulus.size control coordinate).grouping state).2.1.2.1 at actual
  rw [grouping_coordinate, grouping_coordinate] at actual
  exact actual

/-- Active Y translation preserves every original history bit and both full quantum controls. -/
private lemma offsetStep_y_active (modulus : Nat) (control : OffsetControl)
    (constant : Fin (modulus + 1)) (state : Raw modulus.size)
    (activated : ((offsetPlacement modulus.size control .y).grouping state).1 =
      activeValue control) :
    offsetStep modulus control .y constant state =
      (((state.1.1.1, Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus)
        constant state.1.1.2), state.1.2), state.2) := by
  let next := offsetStep modulus control .y constant state
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply (MAU.Inversion.SharedEEA.encoding modulus.size).encode_injective
        apply ProductReadout.word_ext
        intro index
        let bit := completeBit (MAU.Inversion.SharedEEA.encoding modulus.size)
          (MAU.Inversion.SharedEEA.encoding_surjective modulus.size) index
        have preserved := offsetStep_preserves_bit modulus control .y constant state
          (sharedBit modulus.size bit) (by
            intro selected same
            have positions := congrArg Fin.val same
            change index.val = _ at positions
            rw [coordinate_wire] at positions
            have bound := index.isLt
            have whole := MAU.Inversion.SharedEEA.encoding_width modulus.size
            change index.val = 2 * modulus.size + 6 +
              ProductPlacement.tailWidth modulus.size + selected.val at positions
            unfold ProductPlacement.tailWidth at positions
            omega)
        change bit.get next.1.1.1 = bit.get state.1.1.1 at preserved
        rw [ProductReadout.bit_read, ProductReadout.bit_read] at preserved
        exact preserved
      · have actual := offsetStep_word_active modulus control .y constant state activated
        change ProductReadout.numerator modulus.size next.1.1 =
          Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus) constant
            (ProductReadout.numerator modulus.size state.1.1) at actual
        simpa only [ProductReadout.numerator_eq] using actual
    · exact offsetStep_preserves_bit modulus control .y constant state (controlBit modulus.size)
        (control_outside_coordinate modulus.size .y)
  · exact offsetStep_selector modulus control .y constant state

private lemma offsetStep_prepared_y (modulus : Nat) (constant : Fin (modulus + 1))
    (selector : Bool) (x y : Fin (2 ^ modulus.size)) :
    offsetStep modulus .supplied .y constant (preparedRaw modulus true selector x y) =
      preparedRaw modulus true selector x
        (Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus) constant y) := by
  apply offsetStep_y_active
  rw [grouping_suppliedControl]
  rfl

private lemma offsetStep_exceptional_prepared (modulus : Nat) (constant : Fin (modulus + 1))
    (x y : Fin (2 ^ modulus.size)) :
    offsetStep modulus .exceptional .y constant (preparedRaw modulus true false x y) =
      preparedRaw modulus true false x
        (Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord modulus) constant y) := by
  apply offsetStep_y_active
  rw [grouping_exceptionalControl]
  rfl

private lemma offsetStep_exceptional_inactive (modulus : Nat) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) (state : Raw modulus.size)
    (inactive : state.1.2 = false ∨ state.2 = true) :
    offsetStep modulus .exceptional coordinate constant state = state := by
  have absent : ((offsetPlacement modulus.size .exceptional coordinate).grouping state).1 ≠
      activeValue .exceptional := by
    rw [grouping_exceptionalControl]
    rcases inactive with control | selector
    · rw [control]
      cases state.2 <;> decide
    · rw [selector]
      cases state.1.2 <;> decide
  apply (offsetPlacement modulus.size .exceptional coordinate).grouping.injective
  rw [offsetStep_grouping]
  dsimp only []
  rw [if_neg absent]

private def reflectStep (modulus : Nat) (state : Raw modulus.size) : Raw modulus.size :=
  (offsetPlacement modulus.size .supplied .x).step (fun grouped =>
    (grouped.1, if grouped.1 = 1 then
      (MAU.Addition.Gidney.pivotOutput (InPlaceArithmetic.modulusWord modulus) grouped.2.1,
        grouped.2.2) else grouped.2)) state

private lemma reflect_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (reflect modulus) environment.quantum
      (reflectStep modulus) :=
  placedArithmetic_realizes modulus.size .supplied .x _ _
    (MAU.Addition.Gidney.gidneyPivotGates_step modulus.size
      (InPlaceArithmetic.modulusWord modulus))

private lemma reflectStep_grouping_active (modulus : Nat) (state : Raw modulus.size)
    (active : state.1.2 = true) :
    (offsetPlacement modulus.size .supplied .x).grouping (reflectStep modulus state) =
      let grouped := (offsetPlacement modulus.size .supplied .x).grouping state
      (grouped.1,
        ((grouped.2.1.1, (Nat.FixedWidth.pivotWordOutput (InPlaceArithmetic.modulusWord modulus)
          (coordinateValue modulus.size .x state), grouped.2.1.2.2)), grouped.2.2)) := by
  have control : ((offsetPlacement modulus.size .supplied .x).grouping state).1 = 1 := by
    rw [grouping_suppliedControl, active]
    rfl
  change (offsetPlacement modulus.size .supplied .x).grouping
    ((offsetPlacement modulus.size .supplied .x).grouping.symm _) = _
  rw [Equiv.apply_symm_apply]
  dsimp only []
  rw [if_pos control]
  change (_, ((_, (Nat.FixedWidth.pivotWordOutput _
    ((offsetPlacement modulus.size .supplied .x).grouping state).2.1.2.1, _)), _)) = _
  rw [grouping_coordinate]

private lemma reflectStep_inactive (modulus : Nat) (state : Raw modulus.size)
    (inactive : state.1.2 = false) : reflectStep modulus state = state := by
  have control : ((offsetPlacement modulus.size .supplied .x).grouping state).1 ≠ 1 := by
    rw [grouping_suppliedControl, inactive]
    exact Fin.zero_ne_one
  change (offsetPlacement modulus.size .supplied .x).grouping.symm _ = state
  dsimp only []
  rw [if_neg control]
  exact (offsetPlacement modulus.size .supplied .x).grouping.symm_apply_apply state

/-- The real pivot reflection restores every prepared work bit on its active X word. -/
private lemma reflectStep_prepared (modulus : Nat) (selector : Bool)
    (x y : Fin (2 ^ modulus.size)) :
    reflectStep modulus (preparedRaw modulus true selector x y) =
      preparedRaw modulus true selector
        (Nat.FixedWidth.pivotWordOutput (InPlaceArithmetic.modulusWord modulus) x) y := by
  have grouping := reflectStep_grouping_active modulus
    (preparedRaw modulus true selector x y) rfl
  rw [preparedRaw_coordinate] at grouping
  apply prepared_x_of_words modulus selector x y
  · have actual := congrArg (fun grouped => grouped.2.1.2.1) grouping
    rw [grouping_coordinate] at actual
    exact actual
  · exact grouping_word_preserves_bit modulus.size .supplied .x _ _ _ grouping

private def squareWires (width : Nat) :
    Fin (squareEncoding width).width ≃ Fin (encoding width).width :=
  (finCongr (square_width width)).trans
    ((controlWires width .supplied).trans
      ((coordinateWires width .x).trans (coordinateWires width .y)))

private lemma square_address (width : Nat) (index : Fin (squareEncoding width).width) :
    (squareWires width index).val = wordAddress width (coordinateStart width .y)
      (wordAddress width (coordinateStart width .x)
        (prefixAddress (InPlaceControlled.frameWidth width + 1) index.val)) := rfl

private def squareFrameBit (width : Nat)
    (bit : EncodedBit (ProductPlacement.frameEncoding width)) :
    EncodedBit (squareEncoding width) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity 1)
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit (ProductPlacement.frameEncoding width)
      BinaryLabelEncoding.bool bit)

private lemma square_read (width : Nat) (state : Raw width)
    (source : EncodedBit (squareEncoding width)) (observed : EncodedBit (encoding width))
    (same : squareWires width source.wire = observed.wire) :
    source.get ((squarePlacement width).grouping state) = observed.get state :=
  wirePlacement_read (squareEncoding width) (encoding width)
    (prod_total _ _ Function.surjective_id
      (prod_total _ _ (ProductPlacement.frame_total width) bool_total))
    (raw_total width) (squareWires width) source observed same state

private inductive SquarePort where
  | input
  | numerator
  | accumulator

private def squareSourceWord (width : Nat) : SquarePort →
    EncodedBit.Word (ProductPlacement.frameEncoding width) width
  | .input => FramePorts.input width
  | .numerator => FramePorts.numerator width
  | .accumulator => FramePorts.accumulator width

private def squareTargetWord (width : Nat) : SquarePort → EncodedBit.Word (encoding width) width
  | .input => frameWord width (FramePorts.numerator width)
  | .numerator => frameWord width (FramePorts.accumulator width)
  | .accumulator => frameWord width (FramePorts.input width)

/-- The real square placement routes source X/Y/A to caller Y/A/X, with no physical swap charge. -/
private lemma square_word_wires (width : Nat) (port : SquarePort) (index : Fin width) :
    squareWires width (squareFrameBit width ((squareSourceWord width port).bit index)).wire =
      ((squareTargetWord width port).bit index).wire := by
  apply Fin.ext
  rw [square_address]
  have bound := index.isLt
  have frame := frame_count width
  cases port
  · change wordAddress width (coordinateStart width .y)
      (wordAddress width (coordinateStart width .x)
        (prefixAddress (InPlaceControlled.frameWidth width + 1)
          (1 + ((FramePorts.input width).bit index).wire.val))) =
      ((FramePorts.numerator width).bit index).wire.val
    rw [FramePorts.input_wire, FramePorts.numerator_wire]
    dsimp only [coordinateStart, ProductPlacement.tailWidth]
    unfold prefixAddress wordAddress
    split_ifs <;> omega
  · change wordAddress width (coordinateStart width .y)
      (wordAddress width (coordinateStart width .x)
        (prefixAddress (InPlaceControlled.frameWidth width + 1)
          (1 + ((FramePorts.numerator width).bit index).wire.val))) =
      ((FramePorts.accumulator width).bit index).wire.val
    rw [FramePorts.numerator_wire, FramePorts.accumulator_wire]
    dsimp only [coordinateStart, ProductPlacement.tailWidth]
    unfold prefixAddress wordAddress
    split_ifs <;> omega
  · change wordAddress width (coordinateStart width .y)
      (wordAddress width (coordinateStart width .x)
        (prefixAddress (InPlaceControlled.frameWidth width + 1)
          (1 + ((FramePorts.accumulator width).bit index).wire.val))) =
      ((FramePorts.input width).bit index).wire.val
    rw [FramePorts.accumulator_wire, FramePorts.input_wire]
    dsimp only [coordinateStart, ProductPlacement.tailWidth]
    unfold prefixAddress wordAddress
    split_ifs <;> omega

private lemma square_grouping_input (width : Nat) (state : Raw width) :
    ProductReadout.input width ((squarePlacement width).grouping state).2.1 =
      ProductReadout.numerator width state.1.1 := by
  apply ProductReadout.word_ext
  intro index
  have actual := square_read width state
    (squareFrameBit width ((FramePorts.input width).bit index))
    ((frameWord width (FramePorts.numerator width)).bit index)
    (square_word_wires width .input index)
  exact (ProductReadout.readWord_bit (FramePorts.input width)
    ((squarePlacement width).grouping state).2.1 index).trans
      (actual.trans (ProductReadout.readWord_bit (FramePorts.numerator width) state.1.1 index).symm)

private lemma square_grouping_numerator (width : Nat) (state : Raw width) :
    ProductReadout.numerator width ((squarePlacement width).grouping state).2.1 =
      ProductReadout.accumulator width state.1.1 := by
  apply ProductReadout.word_ext
  intro index
  have actual := square_read width state
    (squareFrameBit width ((FramePorts.numerator width).bit index))
    ((frameWord width (FramePorts.accumulator width)).bit index)
    (square_word_wires width .numerator index)
  exact (ProductReadout.readWord_bit (FramePorts.numerator width)
    ((squarePlacement width).grouping state).2.1 index).trans
      (actual.trans
        (ProductReadout.readWord_bit (FramePorts.accumulator width) state.1.1 index).symm)

private lemma square_grouping_accumulator (width : Nat) (state : Raw width) :
    ProductReadout.accumulator width ((squarePlacement width).grouping state).2.1 =
      ProductReadout.input width state.1.1 := by
  apply ProductReadout.word_ext
  intro index
  have actual := square_read width state
    (squareFrameBit width ((FramePorts.accumulator width).bit index))
    ((frameWord width (FramePorts.input width)).bit index)
    (square_word_wires width .accumulator index)
  exact (ProductReadout.readWord_bit (FramePorts.accumulator width)
    ((squarePlacement width).grouping state).2.1 index).trans
      (actual.trans (ProductReadout.readWord_bit (FramePorts.input width) state.1.1 index).symm)

private def frameBit (width : Nat)
    (bit : EncodedBit (ProductPlacement.frameEncoding width)) : EncodedBit (encoding width) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodLeftBit (ProductPlacement.frameEncoding width)
      BinaryLabelEncoding.bool bit)

private lemma square_history_wire (width : Nat)
    (index : Fin (ProductPlacement.historyWidth width)) :
    squareWires width
      (squareFrameBit width (completeBit (ProductPlacement.frameEncoding width)
        (ProductPlacement.frame_total width) (ProductReadout.historyWire width index))).wire =
      (frameBit width (completeBit (ProductPlacement.frameEncoding width)
        (ProductPlacement.frame_total width) (ProductReadout.historyWire width index))).wire := by
  apply Fin.ext
  rw [square_address]
  change wordAddress width (coordinateStart width .y)
    (wordAddress width (coordinateStart width .x)
      (prefixAddress (InPlaceControlled.frameWidth width + 1)
        (1 + (ProductReadout.historyWire width index).val))) =
    (ProductReadout.historyWire width index).val
  have bound := index.isLt
  have frame := frame_count width
  unfold ProductPlacement.historyWidth ProductPlacement.tailWidth at bound
  have position : (ProductReadout.historyWire width index).val =
      if index.val < 6 then width + index.val else 2 * width + index.val := rfl
  rw [position]
  dsimp only [coordinateStart, ProductPlacement.tailWidth]
  unfold prefixAddress wordAddress
  split_ifs <;> omega

private lemma square_grouping_history (width : Nat) (state : Raw width) :
    ProductReadout.history width ((squarePlacement width).grouping state).2.1 =
      ProductReadout.history width state.1.1 := by
  apply ProductReadout.word_ext
  intro index
  let bit := completeBit (ProductPlacement.frameEncoding width)
    (ProductPlacement.frame_total width) (ProductReadout.historyWire width index)
  have actual := square_read width state (squareFrameBit width bit) (frameBit width bit)
    (square_history_wire width index)
  change bit.get ((squarePlacement width).grouping state).2.1 = bit.get state.1.1 at actual
  rw [ProductReadout.bit_read, ProductReadout.bit_read] at actual
  have position : bit.wire = ProductReadout.historyWire width index := rfl
  rw [position] at actual
  simpa only [ProductReadout.history, BinaryBasis.bigEndianEquiv_bit, Equiv.apply_symm_apply]
    using actual

private def squareControlBit (width : Nat) : EncodedBit (squareEncoding width) :=
  BinaryLabelEncoding.prodLeftBit (BinaryLabelEncoding.finIdentity 1)
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.finIdentityBit 1 0)

private lemma square_control_wire (width : Nat) :
    squareWires width (squareControlBit width).wire = (controlBit width).wire := by
  apply Fin.ext
  rw [square_address]
  change wordAddress width (coordinateStart width .y)
    (wordAddress width (coordinateStart width .x)
      (prefixAddress (InPlaceControlled.frameWidth width + 1) 0)) =
    InPlaceControlled.frameWidth width
  have frame := frame_count width
  dsimp only [coordinateStart, ProductPlacement.tailWidth]
  unfold prefixAddress wordAddress
  split_ifs <;> omega

private lemma square_grouping_control (width : Nat) (state : Raw width) :
    ((squarePlacement width).grouping state).1 = BinaryLabelEncoding.bool.encode state.1.2 := by
  have actual := square_read width state (squareControlBit width) (controlBit width)
    (square_control_wire width)
  apply ProductReadout.word_ext (width := 1)
  intro index
  have same : index = 0 := Subsingleton.elim _ _
  subst index
  change ((squarePlacement width).grouping state).1.val.testBit 0 = _
  change ((squarePlacement width).grouping state).1.val.testBit 0 = state.1.2 at actual
  rw [actual]
  cases state.1.2 <;> rfl

private def squareSelectorBit (width : Nat) : EncodedBit (squareEncoding width) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity 1)
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodRightBit (ProductPlacement.frameEncoding width)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)

private lemma square_selector_wire (width : Nat) :
    squareWires width (squareSelectorBit width).wire = (selectorBit width).wire := by
  apply Fin.ext
  rw [square_address]
  change wordAddress width (coordinateStart width .y)
    (wordAddress width (coordinateStart width .x)
      (prefixAddress (InPlaceControlled.frameWidth width + 1)
        (1 + InPlaceControlled.frameWidth width))) = InPlaceControlled.frameWidth width + 1
  have frame := frame_count width
  dsimp only [coordinateStart, ProductPlacement.tailWidth]
  unfold prefixAddress wordAddress
  split_ifs <;> omega

private lemma square_grouping_selector (width : Nat) (state : Raw width) :
    ((squarePlacement width).grouping state).2.2 = state.2 :=
  square_read width state (squareSelectorBit width) (selectorBit width) (square_selector_wire width)

private def squareCopyStep (width : Nat) (state : Raw width) : Raw width :=
  ((InPlaceControlled.copyStep width state.1.1, state.1.2), state.2)

private lemma squareCopy_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (squareCopy width) environment.quantum
      (squareCopyStep width) := by
  apply (EncodedBit.Word.xorInto_realizes
    (environment := environment.quantum) (nativeLayout width) .empty
    (frameWord width (FramePorts.numerator width))
    (frameWord width (FramePorts.accumulator width)) (copy_separate width)).congrStep
  intro state
  have gates : EncodedBit.Word.xorIntoGates (frameWord width (FramePorts.numerator width))
      (frameWord width (FramePorts.accumulator width)) (copy_separate width) =
      ((EncodedBit.Word.xorIntoGates (FramePorts.numerator width) (FramePorts.accumulator width)
        (fun index => (FramePorts.accumulator_numerator_ne width index index).symm)).map
          (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool) := by
    simp only [EncodedBit.Word.xorIntoGates, List.map_ofFn]
    rfl
  rw [EncodedBit.Word.xorIntoStep, gates]
  have first := EncodedBit.GateSpec.stepList_prodLeft BinaryLabelEncoding.bool
    ((EncodedBit.Word.xorIntoGates (FramePorts.numerator width) (FramePorts.accumulator width)
      (fun index => (FramePorts.accumulator_numerator_ne width index index).symm)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)) state
  have second := EncodedBit.GateSpec.stepList_prodLeft BinaryLabelEncoding.bool
    (EncodedBit.Word.xorIntoGates (FramePorts.numerator width) (FramePorts.accumulator width)
      (fun index => (FramePorts.accumulator_numerator_ne width index index).symm)) state.1
  exact first.trans (congrArg (fun frame => (frame, state.2)) second)

private lemma copy_accumulator_bit (width : Nat) (state : ProductPlacement.Frame width)
    (index : Fin width) :
    (ProductReadout.accumulator width (InPlaceControlled.copyStep width state)).val.testBit
        index.rev.val =
      ((ProductReadout.accumulator width state).val.testBit index.rev.val ^^
        (ProductReadout.numerator width state).val.testBit index.rev.val) := by
  simp only [ProductReadout.accumulator, ProductReadout.numerator, ProductReadout.readWord_bit]
  rw [InPlaceControlled.copyStep, EncodedBit.Word.xorIntoStep_get_target _ _ _ index
    (fun other different => FramePorts.accumulator_distinct width other index different)
    (fun other => FramePorts.accumulator_numerator_ne width other index)]

private lemma copyStep_involutive (width : Nat) (state : ProductPlacement.Frame width) :
    InPlaceControlled.copyStep width (InPlaceControlled.copyStep width state) = state := by
  apply ProductPortLaws.frame_ext
  · rw [InPlaceControlled.copy_input, InPlaceControlled.copy_input]
  · rw [InPlaceControlled.copy_numerator, InPlaceControlled.copy_numerator]
  · apply ProductReadout.word_ext
    intro index
    rw [copy_accumulator_bit, copy_accumulator_bit, InPlaceControlled.copy_numerator]
    simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · rw [InPlaceControlled.copy_history, InPlaceControlled.copy_history]

/-- The two actual copies restore A on every frame when the middle action is off. -/
private lemma squareCopyStep_involutive (width : Nat) (state : Raw width) :
    squareCopyStep width (squareCopyStep width state) = state := by
  change ((InPlaceControlled.copyStep width (InPlaceControlled.copyStep width state.1.1),
    state.1.2), state.2) = state
  rw [copyStep_involutive]

/-- Independent full-frame finite product permutation, retaining all physical history fields. -/
private def productPermutation (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Equiv.Perm (ProductPlacement.Frame width) :=
  (ProductPlacement.placement width).grouping.trans
    ((Equiv.prodCongr (Nat.FixedWidth.variableTripleEquiv modulus) (Equiv.refl _)).trans
      (ProductPlacement.placement width).grouping.symm)

private lemma productPermutation_apply (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : ProductPlacement.Frame width) :
    productPermutation width modulus state = NativeProductFrame.step width modulus state := by
  simp only [productPermutation, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Nat.FixedWidth.variableTripleEquiv_apply]
  rfl

/-- Reversing the actual product list inverts the complete finite frame permutation. -/
private lemma product_inverse_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : ProductPlacement.Frame width) :
    EncodedBit.GateSpec.stepList (NativeProductFrame.gates width modulus).reverse state =
      (productPermutation width modulus).symm state := by
  have forward : EncodedBit.GateSpec.stepList (NativeProductFrame.gates width modulus)
      ((productPermutation width modulus).symm state) = state := by
    rw [NativeProductFrame.nativeProductFrame_gates_step, ← productPermutation_apply]
    exact (productPermutation width modulus).apply_symm_apply state
  have backward := congrArg
    (EncodedBit.GateSpec.stepList (NativeProductFrame.gates width modulus).reverse) forward
  rw [EncodedBit.GateSpec.stepList_reverse_stepList] at backward
  exact backward.symm

private def squareStep (modulus : Nat) : Raw modulus.size → Raw modulus.size :=
  (squarePlacement modulus.size).step fun grouped =>
    (grouped.1, if grouped.1 = 1 then
      ((productPermutation modulus.size (InPlaceArithmetic.modulusWord modulus)).symm grouped.2.1,
        grouped.2.2) else grouped.2)

/-- The literal cyclic product placement executes the complete inverse arithmetic under real C. -/
private lemma squareSubtract_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (squareSubtract modulus) environment.quantum
      (squareStep modulus) := by
  apply EncodedBit.GateSpec.realizesList_congrStep (environment := environment.quantum)
  intro state
  rw [squareSubtractGates, EncodedBit.FullPlacement.placeGates_step]
  unfold EncodedBit.FullPlacement.step squareStep
  apply congrArg (squarePlacement modulus.size).grouping.symm
  rw [pointPrefixControlGates_step]
  simp only [EncodedBit.GateSpec.stepList_prodLeft, product_inverse_step, activeValue]

private lemma squareStep_inactive (modulus : Nat) (state : Raw modulus.size)
    (inactive : state.1.2 = false) : squareStep modulus state = state := by
  apply (squarePlacement modulus.size).grouping.injective
  change (squarePlacement modulus.size).grouping
    ((squarePlacement modulus.size).grouping.symm _) = _
  rw [Equiv.apply_symm_apply]
  have controlValue := square_grouping_control modulus.size state
  rw [inactive] at controlValue
  have absent : ((squarePlacement modulus.size).grouping state).1 ≠ 1 := by
    rw [controlValue]
    change (0 : Fin 2) ≠ 1
    exact Fin.zero_ne_one
  dsimp only []
  rw [if_neg absent]

private lemma subtractSquare_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (subtractSquare modulus) environment.quantum
      (squareCopyStep modulus.size ∘ squareStep modulus ∘ squareCopyStep modulus.size) :=
  nativeList_append_realizes _ _ _ _
    (nativeList_append_realizes _ _ _ _
      (squareCopy_realizes modulus.size) (squareSubtract_realizes modulus))
    (squareCopy_realizes modulus.size)

/-- Inactive square subtraction fixes every binary label, including arbitrary entangled work. -/
private lemma subtractSquare_inactive (modulus : Nat) (state : Raw modulus.size)
    (inactive : state.1.2 = false) :
    ((subtractSquare modulus).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding modulus.size).encode state)) =
        NormalizedVector.ket ((encoding modulus.size).encode state) := by
  have actual := nativeRealizes_ket (environment := environment) _ _
    (subtractSquare_realizes modulus) state
  have copied : (squareCopyStep modulus.size state).1.2 = false := inactive
  simpa only [Function.comp_apply, squareStep_inactive modulus _ copied,
    squareCopyStep_involutive] using actual

private lemma prepared_history_independent (modulus : Nat)
    (leftX leftY rightX rightY : Fin (2 ^ modulus.size)) :
    ProductReadout.history modulus.size
      (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus leftX, leftY) =
      ProductReadout.history modulus.size
        (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus rightX, rightY) := by
  apply ProductReadout.word_ext
  intro index
  let position : Fin (MAU.Inversion.SharedEEA.encoding modulus.size).width :=
    ⟨(ProductReadout.historyWire modulus.size index).val,
      InPlaceArithmetic.history_before_numerator modulus.size index⟩
  let bit := completeBit (MAU.Inversion.SharedEEA.encoding modulus.size)
    (MAU.Inversion.SharedEEA.encoding_surjective modulus.size) position
  have outside : bit.wire.val < modulus.size + 6 ∨ 2 * modulus.size + 6 ≤ bit.wire.val := by
    change (ProductReadout.historyWire modulus.size index).val < modulus.size + 6 ∨
      2 * modulus.size + 6 ≤ (ProductReadout.historyWire modulus.size index).val
    have address : (ProductReadout.historyWire modulus.size index).val =
        if index.val < 6 then modulus.size + index.val else 2 * modulus.size + index.val := rfl
    rw [address]
    split_ifs <;> omega
  let lifted := BinaryLabelEncoding.prodLeftBit (MAU.Inversion.SharedEEA.encoding modulus.size)
    (BinaryLabelEncoding.finIdentity modulus.size) bit
  have actual : lifted.get
      (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus leftX, leftY) =
      lifted.get (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus rightX, rightY) :=
    (inputFrame_bit_outside modulus leftX bit outside).trans
      (inputFrame_bit_outside modulus rightX bit outside).symm
  rw [ProductReadout.bit_read, ProductReadout.bit_read] at actual
  have placed : lifted.wire = ProductReadout.historyWire modulus.size index := by
    apply Fin.ext
    rfl
  rw [placed] at actual
  simpa only [ProductReadout.history, BinaryBasis.bigEndianEquiv_bit, Equiv.apply_symm_apply,
    ProductPlacement.frameEncoding] using actual

private lemma copied_square_reads (modulus : Nat) (selector : Bool)
    (x y : Fin (2 ^ modulus.size)) :
    let frame := ((squarePlacement modulus.size).grouping
      (squareCopyStep modulus.size (preparedRaw modulus true selector x y))).2.1
    ProductReadout.input modulus.size frame = y ∧
      ProductReadout.numerator modulus.size frame = y ∧
      ProductReadout.accumulator modulus.size frame = x := by
  constructor
  · rw [square_grouping_input]
    change ProductReadout.numerator modulus.size (InPlaceControlled.copyStep modulus.size
      (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus x, y)) = y
    rw [InPlaceControlled.copy_numerator, ProductReadout.numerator_eq]
  · constructor
    · rw [square_grouping_numerator]
      change ProductReadout.accumulator modulus.size (InPlaceControlled.copyStep modulus.size
        (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus x, y)) = y
      rw [InPlaceControlled.copy_accumulator _ _
        (InPlaceArithmetic.initial_accumulator modulus x y), ProductReadout.numerator_eq]
    · rw [square_grouping_accumulator]
      change ProductReadout.input modulus.size (InPlaceControlled.copyStep modulus.size
        (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus x, y)) = x
      rw [InPlaceControlled.copy_input, InPlaceArithmetic.initial_input]

private lemma copied_square_history (modulus : Nat) (selector : Bool)
    (leftX leftY rightX rightY : Fin (2 ^ modulus.size)) :
    ProductReadout.history modulus.size ((squarePlacement modulus.size).grouping
      (squareCopyStep modulus.size (preparedRaw modulus true selector leftX leftY))).2.1 =
    ProductReadout.history modulus.size ((squarePlacement modulus.size).grouping
      (squareCopyStep modulus.size (preparedRaw modulus true selector rightX rightY))).2.1 := by
  rw [square_grouping_history, square_grouping_history]
  change ProductReadout.history modulus.size (InPlaceControlled.copyStep modulus.size
    (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus leftX, leftY)) =
      ProductReadout.history modulus.size (InPlaceControlled.copyStep modulus.size
        (MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame modulus rightX, rightY))
  rw [InPlaceControlled.copy_history, InPlaceControlled.copy_history]
  exact prepared_history_independent modulus leftX leftY rightX rightY

private lemma product_inverse_of_read_values (width : Nat) (modulus : Fin (2 ^ width + 1))
    (before after : ProductPlacement.Frame width) (x y difference : Fin (2 ^ width))
    (beforeReads : ProductReadout.input width before = y ∧
      ProductReadout.numerator width before = y ∧ ProductReadout.accumulator width before = x)
    (afterReads : ProductReadout.input width after = y ∧
      ProductReadout.numerator width after = y ∧
        ProductReadout.accumulator width after = difference)
    (valid : difference.val < modulus.val)
    (arithmetic : (difference.val + y.val * y.val) % modulus.val = x.val)
    (history : ProductReadout.history width before = ProductReadout.history width after) :
    (productPermutation width modulus).symm before = after := by
  apply (productPermutation width modulus).injective
  rw [Equiv.apply_symm_apply, productPermutation_apply]
  symm
  apply ProductPortLaws.step_eq_of_reads width modulus after before
  · rw [afterReads.2.2]
    exact valid
  · exact beforeReads.1.trans afterReads.1.symm
  · exact beforeReads.2.1.trans afterReads.2.1.symm
  · rw [beforeReads.2.2, afterReads.2.2, afterReads.1, afterReads.2.1]
    exact arithmetic.symm
  · exact history

/-- The actual inverse product restores the exact copied frame prescribed by modular subtraction. -/
private lemma squareStep_copied_prepared (modulus : Nat) (selector : Bool)
    (x y difference : Fin (2 ^ modulus.size)) (valid : difference.val < modulus)
    (arithmetic : (difference.val + y.val * y.val) % modulus = x.val) :
    squareStep modulus (squareCopyStep modulus.size (preparedRaw modulus true selector x y)) =
      squareCopyStep modulus.size (preparedRaw modulus true selector difference y) := by
  let input := squareCopyStep modulus.size (preparedRaw modulus true selector x y)
  let output := squareCopyStep modulus.size (preparedRaw modulus true selector difference y)
  have inputControl : ((squarePlacement modulus.size).grouping input).1 = 1 := by
    rw [square_grouping_control]
    rfl
  have outputControl : ((squarePlacement modulus.size).grouping output).1 = 1 := by
    rw [square_grouping_control]
    rfl
  have beforeReads := copied_square_reads modulus selector x y
  have afterReads := copied_square_reads modulus selector difference y
  apply (squarePlacement modulus.size).grouping.injective
  change (squarePlacement modulus.size).grouping
    ((squarePlacement modulus.size).grouping.symm _) = _
  rw [Equiv.apply_symm_apply]
  dsimp only []
  rw [if_pos inputControl]
  apply Prod.ext
  · exact inputControl.trans outputControl.symm
  · apply Prod.ext
    · exact product_inverse_of_read_values modulus.size (InPlaceArithmetic.modulusWord modulus)
        _ _ x y difference beforeReads afterReads valid arithmetic
        (copied_square_history modulus selector x y difference y)
    · rw [square_grouping_selector, square_grouping_selector]
      rfl

/-- Real copies and the real product adjoint subtract the square and restore all prepared work. -/
private lemma subtractSquare_prepared (modulus : Nat) (selector : Bool)
    (x y difference : Fin (2 ^ modulus.size)) (valid : difference.val < modulus)
    (arithmetic : (difference.val + y.val * y.val) % modulus = x.val) :
    ((subtractSquare modulus).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding modulus.size).encode
        (preparedRaw modulus true selector x y))) =
      NormalizedVector.ket ((encoding modulus.size).encode
        (preparedRaw modulus true selector difference y)) := by
  have actual := nativeRealizes_ket (environment := environment) _ _
    (subtractSquare_realizes modulus)
    (preparedRaw modulus true selector x y)
  simpa only [Function.comp_apply, squareStep_copied_prepared modulus selector x y difference
    valid arithmetic, squareCopyStep_involutive] using actual

private lemma flipBit_bigEndian {width : Nat} (target index : Fin width)
    (value : Fin (2 ^ width)) :
    (WireAddress.flipBit target value).val.testBit index.rev.val =
      (value.val.testBit index.rev.val ^^ decide (target = index)) := by
  have reverse : (WireAddress.bitIndex index).val = index.rev.val := by
    dsimp only [WireAddress.bitIndex]
    rw [Fin.val_rev]
    omega
  simpa only [reverse] using WireAddress.bit_flipBit target index value

private lemma wireBasis_flip {Source Target : Type}
    (source : BinaryLabelEncoding Source) (target : BinaryLabelEncoding Target)
    (wires : Fin source.width ≃ Fin target.width)
    (selected : Fin source.width) (value : Fin (2 ^ source.width)) :
    EncodedBit.FullPlacement.wireBasis source target wires (WireAddress.flipBit selected value) =
      WireAddress.flipBit (wires selected)
        (EncodedBit.FullPlacement.wireBasis source target wires value) := by
  apply ProductReadout.word_ext
  intro observed
  obtain ⟨index, rfl⟩ := wires.surjective observed
  rw [EncodedBit.FullPlacement.wireBasis_bit, flipBit_bigEndian, flipBit_bigEndian,
    EncodedBit.FullPlacement.wireBasis_bit]
  simp only [Equiv.apply_eq_iff_eq]

/-- The same physical wire placement transports a literal native bit flip on every full label. -/
private lemma wirePlacement_flip {Source Target : Type}
    (source : BinaryLabelEncoding Source) (target : BinaryLabelEncoding Target)
    (sourceTotal : Function.Surjective source.encode)
    (targetTotal : Function.Surjective target.encode)
    (wires : Fin source.width ≃ Fin target.width)
    (sourceBit : EncodedBit source) (targetBit : EncodedBit target)
    (same : wires sourceBit.wire = targetBit.wire) (state : Target) :
    (EncodedBit.FullPlacement.ofWires source target sourceTotal targetTotal wires).grouping.symm
      (sourceBit.flip ((EncodedBit.FullPlacement.ofWires source target sourceTotal targetTotal
        wires).grouping state)) = targetBit.flip state := by
  let placed := EncodedBit.FullPlacement.ofWires source target sourceTotal targetTotal wires
  let raw := placed.grouping state
  have encoded := placed.basis_encode (placed.grouping.symm (sourceBit.flip raw))
  rw [Equiv.apply_symm_apply] at encoded
  change EncodedBit.FullPlacement.wireBasis source target wires
    (source.encode (sourceBit.flip raw)) = target.encode
      (placed.grouping.symm (sourceBit.flip raw)) at encoded
  have original := placed.basis_encode state
  change EncodedBit.FullPlacement.wireBasis source target wires (source.encode raw) =
    target.encode state at original
  apply target.encode_injective
  calc
    _ = EncodedBit.FullPlacement.wireBasis source target wires
        (source.encode (sourceBit.flip raw)) := encoded.symm
    _ = EncodedBit.FullPlacement.wireBasis source target wires
        (WireAddress.flipBit sourceBit.wire (source.encode raw)) := by rw [sourceBit.encode_flip]
    _ = WireAddress.flipBit (wires sourceBit.wire)
        (EncodedBit.FullPlacement.wireBasis source target wires (source.encode raw)) :=
      wireBasis_flip source target wires sourceBit.wire (source.encode raw)
    _ = target.encode (targetBit.flip state) := by
      rw [original, same, targetBit.encode_flip]

private def comparisonWires (width : Nat) :
    Fin (offsetEncoding width .supplied).width ≃ Fin (encoding width).width :=
  (arithmeticWires width .supplied .x).trans
    (Equiv.swap ⟨width, by rw [total_width]; omega⟩ (selectorBit width).wire)

private def comparisonFlagBit (width : Nat) : EncodedBit (offsetEncoding width .supplied) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity 1)
    (BinaryLabelEncoding.prod (MAU.Addition.Gidney.encoding width)
      (BinaryLabelEncoding.finIdentity (retainedWidth width .supplied)))
    (BinaryLabelEncoding.prodLeftBit (MAU.Addition.Gidney.encoding width)
      (BinaryLabelEncoding.finIdentity (retainedWidth width .supplied))
      (MAU.Addition.Gidney.flagBit width))

private lemma comparison_flag_wire (width : Nat) :
    comparisonWires width (comparisonFlagBit width).wire = (selectorBit width).wire := by
  have original : arithmeticWires width .supplied .x (comparisonFlagBit width).wire =
      (⟨width, by rw [total_width]; omega⟩ : Fin (encoding width).width) := by
    apply Fin.ext
    rw [arithmetic_address]
    change wordAddress width (coordinateStart width .x)
      (prefixAddress (width + 1) (prefixAddress (InPlaceControlled.frameWidth width + 1) 1)) = width
    rw [prefix_positive (InPlaceControlled.frameWidth width + 1) 1
      (by omega) (by rw [frame_count]; omega)]
    change wordAddress width (width + 6) (prefixAddress (width + 1) 0) = width
    rw [prefix_zero _ (by omega)]
    have reduce : width + 1 - 1 = width := by omega
    rw [reduce, wordAddress, if_neg (by omega), if_neg (by omega)]
  change Equiv.swap _ _ (arithmeticWires width .supplied .x (comparisonFlagBit width).wire) = _
  rw [original, Equiv.swap_apply_left]

private lemma comparison_control_wire (width : Nat) :
    comparisonWires width (sourceControlBit width .supplied 0).wire = (controlBit width).wire := by
  have original : arithmeticWires width .supplied .x (sourceControlBit width .supplied 0).wire =
      (controlBit width).wire := by
    apply Fin.ext
    exact arithmetic_control_address width .supplied .x _ rfl
  change Equiv.swap _ _ (arithmeticWires width .supplied .x
    (sourceControlBit width .supplied 0).wire) = _
  rw [original]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro same
    have values := congrArg Fin.val same
    change InPlaceControlled.frameWidth width = width at values
    have frame := frame_count width
    omega
  · exact controls_separate width

private lemma comparison_word_wire (width : Nat) (index : Fin width) :
    comparisonWires width (sourceWordBit width .supplied index).wire =
      ((coordinateWord width .x).bit index).wire := by
  have original : arithmeticWires width .supplied .x (sourceWordBit width .supplied index).wire =
      ((coordinateWord width .x).bit index).wire := by
    apply Fin.ext
    rw [source_word_wire, arithmetic_word_address, coordinate_wire]
  change Equiv.swap _ _ (arithmeticWires width .supplied .x
    (sourceWordBit width .supplied index).wire) = _
  rw [original]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro same
    have values := congrArg Fin.val same
    rw [coordinate_wire] at values
    change width + 6 + index.val = width at values
    omega
  · exact (selector_outside_coordinate width .x index).symm

private lemma comparison_read (width : Nat) (state : Raw width)
    (source : EncodedBit (offsetEncoding width .supplied))
    (observed : EncodedBit (encoding width))
    (same : comparisonWires width source.wire = observed.wire) :
    source.get ((comparisonPlacement width).grouping state) = observed.get state :=
  wirePlacement_read (offsetEncoding width .supplied) (encoding width)
    (offset_total width .supplied) (raw_total width) (comparisonWires width)
      source observed same state

private lemma comparison_grouping_control (width : Nat) (state : Raw width) :
    ((comparisonPlacement width).grouping state).1 = BinaryLabelEncoding.bool.encode state.1.2 := by
  have actual := comparison_read width state (sourceControlBit width .supplied 0)
    (controlBit width) (comparison_control_wire width)
  apply ProductReadout.word_ext (width := 1)
  intro index
  have same : index = 0 := Subsingleton.elim _ _
  subst index
  change ((comparisonPlacement width).grouping state).1.val.testBit 0 = _
  change ((comparisonPlacement width).grouping state).1.val.testBit 0 = state.1.2 at actual
  rw [actual]
  cases state.1.2 <;> rfl

private lemma comparison_grouping_word (width : Nat) (state : Raw width) :
    ((comparisonPlacement width).grouping state).2.1.2.1 =
      ProductReadout.input width state.1.1 := by
  apply ProductReadout.word_ext
  intro index
  have actual := comparison_read width state (sourceWordBit width .supplied index)
    ((coordinateWord width .x).bit index) (comparison_word_wire width index)
  change (MAU.Addition.Gidney.wordBit width index.rev).get
    ((comparisonPlacement width).grouping state).2.1 = _ at actual
  rw [MAU.Addition.Gidney.gidneyWordBit_get, coordinate_read] at actual
  exact actual

private lemma comparison_grouping_flag (width : Nat) (state : Raw width) :
    ((comparisonPlacement width).grouping state).2.1.1 = state.2 :=
  comparison_read width state (comparisonFlagBit width) (selectorBit width)
    (comparison_flag_wire width)

private lemma comparison_flip (width : Nat) (state : Raw width) :
    (comparisonPlacement width).grouping.symm
      ((comparisonFlagBit width).flip ((comparisonPlacement width).grouping state)) =
      (selectorBit width).flip state :=
  wirePlacement_flip (offsetEncoding width .supplied) (encoding width)
    (offset_total width .supplied) (raw_total width) (comparisonWires width)
    (comparisonFlagBit width) (selectorBit width) (comparison_flag_wire width) state

private def comparisonAction (width : Nat)
    (grouped : Fin 2 × (MAU.Addition.Gidney.Registers width ×
      Fin (2 ^ retainedWidth width .supplied))) :=
  (grouped.1, if grouped.1 = 1 then
    (MAU.Addition.Gidney.comparisonOutput 1 grouped.2.1, grouped.2.2) else grouped.2)

private def compareZeroStep (width : Nat) (state : Raw width) : Raw width :=
  if state.1.2 && decide ((ProductReadout.input width state.1.1).val = 0) then
    (selectorBit width).flip state else state

private lemma comparisonAction_active (width : Nat) (state : Raw width)
    (active : state.1.2 = true) :
    comparisonAction width ((comparisonPlacement width).grouping state) =
      if (ProductReadout.input width state.1.1).val = 0 then
        (comparisonFlagBit width).flip ((comparisonPlacement width).grouping state)
      else (comparisonPlacement width).grouping state := by
  have control : ((comparisonPlacement width).grouping state).1 = 1 := by
    rw [comparison_grouping_control, active]
    rfl
  unfold comparisonAction
  rw [if_pos control]
  have compared : decide (((comparisonPlacement width).grouping state).2.1.2.1.val < 1) =
      decide ((ProductReadout.input width state.1.1).val = 0) := by
    rw [comparison_grouping_word]
    simp only [Nat.lt_one_iff]
  change (((comparisonPlacement width).grouping state).1,
    ((((comparisonPlacement width).grouping state).2.1.1 ^^
      decide (((comparisonPlacement width).grouping state).2.1.2.1.val < 1),
        ((comparisonPlacement width).grouping state).2.1.2),
      ((comparisonPlacement width).grouping state).2.2)) = _
  rw [compared]
  by_cases zero : (ProductReadout.input width state.1.1).val = 0
  · simp only [zero, if_true, decide_true, Bool.xor_true]
    rfl
  · simp only [zero, if_false, decide_false, Bool.xor_false]

private lemma comparisonAction_inactive (width : Nat) (state : Raw width)
    (inactive : state.1.2 = false) :
    comparisonAction width ((comparisonPlacement width).grouping state) =
      (comparisonPlacement width).grouping state := by
  have absent : ((comparisonPlacement width).grouping state).1 ≠ 1 := by
    rw [comparison_grouping_control, inactive]
    change (0 : Fin 2) ≠ 1
    exact Fin.zero_ne_one
  rw [comparisonAction, if_neg absent]
  rfl

/-- The actual comparison toggles precisely N on C=true and X=0, retaining every other bit. -/
private lemma compareZero_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (compareZero width) environment.quantum
      (compareZeroStep width) := by
  apply EncodedBit.GateSpec.realizesList_congrStep (environment := environment.quantum)
  intro state
  rw [compareZeroGates, EncodedBit.FullPlacement.placeGates_step]
  unfold EncodedBit.FullPlacement.step
  rw [arithmeticControlGates, pointPrefixControlGates_step]
  simp only [EncodedBit.GateSpec.stepList_prodLeft,
    MAU.Addition.Gidney.gidneyComparisonGates_step, activeValue]
  change (comparisonPlacement width).grouping.symm
    (comparisonAction width ((comparisonPlacement width).grouping state)) =
      compareZeroStep width state
  by_cases active : state.1.2 = true
  · rw [comparisonAction_active width state active]
    by_cases zero : (ProductReadout.input width state.1.1).val = 0
    · rw [if_pos zero, comparison_flip]
      simp only [compareZeroStep, active, zero, decide_true, Bool.and_self, if_true]
    · rw [if_neg zero, Equiv.symm_apply_apply]
      simp only [compareZeroStep, active, zero, decide_false, Bool.and_false, Bool.false_eq_true,
        if_false]
  · have inactive : state.1.2 = false := Bool.eq_false_iff.mpr active
    rw [comparisonAction_inactive width state inactive, Equiv.symm_apply_apply]
    simp only [compareZeroStep, inactive, Bool.false_and, Bool.false_eq_true, if_false]

private def selectNormalStep (width : Nat) (state : Raw width) : Raw width :=
  (state.1, state.2 ^^ (state.1.2 && decide ((ProductReadout.input width state.1.1).val ≠ 0)))

/-- The actual selector circuit changes only N by C and the nonzero test on X. -/
private lemma selectNormal_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (selectNormal width) environment.quantum
      (selectNormalStep width) := by
  have first := EncodedBit.GateSpec.realizesList (environment := environment.quantum)
    (nativeLayout width) .empty
    [.cnot (controlBit width) (selectorBit width) (controls_separate width)]
  apply (nativeList_append_realizes _ _ _ _ first (compareZero_realizes width)).congrStep
  rintro ⟨⟨frame, control⟩, selector⟩
  change compareZeroStep width
    (EncodedBit.cnotStep (controlBit width) (selectorBit width) ((frame, control), selector)) = _
  cases control <;> cases selector <;>
    by_cases zero : (ProductReadout.input width frame).val = 0 <;>
    simp [compareZeroStep, selectNormalStep, EncodedBit.cnotStep, controlBit, selectorBit,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.boolBit, zero]

private lemma selectNormalStep_involutive (width : Nat) :
    Function.Involutive (selectNormalStep width) := by
  intro state
  dsimp only [selectNormalStep]
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Uncomputing the real selector restores exactly the original bit and full frame. -/
private lemma selectNormal_dagger_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width)
      (EncodedBit.GateSpec.programList (nativeLayout width) .empty
        (selectNormalGates width).reverse) environment.quantum
      (selectNormalStep width) := by
  apply EncodedBit.GateSpec.realizesList_congrStep (environment := environment.quantum)
  intro state
  have forward : EncodedBit.GateSpec.stepList (selectNormalGates width)
      (selectNormalStep width state) = state :=
    (nativeList_step (environment := environment) _ _ (selectNormal_realizes width) _).trans
      (selectNormalStep_involutive width state)
  have backward := congrArg (EncodedBit.GateSpec.stepList (selectNormalGates width).reverse) forward
  rw [EncodedBit.GateSpec.stepList_reverse_stepList] at backward
  exact backward.symm

private def exchangeControlsStep (width : Nat) (state : Raw width) : Raw width :=
  ((state.1.1, state.2), state.1.2)

/-- The three native CNOTs exchange the two actual controls and preserve every other bit. -/
private lemma exchangeControls_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (exchangeControls width) environment.quantum
      (exchangeControlsStep width) := by
  apply (EncodedBit.swap_realizes
    (environment := environment.quantum) (nativeLayout width) .empty
    (controlBit width) (selectorBit width)
    (controls_separate width)).congrStep
  rintro ⟨⟨frame, control⟩, selector⟩
  cases control <;> cases selector <;>
    rfl

private lemma selectNormalStep_inactive (width : Nat) (state : Raw width)
    (inactive : state.1.2 = false) : selectNormalStep width state = state := by
  simp only [selectNormalStep, inactive, Bool.false_and, Bool.xor_false]

private lemma exchangeControlsStep_both_false (width : Nat) (state : Raw width)
    (inactive : state.1.2 = false) (clean : state.2 = false) :
    exchangeControlsStep width state = state := by
  change ((state.1.1, state.2), state.1.2) = state
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact clean.trans inactive.symm
  · exact inactive.trans clean.symm

/-- Every native middle-stage gate fixes the complete inactive input frame. -/
private lemma beforeMultiplication_inactive {p : Nat}
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) (state : Raw p.size)
    (inactive : state.1.2 = false) (clean : state.2 = false) :
    ((beforeMultiplication Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode state)) =
      NormalizedVector.ket ((encoding p.size).encode state) := by
  have realized := nativeList_append_realizes (environment := environment) _ _ _ _
    (nativeList_append_realizes _ _ _ _
      (nativeList_append_realizes _ _ _ _
        (offset_realizes p .supplied .x (constantWord (3 * Q.x)))
        (subtractSquare_realizes p))
      (selectNormal_realizes p.size))
    (exchangeControls_realizes p.size)
  have actual := nativeRealizes_ket (environment := environment) _ _ realized state
  have copied : (squareCopyStep p.size state).1.2 = false := inactive
  simpa only [beforeMultiplication, beforeMultiplicationGates, Function.comp_apply,
    offsetStep_inactive p .x _ state inactive,
    squareStep_inactive p _ copied, squareCopyStep_involutive,
    selectNormalStep_inactive p.size state inactive,
    exchangeControlsStep_both_false p.size state inactive clean] using actual

private def afterMultiplicationStep {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) : Raw p.size → Raw p.size :=
  offsetStep p .supplied .y (constantWord (-Q.y)) ∘
    offsetStep p .supplied .x (constantWord (Q.x + 1)) ∘ reflectStep p ∘
      selectNormalStep p.size ∘
        offsetStep p .exceptional .y (constantWord (-exceptionalSlope E Q)) ∘
          exchangeControlsStep p.size

private lemma afterMultiplication_realizes {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) :
    UnitaryCircuit.Realizes (encoding p.size) (afterMultiplication E Q) environment.quantum
      (afterMultiplicationStep E Q) :=
  nativeList_append_realizes _ _ _ _
    (nativeList_append_realizes _ _ _ _
      (nativeList_append_realizes _ _ _ _
        (nativeList_append_realizes _ _ _ _
          (nativeList_append_realizes _ _ _ _
            (exchangeControls_realizes p.size)
            (offset_realizes p .exceptional .y (constantWord (-exceptionalSlope E Q))))
          (selectNormal_dagger_realizes p.size))
        (reflect_realizes p))
      (offset_realizes p .supplied .x (constantWord (Q.x + 1))))
    (offset_realizes p .supplied .y (constantWord (-Q.y)))

/-- The real exceptional cleanup and all final offsets fix the complete inactive frame. -/
private lemma afterMultiplication_inactive {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (state : Raw p.size)
    (inactive : state.1.2 = false) (clean : state.2 = false) :
    ((afterMultiplication E Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode state)) =
      NormalizedVector.ket ((encoding p.size).encode state) := by
  have realized := nativeList_append_realizes (environment := environment) _ _ _ _
    (nativeList_append_realizes _ _ _ _
      (nativeList_append_realizes _ _ _ _
        (nativeList_append_realizes _ _ _ _
          (nativeList_append_realizes _ _ _ _
            (exchangeControls_realizes p.size)
            (offset_realizes p .exceptional .y (constantWord (-exceptionalSlope E Q))))
          (selectNormal_dagger_realizes p.size))
        (reflect_realizes p))
      (offset_realizes p .supplied .x (constantWord (Q.x + 1))))
    (offset_realizes p .supplied .y (constantWord (-Q.y)))
  have actual := nativeRealizes_ket (environment := environment) _ _ realized state
  simpa only [afterMultiplication, afterMultiplicationGates, Function.comp_apply,
    exchangeControlsStep_both_false p.size state inactive clean,
    offsetStep_exceptional_inactive p .y _ state (Or.inl inactive),
    selectNormalStep_inactive p.size state inactive, reflectStep_inactive p state inactive,
    offsetStep_inactive p .x _ state inactive, offsetStep_inactive p .y _ state inactive]
    using actual

/-- False C accepts every binary original X/Y word with the prescribed preparation. -/
private lemma beforeMultiplication_prepared_inactive {p : Nat}
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) (x y : Fin (2 ^ p.size)) :
    ((beforeMultiplication Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode (preparedRaw p false false x y))) =
      NormalizedVector.ket ((encoding p.size).encode (preparedRaw p false false x y)) :=
  beforeMultiplication_inactive Q (preparedRaw p false false x y) rfl rfl

/-- Native final cleanup preserves all inactive binary words and returns the full fixed frame. -/
private lemma afterMultiplication_prepared_inactive {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (x y : Fin (2 ^ p.size)) :
    ((afterMultiplication E Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode (preparedRaw p false false x y))) =
      NormalizedVector.ket ((encoding p.size).encode (preparedRaw p false false x y)) :=
  afterMultiplication_inactive E Q (preparedRaw p false false x y) rfl rfl

/-- The first native stage is a composition of complete real offset basis actions. -/
private lemma beforeDivision_realizes {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) :
    UnitaryCircuit.Realizes (encoding p.size) (beforeDivision Q) environment.quantum
      ((offsetStep p .supplied .y (constantWord (-Q.y))) ∘
        (offsetStep p .supplied .x (constantWord (-Q.x)))) :=
  nativeList_append_realizes _ _ _ _
    (offset_realizes p .supplied .x (constantWord (-Q.x)))
    (offset_realizes p .supplied .y (constantWord (-Q.y)))

/-- Real coordinate subtraction retains the complete prepared frame on the active input sector. -/
private lemma beforeDivision_prepared {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) (selector : Bool) (x y : Fin (2 ^ p.size)) :
    ((beforeDivision Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode (preparedRaw p true selector x y))) =
      NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p true selector
          (Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord p)
            (constantWord (p := p) (-Q.x)) x)
          (Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord p)
            (constantWord (p := p) (-Q.y)) y))) := by
  have actual := nativeRealizes_ket (environment := environment) _ _
    (beforeDivision_realizes Q)
    (preparedRaw p true selector x y)
  simpa only [Function.comp_apply, offsetStep_prepared_x, offsetStep_prepared_y] using actual

/-- The complete first stage fixes arbitrary data and arbitrary history on the inactive sector. -/
private lemma beforeDivision_inactive {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) (state : Raw p.size) (inactive : state.1.2 = false) :
    ((beforeDivision Q).binaryMatrix environment.quantum).apply (NormalizedVector.ket ((encoding
      p.size).encode state)) =
      NormalizedVector.ket ((encoding p.size).encode state) := by
  have actual := nativeRealizes_ket (environment := environment) _ _
    (beforeDivision_realizes Q) state
  simpa only [beforeMultiplication, beforeMultiplicationGates, Function.comp_apply,
    offsetStep_inactive p .x _ state inactive,
    offsetStep_inactive p .y _ state inactive] using actual

/-- Actual runtime coordinates retain the exact normalized action of every native frame program. -/
private lemma runtimeProgram_ket (width : Nat)
    (program : NativeCircuit width)
    (input output : Raw width)
    (actual : (program.binaryMatrix environment.quantum).apply (NormalizedVector.ket ((encoding
      width).encode input)) =
      NormalizedVector.ket ((encoding width).encode output)) :
    (runtimeProgram width program).applyNormalized environment.quantum
      (NormalizedVector.ket ((basis width).symm ((encoding width).encode input))) =
      NormalizedVector.ket ((basis width).symm ((encoding width).encode output)) := by
  apply NormalizedVector.ext
  intro row
  have column := congrArg (fun vector : NormalizedVector (Qubits (encoding width).width) =>
    vector (basis width row)) actual
  change (program.binaryMatrix environment.quantum).applyVec (NormalizedVector.ket ((encoding
    width).encode input)).vec
    (basis width row) = _ at column
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] at column
  change (runtimeProgram width program).applyVec environment.quantum
    (NormalizedVector.ket ((basis width).symm ((encoding width).encode input))).vec row = _
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    runtimeProgram_binary_matrix, Equiv.apply_symm_apply, column, NormalizedVector.ket_apply]
  have same : basis width row = (encoding width).encode output ↔
      row = (basis width).symm ((encoding width).encode output) := by
    constructor
    · intro equal
      exact (basis width).injective (equal.trans (Equiv.apply_symm_apply _ _).symm)
    · intro equal
      rw [equal, Equiv.apply_symm_apply]
  simp only [same]

/-- The native instruction acts on the complete joint reference register. -/
private def nativeJoint (width : Nat) (Reference : Register)
    (program : NativeCircuit width) :
    UnitaryOperator (Register.prod (context width).register Reference) :=
  UnitaryOperator.prodTensor ((runtimeProgram width program).matrix environment.quantum) (1 :
    UnitaryOperator Reference)

private lemma nativeCode_density (width : Nat) (program : NativeCircuit width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (allowAllocation : Bool := true) :
    ((nativeCode width program allowAllocation).execute environment Reference
      state).quantumMarginal =
      DensityOperator.applyUnitary (nativeJoint (environment := environment) width Reference
        program) state.quantumMarginal :=
  Circuit.unitary_jointDensity (environment := environment)
    (allowAllocation := allowAllocation) (runtimeProgram width program)
    state

private lemma reindex_marginal {Classical : Type} [Fintype Classical] {R S : Register}
    (state : ExecutionState Classical R) (coordinates : R.Index ≃ S.Index) :
    (state.reindex coordinates).quantumMarginal = state.quantumMarginal.reindex coordinates := by
  apply DensityOperator.ext
  ext row column
  change (∑ value, (state.block value).matrix.submatrix coordinates.symm coordinates.symm)
    row column =
    (∑ value, (state.block value).matrix) (coordinates.symm row) (coordinates.symm column)
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]

private lemma split_marginal (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference History) :
    (splitState (InPlaceControlled.context width) (selectorContext width) (selector_disjoint width)
      state).quantumMarginal = state.quantumMarginal.reindex
        (referenceBasis (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width) Reference) := by
  rw [splitState, reindex_marginal, ExecutionState.mapClassical_quantumMarginal]

private lemma splitService_marginal (width : Nat) {Reference : Register}
    {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State (context width) Reference (Hidden × History)) :
    (splitServiceState (InPlaceControlled.context width) (selectorContext width)
      (selector_disjoint width) state).quantumMarginal =
      state.quantumMarginal.reindex
        (referenceBasis (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width) Reference) := by
  rw [splitServiceState, State.mapHistory_quantumMarginal, split_marginal]

/-- Mathematical arithmetic retains the physical selector through the exact union basis. -/
private def arithmeticTarget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) :
    UnitaryOperator (Register.prod (context modulus.size).register Reference) :=
  UnitaryOperator.reindex
    (referenceBasis (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
      (selector_disjoint modulus.size) Reference).symm
    (InPlaceControlled.target operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference))

/-- The actual framed measured call preserves all mixed control/selector/reference coherences. -/
private lemma arithmetic_density (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ original : (Register.prod (context modulus.size).register Reference).Index,
      ¬InPlaceControlled.admissible modulus
        ((unionBasisEquiv (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
          (selector_disjoint modulus.size) original.1).1) →
        state.quantumMarginal.matrix original original = 0)
    (allowAllocation : Bool := true) :
    ((arithmetic operation modulus prime allowAllocation).execute environment Reference
      state).quantumMarginal =
      DensityOperator.applyUnitary (arithmeticTarget operation modulus prime Reference)
        state.quantumMarginal := by
  classical
  let placement := ContextEmbedding.alongUnion (InPlaceControlled.context modulus.size)
    (selectorContext modulus.size) (selector_disjoint modulus.size)
  let coordinates := placement.referenceBasis Reference
  let localState := (placement.split state).mapHistory
    (fun record => (record.2.1, (record.1, record.2.2)))
  have coordinatesSame : coordinates =
      referenceBasis (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
        (selector_disjoint modulus.size) Reference :=
    ContextEmbedding.alongUnion_referenceBasis _ _ _ Reference
  have splitMarginal {K : Type} [Fintype K]
      (initial : State (context modulus.size) Reference K) :
      (placement.split initial).quantumMarginal = initial.quantumMarginal.reindex coordinates := by
    rw [ContextEmbedding.split, reindex_marginal, ExecutionState.mapClassical_quantumMarginal]
  have localMarginal : localState.quantumMarginal =
      state.quantumMarginal.reindex coordinates := by
    exact (State.mapHistory_quantumMarginal _ _).trans (splitMarginal state)
  have localSupport : ∀ original :
      (Register.prod (InPlaceControlled.context modulus.size).register
        (Register.prod (selectorContext modulus.size).register Reference)).Index,
      ¬InPlaceControlled.admissible modulus original.1 →
        localState.quantumMarginal.matrix original original = 0 := by
    intro original absent
    have entry : localState.quantumMarginal.matrix original original =
        state.quantumMarginal.matrix (coordinates.symm original) (coordinates.symm original) :=
      (congrArg (fun density : DensityOperator
        (Register.prod (InPlaceControlled.context modulus.size).register
          (Register.prod (selectorContext modulus.size).register Reference)) =>
          density.matrix original original) localMarginal).trans
        (DensityOperator.reindex_entry state.quantumMarginal coordinates original original)
    apply entry.trans
    apply support
    have projection :
        (unionBasisEquiv (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
          (selector_disjoint modulus.size) (coordinates.symm original).1).1 = original.1 := by
      rw [coordinatesSame]
      change ((unionBasisEquiv _ _ (selector_disjoint modulus.size))
        ((unionBasisEquiv _ _ (selector_disjoint modulus.size)).symm
          (original.1, original.2.1))).1 = original.1
      rw [Equiv.apply_symm_apply]
    intro present
    exact absent (projection ▸ present)
  have originalRun := InPlaceControlled.body_density (environment := environment) operation
    modulus prime localState
    localSupport (allowAllocation := false)
  have natural := Circuit.split_execute_embed_history (environment := environment)
    (allowAllocation := allowAllocation)
    placement (InPlaceControlled.body operation modulus prime (allowAllocation := false))
    Reference state
  have averaged := congrArg (fun output => output.quantumMarginal) natural
  simp only [State.mapHistory_quantumMarginal] at averaged
  change (placement.split
      ((arithmetic operation modulus prime allowAllocation).execute environment Reference
        state)).quantumMarginal =
    ((InPlaceControlled.body operation modulus prime (allowAllocation := false)).execute environment
      (placement.frame.register.prod Reference) localState).quantumMarginal at averaged
  rw [splitMarginal, originalRun, localMarginal] at averaged
  have restored := congrArg
    (fun density : DensityOperator
        (Register.prod (InPlaceControlled.context modulus.size).register
          (Register.prod (selectorContext modulus.size).register Reference)) =>
      density.reindex (S := Register.prod (context modulus.size).register Reference)
        coordinates.symm) averaged
  have cancel (density : DensityOperator
      (Register.prod (context modulus.size).register Reference)) :
      (density.reindex (S := Register.prod (InPlaceControlled.context modulus.size).register
        (Register.prod (selectorContext modulus.size).register Reference)) coordinates).reindex
          (S := Register.prod (context modulus.size).register Reference) coordinates.symm =
            density := by
    calc
      _ = density.reindex (S := Register.prod (context modulus.size).register Reference)
          (coordinates.trans coordinates.symm) :=
        DensityOperator.reindex_trans density coordinates coordinates.symm
      _ = density := by rw [Equiv.self_trans_symm, DensityOperator.reindex_refl]
  have transported := DensityOperator.applyUnitary_reindex
    (S := Register.prod (context modulus.size).register Reference)
    (InPlaceControlled.target operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference))
    (state.quantumMarginal.reindex
      (S := Register.prod (InPlaceControlled.context modulus.size).register
        (Register.prod (selectorContext modulus.size).register Reference)) coordinates)
      coordinates.symm
  have restoredCanonical :=
    (cancel ((arithmetic operation modulus prime allowAllocation).execute environment Reference
      state).quantumMarginal).symm.trans
      (restored.trans (transported.trans
        (congrArg (DensityOperator.applyUnitary
          (UnitaryOperator.reindex
            (S := Register.prod (context modulus.size).register Reference) coordinates.symm
            (InPlaceControlled.target operation modulus prime
              (Register.prod (selectorContext modulus.size).register Reference))))
          (cancel state.quantumMarginal))))
  have targetSame :
      UnitaryOperator.reindex
        (S := Register.prod (context modulus.size).register Reference) coordinates.symm
        (InPlaceControlled.target operation modulus prime
          (Register.prod (selectorContext modulus.size).register Reference)) =
        arithmeticTarget operation modulus prime Reference := by
    rw [coordinatesSame]
    rfl
  exact restoredCanonical.trans
    (congrArg (fun operator : UnitaryOperator
      (Register.prod (context modulus.size).register Reference) =>
        DensityOperator.applyUnitary operator state.quantumMarginal) targetSame)

private lemma operator_reindex_ket {R S : Register}
    (coordinates : R.Index ≃ S.Index) (operator : UnitaryOperator R)
    (input output : R.Index)
    (action : operator.applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket output).vec) :
    (UnitaryOperator.reindex coordinates operator).applyVec
      (NormalizedVector.ket (coordinates input)).vec =
      (NormalizedVector.ket (coordinates output)).vec := by
  ext row
  have column := congrArg (fun vector : HilbertVector R => vector (coordinates.symm row)) action
  change HilbertOperator.applyVec (operator : HilbertOperator R)
    (NormalizedVector.ket input).vec (coordinates.symm row) = _ at column
  rw [HilbertOperator.applyVec_ket] at column
  change HilbertOperator.applyVec
    (UnitaryOperator.reindex coordinates operator : HilbertOperator S)
    (NormalizedVector.ket (coordinates input)).vec row = _
  rw [HilbertOperator.applyVec_ket]
  change operator (coordinates.symm row) (coordinates.symm (coordinates input)) = _
  rw [Equiv.symm_apply_apply, column, NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  have same : coordinates.symm row = output ↔ row = coordinates output := by
    constructor
    · intro equal
      exact (coordinates.apply_symm_apply row).symm.trans (congrArg coordinates equal)
    · intro equal
      rw [equal, Equiv.symm_apply_apply]
  simp only [same]

private lemma operator_controlled_ket {R : Register} (Control : Register)
    (activation : Control.Index) (operator : UnitaryOperator R)
    (control : Control.Index) (input output : R.Index)
    (action : operator.applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket output).vec) :
    (UnitaryOperator.controlled Control activation operator).applyVec
      (NormalizedVector.ket (control, input)).vec =
      (NormalizedVector.ket (control, if control = activation then output else input)).vec := by
  ext row
  have column := congrArg (fun vector : HilbertVector R => vector row.2) action
  change HilbertOperator.applyVec (operator : HilbertOperator R)
    (NormalizedVector.ket input).vec row.2 = _ at column
  rw [HilbertOperator.applyVec_ket] at column
  change HilbertOperator.applyVec
    (UnitaryOperator.controlled Control activation operator :
      HilbertOperator (Register.prod Control R))
    (NormalizedVector.ket (control, input)).vec row = _
  rw [HilbertOperator.applyVec_ket, UnitaryOperator.controlled_apply]
  by_cases sameControl : row.1 = control
  · rw [if_pos sameControl]
    have pair (value : R.Index) : row = (control, value) ↔ row.2 = value := by
      constructor
      · exact congrArg Prod.snd
      · intro equal
        exact Prod.ext sameControl equal
    by_cases active : control = activation
    · rw [if_pos (sameControl.trans active), if_pos active, column,
        NormalizedVector.ket_apply, NormalizedVector.ket_apply]
      simp only [pair]
    · have inactive : row.1 ≠ activation := fun equal => active (sameControl.symm.trans equal)
      rw [if_neg inactive, if_neg active, NormalizedVector.ket_apply]
      simp only [pair]
  · rw [if_neg sameControl, NormalizedVector.ket_apply]
    exact (if_neg (fun equal => sameControl (congrArg Prod.fst equal))).symm

private lemma controlledTarget_prepared_ket
    (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (control : Fin 2) (value numerator : Fin (2 ^ modulus.size))
    {Reference : Register} (reference : Reference.Index) :
    (InPlaceControlled.target operation modulus prime Reference).applyVec
      (NormalizedVector.ket
        (InPlaceControlled.label modulus.size control
          (InPlaceTarget.preparedBasis modulus value numerator), reference)).vec =
      (NormalizedVector.ket
        (InPlaceControlled.label modulus.size control
          (InPlaceTarget.preparedBasis modulus value
            (if control = 1 then InPlaceTarget.resultWord operation modulus prime value numerator
             else numerator)), reference)).vec := by
  let coordinates := ((InPlaceControlled.jointCoordinates modulus.size Reference).trans
    (Equiv.prodComm _ _)).symm
  have restored (original : (NumeratorMeasurement.context modulus.size).register.Index) :
      coordinates (control, (original, reference)) =
        (InPlaceControlled.label modulus.size control original, reference) := by
    apply ((InPlaceControlled.jointCoordinates modulus.size Reference).trans
      (Equiv.prodComm _ _)).injective
    change ((InPlaceControlled.jointCoordinates modulus.size Reference).trans
      (Equiv.prodComm _ _))
        (((InPlaceControlled.jointCoordinates modulus.size Reference).trans
          (Equiv.prodComm _ _)).symm (control, (original, reference))) = _
    rw [Equiv.apply_symm_apply]
    change (control, (original, reference)) =
      (Equiv.prodComm _ _) (InPlaceControlled.jointCoordinates modulus.size Reference
        (InPlaceControlled.label modulus.size control original, reference))
    rw [InPlaceControlled.jointCoordinates_label]
    rfl
  have active := operator_controlled_ket (Qubits 1) (1 : Fin 2)
    (InPlaceTarget.jointOperator operation modulus prime Reference) control
    (InPlaceTarget.preparedBasis modulus value numerator, reference)
    (InPlaceTarget.preparedBasis modulus value
      (InPlaceTarget.resultWord operation modulus prime value numerator), reference)
    (InPlaceTarget.prepared_operator_ket operation modulus prime value numerator reference)
  have transported := operator_reindex_ket
    (S := Register.prod (InPlaceControlled.context modulus.size).register Reference)
    coordinates
    (UnitaryOperator.controlled (Qubits 1) (1 : Fin 2)
      (InPlaceTarget.jointOperator operation modulus prime Reference)) _ _ active
  change (InPlaceControlled.target operation modulus prime Reference).applyVec _ = _
    at transported
  by_cases selected : control = 1
  · simpa only [if_pos selected, restored] using transported
  · simpa only [if_neg selected, restored] using transported

private lemma arithmeticTarget_prepared_ket
    (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (control selector : Fin 2) (value numerator : Fin (2 ^ modulus.size))
    {Reference : Register} (reference : Reference.Index) :
    (arithmeticTarget operation modulus prime Reference).applyVec
      (NormalizedVector.ket
        (label modulus.size control selector
          (InPlaceTarget.preparedBasis modulus value numerator), reference)).vec =
      (NormalizedVector.ket
        (label modulus.size control selector
          (InPlaceTarget.preparedBasis modulus value
            (if control = 1 then InPlaceTarget.resultWord operation modulus prime value numerator
             else numerator)), reference)).vec := by
  let coordinates := (referenceBasis (InPlaceControlled.context modulus.size)
    (selectorContext modulus.size) (selector_disjoint modulus.size) Reference).symm
  have restored (original : (NumeratorMeasurement.context modulus.size).register.Index) :
      coordinates (InPlaceControlled.label modulus.size control original,
        ((selectorBasis modulus.size).symm selector, reference)) =
        (label modulus.size control selector original, reference) := by
    rfl
  have original := controlledTarget_prepared_ket operation modulus prime control value numerator
    (Reference := Register.prod (selectorContext modulus.size).register Reference)
    ((selectorBasis modulus.size).symm selector, reference)
  have transported := operator_reindex_ket
    (S := Register.prod (context modulus.size).register Reference) coordinates
    (InPlaceControlled.target operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference)) _ _ original
  change (arithmeticTarget operation modulus prime Reference).applyVec _ = _ at transported
  simpa only [restored] using transported

/- This matrix form deliberately needs no output map or injectivity claim. -/
private lemma applyUnitary_support_of_columns {R : Register}
    (state : DensityOperator R) (operator : UnitaryOperator R)
    (inputAllowed outputAllowed : R.Index → Prop)
    (support : ∀ input, ¬inputAllowed input → state.matrix input input = 0)
    (columns : ∀ input, inputAllowed input → ∀ output, ¬outputAllowed output →
      operator output input = 0) :
    ∀ output, ¬outputAllowed output →
      (DensityOperator.applyUnitary operator state).matrix output output = 0 := by
  intro output absent
  change ((operator : HilbertOperator R) * state.matrix *
    (operator : HilbertOperator R).conjTranspose) output output = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro column _
  have vanished : ((operator : HilbertOperator R) * state.matrix) output column = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro input _
    by_cases present : inputAllowed input
    · rw [columns input present output absent, zero_mul]
    · rw [DensityOperator.row_zero_of_diagonal_zero state input
        (support input present) column, mul_zero]
  rw [vanished, zero_mul]

/- The call sites supply one actual normalized output label for each original input. -/
private lemma applyUnitary_support_of_kets {R : Register}
    (state : DensityOperator R) (operator : UnitaryOperator R)
    (inputAllowed outputAllowed : R.Index → Prop)
    (support : ∀ input, ¬inputAllowed input → state.matrix input input = 0)
    (action : ∀ input, inputAllowed input → ∃ output, outputAllowed output ∧
      operator.applyVec (NormalizedVector.ket input).vec =
        (NormalizedVector.ket output).vec) :
    ∀ output, ¬outputAllowed output →
      (DensityOperator.applyUnitary operator state).matrix output output = 0 := by
  apply applyUnitary_support_of_columns state operator inputAllowed outputAllowed support
  intro input present row absent
  obtain ⟨output, allowed, actual⟩ := action input present
  have column := congrArg (fun vector : HilbertVector R => vector row) actual
  change HilbertOperator.applyVec (operator : HilbertOperator R)
    (NormalizedVector.ket input).vec row = _ at column
  rw [HilbertOperator.applyVec_ket] at column
  rw [column, NormalizedVector.ket_apply]
  apply if_neg
  intro equal
  exact absent (equal.symm ▸ allowed)

/- Arbitrary external references are retained without a tensor-state assumption. -/
private lemma operator_prodTensor_identity_ket {R Reference : Register}
    (operator : UnitaryOperator R) (input output : R.Index) (reference : Reference.Index)
    (action : operator.applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket output).vec) :
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)).applyVec
      (NormalizedVector.ket (input, reference)).vec =
      (NormalizedVector.ket (output, reference)).vec := by
  ext row
  have column := congrArg (fun vector : HilbertVector R => vector row.1) action
  change HilbertOperator.applyVec (operator : HilbertOperator R)
    (NormalizedVector.ket input).vec row.1 = _ at column
  rw [HilbertOperator.applyVec_ket] at column
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod R Reference))
    (NormalizedVector.ket (input, reference)).vec row = _
  rw [HilbertOperator.applyVec_ket, UnitaryOperator.prodTensor_apply, column]
  change (NormalizedVector.ket output) row.1 *
    (if row.2 = reference then 1 else 0) = (NormalizedVector.ket (output, reference)) row
  rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  have pair : row = (output, reference) ↔ row.1 = output ∧ row.2 = reference := by
    constructor
    · intro equal
      exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩
    · intro equal
      exact Prod.ext equal.1 equal.2
  simp only [pair]
  by_cases same : row.1 = output <;> by_cases retained : row.2 = reference <;>
    simp only [same, retained, ite_true, ite_false, true_and, false_and, mul_one, mul_zero]

/-- Independent modular translation of one complete finite word, fixing its padding labels. -/
private def wordTranslation {p : Nat} [Fact p.Prime] (constant : ZMod p) :
    Equiv.Perm (Fin (2 ^ p.size)) :=
  Nat.FixedWidth.modularWordEquiv (InPlaceTarget.modulusWord p)
    ⟨constant.val, (ZMod.val_lt constant).trans (Nat.lt_succ_self p)⟩

private def coordinateTranslation {p : Nat} [Fact p.Prime] (x y : ZMod p) :
    Equiv.Perm (Fin (2 ^ p.size) × Fin (2 ^ p.size)) :=
  Equiv.prodCongr (wordTranslation x) (wordTranslation y)

private def squareTranslation {p : Nat} [Fact p.Prime] :
    Equiv.Perm (Fin (2 ^ p.size) × Fin (2 ^ p.size)) :=
  Equiv.prodCongrLeft fun y => wordTranslation (-((y.val : ZMod p) ^ 2))

/-- The independent exceptional second operation is a residue translation when D is zero. -/
private def secondProduct {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : Equiv.Perm (Fin (2 ^ p.size) × Fin (2 ^ p.size)) :=
  Equiv.prodCongrRight fun x => if x.val = 0 then wordTranslation (-exceptionalSlope E Q)
    else Nat.FixedWidth.unitProductWordPerm (InPlaceTarget.modulusWord p)
      (show 0 < (InPlaceTarget.modulusWord p).val from (Fact.out : Nat.Prime p).pos)
      (Nat.FixedWidth.PrimeWordProduct.factorUnit (InPlaceTarget.modulusWord p)
        (show Nat.Prime (InPlaceTarget.modulusWord p).val from (Fact.out : Nat.Prime p)) x)

/-- Independent reversible word arithmetic specifies the complete affine translation target. -/
def translationWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : Equiv.Perm (Fin (2 ^ p.size) × Fin (2 ^ p.size)) :=
  (coordinateTranslation (-Q.x) (-Q.y)).trans
    ((InPlaceTarget.words .division p Fact.out).trans
      ((Equiv.prodCongr (wordTranslation (3 * Q.x)) (Equiv.refl _)).trans
        (squareTranslation.trans ((secondProduct E Q).trans
          ((Equiv.prodCongr (Nat.FixedWidth.pivotWordEquiv (InPlaceTarget.modulusWord p))
            (Equiv.refl _)).trans (coordinateTranslation (Q.x + 1) (-Q.y)))))))

/-- Canonical field values use exactly the original n-bit mathematical word. -/
private def fieldWord {p : Nat} [Fact p.Prime] (value : ZMod p) : Fin (2 ^ p.size) :=
  ⟨value.val, (ZMod.val_lt value).trans (Nat.lt_size_self p)⟩

private lemma fieldWord_cast {p : Nat} [Fact p.Prime] (value : ZMod p) :
    ((fieldWord value).val : ZMod p) = value := ZMod.natCast_zmod_val value

private lemma wordTranslation_fieldWord {p : Nat} [Fact p.Prime] (constant value : ZMod p) :
    wordTranslation constant (fieldWord value) = fieldWord (value + constant) := by
  apply Fin.ext
  rw [wordTranslation, Nat.FixedWidth.modularWordEquiv_apply]
  exact (Nat.FixedWidth.gidneyModularWord_valid (InPlaceTarget.modulusWord p)
    ⟨constant.val, (ZMod.val_lt constant).trans (Nat.lt_succ_self p)⟩
    (fieldWord value) (ZMod.val_lt value)).trans (ZMod.val_add value constant).symm

private lemma coordinateTranslation_fieldWords {p : Nat} [Fact p.Prime]
    (dx dy x y : ZMod p) :
    coordinateTranslation dx dy (fieldWord x, fieldWord y) =
      (fieldWord (x + dx), fieldWord (y + dy)) :=
  Prod.ext (wordTranslation_fieldWord dx x) (wordTranslation_fieldWord dy y)

private lemma squareTranslation_fieldWords {p : Nat} [Fact p.Prime] (x y : ZMod p) :
    squareTranslation (fieldWord x, fieldWord y) =
      (fieldWord (x - y ^ 2), fieldWord y) := by
  change (wordTranslation (-(((fieldWord y).val : ZMod p) ^ 2)) (fieldWord x), fieldWord y) = _
  rw [fieldWord_cast, wordTranslation_fieldWord]
  simp only [sub_eq_add_neg]

private lemma division_fieldWords {p : Nat} [Fact p.Prime] (x y : ZMod p) (nonzero : x ≠ 0) :
    InPlaceTarget.words .division p Fact.out (fieldWord x, fieldWord y) =
      (fieldWord x, fieldWord (y / x)) := by
  apply Prod.ext
  · exact InPlaceTarget.words_first _ _ _ _
  · apply Fin.ext
    change (InPlaceTarget.resultWord .division p Fact.out (fieldWord x) (fieldWord y)).val = _
    have actual := InPlaceTarget.division_value p Fact.out (fieldWord x) (fieldWord y)
      (ZMod.val_pos.mpr nonzero) (ZMod.val_lt x) (ZMod.val_lt y)
    rw [fieldWord_cast] at actual
    calc
      _ = ((x⁻¹).val * y.val) % p := actual
      _ = (x⁻¹ * y).val := (ZMod.val_mul _ _).symm
      _ = (y / x).val := by rw [div_eq_mul_inv, mul_comm]

private lemma multiplication_fieldWords {p : Nat} [Fact p.Prime]
    (x y : ZMod p) (nonzero : x ≠ 0) :
    InPlaceTarget.words .multiplication p Fact.out (fieldWord x, fieldWord y) =
      (fieldWord x, fieldWord (x * y)) := by
  apply Prod.ext
  · exact InPlaceTarget.words_first _ _ _ _
  · apply Fin.ext
    exact (InPlaceTarget.multiplication_value p Fact.out (fieldWord x) (fieldWord y)
      (ZMod.val_pos.mpr nonzero) (ZMod.val_lt x) (ZMod.val_lt y)).trans (ZMod.val_mul x y).symm

private lemma secondProduct_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (x y : ZMod p) :
    secondProduct E Q (fieldWord x, fieldWord y) =
      (fieldWord x, fieldWord (if x = 0 then y - exceptionalSlope E Q else x * y)) := by
  by_cases zero : x = 0
  · subst x
    change (fieldWord 0, (if (fieldWord (0 : ZMod p)).val = 0 then
      wordTranslation (-exceptionalSlope E Q) else _ ) (fieldWord y)) = _
    have same : (fieldWord (0 : ZMod p)).val = 0 := by simp [fieldWord]
    rw [if_pos same, if_pos rfl, wordTranslation_fieldWord]
    simp only [sub_eq_add_neg]
  · have nonzero : (fieldWord x).val ≠ 0 := Nat.ne_of_gt (ZMod.val_pos.mpr zero)
    change (fieldWord x, (if (fieldWord x).val = 0 then
      wordTranslation (-exceptionalSlope E Q) else _) (fieldWord y)) = _
    rw [if_neg nonzero, if_neg zero]
    exact multiplication_fieldWords x y zero

private lemma pivot_fieldWord {p : Nat} [Fact p.Prime] (value : ZMod p) :
    Nat.FixedWidth.pivotWordEquiv (InPlaceTarget.modulusWord p) (fieldWord value) =
      fieldWord (-value - 1) := by
  have bounded := ZMod.val_lt value
  have positive := (Fact.out : Nat.Prime p).pos
  have remainderBound : p - 1 - value.val < p := by omega
  have cast : ((p - 1 - value.val : Nat) : ZMod p) = -value - 1 := by
    rw [Nat.cast_sub (by omega : value.val ≤ p - 1), Nat.cast_sub (by omega : 1 ≤ p)]
    simp only [Nat.cast_one, ZMod.natCast_self, ZMod.natCast_zmod_val]
    ring
  apply Fin.ext
  change Nat.FixedWidth.pivotFlip p value.val = (-value - 1).val
  rw [Nat.FixedWidth.pivotFlip, if_pos bounded, ← cast, ZMod.val_natCast_of_lt remainderBound]
  omega

private def controlLabel (control : Bool) : Fin 2 := BinaryLabelEncoding.bool.encode control

private lemma nativeJoint_prepared_ket {p : Nat}
    (program : NativeCircuit p.size)
    (control selector nextControl nextSelector : Bool)
    (x y nextX nextY : Fin (2 ^ p.size))
    {Reference : Register} (reference : Reference.Index)
    (actual : (program.binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode (preparedRaw p control selector x y))) =
      NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p nextControl nextSelector nextX nextY))) :
    (nativeJoint (environment := environment) p.size Reference program).applyVec
      (NormalizedVector.ket (label p.size (controlLabel control)
        (controlLabel selector) (InPlaceTarget.preparedBasis p x y),
          reference)).vec =
      (NormalizedVector.ket (label p.size (controlLabel nextControl)
        (controlLabel nextSelector)
          (InPlaceTarget.preparedBasis p nextX nextY), reference)).vec := by
  have runtime := runtimeProgram_ket p.size program _ _ actual
  rw [preparedRaw_label, preparedRaw_label] at runtime
  apply operator_prodTensor_identity_ket
  exact congrArg NormalizedVector.vec runtime

private lemma modularOutput_fieldWord {p : Nat} [Fact p.Prime] (constant value : ZMod p) :
    Nat.FixedWidth.modularWordOutput (InPlaceArithmetic.modulusWord p)
      (constantWord (p := p) constant) (fieldWord value) = fieldWord (value + constant) := by
  have actual := wordTranslation_fieldWord constant value
  rw [wordTranslation, Nat.FixedWidth.modularWordEquiv_apply] at actual
  exact actual

private lemma pivotOutput_fieldWord {p : Nat} [Fact p.Prime] (value : ZMod p) :
    Nat.FixedWidth.pivotWordOutput (InPlaceArithmetic.modulusWord p) (fieldWord value) =
      fieldWord (-value - 1) := pivot_fieldWord value

private lemma square_subtraction_residue {p : Nat} [Fact p.Prime] (x y : ZMod p) :
    ((fieldWord (x - y ^ 2)).val + (fieldWord y).val * (fieldWord y).val) % p =
      (fieldWord x).val := by
  have value : x - y ^ 2 + y * y = x := by ring
  have actual := congrArg ZMod.val value
  rw [ZMod.val_add, ZMod.val_mul] at actual
  change ((x - y ^ 2).val + y.val * y.val) % p = x.val
  rw [← Nat.add_mod_mod]
  exact actual

private lemma selectNormalStep_prepared (modulus : Nat) (control selector : Bool)
    (x y : Fin (2 ^ modulus.size)) :
    selectNormalStep modulus.size (preparedRaw modulus control selector x y) =
      preparedRaw modulus control (selector ^^ (control && decide (x.val ≠ 0))) x y := by
  have input := preparedRaw_coordinate modulus control selector x y .x
  change ProductReadout.input modulus.size (preparedRaw modulus control selector x y).1.1 = x
    at input
  change (_, selector ^^ (control && decide
    ((ProductReadout.input modulus.size (preparedRaw modulus control selector x y).1.1).val ≠ 0)))
      = _
  rw [input]
  rfl

private lemma selectNormalStep_fieldWords {p : Nat} [Fact p.Prime]
    (control selector : Bool) (x y : ZMod p) :
    selectNormalStep p.size (preparedRaw p control selector (fieldWord x) (fieldWord y)) =
      preparedRaw p control (selector ^^ (control && decide (x ≠ 0)))
        (fieldWord x) (fieldWord y) := by
  rw [selectNormalStep_prepared]
  have same : decide ((fieldWord x).val ≠ 0) = decide (x ≠ 0) := by
    change decide (x.val ≠ 0) = decide (x ≠ 0)
    simp only [ZMod.val_ne_zero]
  rw [same]

private lemma exchangeControlsStep_prepared (modulus : Nat) (control selector : Bool)
    (x y : Fin (2 ^ modulus.size)) :
    exchangeControlsStep modulus.size (preparedRaw modulus control selector x y) =
      preparedRaw modulus selector control x y := rfl

private lemma beforeDivision_fieldWords {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) (x y : ZMod p) :
    ((beforeDivision Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p true false (fieldWord x) (fieldWord y)))) =
      NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p true false (fieldWord (x - Q.x)) (fieldWord (y - Q.y)))) := by
  have actual := beforeDivision_prepared (environment := environment)
    Q false (fieldWord x) (fieldWord y)
  simpa only [modularOutput_fieldWord, sub_eq_add_neg] using actual

-- Keep instruction lists opaque while rewriting their already proved all-label actions.
attribute [local irreducible] offsetGates subtractSquareGates selectNormalGates
  exchangeControlGates reflectGates

private lemma beforeMultiplication_fieldWords {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) (x y : ZMod p) :
    ((beforeMultiplication Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p true false (fieldWord x) (fieldWord y)))) =
      NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p (decide (x + 3 * Q.x - y ^ 2 ≠ 0)) true
          (fieldWord (x + 3 * Q.x - y ^ 2)) (fieldWord y))) := by
  simp only [beforeMultiplication, beforeMultiplicationGates,
    nativeList_binary_append, binary_apply_mul]
  erw [nativeRealizes_ket (environment := environment) _ _
    (offset_realizes p .supplied .x (constantWord (3 * Q.x)))]
  rw [offsetStep_prepared_x, modularOutput_fieldWord]
  erw [subtractSquare_prepared (environment := environment) p false
    (fieldWord (x + 3 * Q.x)) (fieldWord y)
    (fieldWord (x + 3 * Q.x - y ^ 2)) (ZMod.val_lt _)
    (square_subtraction_residue (x + 3 * Q.x) y)]
  erw [nativeRealizes_ket (environment := environment) _ _ (selectNormal_realizes p.size)]
  rw [selectNormalStep_fieldWords]
  erw [nativeRealizes_ket (environment := environment) _ _ (exchangeControls_realizes p.size)]
  rw [exchangeControlsStep_prepared]
  simp only [Bool.true_and, Bool.false_xor]

private lemma afterMultiplication_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (x y : ZMod p) :
    ((afterMultiplication E Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p (decide (x ≠ 0)) true (fieldWord x) (fieldWord y)))) =
      NormalizedVector.ket ((encoding p.size).encode
        (preparedRaw p true false (fieldWord (Q.x - x))
          (fieldWord ((if x = 0 then y - exceptionalSlope E Q else y) - Q.y)))) := by
  rw [nativeRealizes_ket _ _ (afterMultiplication_realizes E Q)]
  apply congrArg (fun state : Raw p.size =>
    NormalizedVector.ket (R := Qubits (encoding p.size).width) ((encoding p.size).encode state))
  dsimp only [afterMultiplicationStep, Function.comp_apply]
  rw [exchangeControlsStep_prepared]
  by_cases zero : x = 0
  · have inactive : decide (x ≠ 0) = false := by simp only [zero, ne_eq, not_true_eq_false,
      decide_false]
    rw [inactive, offsetStep_exceptional_prepared, modularOutput_fieldWord,
      selectNormalStep_fieldWords]
    rw [inactive]
    rw [reflectStep_prepared, pivotOutput_fieldWord,
      offsetStep_prepared_x, modularOutput_fieldWord,
      offsetStep_prepared_y, modularOutput_fieldWord, if_pos zero]
    have restored : -x - 1 + (Q.x + 1) = Q.x - x := by ring
    rw [restored]
    simp only [sub_eq_add_neg, Bool.true_and, Bool.xor_self]
  · have active : decide (x ≠ 0) = true := decide_eq_true zero
    rw [active, offsetStep_exceptional_inactive p .y _ _ (Or.inr rfl), selectNormalStep_fieldWords,
      active]
    rw [reflectStep_prepared, pivotOutput_fieldWord,
      offsetStep_prepared_x, modularOutput_fieldWord,
      offsetStep_prepared_y, modularOutput_fieldWord, if_neg zero]
    have restored : -x - 1 + (Q.x + 1) = Q.x - x := by ring
    rw [restored]
    simp only [sub_eq_add_neg, Bool.true_and, Bool.xor_self]

/-- Independent finite-word arithmetic agrees with the field formula on its original domain. -/
private lemma translationWords_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (x y : ZMod p) (nonzero : firstDifference x Q.x ≠ 0) :
    translationWords E Q (fieldWord x, fieldWord y) =
      (fieldWord (fieldOutput E Q true x y).1, fieldWord (fieldOutput E Q true x y).2) := by
  let a := x - Q.x
  let b := y - Q.y
  let quotient := b / a
  let difference := a + 3 * Q.x - quotient ^ 2
  let ordinate := if difference = 0 then quotient - exceptionalSlope E Q else difference * quotient
  have first : coordinateTranslation (-Q.x) (-Q.y) (fieldWord x, fieldWord y) =
      (fieldWord a, fieldWord b) := by
    simpa only [a, b, sub_eq_add_neg] using coordinateTranslation_fieldWords (-Q.x) (-Q.y) x y
  have offset : (Equiv.prodCongr (wordTranslation (3 * Q.x)) (Equiv.refl _))
      (fieldWord a, fieldWord quotient) = (fieldWord (a + 3 * Q.x), fieldWord quotient) :=
    Prod.ext (wordTranslation_fieldWord _ _) rfl
  change coordinateTranslation (Q.x + 1) (-Q.y)
    ((Equiv.prodCongr (Nat.FixedWidth.pivotWordEquiv (InPlaceTarget.modulusWord p)) (Equiv.refl _))
      (secondProduct E Q (squareTranslation
        ((Equiv.prodCongr (wordTranslation (3 * Q.x)) (Equiv.refl _))
          (InPlaceTarget.words .division p Fact.out
            (coordinateTranslation (-Q.x) (-Q.y) (fieldWord x, fieldWord y))))))) = _
  rw [first, division_fieldWords a b nonzero, offset, squareTranslation_fieldWords,
    secondProduct_fieldWords]
  change coordinateTranslation (Q.x + 1) (-Q.y)
    (Nat.FixedWidth.pivotWordEquiv (InPlaceTarget.modulusWord p) (fieldWord difference),
      fieldWord ordinate) = _
  rw [pivot_fieldWord, coordinateTranslation_fieldWords]
  have output : fieldOutput E Q true x y = (Q.x - difference, ordinate - Q.y) := rfl
  rw [output]
  apply Prod.ext
  · apply congrArg fieldWord
    ring
  · apply congrArg fieldWord
    exact (sub_eq_add_neg ordinate Q.y).symm

private abbrev OriginalAuxiliary (width : Nat) :=
  (MAU.Inversion.SharedEEA.InputPreparation.auxiliaryLayout width).register.Index

private abbrev Coordinates (width : Nat) :=
  ((OriginalAuxiliary width × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin 2) × Fin 2

/-- The mathematical coordinates retain every original auxiliary bit and both actual controls. -/
private def targetCoordinates (width : Nat) : (context width).register.Index ≃ Coordinates width :=
  (unionBasisEquiv (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width)).trans
      (Equiv.prodCongr
        ((unionBasisEquiv (NumeratorMeasurement.context width)
          (InPlaceControlled.controlContext width)
          (InPlaceControlled.control_disjoint width)).trans
            (Equiv.prodCongr (InPlaceTarget.frameEquiv width).symm
              (InPlaceControlled.controlBasis width)))
        (selectorBasis width))

private def controlledWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) :
    Equiv.Perm ((Fin (2 ^ p.size) × Fin (2 ^ p.size)) × Fin 2) :=
  Equiv.prodCongrLeft fun control => if control = 1 then translationWords E Q else Equiv.refl _

private def targetFields {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : Equiv.Perm (Coordinates p.size) :=
  Equiv.prodCongr
      ((Equiv.prodAssoc (OriginalAuxiliary p.size)
        (Fin (2 ^ p.size) × Fin (2 ^ p.size)) (Fin 2)).trans
          ((Equiv.prodCongr (Equiv.refl _) (controlledWords E Q)).trans
            (Equiv.prodAssoc (OriginalAuxiliary p.size)
              (Fin (2 ^ p.size) × Fin (2 ^ p.size)) (Fin 2)).symm))
      (Equiv.refl _)

private def targetPermutation {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : Equiv.Perm (context p.size).register.Index :=
  (targetCoordinates p.size).trans ((targetFields E Q).trans (targetCoordinates p.size).symm)

private lemma targetCoordinates_label (width : Nat) (control selector : Fin 2)
    (fresh : OriginalAuxiliary width) (words : Fin (2 ^ width) × Fin (2 ^ width)) :
    targetCoordinates width
      (label width control selector (InPlaceTarget.frameEquiv width (fresh, words))) =
      (((fresh, words), control), selector) := by
  simp only [targetCoordinates, label, InPlaceControlled.label, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The independent complete permutation retains every auxiliary value and both controls. -/
private lemma targetPermutation_label {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control selector : Fin 2) (fresh : OriginalAuxiliary p.size)
    (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) :
    targetPermutation E Q (label p.size control selector (InPlaceTarget.frameEquiv p.size
      (fresh, words))) =
      label p.size control selector (InPlaceTarget.frameEquiv p.size
        (fresh, if control = 1 then translationWords E Q words else words)) := by
  apply (targetCoordinates p.size).injective
  change targetCoordinates p.size ((targetCoordinates p.size).symm
    (targetFields E Q (targetCoordinates p.size
      (label p.size control selector (InPlaceTarget.frameEquiv p.size (fresh, words)))))) = _
  rw [Equiv.apply_symm_apply, targetCoordinates_label, targetCoordinates_label]
  change (((fresh, (if control = 1 then translationWords E Q else Equiv.refl _) words), control),
    selector) = _
  by_cases active : control = 1
  · simp only [if_pos active]
  · simp only [if_neg active]
    rfl

/-- Independent full target retains all auxiliaries, C, N, and the complete arbitrary reference. -/
def target {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) :
    UnitaryOperator (Register.prod (context p.size).register Reference) :=
  UnitaryOperator.prodTensor (UnitaryOperator.ofPerm (targetPermutation E Q).symm)
    (1 : UnitaryOperator Reference)

private lemma operator_three_kets {R : Register} {first second third : UnitaryOperator R}
    {input one two output : R.Index}
    (firstAction : first.applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket one).vec)
    (secondAction : second.applyVec (NormalizedVector.ket one).vec =
      (NormalizedVector.ket two).vec)
    (thirdAction : third.applyVec (NormalizedVector.ket two).vec =
      (NormalizedVector.ket output).vec) :
    (third * second * first).applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket output).vec := by
  rw [UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec,
    firstAction, secondAction, thirdAction]

private lemma operator_five_kets {R : Register}
    {first second third fourth fifth : UnitaryOperator R}
    {input one two three four output : R.Index}
    (firstAction : first.applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket one).vec)
    (secondAction : second.applyVec (NormalizedVector.ket one).vec =
      (NormalizedVector.ket two).vec)
    (thirdAction : third.applyVec (NormalizedVector.ket two).vec =
      (NormalizedVector.ket three).vec)
    (fourthAction : fourth.applyVec (NormalizedVector.ket three).vec =
      (NormalizedVector.ket four).vec)
    (fifthAction : fifth.applyVec (NormalizedVector.ket four).vec =
      (NormalizedVector.ket output).vec) :
    (fifth * fourth * third * second * first).applyVec (NormalizedVector.ket input).vec =
      (NormalizedVector.ket output).vec := by
  simp only [UnitaryOperator.mul_applyVec]
  rw [firstAction, secondAction, thirdAction, fourthAction, fifthAction]

private def executionOperator {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) :
    UnitaryOperator (Register.prod (context p.size).register Reference) :=
  nativeJoint (environment := environment) p.size Reference (afterMultiplication E Q) *
    arithmeticTarget .multiplication p Fact.out Reference *
    nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q) *
    arithmeticTarget .division p Fact.out Reference *
    nativeJoint (environment := environment) p.size Reference (beforeDivision Q)

/-- The independent target retains the full prepared auxiliary frame and both actual controls. -/
lemma target_prepared_ket {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control selector : Fin 2) (x y : Fin (2 ^ p.size))
    {Reference : Register} (reference : Reference.Index) :
    (target E Q Reference).applyVec
      (NormalizedVector.ket (label p.size control selector
        (InPlaceTarget.preparedBasis p x y), reference)).vec =
      (NormalizedVector.ket (label p.size control selector
        (InPlaceTarget.frameEquiv p.size ((InPlacePreparation.preparation p).value,
          if control = 1 then translationWords E Q (x, y) else (x, y))), reference)).vec := by
  apply operator_prodTensor_identity_ket
  have actual := UnitaryOperator.ofPerm_applyVec_ket (targetPermutation E Q).symm
    (label p.size control selector (InPlaceTarget.preparedBasis p x y))
  change (UnitaryOperator.ofPerm (targetPermutation E Q).symm).applyVec
    (NormalizedVector.ket (label p.size control selector
      (InPlaceTarget.preparedBasis p x y))).vec =
    (NormalizedVector.ket (targetPermutation E Q
      (label p.size control selector (InPlaceTarget.preparedBasis p x y)))).vec at actual
  simpa only [InPlaceTarget.preparedBasis, targetPermutation_label] using actual

private lemma arithmeticTarget_division_fieldWords {p : Nat} [Fact p.Prime]
    (x y : ZMod p) (nonzero : x ≠ 0) (selector : Fin 2)
    {Reference : Register} (reference : Reference.Index) :
    (arithmeticTarget .division p Fact.out Reference).applyVec
      (NormalizedVector.ket (label p.size 1 selector
        (InPlaceTarget.preparedBasis p (fieldWord x) (fieldWord y)), reference)).vec =
      (NormalizedVector.ket (label p.size 1 selector
        (InPlaceTarget.preparedBasis p (fieldWord x) (fieldWord (y / x))), reference)).vec := by
  have quotient := congrArg Prod.snd (division_fieldWords x y nonzero)
  change InPlaceTarget.resultWord .division p Fact.out (fieldWord x) (fieldWord y) =
    fieldWord (y / x) at quotient
  have actual := arithmeticTarget_prepared_ket .division p Fact.out 1 selector
    (fieldWord x) (fieldWord y) reference
  rw [if_pos rfl, quotient] at actual
  exact actual

private lemma arithmeticTarget_multiplication_fieldWords {p : Nat} [Fact p.Prime]
    (x y : ZMod p) {Reference : Register} (reference : Reference.Index) :
    (arithmeticTarget .multiplication p Fact.out Reference).applyVec
      (NormalizedVector.ket (label p.size (controlLabel (decide (x ≠ 0))) 1
        (InPlaceTarget.preparedBasis p (fieldWord x) (fieldWord y)), reference)).vec =
      (NormalizedVector.ket (label p.size (controlLabel (decide (x ≠ 0))) 1
        (InPlaceTarget.preparedBasis p (fieldWord x)
          (fieldWord (if x = 0 then y else x * y))), reference)).vec := by
  by_cases zero : x = 0
  · have control : controlLabel (decide (x ≠ 0)) = (0 : Fin 2) := by
      change (if decide (x ≠ 0) then (1 : Fin 2) else 0) = 0
      exact congrArg (fun flag : Bool => if flag then (1 : Fin 2) else 0)
        (decide_eq_false (not_not_intro zero))
    rw [control, if_pos zero]
    have actual := arithmeticTarget_prepared_ket .multiplication p Fact.out 0 1
      (fieldWord x) (fieldWord y) reference
    simpa only [if_neg Fin.zero_ne_one] using actual
  · have control : controlLabel (decide (x ≠ 0)) = (1 : Fin 2) := by
      change (if decide (x ≠ 0) then (1 : Fin 2) else 0) = 1
      exact congrArg (fun flag : Bool => if flag then (1 : Fin 2) else 0)
        (decide_eq_true zero)
    rw [control, if_neg zero]
    have product := congrArg Prod.snd (multiplication_fieldWords x y zero)
    change InPlaceTarget.resultWord .multiplication p Fact.out (fieldWord x) (fieldWord y) =
      fieldWord (x * y) at product
    have actual := arithmeticTarget_prepared_ket .multiplication p Fact.out 1 1
      (fieldWord x) (fieldWord y) reference
    rw [if_pos rfl, product] at actual
    exact actual

/-- The actual operator restores prepared work and yields the independent affine formula. -/
private lemma executionOperator_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (x y : ZMod p)
    (nonzero : firstDifference x Q.x ≠ 0)
    {Reference : Register} (reference : Reference.Index) :
    (executionOperator (environment := environment) E Q Reference).applyVec
      (NormalizedVector.ket (label p.size 1 0
        (InPlaceTarget.preparedBasis p (fieldWord x) (fieldWord y)), reference)).vec =
      (NormalizedVector.ket (label p.size 1 0
        (InPlaceTarget.preparedBasis p (fieldWord (fieldOutput E Q true x y).1)
          (fieldWord (fieldOutput E Q true x y).2)), reference)).vec := by
  let a := x - Q.x
  let b := y - Q.y
  let quotient := b / a
  let difference := a + 3 * Q.x - quotient ^ 2
  let ordinate := if difference = 0 then quotient else difference * quotient
  have first := nativeJoint_prepared_ket (environment := environment)
    (beforeDivision Q) true false true false
    (fieldWord x) (fieldWord y) (fieldWord a) (fieldWord b) reference
    (beforeDivision_fieldWords Q x y)
  have middle := nativeJoint_prepared_ket (environment := environment)
    (beforeMultiplication Q) true false
    (decide (difference ≠ 0)) true (fieldWord a) (fieldWord quotient)
    (fieldWord difference) (fieldWord quotient) reference
    (beforeMultiplication_fieldWords Q a quotient)
  have last := nativeJoint_prepared_ket (environment := environment)
    (afterMultiplication E Q) (decide (difference ≠ 0)) true
    true false (fieldWord difference) (fieldWord ordinate) (fieldWord (Q.x - difference))
    (fieldWord ((if difference = 0 then ordinate - exceptionalSlope E Q else ordinate) - Q.y))
    reference (afterMultiplication_fieldWords E Q difference ordinate)
  have actual := operator_five_kets first
    (arithmeticTarget_division_fieldWords a b nonzero 0 reference) middle
    (arithmeticTarget_multiplication_fieldWords difference quotient reference) last
  have output : fieldOutput E Q true x y =
      (Q.x - difference,
        (if difference = 0 then ordinate - exceptionalSlope E Q else ordinate) - Q.y) := by
    change (Q.x - difference,
      (if difference = 0 then quotient - exceptionalSlope E Q else difference * quotient) - Q.y) = _
    by_cases zero : difference = 0 <;> simp only [ordinate, zero, if_true, if_false]
  rw [output]
  exact actual

/-- False C retains all binary words, including padding labels, through all five actual stages. -/
private lemma executionOperator_inactive {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (x y : Fin (2 ^ p.size))
    {Reference : Register} (reference : Reference.Index) :
    (executionOperator (environment := environment) E Q Reference).applyVec
      (NormalizedVector.ket (label p.size 0 0 (InPlaceTarget.preparedBasis p x y), reference)).vec =
      (NormalizedVector.ket (label p.size 0 0
        (InPlaceTarget.preparedBasis p x y), reference)).vec := by
  have first := nativeJoint_prepared_ket (environment := environment) (beforeDivision Q)
    false false false false x y x y
    reference (beforeDivision_inactive Q _ rfl)
  have middle := nativeJoint_prepared_ket (environment := environment) (beforeMultiplication Q)
    false false false false x y x y
    reference (beforeMultiplication_prepared_inactive Q x y)
  have last := nativeJoint_prepared_ket (environment := environment) (afterMultiplication E Q)
    false false false false x y x y
    reference (afterMultiplication_prepared_inactive E Q x y)
  have division := arithmeticTarget_prepared_ket .division p Fact.out 0 0 x y reference
  have multiplication := arithmeticTarget_prepared_ket .multiplication p Fact.out 0 0 x y reference
  simp only [if_neg Fin.zero_ne_one] at division multiplication
  exact operator_five_kets first division middle multiplication last

private lemma executionOperator_target_columns {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E)
    {Reference : Register}
    (input : (Register.prod (context p.size).register Reference).Index)
    (allowed : admissible E Q input.1) (row) :
    executionOperator (environment := environment)
      E Q Reference row input = target E Q Reference row input := by
  rcases input with ⟨original, reference⟩
  obtain ⟨control, x, y, rfl, active⟩ := allowed
  have kernels : (executionOperator (environment := environment) E Q Reference).applyVec
      (NormalizedVector.ket (label p.size control 0
        (InPlaceTarget.preparedBasis p x y), reference)).vec =
      (target E Q Reference).applyVec
        (NormalizedVector.ket (label p.size control 0
          (InPlaceTarget.preparedBasis p x y), reference)).vec := by
    fin_cases control
    · have actual := executionOperator_inactive (environment := environment) E Q x y reference
      have ideal := target_prepared_ket E Q 0 0 x y reference
      rw [if_neg Fin.zero_ne_one] at ideal
      exact actual.trans ideal.symm
    · obtain ⟨P, xValue, yValue, different, inverseDifferent⟩ := active rfl
      have xWord : x = fieldWord P.x := Fin.ext xValue
      have yWord : y = fieldWord P.y := Fin.ext yValue
      subst x y
      have nonzero : firstDifference P.x Q.x ≠ 0 :=
        sub_ne_zero.mpr (genericAddDomain_of_ne_of_ne_negate E P Q different inverseDifferent)
      have actual := executionOperator_fieldWords (environment := environment)
        E Q P.x P.y nonzero reference
      have ideal := target_prepared_ket E Q 1 0 (fieldWord P.x) (fieldWord P.y) reference
      rw [if_pos rfl, translationWords_fieldWords E Q P.x P.y nonzero] at ideal
      exact actual.trans ideal.symm
  have column := congrArg (fun vector :
    HilbertVector (Register.prod (context p.size).register Reference) => vector row) kernels
  change HilbertOperator.applyVec (executionOperator (environment := environment)
    E Q Reference : HilbertOperator _)
    (NormalizedVector.ket _).vec row =
    HilbertOperator.applyVec (target E Q Reference : HilbertOperator _)
      (NormalizedVector.ket _).vec row at column
  simpa only [HilbertOperator.applyVec_ket] using column

private lemma arithmetic_admissible_label (modulus : Nat)
    (control selector : Fin 2) (value numerator : Fin (2 ^ modulus.size))
    (domain : control = 1 →
      0 < value.val ∧ value.val < modulus ∧ numerator.val < modulus) :
    InPlaceControlled.admissible modulus
      ((unionBasisEquiv (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
        (selector_disjoint modulus.size)
        (label modulus.size control selector
          (InPlaceTarget.preparedBasis modulus value numerator))).1) := by
  change InPlaceControlled.admissible modulus
    (((unionBasisEquiv (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
      (selector_disjoint modulus.size))
      ((unionBasisEquiv (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
        (selector_disjoint modulus.size)).symm
        (InPlaceControlled.label modulus.size control
          (InPlaceTarget.preparedBasis modulus value numerator),
          (selectorBasis modulus.size).symm selector))).1)
  rw [Equiv.apply_symm_apply]
  exact ⟨control, value, numerator, rfl, domain⟩

private lemma first_arithmetic_reachable {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E)
    {Reference : Register}
    (input : (Register.prod (context p.size).register Reference).Index)
    (allowed : admissible E Q input.1) :
    ∃ output : (Register.prod (context p.size).register Reference).Index,
      InPlaceControlled.admissible p
        ((unionBasisEquiv (InPlaceControlled.context p.size) (selectorContext p.size)
          (selector_disjoint p.size) output.1).1) ∧
      (nativeJoint (environment := environment) p.size Reference (beforeDivision Q)).applyVec
        (NormalizedVector.ket input).vec = (NormalizedVector.ket output).vec := by
  rcases input with ⟨original, reference⟩
  obtain ⟨control, x, y, rfl, domain⟩ := allowed
  fin_cases control
  · refine ⟨(label p.size 0 0 (InPlaceTarget.preparedBasis p x y), reference), ?_, ?_⟩
    · exact arithmetic_admissible_label p 0 0 x y
        (fun active => (Fin.zero_ne_one active).elim)
    · exact nativeJoint_prepared_ket (p := p) (beforeDivision Q)
        false false false false x y x y reference
        (beforeDivision_inactive Q (preparedRaw p false false x y) rfl)
  · obtain ⟨P, xValue, yValue, different, inverseDifferent⟩ := domain rfl
    have xField : x = fieldWord P.x := Fin.ext xValue
    have yField : y = fieldWord P.y := Fin.ext yValue
    subst x
    subst y
    have nonzero : P.x - Q.x ≠ 0 := sub_ne_zero.mpr
      (genericAddDomain_of_ne_of_ne_negate E P Q different inverseDifferent)
    refine ⟨(label p.size 1 0 (InPlaceTarget.preparedBasis p
      (fieldWord (P.x - Q.x)) (fieldWord (P.y - Q.y))), reference), ?_, ?_⟩
    · exact arithmetic_admissible_label p 1 0 _ _
        (fun _ => ⟨ZMod.val_pos.mpr nonzero, ZMod.val_lt _, ZMod.val_lt _⟩)
    · exact nativeJoint_prepared_ket (p := p) (beforeDivision Q)
        true false true false (fieldWord P.x) (fieldWord P.y)
        (fieldWord (P.x - Q.x)) (fieldWord (P.y - Q.y)) reference
        (beforeDivision_fieldWords Q P.x P.y)

private lemma second_arithmetic_reachable {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E)
    {Reference : Register}
    (input : (Register.prod (context p.size).register Reference).Index)
    (allowed : admissible E Q input.1) :
    ∃ output : (Register.prod (context p.size).register Reference).Index,
      InPlaceControlled.admissible p
        ((unionBasisEquiv (InPlaceControlled.context p.size) (selectorContext p.size)
          (selector_disjoint p.size) output.1).1) ∧
      (nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q) *
        arithmeticTarget .division p Fact.out Reference *
        nativeJoint (environment := environment) p.size Reference (beforeDivision Q)).applyVec
        (NormalizedVector.ket input).vec = (NormalizedVector.ket output).vec := by
  rcases input with ⟨original, reference⟩
  obtain ⟨control, x, y, rfl, domain⟩ := allowed
  fin_cases control
  · refine ⟨(label p.size 0 0 (InPlaceTarget.preparedBasis p x y), reference), ?_, ?_⟩
    · exact arithmetic_admissible_label p 0 0 x y
        (fun active => (Fin.zero_ne_one active).elim)
    · have first := nativeJoint_prepared_ket (environment := environment)
        (p := p) (beforeDivision Q)
        false false false false x y x y reference
        (beforeDivision_inactive Q (preparedRaw p false false x y) rfl)
      have divided := arithmeticTarget_prepared_ket .division p Fact.out 0 0 x y reference
      rw [if_neg (show (0 : Fin 2) ≠ 1 from Fin.zero_ne_one)] at divided
      have middle := nativeJoint_prepared_ket (environment := environment)
        (p := p) (beforeMultiplication Q)
        false false false false x y x y reference
        (beforeMultiplication_prepared_inactive Q x y)
      exact operator_three_kets first divided middle
  · obtain ⟨P, xValue, yValue, different, inverseDifferent⟩ := domain rfl
    have xField : x = fieldWord P.x := Fin.ext xValue
    have yField : y = fieldWord P.y := Fin.ext yValue
    subst x
    subst y
    let a : ZMod p := P.x - Q.x
    let b : ZMod p := P.y - Q.y
    let slopeValue : ZMod p := b / a
    let difference : ZMod p := a + 3 * Q.x - slopeValue ^ 2
    have nonzero : a ≠ 0 := sub_ne_zero.mpr
      (genericAddDomain_of_ne_of_ne_negate E P Q different inverseDifferent)
    refine ⟨(label p.size (controlLabel (decide (difference ≠ 0))) 1
      (InPlaceTarget.preparedBasis p (fieldWord difference) (fieldWord slopeValue)), reference),
      ?_, ?_⟩
    · apply arithmetic_admissible_label
      intro active
      have selected : decide (difference ≠ 0) = true :=
        BinaryLabelEncoding.bool.encode_injective active
      have valid : difference ≠ 0 := of_decide_eq_true selected
      exact ⟨ZMod.val_pos.mpr valid, ZMod.val_lt _, ZMod.val_lt _⟩
    · have first := nativeJoint_prepared_ket (environment := environment)
        (p := p) (beforeDivision Q)
        true false true false (fieldWord P.x) (fieldWord P.y)
        (fieldWord a) (fieldWord b) reference (beforeDivision_fieldWords Q P.x P.y)
      have quotient : InPlaceTarget.resultWord .division p Fact.out
          (fieldWord a) (fieldWord b) = fieldWord slopeValue :=
        congrArg Prod.snd (division_fieldWords a b nonzero)
      have divided := arithmeticTarget_prepared_ket .division p Fact.out 1 0
        (fieldWord a) (fieldWord b) reference
      rw [if_pos rfl, quotient] at divided
      have middle := nativeJoint_prepared_ket (environment := environment)
        (p := p) (beforeMultiplication Q)
        true false (decide (difference ≠ 0)) true
        (fieldWord a) (fieldWord slopeValue) (fieldWord difference) (fieldWord slopeValue)
        reference (beforeMultiplication_fieldWords Q a slopeValue)
      exact operator_three_kets first divided middle

private lemma execute_pair_marginal {allowAllocation : Bool} {ctx : RuntimeCtx .quantum}
    (first second : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx allowAllocation)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    ((first.seq second).execute environment Reference state).quantumMarginal =
      (second.execute environment Reference (first.execute environment Reference
        state)).quantumMarginal := by
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal]

private lemma execute_five_marginal {allowAllocation : Bool} {ctx : RuntimeCtx .quantum}
    (first second third fourth fifth : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx
      allowAllocation)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    ((first.seq (second.seq (third.seq (fourth.seq fifth)))).execute environment
      Reference state).quantumMarginal =
      (fifth.execute environment Reference
        (fourth.execute environment Reference
          (third.execute environment Reference
            (second.execute environment Reference (first.execute environment Reference
              state))))).quantumMarginal := by
  calc
    ((first.seq (second.seq (third.seq (fourth.seq fifth)))).execute environment
        Reference state).quantumMarginal =
        ((second.seq (third.seq (fourth.seq fifth))).execute environment Reference
          (first.execute environment Reference state)).quantumMarginal :=
      execute_pair_marginal first (second.seq (third.seq (fourth.seq fifth))) state
    _ = ((third.seq (fourth.seq fifth)).execute environment Reference
        (second.execute environment Reference (first.execute environment Reference
          state))).quantumMarginal :=
      execute_pair_marginal second (third.seq (fourth.seq fifth))
        (first.execute environment Reference state)
    _ = ((fourth.seq fifth).execute environment Reference
        (third.execute environment Reference
          (second.execute environment Reference (first.execute environment Reference
            state)))).quantumMarginal :=
      execute_pair_marginal third (fourth.seq fifth)
        (second.execute environment Reference (first.execute environment Reference state))
    _ = (fifth.execute environment Reference
        (fourth.execute environment Reference
          (third.execute environment Reference
            (second.execute environment Reference (first.execute environment Reference
              state))))).quantumMarginal :=
      execute_pair_marginal fourth fifth
        (third.execute environment Reference (second.execute environment Reference (first.execute
          environment Reference state)))


private lemma body_density_of_columns {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ input : (Register.prod (context p.size).register Reference).Index,
      ¬admissible E Q input.1 → state.quantumMarginal.matrix input input = 0)
    (firstReachable : ∀ input : (Register.prod (context p.size).register Reference).Index,
      admissible E Q input.1 →
        ∃ output : (Register.prod (context p.size).register Reference).Index,
        InPlaceControlled.admissible p
          ((unionBasisEquiv (InPlaceControlled.context p.size) (selectorContext p.size)
            (selector_disjoint p.size) output.1).1) ∧
        (nativeJoint (environment := environment) p.size Reference (beforeDivision Q)).applyVec
          (NormalizedVector.ket input).vec = (NormalizedVector.ket output).vec)
    (secondReachable : ∀ input : (Register.prod (context p.size).register Reference).Index,
      admissible E Q input.1 →
        ∃ output : (Register.prod (context p.size).register Reference).Index,
        InPlaceControlled.admissible p
          ((unionBasisEquiv (InPlaceControlled.context p.size) (selectorContext p.size)
            (selector_disjoint p.size) output.1).1) ∧
        (nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q) *
          arithmeticTarget .division p Fact.out Reference *
          nativeJoint (environment := environment) p.size Reference (beforeDivision Q)).applyVec
          (NormalizedVector.ket input).vec = (NormalizedVector.ket output).vec)
    (columns : ∀ input : (Register.prod (context p.size).register Reference).Index,
      admissible E Q input.1 → ∀ row,
        (nativeJoint (environment := environment) p.size Reference (afterMultiplication E Q) *
          arithmeticTarget .multiplication p Fact.out Reference *
          nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q) *
          arithmeticTarget .division p Fact.out Reference *
          nativeJoint (environment := environment) p.size Reference (beforeDivision Q) :
            UnitaryOperator (Register.prod (context p.size).register Reference)) row input =
          target E Q Reference row input)
    (allowAllocation : Bool := true) :
    ((body E Q allowAllocation).execute environment Reference state).quantumMarginal =
      DensityOperator.applyUnitary (target E Q Reference) state.quantumMarginal := by
  let firstCode := nativeCode p.size (beforeDivision Q) allowAllocation
  let middleCode := nativeCode p.size (beforeMultiplication Q) allowAllocation
  let lastCode := nativeCode p.size (afterMultiplication E Q) allowAllocation
  let firstState := firstCode.execute environment Reference state
  let secondState := (arithmetic .division p Fact.out allowAllocation).execute environment
    Reference firstState
  let thirdState := middleCode.execute environment Reference secondState
  let fourthState := (arithmetic .multiplication p Fact.out allowAllocation).execute environment
    Reference
    thirdState
  let arithmeticAllowed := fun input :
      (Register.prod (context p.size).register Reference).Index =>
    InPlaceControlled.admissible p
      ((unionBasisEquiv (InPlaceControlled.context p.size) (selectorContext p.size)
        (selector_disjoint p.size) input.1).1)
  have firstDensity : firstState.quantumMarginal =
      DensityOperator.applyUnitary (nativeJoint (environment := environment) p.size Reference
        (beforeDivision Q))
        state.quantumMarginal :=
    nativeCode_density (allowAllocation := allowAllocation) p.size (beforeDivision Q) state
  have firstSupport : ∀ input, ¬arithmeticAllowed input →
      firstState.quantumMarginal.matrix input input = 0 := by
    rw [firstDensity]
    exact applyUnitary_support_of_kets state.quantumMarginal
      (nativeJoint (environment := environment) p.size Reference (beforeDivision Q))
      (fun input => admissible E Q input.1) arithmeticAllowed support firstReachable
  have secondDensity := arithmetic_density (environment := environment)
    (allowAllocation := allowAllocation) .division p
    Fact.out firstState firstSupport
  have thirdDensity := nativeCode_density (environment := environment)
    (allowAllocation := allowAllocation) p.size
    (beforeMultiplication Q)
    secondState
  have thirdCombined : thirdState.quantumMarginal =
      DensityOperator.applyUnitary
        (nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q) *
          arithmeticTarget .division p Fact.out Reference *
          nativeJoint (environment := environment) p.size Reference (beforeDivision Q))
            state.quantumMarginal := by
    rw [DensityOperator.applyUnitary_mul, DensityOperator.applyUnitary_mul]
    exact thirdDensity.trans
      (congrArg (DensityOperator.applyUnitary
        (nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q)))
          (secondDensity.trans
            (congrArg (DensityOperator.applyUnitary
              (arithmeticTarget .division p Fact.out Reference)) firstDensity)))
  have secondSupport : ∀ input, ¬arithmeticAllowed input →
      thirdState.quantumMarginal.matrix input input = 0 := by
    rw [thirdCombined]
    exact applyUnitary_support_of_kets state.quantumMarginal
      (nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q) *
        arithmeticTarget .division p Fact.out Reference *
        nativeJoint (environment := environment) p.size Reference (beforeDivision Q))
      (fun input => admissible E Q input.1) arithmeticAllowed support secondReachable
  have fourthDensity := arithmetic_density (environment := environment)
    (allowAllocation := allowAllocation) .multiplication p
    Fact.out thirdState secondSupport
  have fifthDensity := nativeCode_density (environment := environment)
    (allowAllocation := allowAllocation) p.size
    (afterMultiplication E Q)
    fourthState
  have complete : ((body E Q allowAllocation).execute environment Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (nativeJoint (environment := environment) p.size Reference (afterMultiplication E Q) *
          arithmeticTarget .multiplication p Fact.out Reference *
          nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q) *
          arithmeticTarget .division p Fact.out Reference *
          nativeJoint (environment := environment) p.size Reference (beforeDivision Q))
            state.quantumMarginal := by
    have sequence : ((body E Q allowAllocation).execute environment Reference
      state).quantumMarginal =
        (lastCode.execute environment Reference fourthState).quantumMarginal :=
      execute_five_marginal (allowAllocation := allowAllocation) firstCode (arithmetic .division p
        Fact.out allowAllocation)
        middleCode (arithmetic .multiplication p Fact.out allowAllocation) lastCode state
    have actual := sequence.trans (fifthDensity.trans
      (congrArg (DensityOperator.applyUnitary
        (nativeJoint (environment := environment) p.size Reference (afterMultiplication E Q)))
        (fourthDensity.trans (congrArg (DensityOperator.applyUnitary
          (arithmeticTarget .multiplication p Fact.out Reference))
          (thirdDensity.trans (congrArg (DensityOperator.applyUnitary
            (nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q)))
            (secondDensity.trans (congrArg (DensityOperator.applyUnitary
              (arithmeticTarget .division p Fact.out Reference)) firstDensity))))))))
    simpa only [DensityOperator.applyUnitary_mul] using actual
  rw [complete]
  apply DensityOperator.ext
  exact DensityOperator.conjugation_eq_on_basis_support state.quantumMarginal
    (fun input => admissible E Q input.1) _ _ support columns

/-- The complete actual body preserves arbitrary reference entanglement and control coherence. -/
lemma body_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ input : (Register.prod (context p.size).register Reference).Index,
      ¬admissible E Q input.1 → state.quantumMarginal.matrix input input = 0)
    (allowAllocation : Bool := true) :
    ((body E Q allowAllocation).execute environment Reference state).quantumMarginal =
      DensityOperator.applyUnitary (target E Q Reference) state.quantumMarginal :=
  body_density_of_columns (environment := environment)
    (allowAllocation := allowAllocation) E Q state support
    (first_arithmetic_reachable E Q)
    (second_arithmetic_reachable E Q) (executionOperator_target_columns (environment := environment)
      E Q)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The original active point exclusions imply the first denominator is nonzero. -/
lemma firstDifference_ne_zero (P Q : AffinePoint E)
    (allowed : affineAllowed true P Q) : firstDifference P.x Q.x ≠ 0 := by
  obtain ⟨different, inverseDifferent⟩ := allowed rfl
  exact sub_ne_zero.mpr (genericAddDomain_of_ne_of_ne_negate E P Q different inverseDifferent)

/-- The actual first quotient is the independent affine secant slope. -/
lemma slope_eq_generic (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    slope P.x P.y Q.x Q.y = genericAddSlope E P Q := by
  rw [genericAddSlope_eq_secant_quotient E P Q domain]
  rfl

/-- The second multiplier is zero exactly when the result shares the fixed x coordinate. -/
lemma secondDifference_eq (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    secondDifference P.x P.y Q.x Q.y = Q.x - genericAddX E P Q := by
  have known := GenericPointAddition.InPlace.PointSemantics.secondDenominator_true_eq E P Q domain
  rw [GenericPointAddition.InPlace.Semantics.secondDenominator, if_pos rfl,
    GenericPointAddition.InPlace.PointSemantics.selectedSlope_true_eq_genericAddSlope
      E P Q domain] at known
  rw [secondDifference, slope_eq_generic E P Q domain, firstDifference]
  linear_combination known

private lemma result_group (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    P.toMathlib + Q.toMathlib = (genericAddPoint E P Q domain).toMathlib :=
  genericAdd_group_law_mathlib E P Q domain

private lemma result_eq_negate (P Q : AffinePoint E) (domain : GenericAddDomain P Q)
    (sameX : (genericAddPoint E P Q domain).x = Q.x) :
    genericAddPoint E P Q domain = AffinePoint.negate Q := by
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (W := E.toWeierstrassCurve.toAffine)
      (h₁ := (genericAddPoint E P Q domain).nonsingular) (h₂ := Q.nonsingular)).mp sameX with
    same | opposite
  · exfalso
    have samePoint : (genericAddPoint E P Q domain).toMathlib = Q.toMathlib := by
      simpa only [AffinePoint.toMathlib] using same
    have zero : P.toMathlib = 0 := by
      apply add_right_cancel (b := Q.toMathlib)
      simpa only [zero_add] using (result_group E P Q domain).trans samePoint
    exact (WeierstrassCurve.Affine.Point.some_ne_zero P.nonsingular) zero
  · have oppositePoint : (genericAddPoint E P Q domain).toMathlib = -Q.toMathlib := by
      simpa only [AffinePoint.toMathlib] using opposite
    have samePoint : (genericAddPoint E P Q domain).toMathlib =
        (AffinePoint.negate Q).toMathlib := by
      rw [AffinePoint.negate_toMathlib]
      exact oppositePoint
    have coordinates := WeierstrassCurve.Affine.Point.some.inj samePoint
    exact AffinePoint.ext_coordinates _ _ coordinates.1 coordinates.2

private lemma negate_self_of_two_mul_y_zero (R : AffinePoint E)
    (zero : (2 : ZMod p) * R.y = 0) : AffinePoint.negate R = R := by
  apply AffinePoint.ext_coordinates
  · rfl
  · have same : -R.y = R.y := by linear_combination -zero
    simpa [toWeierstrassCurve, WeierstrassCurve.Affine.negY] using same

private lemma exceptional_double_domain (P Q : AffinePoint E)
    (domain : GenericAddDomain P Q)
    (sameX : (genericAddPoint E P Q domain).x = Q.x) :
    GenericDoubleDomain (AffinePoint.negate Q) := by
  intro zero
  have same := negate_self_of_two_mul_y_zero E (AffinePoint.negate Q) zero
  have negateSame : AffinePoint.negate Q = Q := by
    calc
      AffinePoint.negate Q = AffinePoint.negate (AffinePoint.negate Q) := same.symm
      _ = Q := AffinePoint.negate_negate Q
  have resultSame : (genericAddPoint E P Q domain).toMathlib = Q.toMathlib :=
    congrArg AffinePoint.toMathlib ((result_eq_negate E P Q domain sameX).trans negateSame)
  have pointZero : P.toMathlib = 0 := by
    apply add_right_cancel (b := Q.toMathlib)
    simpa only [zero_add] using (result_group E P Q domain).trans resultSame
  exact (WeierstrassCurve.Affine.Point.some_ne_zero P.nonsingular) pointZero

private lemma exceptional_coordinates (P Q : AffinePoint E)
    (domain : GenericAddDomain P Q)
    (sameX : (genericAddPoint E P Q domain).x = Q.x) :
    doubleX E (AffinePoint.negate Q) = P.x ∧ doubleY E (AffinePoint.negate Q) = P.y := by
  have doubleDomain := exceptional_double_domain E P Q domain sameX
  have sum : P.toMathlib + Q.toMathlib = -Q.toMathlib := by
    rw [result_group E P Q domain, result_eq_negate E P Q domain sameX,
      AffinePoint.negate_toMathlib]
  have input : P.toMathlib = (AffinePoint.negate Q).toMathlib +
      (AffinePoint.negate Q).toMathlib := by
    calc
      P.toMathlib = (P.toMathlib + Q.toMathlib) + -Q.toMathlib := by abel
      _ = -Q.toMathlib + -Q.toMathlib := by rw [sum]
      _ = _ := by rw [AffinePoint.negate_toMathlib]
  have doubled : WeierstrassCurve.Affine.Point.some
      (doubleX E (AffinePoint.negate Q)) (doubleY E (AffinePoint.negate Q))
      (double_nonsingular E (AffinePoint.negate Q) doubleDomain) = P.toMathlib := by
    rw [← double_group_law_mathlib E (AffinePoint.negate Q) doubleDomain]
    exact input.symm
  have coordinates := WeierstrassCurve.Affine.Point.some.inj doubled
  exact ⟨coordinates.1, coordinates.2⟩

/-- A reachable zero second multiplier makes the slope the same total classical constant. -/
lemma exceptional_slope (P Q : AffinePoint E) (domain : GenericAddDomain P Q)
    (zero : secondDifference P.x P.y Q.x Q.y = 0) :
    slope P.x P.y Q.x Q.y = exceptionalSlope E Q := by
  have sameX : (genericAddPoint E P Q domain).x = Q.x := by
    rw [secondDifference_eq E P Q domain] at zero
    exact (sub_eq_zero.mp zero).symm
  have coordinates := exceptional_coordinates E P Q domain sameX
  rw [exceptionalSlope, coordinates.1, coordinates.2]
  rfl

/-- The normal selector supplies the multiplier domain internally, including coherent control. -/
lemma normalControl_true (control : Bool) (difference : ZMod p)
    (active : normalControl control difference = true) :
    control = true ∧ difference ≠ 0 := by
  simpa [normalControl] using active

/-- Every inactive binary-field input is preserved without a denominator premise. -/
lemma fieldOutput_false (Q : AffinePoint E) (x y : ZMod p) :
    fieldOutput E Q false x y = (x, y) := rfl

/-- Both active branches give the original generic affine point without a reverse-domain premise. -/
lemma fieldOutput_true (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    fieldOutput E Q true P.x P.y = (genericAddX E P Q, genericAddY E P Q) := by
  have outputY := GenericPointAddition.InPlace.PointSemantics.selectedOutputY_true E P Q domain
  rw [GenericPointAddition.InPlace.Semantics.selectedOutputY, if_pos rfl,
    GenericPointAddition.InPlace.PointSemantics.selectedSlope_true_eq_genericAddSlope
      E P Q domain,
    GenericPointAddition.InPlace.PointSemantics.secondDenominator_true_eq E P Q domain] at outputY
  have xResult : Q.x - secondDifference P.x P.y Q.x Q.y = genericAddX E P Q := by
    rw [secondDifference_eq E P Q domain]
    ring
  have yResult :
      (if secondDifference P.x P.y Q.x Q.y = 0 then
        slope P.x P.y Q.x Q.y - exceptionalSlope E Q
      else secondDifference P.x P.y Q.x Q.y * slope P.x P.y Q.x Q.y) - Q.y =
      genericAddY E P Q := by
    by_cases zero : secondDifference P.x P.y Q.x Q.y = 0
    · rw [if_pos zero, exceptional_slope E P Q domain zero, sub_self, zero_sub]
      rw [← slope_eq_generic E P Q domain, ← secondDifference_eq E P Q domain, zero,
        mul_zero, zero_sub] at outputY
      exact outputY
    · rw [if_neg zero, secondDifference_eq E P Q domain, slope_eq_generic E P Q domain]
      simpa only [mul_comm] using outputY
  exact Prod.ext xResult yResult

/-- The original active affine exclusions give P+Q with every prepared work bit restored. -/
lemma target_affine_prepared (P Q : AffinePoint E)
    (different : P ≠ Q) (inverseDifferent : P ≠ AffinePoint.negate Q)
    {Reference : Register} (reference : Reference.Index) :
    (target E Q Reference).applyVec
      (NormalizedVector.ket (label p.size 1 0
        (InPlaceTarget.preparedBasis p (fieldWord P.x) (fieldWord P.y)), reference)).vec =
      (NormalizedVector.ket (label p.size 1 0
        (InPlaceTarget.preparedBasis p (fieldWord (genericAddX E P Q))
          (fieldWord (genericAddY E P Q))), reference)).vec := by
  have domain := genericAddDomain_of_ne_of_ne_negate E P Q different inverseDifferent
  have nonzero : firstDifference P.x Q.x ≠ 0 := sub_ne_zero.mpr domain
  have actual := target_prepared_ket E Q 1 0 (fieldWord P.x) (fieldWord P.y) reference
  rw [if_pos rfl, translationWords_fieldWords E Q P.x P.y nonzero,
    fieldOutput_true E P Q domain] at actual
  exact actual

/-- False C fixes arbitrary binary X/Y and all prescribed preparation, including padding labels. -/
lemma target_inactive_prepared (Q : AffinePoint E) (x y : Fin (2 ^ p.size))
    {Reference : Register} (reference : Reference.Index) :
    (target E Q Reference).applyVec
      (NormalizedVector.ket (label p.size 0 0 (InPlaceTarget.preparedBasis p x y), reference)).vec =
      (NormalizedVector.ket (label p.size 0 0
        (InPlaceTarget.preparedBasis p x y), reference)).vec := by
  have actual := target_prepared_ket E Q 0 0 x y reference
  simpa only [if_neg Fin.zero_ne_one, InPlaceTarget.preparedBasis] using actual

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
