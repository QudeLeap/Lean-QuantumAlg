/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement.Resources
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries

/-!
# Place the HRS controlled increment inside the existing low word

The low word contains `extra + high` bits. Its least-significant `high`
bits supply the incrementer's borrowed word; its `extra` leading bits are
untouched. The target is the high word and the final wire is the dirty
control [HRS16, paper.tex:219-226,232-260]. The literal native list follows
these exact physical addresses and retains its full original event trace.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

private def incrementSourceLayout (extra high : Nat) :
    QuantumLayout (extra + (TTK.overflowEncoding high).width) :=
  (QubitLayout.canonical (extra + (TTK.overflowEncoding high).width)).toQuantum

private def incrementTargetLayout (extra high : Nat) :
    QuantumLayout (bridgeEncoding (extra + high) high).width :=
  (QubitLayout.canonical (bridgeEncoding (extra + high) high).width).toQuantum

/-- Place the source order `unused/borrowed/target/dirty` on the bridge order
`target/unused/borrowed/dirty`.  This changes only physical addresses; it is
not a zero-cost logical basis permutation. -/
private def incrementPlacementPositionValue (extra high index : Nat) : Nat :=
  if index < extra + high then high + index
  else if index < extra + high + high then index - (extra + high)
  else high + extra + high

private def incrementPlacementPosition (extra high : Nat) :
    Fin (extra + (TTK.overflowEncoding high).width) ↪
      Fin (bridgeEncoding (extra + high) high).width where
  toFun index :=
    ⟨incrementPlacementPositionValue extra high index.val, by
      simp only [incrementPlacementPositionValue]
      split_ifs <;> rw [hrsBridgeEncoding_width] <;> omega⟩
  inj' := by
    intro left right same
    apply Fin.ext
    have leftBound : left.val < extra + (2 * high + 1) := by
      simpa only [TTK.ttkOverflowEncoding_width] using left.isLt
    have rightBound : right.val < extra + (2 * high + 1) := by
      simpa only [TTK.ttkOverflowEncoding_width] using right.isLt
    have sameValue := congrArg Fin.val same
    change incrementPlacementPositionValue extra high left.val =
      incrementPlacementPositionValue extra high right.val at sameValue
    simp only [incrementPlacementPositionValue] at sameValue
    split_ifs at sameValue <;> omega

@[simp] private lemma incrementPlacementPosition_val (extra high : Nat)
    (index : Fin (extra + (TTK.overflowEncoding high).width)) :
    (incrementPlacementPosition extra high index).val =
      if index.val < extra + high then high + index.val
      else if index.val < extra + high + high then index.val - (extra + high)
      else high + extra + high := by
  rfl

private lemma incrementPlacementPosition_surjective (extra high : Nat) :
    Function.Surjective (incrementPlacementPosition extra high) := by
  intro target
  by_cases inTarget : target.val < high
  · refine ⟨⟨extra + high + target.val, ?_⟩, ?_⟩
    · rw [TTK.ttkOverflowEncoding_width]
      omega
    · apply Fin.ext
      have notBefore : ¬ extra + high + target.val < extra + high := by omega
      have within : extra + high + target.val < extra + high + high := by omega
      rw [incrementPlacementPosition_val]
      simp only [notBefore, within, ↓reduceIte]
      omega
  · by_cases dirty : target.val = high + extra + high
    · refine ⟨⟨extra + high + high, ?_⟩, ?_⟩
      · rw [TTK.ttkOverflowEncoding_width]
        omega
      · apply Fin.ext
        have notBefore : ¬ extra + high + high < extra + high := by omega
        have notTarget : ¬ extra + high + high < extra + high + high := by omega
        rw [incrementPlacementPosition_val]
        simp only [notBefore, notTarget, ↓reduceIte, dirty]
    · refine ⟨⟨target.val - high, ?_⟩, ?_⟩
      · rw [TTK.ttkOverflowEncoding_width]
        have targetBound : target.val < (extra + high) + high + 1 := by
          simpa only [hrsBridgeEncoding_width] using target.isLt
        omega
      · apply Fin.ext
        have targetBound : target.val < (extra + high) + high + 1 := by
          simpa only [hrsBridgeEncoding_width] using target.isLt
        have before : target.val - high < extra + high := by omega
        rw [incrementPlacementPosition_val]
        simp only [before, ↓reduceIte]
        omega

private lemma incrementPlacementDimensions (extra high : Nat)
    (index : Fin (extra + (TTK.overflowEncoding high).width)) :
    ((incrementSourceLayout extra high).wire index).dimension =
      ((incrementTargetLayout extra high).wire
        (incrementPlacementPosition extra high index)).dimension := rfl

private abbrev incrementSourceEncoding (extra high : Nat) :
    BinaryLabelEncoding (Fin (2 ^ extra) × TTK.OverflowRegisters high) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity extra)
    (TTK.overflowEncoding high)

private lemma binaryBasis_prod_left {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth))
    (index : Fin leftWidth) :
    (BinaryBasis.bigEndianEquiv (leftWidth + rightWidth)).symm
        (prodEquiv (left, right))
        ⟨index.val, by omega⟩ =
      (BinaryBasis.bigEndianEquiv leftWidth).symm left index := by
  apply finTwoEquiv.injective
  rw [BinaryBasis.bigEndianEquiv_symm_value,
    BinaryBasis.bigEndianEquiv_symm_value]
  simp only [Equiv.apply_symm_apply]
  have bitPosition :
      (⟨index.val, by omega⟩ : Fin (leftWidth + rightWidth)).rev.val =
        rightWidth + index.rev.val := by
    simp only [Fin.rev]
    omega
  rw [bitPosition]
  exact prodEquiv_testBit_left left right index.rev

private lemma binaryBasis_prod_right {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth))
    (index : Fin rightWidth) :
    (BinaryBasis.bigEndianEquiv (leftWidth + rightWidth)).symm
        (prodEquiv (left, right))
        ⟨leftWidth + index.val, by omega⟩ =
      (BinaryBasis.bigEndianEquiv rightWidth).symm right index := by
  apply finTwoEquiv.injective
  rw [BinaryBasis.bigEndianEquiv_symm_value,
    BinaryBasis.bigEndianEquiv_symm_value]
  simp only [Equiv.apply_symm_apply]
  have bitPosition :
      (⟨leftWidth + index.val, by omega⟩ : Fin (leftWidth + rightWidth)).rev.val =
        index.rev.val := by
    simp only [Fin.rev]
    omega
  rw [bitPosition]
  exact prodEquiv_testBit_right left right index.rev

private lemma incrementPlacement_selectedInput (extra high : Nat)
    (unused : Fin (2 ^ extra)) (borrowed target : Fin (2 ^ high)) (dirty : Bool) :
    UnitaryCircuit.selectedInput (incrementSourceLayout extra high)
        (incrementTargetLayout extra high) (incrementPlacementPosition extra high)
        (incrementPlacementDimensions extra high)
        ((QubitLayout.canonical (bridgeEncoding (extra + high) high).width).basisEquiv.symm
          ((bridgeEncoding (extra + high) high).encode
            ((prodEquiv (unused, borrowed), target), dirty))) =
      (QubitLayout.canonical
        (extra + (TTK.overflowEncoding high).width)).basisEquiv.symm
          ((incrementSourceEncoding extra high).encode
            (unused, ((borrowed, target), dirty))) := by
  funext index
  change
    (BinaryBasis.bigEndianEquiv (bridgeEncoding (extra + high) high).width).symm
        ((bridgeEncoding (extra + high) high).encode
          ((prodEquiv (unused, borrowed), target), dirty))
        (incrementPlacementPosition extra high index) =
      (BinaryBasis.bigEndianEquiv (extra + (TTK.overflowEncoding high).width)).symm
        ((incrementSourceEncoding extra high).encode
          (unused, ((borrowed, target), dirty))) index
  let dirtyLabel : Fin (2 ^ 1) := BinaryLabelEncoding.bool.encode dirty
  let lowLabel : Fin (2 ^ (extra + high)) := prodEquiv (unused, borrowed)
  let targetPair : Fin (2 ^ (high + (extra + high))) := prodEquiv (target, lowLabel)
  let sourcePair : Fin (2 ^ (high + high)) := prodEquiv (borrowed, target)
  let overflowLabel : Fin (2 ^ ((high + high) + 1)) := prodEquiv (sourcePair, dirtyLabel)
  let sourceLabel : Fin (2 ^ (extra + ((high + high) + 1))) :=
    prodEquiv (unused, overflowLabel)
  let targetLabel : Fin (2 ^ ((high + (extra + high)) + 1)) :=
    prodEquiv (targetPair, dirtyLabel)
  have targetEncode : (bridgeEncoding (extra + high) high).encode
      ((prodEquiv (unused, borrowed), target), dirty) = targetLabel := rfl
  have sourceEncode : (incrementSourceEncoding extra high).encode
      (unused, ((borrowed, target), dirty)) = sourceLabel := rfl
  rw [targetEncode, sourceEncode]
  change (BinaryBasis.bigEndianEquiv ((high + (extra + high)) + 1)).symm
      targetLabel (incrementPlacementPosition extra high index) =
    (BinaryBasis.bigEndianEquiv (extra + ((high + high) + 1))).symm
      sourceLabel index
  by_cases inUnused : index.val < extra
  · let fieldIndex : Fin extra := ⟨index.val, inUnused⟩
    have sourcePosition :
        (⟨fieldIndex.val, by omega⟩ : Fin (extra + ((high + high) + 1))) = index := by
      apply Fin.ext
      rfl
    have placed : incrementPlacementPosition extra high index =
        (⟨high + fieldIndex.val, by omega⟩ : Fin ((high + (extra + high)) + 1)) := by
      apply Fin.ext
      rw [incrementPlacementPosition_val]
      have before : index.val < extra + high := by omega
      simp only [before, ↓reduceIte, fieldIndex]
    rw [placed]
    calc
      _ = (BinaryBasis.bigEndianEquiv (high + (extra + high))).symm
          targetPair ⟨high + fieldIndex.val, by omega⟩ :=
        binaryBasis_prod_left targetPair dirtyLabel ⟨high + fieldIndex.val, by omega⟩
      _ = (BinaryBasis.bigEndianEquiv (extra + high)).symm lowLabel
          ⟨fieldIndex.val, by omega⟩ :=
        binaryBasis_prod_right target lowLabel ⟨fieldIndex.val, by omega⟩
      _ = (BinaryBasis.bigEndianEquiv extra).symm unused fieldIndex :=
        binaryBasis_prod_left unused borrowed fieldIndex
      _ = _ := by
        calc
          _ = (BinaryBasis.bigEndianEquiv (extra + ((high + high) + 1))).symm
              sourceLabel ⟨fieldIndex.val, by omega⟩ := by
            simpa only [sourceLabel] using
              (binaryBasis_prod_left unused overflowLabel fieldIndex).symm
          _ = _ := congrArg
            (fun position => (BinaryBasis.bigEndianEquiv
              (extra + ((high + high) + 1))).symm sourceLabel position)
            sourcePosition
  · by_cases inBorrowed : index.val < extra + high
    · let fieldIndex : Fin high := ⟨index.val - extra, by omega⟩
      have indexValue : index.val = extra + fieldIndex.val := by
        dsimp only [fieldIndex]
        omega
      have sourcePosition :
          (⟨extra + fieldIndex.val, by omega⟩ :
            Fin (extra + ((high + high) + 1))) = index := by
        apply Fin.ext
        exact indexValue.symm
      have placed : incrementPlacementPosition extra high index =
          (⟨high + extra + fieldIndex.val, by omega⟩ :
            Fin ((high + (extra + high)) + 1)) := by
        apply Fin.ext
        rw [incrementPlacementPosition_val]
        simp only [inBorrowed, ↓reduceIte]
        omega
      rw [placed]
      calc
        _ = (BinaryBasis.bigEndianEquiv (high + (extra + high))).symm
            targetPair ⟨high + extra + fieldIndex.val, by omega⟩ :=
          binaryBasis_prod_left targetPair dirtyLabel
            ⟨high + extra + fieldIndex.val, by omega⟩
        _ = (BinaryBasis.bigEndianEquiv (extra + high)).symm lowLabel
            ⟨extra + fieldIndex.val, by omega⟩ :=
          by
            simpa only [Nat.add_assoc] using
              binaryBasis_prod_right target lowLabel
                ⟨extra + fieldIndex.val, by omega⟩
        _ = (BinaryBasis.bigEndianEquiv high).symm borrowed fieldIndex :=
          binaryBasis_prod_right unused borrowed fieldIndex
        _ = (BinaryBasis.bigEndianEquiv (high + high)).symm sourcePair
            ⟨fieldIndex.val, by omega⟩ :=
          (binaryBasis_prod_left borrowed target fieldIndex).symm
        _ = (BinaryBasis.bigEndianEquiv ((high + high) + 1)).symm
            overflowLabel ⟨fieldIndex.val, by omega⟩ :=
          (binaryBasis_prod_left sourcePair dirtyLabel
            ⟨fieldIndex.val, by omega⟩).symm
        _ = _ := by
          calc
            _ = (BinaryBasis.bigEndianEquiv (extra + ((high + high) + 1))).symm
                sourceLabel ⟨extra + fieldIndex.val, by omega⟩ := by
              simpa only [sourceLabel] using
                (binaryBasis_prod_right unused overflowLabel
                  ⟨fieldIndex.val, by omega⟩).symm
            _ = _ := congrArg
              (fun position => (BinaryBasis.bigEndianEquiv
                (extra + ((high + high) + 1))).symm sourceLabel position)
              sourcePosition
    · by_cases inTarget : index.val < extra + high + high
      · let fieldIndex : Fin high := ⟨index.val - (extra + high), by omega⟩
        have indexValue : index.val = extra + (high + fieldIndex.val) := by
          dsimp only [fieldIndex]
          omega
        have sourcePosition :
            (⟨extra + (high + fieldIndex.val), by omega⟩ :
              Fin (extra + ((high + high) + 1))) = index := by
          apply Fin.ext
          exact indexValue.symm
        have placed : incrementPlacementPosition extra high index =
            (⟨fieldIndex.val, by omega⟩ : Fin ((high + (extra + high)) + 1)) := by
          apply Fin.ext
          rw [incrementPlacementPosition_val]
          simp only [inBorrowed, inTarget, ↓reduceIte]
          dsimp only [fieldIndex]
        rw [placed]
        calc
          _ = (BinaryBasis.bigEndianEquiv (high + (extra + high))).symm
              targetPair ⟨fieldIndex.val, by omega⟩ :=
            binaryBasis_prod_left targetPair dirtyLabel
              ⟨fieldIndex.val, by omega⟩
          _ = (BinaryBasis.bigEndianEquiv high).symm target fieldIndex :=
            binaryBasis_prod_left target lowLabel fieldIndex
          _ = (BinaryBasis.bigEndianEquiv (high + high)).symm sourcePair
              ⟨high + fieldIndex.val, by omega⟩ :=
            (binaryBasis_prod_right borrowed target fieldIndex).symm
          _ = (BinaryBasis.bigEndianEquiv ((high + high) + 1)).symm
              overflowLabel ⟨high + fieldIndex.val, by omega⟩ :=
            (binaryBasis_prod_left sourcePair dirtyLabel
              ⟨high + fieldIndex.val, by omega⟩).symm
          _ = _ := by
            calc
              _ = (BinaryBasis.bigEndianEquiv (extra + ((high + high) + 1))).symm
                  sourceLabel ⟨extra + (high + fieldIndex.val), by omega⟩ := by
                simpa only [sourceLabel, Nat.add_assoc] using
                  (binaryBasis_prod_right unused overflowLabel
                    ⟨high + fieldIndex.val, by omega⟩).symm
              _ = _ := congrArg
                (fun position => (BinaryBasis.bigEndianEquiv
                  (extra + ((high + high) + 1))).symm sourceLabel position)
                sourcePosition
      · have indexValue : index.val = extra + high + high := by
          have bound : index.val < extra + (2 * high + 1) := by
            simpa only [TTK.ttkOverflowEncoding_width] using index.isLt
          omega
        have sourcePosition :
            (⟨extra + (high + high), by omega⟩ :
              Fin (extra + ((high + high) + 1))) = index := by
          apply Fin.ext
          change extra + (high + high) = index.val
          omega
        have placed : incrementPlacementPosition extra high index =
            (⟨high + extra + high, by omega⟩ :
              Fin ((high + (extra + high)) + 1)) := by
          apply Fin.ext
          rw [incrementPlacementPosition_val]
          simp only [inBorrowed, inTarget, ↓reduceIte]
        let bit : Fin 1 := ⟨0, by omega⟩
        rw [placed]
        calc
          _ = (BinaryBasis.bigEndianEquiv 1).symm dirtyLabel bit := by
            simpa only [bit, targetLabel, Nat.add_assoc, Nat.add_zero] using
              binaryBasis_prod_right targetPair dirtyLabel bit
          _ = (BinaryBasis.bigEndianEquiv ((high + high) + 1)).symm
              overflowLabel ⟨high + high, by omega⟩ := by
            simpa only [bit, overflowLabel, Nat.add_zero] using
              (binaryBasis_prod_right sourcePair dirtyLabel bit).symm
          _ = _ := by
            calc
              _ = (BinaryBasis.bigEndianEquiv (extra + ((high + high) + 1))).symm
                  sourceLabel ⟨extra + (high + high), by omega⟩ := by
                simpa only [sourceLabel] using
                  (binaryBasis_prod_right unused overflowLabel
                    ⟨high + high, by omega⟩).symm
              _ = _ := congrArg
                (fun position => (BinaryBasis.bigEndianEquiv
                  (extra + ((high + high) + 1))).symm sourceLabel position)
                sourcePosition

private def incrementGrouping (extra high : Nat) :
    BridgeRegisters (Fin (2 ^ (extra + high))) high ≃
      (Fin (2 ^ extra) × TTK.OverflowRegisters high) where
  toFun state :=
    let fields := (prodEquiv (m := extra) (n := high)).symm state.1.1
    (fields.1, ((fields.2, state.1.2), state.2))
  invFun state := ((prodEquiv (state.1, state.2.1.1), state.2.1.2), state.2.2)
  left_inv state := by
    rcases state with ⟨⟨low, target⟩, dirty⟩
    simp
  right_inv state := by
    rcases state with ⟨unused, ⟨borrowed, target⟩, dirty⟩
    simp

private def incrementFullPlacement (extra high : Nat) :
    EncodedBit.FullPlacement (incrementSourceEncoding extra high)
      (bridgeEncoding (extra + high) high) :=
  EncodedBit.FullPlacement.ofGrouping _ _ (incrementGrouping extra high)
    (Equiv.ofBijective (incrementPlacementPosition extra high)
      ⟨(incrementPlacementPosition extra high).injective,
        incrementPlacementPosition_surjective extra high⟩) (by
      rintro ⟨⟨low, target⟩, dirty⟩ index
      obtain ⟨⟨unused, borrowed⟩, rfl⟩ :=
        (prodEquiv (m := extra) (n := high)).surjective low
      have selected := congrFun
        (incrementPlacement_selectedInput extra high unused borrowed target dirty) index
      change (BinaryBasis.bigEndianEquiv (bridgeEncoding (extra + high) high).width).symm
        ((bridgeEncoding (extra + high) high).encode
          ((prodEquiv (unused, borrowed), target), dirty))
        (incrementPlacementPosition extra high index) =
          (BinaryBasis.bigEndianEquiv (incrementSourceEncoding extra high).width).symm
            ((incrementSourceEncoding extra high).encode
              (unused, ((borrowed, target), dirty))) index at selected
      dsimp only [incrementGrouping, Equiv.coe_fn_mk]
      rw [Equiv.symm_apply_apply]
      exact selected)

/-- The original incrementer's native list on the existing high/low/dirty wires. -/
def placedIncrementGates (extra high : Nat) :
    List (EncodedBit.GateSpec (bridgeEncoding (extra + high) high)) :=
  ((controlledBorrowedIncrementGates high).map
    (EncodedBit.GateSpec.prodRight (BinaryLabelEncoding.finIdentity extra))).map
      (incrementFullPlacement extra high).placeGate

/-- The literal placed list increments the high word and restores its borrowed low bits. -/
lemma hrsPlacedIncrementGates_step (extra high : Nat)
    (state : BridgeRegisters (Fin (2 ^ (extra + high))) high) :
    EncodedBit.GateSpec.stepList (placedIncrementGates extra high) state =
      bridgeIncrementStep state := by
  rw [placedIncrementGates, EncodedBit.FullPlacement.placeGates_step]
  rcases state with ⟨⟨low, target⟩, dirty⟩
  obtain ⟨⟨unused, borrowed⟩, rfl⟩ :=
    (prodEquiv (m := extra) (n := high)).surjective low
  simp only [EncodedBit.FullPlacement.step, incrementFullPlacement,
    EncodedBit.FullPlacement.ofGrouping, incrementGrouping,
    Equiv.coe_fn_mk, Equiv.symm_apply_apply,
    EncodedBit.GateSpec.stepList_prodRight, hrsControlledBorrowedIncrement_step]
  cases dirty <;> rfl

/-- Run the literal native incrementer at its original borrowed physical coordinates. -/
def placedIncrementProgram (extra high : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (bridgeEncoding (extra + high) high).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (placedIncrementGates extra high)

/-- The placed actual program increments only the high word when the dirty bit is set. -/
lemma hrsPlacedIncrement_realizes (extra high : Nat) :
    UnitaryCircuit.Realizes (bridgeEncoding (extra + high) high)
      (placedIncrementProgram extra high) environment bridgeIncrementStep :=
  EncodedBit.GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (placedIncrementGates extra high) (hrsPlacedIncrementGates_step extra high) environment

/-- The canonical physical layout is exactly the low word, high word, and one dirty bit. -/
lemma hrsPlacedIncrement_physical_range (extra high : Nat) :
    (QubitLayout.canonical (bridgeEncoding (extra + high) high).width).systemIdx =
      List.range ((extra + high) + high + 1) := by
  rw [hrsBridgeEncoding_width]
  exact QubitLayout.canonical_systemIdx ((extra + high) + high + 1)

/-- Placement retains the original actual native-event ledger and evaluated depth. -/
lemma hrsPlacedIncrement_resources (extra high : Nat)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (placedIncrementProgram extra high).eventCost =
        (controlledBorrowedIncrementProgram high).eventCost ∧
      (placedIncrementProgram extra high).evaluatedEventDepth assign =
        (controlledBorrowedIncrementProgram high).evaluatedEventDepth assign := by
  constructor
  · simp only [placedIncrementProgram, controlledBorrowedIncrementProgram,
      EncodedBit.GateSpec.programList_eventCost, placedIncrementGates,
      List.map_map, Function.comp_def, EncodedBit.FullPlacement.placeGate_event,
      EncodedBit.GateSpec.event_prodRight]
  · simp only [UnitaryCircuit.evaluatedEventDepth, placedIncrementProgram,
      controlledBorrowedIncrementProgram, EncodedBit.GateSpec.programList_eventDepth,
      placedIncrementGates, List.map_map, Function.comp_def,
      EncodedBit.FullPlacement.placeGate_event, EncodedBit.GateSpec.event_prodRight]

end

end QuantumAlg.MAU.Addition.HRS
