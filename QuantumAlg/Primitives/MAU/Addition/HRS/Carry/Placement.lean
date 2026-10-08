/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.WorkLayout
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Place the HRS carry inside the inactive high word

The high word contains `low - 2` internally borrowed bits followed by
`extra` unused bits. The carry body acts on the low word, its dirty output,
and the borrowed prefix. An explicit typed placement sends those source
coordinates to the existing high/low/dirty carrier and leaves every unused
high-word coordinate as a spectator [HRS16, paper.tex:232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

private def carryPlacementWire (low extra index : Nat) : Nat :=
  if index < low then (low - 2) + extra + index
  else if index = low then (low - 2) + extra + low
  else index - (low + 1)

private theorem carryPlacementWire_range (low extra index : Nat)
    (within : index < low + (low - 2 + 1)) :
    carryPlacementWire low extra index < low + ((low - 2) + extra) + 1 := by
  unfold carryPlacementWire
  split_ifs <;> omega

private theorem carryPlacementWire_injective_on (low extra : Nat)
    {left right : Nat}
    (leftWithin : left < low + (low - 2 + 1))
    (rightWithin : right < low + (low - 2 + 1))
    (same : carryPlacementWire low extra left = carryPlacementWire low extra right) :
    left = right := by
  unfold carryPlacementWire at same
  split_ifs at same <;> omega

/-- Source carry coordinates embedded into the shared high/low/dirty carrier. -/
def carryPlacementPosition (low extra : Nat) :
    Fin (carryEncoding low).width ↪
      Fin (bridgeEncoding low ((low - 2) + extra)).width where
  toFun index :=
    ⟨carryPlacementWire low extra index.val, by
      rw [hrsBridgeEncoding_width]
      apply carryPlacementWire_range
      exact index.isLt⟩
  inj' := by
    intro left right same
    apply Fin.ext
    apply carryPlacementWire_injective_on low extra left.isLt right.isLt
    exact congrArg Fin.val same

private theorem carryPlacementDimensions (low extra : Nat)
    (index : Fin (carryEncoding low).width) :
    ((QubitLayout.canonical (carryEncoding low).width).toQuantum.wire index).dimension =
      ((QubitLayout.canonical
        (bridgeEncoding low ((low - 2) + extra)).width).toQuantum.wire
          (carryPlacementPosition low extra index)).dimension := by
  simp

private def carryBasis (low : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (dirty : Bool) :
    (QubitLayout.canonical (carryEncoding low).width).toQuantum.Basis :=
  (QubitLayout.canonical (carryEncoding low).width).basisEquiv.symm
    ((carryEncoding low).encode (input, carryWorkEquiv low (borrowed, dirty)))

private def bridgeBasis (low extra : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (unused : Fin (2 ^ extra)) (dirty : Bool) :
    (QubitLayout.canonical
      (bridgeEncoding low ((low - 2) + extra)).width).toQuantum.Basis :=
  (QubitLayout.canonical
    (bridgeEncoding low ((low - 2) + extra)).width).basisEquiv.symm
      ((bridgeEncoding low ((low - 2) + extra)).encode
        ((input, prodEquiv (borrowed, unused)), dirty))

private theorem carryWorkBasis_dirty (low : Nat)
    (borrowed : Fin (2 ^ (low - 2))) (dirty : Bool) :
    (BinaryBasis.bigEndianEquiv (low - 2 + 1)).symm
        (carryWorkEquiv low (borrowed, dirty)) ⟨0, by omega⟩ =
      finTwoEquiv.symm dirty := by
  rw [BinaryBasis.bigEndianEquiv_symm_value]
  have bit := hrsCarryWorkEquiv_dirty low borrowed dirty
  have position : (⟨0, by omega⟩ : Fin (low - 2 + 1)).rev.val = low - 2 := by
    simp
  rw [position, bit]

private theorem carryWorkBasis_borrowed (low : Nat)
    (borrowed : Fin (2 ^ (low - 2))) (dirty : Bool) (index : Fin (low - 2)) :
    (BinaryBasis.bigEndianEquiv (low - 2 + 1)).symm
        (carryWorkEquiv low (borrowed, dirty)) ⟨1 + index.val, by omega⟩ =
      (BinaryBasis.bigEndianEquiv (low - 2)).symm borrowed index := by
  simp only [BinaryBasis.bigEndianEquiv_symm_value]
  have position : (⟨1 + index.val, by omega⟩ : Fin (low - 2 + 1)).rev.val =
      index.rev.val := by
    simp only [Fin.val_rev]
    have := index.isLt
    omega
  rw [position, hrsCarryWorkEquiv_borrowed low borrowed dirty index.rev]

private theorem carryBasis_input (low : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (dirty : Bool) (index : Fin low) :
    carryBasis low input borrowed dirty
        (Fin.castAdd (low - 2 + 1) index) =
      (BinaryBasis.bigEndianEquiv low).symm input index := by
  change (BinaryBasis.bigEndianEquiv (low + (low - 2 + 1))).symm
      (prodEquiv (input, carryWorkEquiv low (borrowed, dirty)))
        (Fin.castAdd (low - 2 + 1) index) = _
  exact BinaryBasis.bigEndianEquiv_prod_left input
    (carryWorkEquiv low (borrowed, dirty)) index

private theorem carryBasis_dirty (low : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (dirty : Bool) :
    carryBasis low input borrowed dirty ⟨low, by
      change low < low + (low - 2 + 1)
      omega⟩ = finTwoEquiv.symm dirty := by
  have outer := BinaryBasis.bigEndianEquiv_prod_right input
    (carryWorkEquiv low (borrowed, dirty)) (⟨0, by omega⟩ : Fin (low - 2 + 1))
  change (BinaryBasis.bigEndianEquiv (low + (low - 2 + 1))).symm
      (prodEquiv (input, carryWorkEquiv low (borrowed, dirty))) _ = _
  rw [show (⟨low, by
      change low < low + (low - 2 + 1)
      omega⟩ : Fin (carryEncoding low).width) =
        Fin.natAdd low (⟨0, by omega⟩ : Fin (low - 2 + 1)) by
    apply Fin.ext
    rfl]
  exact outer.trans (carryWorkBasis_dirty low borrowed dirty)

private theorem carryBasis_borrowed (low : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (dirty : Bool) (index : Fin (low - 2)) :
    carryBasis low input borrowed dirty ⟨low + 1 + index.val, by
      change low + 1 + index.val < low + (low - 2 + 1)
      omega⟩ =
      (BinaryBasis.bigEndianEquiv (low - 2)).symm borrowed index := by
  have outer := BinaryBasis.bigEndianEquiv_prod_right input
    (carryWorkEquiv low (borrowed, dirty))
      (⟨1 + index.val, by omega⟩ : Fin (low - 2 + 1))
  change (BinaryBasis.bigEndianEquiv (low + (low - 2 + 1))).symm
      (prodEquiv (input, carryWorkEquiv low (borrowed, dirty))) _ = _
  rw [show (⟨low + 1 + index.val, by
      change low + 1 + index.val < low + (low - 2 + 1)
      omega⟩ : Fin (carryEncoding low).width) =
        Fin.natAdd low (⟨1 + index.val, by omega⟩ : Fin (low - 2 + 1)) by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    omega]
  exact outer.trans (carryWorkBasis_borrowed low borrowed dirty index)

private theorem bridgeBasis_input (low extra : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (unused : Fin (2 ^ extra))
    (dirty : Bool) (index : Fin low) :
    bridgeBasis low extra input borrowed unused dirty
        ⟨(low - 2) + extra + index.val, by rw [hrsBridgeEncoding_width]; omega⟩ =
      (BinaryBasis.bigEndianEquiv low).symm input index := by
  have outer := BinaryBasis.bigEndianEquiv_prod_left
    (prodEquiv (prodEquiv (borrowed, unused), input))
    (BinaryLabelEncoding.bool.encode dirty)
    (Fin.natAdd ((low - 2) + extra) index)
  have inner := BinaryBasis.bigEndianEquiv_prod_right
    (prodEquiv (borrowed, unused)) input index
  change (BinaryBasis.bigEndianEquiv
      (low - 2 + extra + low + BinaryLabelEncoding.bool.width)).symm
      (prodEquiv (prodEquiv (prodEquiv (borrowed, unused), input),
        BinaryLabelEncoding.bool.encode dirty)) _ = _
  rw [show (⟨(low - 2) + extra + index.val, by
      rw [hrsBridgeEncoding_width]
      omega⟩ : Fin (bridgeEncoding low ((low - 2) + extra)).width) =
        Fin.castAdd BinaryLabelEncoding.bool.width
          (Fin.natAdd ((low - 2) + extra) index) by
      apply Fin.ext
      rfl]
  exact outer.trans inner

private theorem bridgeBasis_dirty (low extra : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (unused : Fin (2 ^ extra)) (dirty : Bool) :
    bridgeBasis low extra input borrowed unused dirty
        ⟨(low - 2) + extra + low, by rw [hrsBridgeEncoding_width]; omega⟩ =
      finTwoEquiv.symm dirty := by
  have outer := BinaryBasis.bigEndianEquiv_prod_right
    (prodEquiv (prodEquiv (borrowed, unused), input))
    (BinaryLabelEncoding.bool.encode dirty) (0 : Fin 1)
  change (BinaryBasis.bigEndianEquiv
      (low - 2 + extra + low + BinaryLabelEncoding.bool.width)).symm
      (prodEquiv (prodEquiv (prodEquiv (borrowed, unused), input),
        BinaryLabelEncoding.bool.encode dirty)) _ = _
  rw [show (⟨(low - 2) + extra + low, by
      rw [hrsBridgeEncoding_width]
      omega⟩ : Fin (bridgeEncoding low ((low - 2) + extra)).width) =
        Fin.natAdd (low - 2 + extra + low) (0 : Fin 1) by
      apply Fin.ext
      rfl]
  exact outer.trans (by cases dirty <;> rfl)

private theorem bridgeBasis_borrowed (low extra : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (unused : Fin (2 ^ extra))
    (dirty : Bool) (index : Fin (low - 2)) :
    bridgeBasis low extra input borrowed unused dirty ⟨index.val, by
        rw [hrsBridgeEncoding_width]
        omega⟩ =
      (BinaryBasis.bigEndianEquiv (low - 2)).symm borrowed index := by
  have outer := BinaryBasis.bigEndianEquiv_prod_left
    (prodEquiv (prodEquiv (borrowed, unused), input))
    (BinaryLabelEncoding.bool.encode dirty)
    (Fin.castAdd low (Fin.castAdd extra index))
  have middle := BinaryBasis.bigEndianEquiv_prod_left
    (prodEquiv (borrowed, unused)) input (Fin.castAdd extra index)
  have inner := BinaryBasis.bigEndianEquiv_prod_left borrowed unused index
  change (BinaryBasis.bigEndianEquiv
      (low - 2 + extra + low + BinaryLabelEncoding.bool.width)).symm
      (prodEquiv (prodEquiv (prodEquiv (borrowed, unused), input),
        BinaryLabelEncoding.bool.encode dirty)) _ = _
  rw [show (⟨index.val, by
      rw [hrsBridgeEncoding_width]
      omega⟩ : Fin (bridgeEncoding low ((low - 2) + extra)).width) =
        Fin.castAdd BinaryLabelEncoding.bool.width
          (Fin.castAdd low (Fin.castAdd extra index)) by
      apply Fin.ext
      rfl]
  exact outer.trans (middle.trans inner)

private theorem carryPlacement_selected (low extra : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (unused : Fin (2 ^ extra)) (dirty : Bool) :
    UnitaryCircuit.selectedInput
        (QubitLayout.canonical (carryEncoding low).width).toQuantum
        (QubitLayout.canonical
          (bridgeEncoding low ((low - 2) + extra)).width).toQuantum
        (carryPlacementPosition low extra) (carryPlacementDimensions low extra)
        (bridgeBasis low extra input borrowed unused dirty) =
      carryBasis low input borrowed dirty := by
  funext index
  apply Fin.ext
  change (bridgeBasis low extra input borrowed unused dirty
      (carryPlacementPosition low extra index)).val =
    (carryBasis low input borrowed dirty index).val
  by_cases inputCoordinate : index.val < low
  · let source : Fin low := ⟨index.val, inputCoordinate⟩
    have sourceIndex : index = Fin.castAdd (low - 2 + 1) source := Fin.ext rfl
    have targetIndex : carryPlacementPosition low extra index =
        ⟨(low - 2) + extra + source.val, by rw [hrsBridgeEncoding_width]; omega⟩ := by
      apply Fin.ext
      simp [carryPlacementPosition, carryPlacementWire, inputCoordinate, source]
    calc
      (bridgeBasis low extra input borrowed unused dirty
          (carryPlacementPosition low extra index)).val =
          (bridgeBasis low extra input borrowed unused dirty
            ⟨(low - 2) + extra + source.val, by
              rw [hrsBridgeEncoding_width]
              omega⟩).val := congrArg
                (fun position => (bridgeBasis low extra input borrowed unused dirty position).val)
                targetIndex
      _ = ((BinaryBasis.bigEndianEquiv low).symm input source).val := congrArg Fin.val
        (bridgeBasis_input low extra input borrowed unused dirty source)
      _ = (carryBasis low input borrowed dirty
          (Fin.castAdd (low - 2 + 1) source)).val := (congrArg Fin.val
            (carryBasis_input low input borrowed dirty source)).symm
      _ = (carryBasis low input borrowed dirty index).val := congrArg
        (fun position => (carryBasis low input borrowed dirty position).val) sourceIndex.symm
  · by_cases dirtyCoordinate : index.val = low
    · have lowWithin : low < (carryEncoding low).width := by
        change low < low + (low - 2 + 1)
        omega
      have sourceIndex : index = ⟨low, lowWithin⟩ := Fin.ext dirtyCoordinate
      have targetIndex : carryPlacementPosition low extra index =
          ⟨(low - 2) + extra + low, by rw [hrsBridgeEncoding_width]; omega⟩ := by
        apply Fin.ext
        simp [carryPlacementPosition, carryPlacementWire, dirtyCoordinate]
      calc
        (bridgeBasis low extra input borrowed unused dirty
            (carryPlacementPosition low extra index)).val =
            (bridgeBasis low extra input borrowed unused dirty
              ⟨(low - 2) + extra + low, by
                rw [hrsBridgeEncoding_width]
                omega⟩).val := congrArg
                  (fun position =>
                    (bridgeBasis low extra input borrowed unused dirty position).val)
                  targetIndex
        _ = (finTwoEquiv.symm dirty).val := congrArg Fin.val
          (bridgeBasis_dirty low extra input borrowed unused dirty)
        _ = (carryBasis low input borrowed dirty ⟨low, lowWithin⟩).val :=
          (congrArg Fin.val (carryBasis_dirty low input borrowed dirty)).symm
        _ = (carryBasis low input borrowed dirty index).val := congrArg
          (fun position => (carryBasis low input borrowed dirty position).val)
          sourceIndex.symm
    · have indexWithin : index.val < low + (low - 2 + 1) := by
          have within := index.isLt
          change index.val < low + (low - 2 + 1) at within
          exact within
      let source : Fin (low - 2) := ⟨index.val - (low + 1), by
          omega⟩
      have sourceIndex : index = ⟨low + 1 + source.val, by
          change low + 1 + source.val < low + (low - 2 + 1)
          have := source.isLt
          omega⟩ := by
        apply Fin.ext
        dsimp [source]
        omega
      have targetIndex : carryPlacementPosition low extra index =
          ⟨source.val, by rw [hrsBridgeEncoding_width]; omega⟩ := by
        apply Fin.ext
        simp [carryPlacementPosition, carryPlacementWire, inputCoordinate,
          dirtyCoordinate, source]
      calc
        (bridgeBasis low extra input borrowed unused dirty
            (carryPlacementPosition low extra index)).val =
            (bridgeBasis low extra input borrowed unused dirty
              ⟨source.val, by rw [hrsBridgeEncoding_width]; omega⟩).val := congrArg
                (fun position =>
                  (bridgeBasis low extra input borrowed unused dirty position).val)
                targetIndex
        _ = ((BinaryBasis.bigEndianEquiv (low - 2)).symm borrowed source).val :=
          congrArg Fin.val (bridgeBasis_borrowed low extra input borrowed unused dirty source)
        _ = (carryBasis low input borrowed dirty
            ⟨low + 1 + source.val, by
              change low + 1 + source.val < low + (low - 2 + 1)
              have := source.isLt
              omega⟩).val := (congrArg Fin.val
                (carryBasis_borrowed low input borrowed dirty source)).symm
        _ = (carryBasis low input borrowed dirty index).val := congrArg
          (fun position => (carryBasis low input borrowed dirty position).val)
          sourceIndex.symm

private abbrev carryFullEncoding (low extra : Nat) :=
  BinaryLabelEncoding.prod (carryEncoding low) (BinaryLabelEncoding.finIdentity extra)

private def carryFullGrouping (low extra : Nat) :
    BridgeRegisters (Fin (2 ^ low)) ((low - 2) + extra) ≃
      (CarryRegisters low × Fin (2 ^ extra)) where
  toFun state :=
    let high := (prodEquiv (m := low - 2) (n := extra)).symm state.1.2
    ((state.1.1, carryWorkEquiv low (high.1, state.2)), high.2)
  invFun state :=
    let work := (carryWorkEquiv low).symm state.1.2
    ((state.1.1, prodEquiv (work.1, state.2)), work.2)
  left_inv state := by
    rcases state with ⟨⟨input, high⟩, dirty⟩
    simp
  right_inv state := by
    rcases state with ⟨⟨input, work⟩, unused⟩
    simp

private def carryFullPosition (low extra : Nat) :
    Fin (carryFullEncoding low extra).width ↪
      Fin (bridgeEncoding low ((low - 2) + extra)).width where
  toFun index := ⟨carryPlacementWire low extra index.val, by
    have within : index.val < low + (low - 2 + 1) + extra := index.isLt
    rw [hrsBridgeEncoding_width]
    unfold carryPlacementWire
    split_ifs <;> omega⟩
  inj' := by
    intro first second same
    apply Fin.ext
    have firstBound : first.val < low + (low - 2 + 1) + extra := first.isLt
    have secondBound : second.val < low + (low - 2 + 1) + extra := second.isLt
    have values := congrArg Fin.val same
    change carryPlacementWire low extra first.val =
      carryPlacementWire low extra second.val at values
    unfold carryPlacementWire at values
    split_ifs at values <;> omega

private theorem carryFullPosition_surjective (low extra : Nat) :
    Function.Surjective (carryFullPosition low extra) := by
  intro target
  have bound : target.val < low + ((low - 2) + extra) + 1 := by
    simpa only [hrsBridgeEncoding_width] using target.isLt
  by_cases high : target.val < (low - 2) + extra
  · refine ⟨⟨low + 1 + target.val, by
      change low + 1 + target.val < low + (low - 2 + 1) + extra
      omega⟩, ?_⟩
    apply Fin.ext
    change carryPlacementWire low extra (low + 1 + target.val) = target.val
    unfold carryPlacementWire
    split_ifs <;> omega
  · by_cases dirty : target.val = (low - 2) + extra + low
    · refine ⟨⟨low, by
        change low < low + (low - 2 + 1) + extra
        omega⟩, ?_⟩
      apply Fin.ext
      change carryPlacementWire low extra low = target.val
      simp [carryPlacementWire, dirty]
    · refine ⟨⟨target.val - ((low - 2) + extra), by
        change target.val - ((low - 2) + extra) < low + (low - 2 + 1) + extra
        omega⟩, ?_⟩
      apply Fin.ext
      change carryPlacementWire low extra (target.val - ((low - 2) + extra)) = target.val
      unfold carryPlacementWire
      split_ifs <;> omega

private theorem bridgeBasis_unused (low extra : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (unused : Fin (2 ^ extra))
    (dirty : Bool) (index : Fin extra) :
    bridgeBasis low extra input borrowed unused dirty
      ⟨(low - 2) + index.val, by rw [hrsBridgeEncoding_width]; omega⟩ =
        (BinaryBasis.bigEndianEquiv extra).symm unused index := by
  change (BinaryBasis.bigEndianEquiv
    (((low - 2) + extra) + low + 1)).symm
      (prodEquiv (prodEquiv (prodEquiv (borrowed, unused), input),
        BinaryLabelEncoding.bool.encode dirty)) _ = _
  exact (BinaryBasis.bigEndianEquiv_prod_left
    (prodEquiv (prodEquiv (borrowed, unused), input))
    (BinaryLabelEncoding.bool.encode dirty)
    (Fin.castAdd low (Fin.natAdd (low - 2) index))).trans
      ((BinaryBasis.bigEndianEquiv_prod_left (prodEquiv (borrowed, unused)) input
        (Fin.natAdd (low - 2) index)).trans
          (BinaryBasis.bigEndianEquiv_prod_right borrowed unused index))

private theorem carryFull_coordinates (low extra : Nat)
    (state : BridgeRegisters (Fin (2 ^ low)) ((low - 2) + extra))
    (index : Fin (carryFullEncoding low extra).width) :
    (BinaryBasis.bigEndianEquiv (bridgeEncoding low ((low - 2) + extra)).width).symm
        ((bridgeEncoding low ((low - 2) + extra)).encode state)
        (carryFullPosition low extra index) =
      (BinaryBasis.bigEndianEquiv (carryFullEncoding low extra).width).symm
        ((carryFullEncoding low extra).encode (carryFullGrouping low extra state)) index := by
  rcases state with ⟨⟨input, high⟩, dirty⟩
  obtain ⟨⟨borrowed, unused⟩, rfl⟩ :=
    (prodEquiv (m := low - 2) (n := extra)).surjective high
  dsimp only [carryFullGrouping, Equiv.coe_fn_mk]
  rw [Equiv.symm_apply_apply]
  let sourceLabel := (carryEncoding low).encode (input, carryWorkEquiv low (borrowed, dirty))
  change bridgeBasis low extra input borrowed unused dirty (carryFullPosition low extra index) =
    (BinaryBasis.bigEndianEquiv ((carryEncoding low).width + extra)).symm
      (prodEquiv (sourceLabel, unused)) index
  by_cases source : index.val < (carryEncoding low).width
  · let old : Fin (carryEncoding low).width := ⟨index.val, source⟩
    have oldIndex : Fin.castAdd extra old = index := Fin.ext rfl
    have placed : carryFullPosition low extra index = carryPlacementPosition low extra old :=
      Fin.ext rfl
    rw [placed, ← oldIndex, BinaryBasis.bigEndianEquiv_prod_left]
    exact congrFun (carryPlacement_selected low extra input borrowed unused dirty) old
  · let last : Fin extra := ⟨index.val - (carryEncoding low).width, by
      have bound : index.val < (carryEncoding low).width + extra := index.isLt
      omega⟩
    have lastIndex : Fin.natAdd (carryEncoding low).width last = index := by
      apply Fin.ext
      change (carryEncoding low).width + (index.val - (carryEncoding low).width) = index.val
      omega
    have placed : carryFullPosition low extra index =
        ⟨(low - 2) + last.val, by rw [hrsBridgeEncoding_width]; omega⟩ := by
      apply Fin.ext
      change carryPlacementWire low extra index.val = (low - 2) + last.val
      have excluded : low + (low - 2 + 1) ≤ index.val := by exact Nat.le_of_not_gt source
      dsimp only [last]
      change carryPlacementWire low extra index.val =
        (low - 2) + (index.val - (low + (low - 2 + 1)))
      unfold carryPlacementWire
      split_ifs <;> omega
    rw [placed]
    have sourceRead := BinaryBasis.bigEndianEquiv_prod_right sourceLabel unused last
    have same := congrArg
      ((BinaryBasis.bigEndianEquiv ((carryEncoding low).width + extra)).symm
        (prodEquiv (sourceLabel, unused))) lastIndex
    exact (bridgeBasis_unused low extra input borrowed unused dirty last).trans
      (same.symm.trans sourceRead).symm

private def carryFullPlacement (low extra : Nat) :
    EncodedBit.FullPlacement (carryFullEncoding low extra)
      (bridgeEncoding low ((low - 2) + extra)) :=
  EncodedBit.FullPlacement.ofGrouping _ _ (carryFullGrouping low extra)
    (Equiv.ofBijective (carryFullPosition low extra)
      ⟨(carryFullPosition low extra).injective, carryFullPosition_surjective low extra⟩)
    (carryFull_coordinates low extra)

/-- The original carry instructions placed on existing low/high/dirty wires. -/
def placedCarryGates (low extra : Nat) (constant : Fin (2 ^ low)) :
    List (EncodedBit.GateSpec (bridgeEncoding low ((low - 2) + extra))) :=
  ((carryGates low constant).map
    (EncodedBit.GateSpec.prodLeft (BinaryLabelEncoding.finIdentity extra))).map
      (carryFullPlacement low extra).placeGate

/-- The complete literal list restores both words and toggles only the original dirty carry bit. -/
theorem hrsPlacedCarryGates_step (low extra : Nat) (constant : Fin (2 ^ low))
    (state : BridgeRegisters (Fin (2 ^ low)) ((low - 2) + extra)) :
    EncodedBit.GateSpec.stepList (placedCarryGates low extra constant) state =
      bridgeCarryStep (fun input : Fin (2 ^ low) =>
        decide (2 ^ low ≤ input.val + constant.val)) state := by
  rw [placedCarryGates, EncodedBit.FullPlacement.placeGates_step]
  rcases state with ⟨⟨input, high⟩, dirty⟩
  obtain ⟨⟨borrowed, unused⟩, rfl⟩ :=
    (prodEquiv (m := low - 2) (n := extra)).surjective high
  simp only [EncodedBit.FullPlacement.step, carryFullPlacement,
    EncodedBit.FullPlacement.ofGrouping, carryFullGrouping, Equiv.coe_fn_mk,
    Equiv.symm_apply_apply, EncodedBit.GateSpec.stepList_prodLeft, hrsCarry_packed_step]
  change ((input, prodEquiv
      (((carryWorkEquiv low).symm (carryWorkEquiv low
        (borrowed, dirty ^^ decide (2 ^ low ≤ input.val + constant.val)))).1, unused)),
      ((carryWorkEquiv low).symm (carryWorkEquiv low
        (borrowed, dirty ^^ decide (2 ^ low ≤ input.val + constant.val)))).2) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The placed list retains every native coordinate of the actual carry source. -/
theorem hrsPlacedCarryGates_events (low extra : Nat) (constant : Fin (2 ^ low))
    (oracles : OracleModel) :
    (placedCarryGates low extra constant).map (EncodedBit.GateSpec.event oracles) =
      (carryGates low constant).map (EncodedBit.GateSpec.event oracles) := by
  simp only [placedCarryGates, List.map_map, Function.comp_def,
    EncodedBit.FullPlacement.placeGate_event, EncodedBit.GateSpec.event_prodLeft]

/-- Execute the literal carry list on the existing low, borrowed and dirty coordinates. -/
def placedCarryProgram (low extra : Nat) (constant : Fin (2 ^ low)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (bridgeEncoding low ((low - 2) + extra)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (placedCarryGates low extra constant)

/-- The placed carry toggles the final dirty bit and restores the entire low and high words. -/
theorem hrsPlacedCarry_realizes (low extra : Nat) (constant : Fin (2 ^ low)) :
    UnitaryCircuit.Realizes (bridgeEncoding low ((low - 2) + extra))
      (placedCarryProgram low extra constant)
      (bridgeCarryStep (fun input : Fin (2 ^ low) =>
        decide (2 ^ low ≤ input.val + constant.val))) :=
  EncodedBit.GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (placedCarryGates low extra constant) (hrsPlacedCarryGates_step low extra constant)

/-- The canonical carrier contains exactly the high word, low word and dirty bit. -/
theorem hrsPlacedCarry_physical_range (low extra : Nat) :
    (QubitLayout.canonical
      (bridgeEncoding low ((low - 2) + extra)).width).systemIdx =
        List.range (low + ((low - 2) + extra) + 1) := by
  rw [hrsBridgeEncoding_width]
  exact QubitLayout.canonical_systemIdx (low + (low - 2 + extra) + 1)

/-- Exact placement retains the carry's literal resource ledger. -/
theorem hrsPlacedCarry_resources (low extra : Nat) (constant : Fin (2 ^ low))
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (placedCarryProgram low extra constant).eventCost = (carryProgram low constant).eventCost ∧
      (placedCarryProgram low extra constant).evaluatedEventDepth assign =
        (carryProgram low constant).evaluatedEventDepth assign := by
  constructor
  · simp only [placedCarryProgram, carryProgram, EncodedBit.GateSpec.programList_eventCost,
      hrsPlacedCarryGates_events]
  · simp only [UnitaryCircuit.evaluatedEventDepth, placedCarryProgram, carryProgram,
      EncodedBit.GateSpec.programList_eventDepth, hrsPlacedCarryGates_events]

end

end QuantumAlg.MAU.Addition.HRS
