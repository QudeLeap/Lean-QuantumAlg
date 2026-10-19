/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Native
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program

/-!
# Actual coordinate and auxiliary ports for constant-unit conversion

The native two-word multiplier uses the selected original X or Y word and
then the existing A word. One explicit physical wire permutation supplies
its complete binary grouping, retaining every other original frame bit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open MeasuredUncompute

/-- The coordinate port is the original physical X or Y word in the shared EEA frame. -/
def coordinateStart (width : Nat) : MeasuredPointAddition.Coordinate → Nat
  | .x => width + 6
  | .y => 2 * width + 6 + ProductPlacement.tailWidth width

private def portAddress (width start index : Nat) : Nat :=
  if index < width then start + index
  else if index < start + width then index - width else index

private def portInverse (width start index : Nat) : Nat :=
  if index < start then index + width
  else if index < start + width then index - start else index

private def portWires (total width start : Nat) (fits : start + width ≤ total) :
    Equiv.Perm (Fin total) where
  toFun index := ⟨portAddress width start index.val, by
    have bound := index.isLt
    unfold portAddress
    split_ifs <;> omega⟩
  invFun index := ⟨portInverse width start index.val, by
    have bound := index.isLt
    unfold portInverse
    split_ifs <;> omega⟩
  left_inv index := by
    apply Fin.ext
    change portInverse width start (portAddress width start index.val) = index.val
    unfold portAddress portInverse
    split_ifs <;> omega
  right_inv index := by
    apply Fin.ext
    change portAddress width start (portInverse width start index.val) = index.val
    unfold portAddress portInverse
    split_ifs <;> omega

/-- All original small history fields remain beside the two actual conversion words. -/
def retainedWidth (width : Nat) : Nat := width + ProductPlacement.historyWidth width

/-- The native multiplier sees the selected coordinate, A, and all retained fields. -/
def sourceEncoding (width : Nat) :=
  BinaryLabelEncoding.prod (MAU.Multiplication.Accumulate.Gidney.encoding width)
    (BinaryLabelEncoding.finIdentity (retainedWidth width))

private lemma encoding_width (width : Nat) :
    (sourceEncoding width).width = (ProductPlacement.frameEncoding width).width := by
  rw [ProductPlacement.frame_width]
  change (width + width) + retainedWidth width = _
  unfold retainedWidth ProductPlacement.historyWidth ProductWires.width
  omega

private lemma source_total (width : Nat) :
    Function.Surjective (sourceEncoding width).encode := by
  intro label
  obtain ⟨⟨pair, rest⟩, rfl⟩ :=
    (prodEquiv (m := width + width) (n := retainedWidth width)).surjective label
  obtain ⟨⟨input, auxiliary⟩, rfl⟩ := (prodEquiv (m := width) (n := width)).surjective pair
  exact ⟨((input, auxiliary), rest), rfl⟩

/-- The first native word is the selected coordinate, and the second is the existing A word. -/
def wires (width : Nat) (coordinate : MeasuredPointAddition.Coordinate) :
    Fin (sourceEncoding width).width ≃ Fin (ProductPlacement.frameEncoding width).width :=
  (finCongr (encoding_width width)).trans
    (portWires _ width (coordinateStart width coordinate) (by
      rw [ProductPlacement.frame_width]
      cases coordinate <;>
        simp only [coordinateStart, ProductWires.width, ProductPlacement.tailWidth] <;> omega))

/-- The complete field grouping and physical circuit placement come from the same wire map. -/
def placement (width : Nat) (coordinate : MeasuredPointAddition.Coordinate) :
    EncodedBit.FullPlacement (sourceEncoding width) (ProductPlacement.frameEncoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (source_total width) (ProductPlacement.frame_total width)
    (wires width coordinate)

/-- Every native input-word bit addresses its original coordinate bit. -/
lemma wires_coordinate (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (index : Fin width) :
    (wires width coordinate ⟨index.val, by
      change index.val < (width + width) + retainedWidth width
      have bound := index.isLt
      omega⟩).val = coordinateStart width coordinate + index.val := by
  change portAddress width (coordinateStart width coordinate) index.val = _
  simp only [portAddress, if_pos index.isLt]

/-- Every native auxiliary-word bit addresses the already resident A word at
physical offset zero. -/
lemma wires_auxiliary (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (index : Fin width) :
    (wires width coordinate ⟨width + index.val, by
      change width + index.val < (width + width) + retainedWidth width
      have bound := index.isLt
      omega⟩).val = index.val := by
  have separate : width ≤ coordinateStart width coordinate := by
    cases coordinate <;> simp only [coordinateStart] <;> omega
  have bound := index.isLt
  change portAddress width (coordinateStart width coordinate) (width + index.val) = _
  rw [portAddress, if_neg (by omega), if_pos (by omega)]
  omega

/-- Grouping reads exactly the corresponding real physical bit for every complete input. -/
lemma grouping_bit (width : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (state : ProductPlacement.Frame width) (index : Fin (sourceEncoding width).width) :
    ((sourceEncoding width).encode ((placement width coordinate).grouping state)).val.testBit
        index.rev.val =
      ((ProductPlacement.frameEncoding width).encode state).val.testBit
        (wires width coordinate index).rev.val := by
  have actual := EncodedBit.FullPlacement.wireBasis_bit (sourceEncoding width)
    (ProductPlacement.frameEncoding width) (wires width coordinate)
    ((sourceEncoding width).encode ((placement width coordinate).grouping state)) index
  have encoded := (placement width coordinate).basis_encode state
  change EncodedBit.FullPlacement.wireBasis _ _ (wires width coordinate)
    ((sourceEncoding width).encode ((placement width coordinate).grouping state)) = _ at encoded
  rw [encoded] at actual
  exact actual.symm

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
