/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Coordinates
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness

/-!
# Exact prepared-frame action of the placed coordinate multiplier

The actual wire grouping retains every prepared history bit when its
selected coordinate changes. On a canonical coordinate, the existing
multiplier restores the original A word to zero and reconstructs the
complete prepared frame with only that coordinate updated.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open MeasuredUncompute BinaryLabelEncoding
open MAU.Inversion.SharedEEA

private lemma shared_width (width : Nat) :
    (MAU.Inversion.SharedEEA.encoding width).width = coordinateStart width .y := by
  rw [MAU.Inversion.SharedEEA.encoding_width]
  simp only [coordinateStart, ProductPlacement.tailWidth]
  omega

private def liftedSharedBit (width : Nat)
    (bit : EncodedBit (MAU.Inversion.SharedEEA.encoding width)) :
    EncodedBit (ProductPlacement.frameEncoding width) :=
  prodLeftBit (MAU.Inversion.SharedEEA.encoding width) (finIdentity width) bit

/-- Every actual prepared bit outside the selected coordinate is independent of its value. -/
private lemma prepared_bit_outside (modulus : Nat)
    (coordinate : MeasuredPointAddition.Coordinate) (x y next : Fin (2 ^ modulus.size))
    (bit : EncodedBit (ProductPlacement.frameEncoding modulus.size))
    (separate : ∀ selected : Fin modulus.size,
      bit.wire ≠ ((coordinateWord modulus.size coordinate).bit selected).wire) :
    bit.get (preparedUpdate modulus coordinate x y next) =
      bit.get (preparedFrame modulus x y) := by
  by_cases shared : bit.wire.val < (MAU.Inversion.SharedEEA.encoding modulus.size).width
  · let index : Fin (MAU.Inversion.SharedEEA.encoding modulus.size).width :=
      ⟨bit.wire.val, shared⟩
    let inner := MeasuredPointAddition.completeBit (MAU.Inversion.SharedEEA.encoding modulus.size)
      (MAU.Inversion.SharedEEA.encoding_surjective modulus.size) index
    have same : bit.wire = (liftedSharedBit modulus.size inner).wire := Fin.ext rfl
    rw [MeasuredPointAddition.bit_get_of_wire_eq bit _ same,
      MeasuredPointAddition.bit_get_of_wire_eq bit _ same]
    cases coordinate with
    | y => rfl
    | x =>
        change inner.get (InitialPortProgram.inputFrame modulus next) =
          inner.get (InitialPortProgram.inputFrame modulus x)
        have outside : inner.wire.val < modulus.size + 6 ∨
            2 * modulus.size + 6 ≤ inner.wire.val := by
          by_contra inside
          let selected : Fin modulus.size := ⟨inner.wire.val - (modulus.size + 6), by omega⟩
          apply separate selected
          apply Fin.ext
          rw [coordinate_wire]
          change inner.wire.val = modulus.size + 6 + selected.val
          dsimp only [selected]
          omega
        exact (MeasuredPointAddition.inputFrame_bit_outside modulus next inner outside).trans
          (MeasuredPointAddition.inputFrame_bit_outside modulus x inner outside).symm
  · have bound := bit.wire.isLt
    change bit.wire.val < (MAU.Inversion.SharedEEA.encoding modulus.size).width + modulus.size
      at bound
    let index : Fin modulus.size :=
      ⟨bit.wire.val - (MAU.Inversion.SharedEEA.encoding modulus.size).width, by omega⟩
    have same : bit.wire = ((FramePorts.numerator modulus.size).bit index).wire := by
      apply Fin.ext
      have ending := shared_width modulus.size
      change (MAU.Inversion.SharedEEA.encoding modulus.size).width =
        2 * modulus.size + 6 + ProductPlacement.tailWidth modulus.size at ending
      rw [FramePorts.numerator_wire, ← ending]
      change bit.wire.val = (MAU.Inversion.SharedEEA.encoding modulus.size).width + index.val
      dsimp only [index]
      omega
    cases coordinate with
    | x =>
        rw [MeasuredPointAddition.bit_get_of_wire_eq bit _ same,
          MeasuredPointAddition.bit_get_of_wire_eq bit _ same]
        rfl
    | y => exact False.elim (separate index same)

/-- Replacing one original coordinate preserves the complete grouped retained frame bit for bit. -/
lemma grouping_prepared_retained (modulus : Nat)
    (coordinate : MeasuredPointAddition.Coordinate) (x y next : Fin (2 ^ modulus.size)) :
    ((placement modulus.size coordinate).grouping
      (preparedUpdate modulus coordinate x y next)).2 =
        ((placement modulus.size coordinate).grouping (preparedFrame modulus x y)).2 := by
  apply ProductReadout.word_ext
  intro index
  let source := retainedBit modulus.size index
  let target := MeasuredPointAddition.completeBit (ProductPlacement.frameEncoding modulus.size)
    (ProductPlacement.frame_total modulus.size) (wires modulus.size coordinate source.wire)
  have separate : ∀ selected : Fin modulus.size,
      target.wire ≠ ((coordinateWord modulus.size coordinate).bit selected).wire := by
    intro selected same
    have inputWire : wires modulus.size coordinate (inputBit modulus.size selected).wire =
        ((coordinateWord modulus.size coordinate).bit selected).wire := by
      apply Fin.ext
      exact (wires_coordinate modulus.size coordinate selected).trans
        (coordinate_wire modulus.size coordinate selected).symm
    have sourceSame := (wires modulus.size coordinate).injective (same.trans inputWire.symm)
    have positions := congrArg Fin.val sourceSame
    change (modulus.size + modulus.size) + index.val = selected.val at positions
    have bound := selected.isLt
    omega
  have actual := (placed_read modulus.size coordinate
    (preparedUpdate modulus coordinate x y next) source target rfl).trans
      ((prepared_bit_outside modulus coordinate x y next target separate).trans
        (placed_read modulus.size coordinate (preparedFrame modulus x y) source target rfl).symm)
  change (finIdentityBit (retainedWidth modulus.size) index).get
    ((placement modulus.size coordinate).grouping
      (preparedUpdate modulus coordinate x y next)).2 =
        (finIdentityBit (retainedWidth modulus.size) index).get
          ((placement modulus.size coordinate).grouping (preparedFrame modulus x y)).2 at actual
  rw [ProductReadout.bit_read, ProductReadout.bit_read] at actual
  exact actual

/-- Complete actual grouping of the updated prepared frame restores A and every retained field. -/
lemma grouping_prepared_update (modulus : Nat)
    (coordinate : MeasuredPointAddition.Coordinate) (x y next : Fin (2 ^ modulus.size)) :
    (placement modulus.size coordinate).grouping (preparedUpdate modulus coordinate x y next) =
      ((next, 0),
        ((placement modulus.size coordinate).grouping (preparedFrame modulus x y)).2) := by
  apply Prod.ext
  · apply Prod.ext
    · cases coordinate <;> exact grouping_prepared_coordinate _ _ _ _
    · cases coordinate <;> exact grouping_prepared_auxiliary _ _ _ _
  · exact grouping_prepared_retained modulus coordinate x y next

private def selectedInput {width : Nat} (coordinate : MeasuredPointAddition.Coordinate)
    (x y : Fin (2 ^ width)) : Fin (2 ^ width) :=
  match coordinate with | .x => x | .y => y

/-- Canonical unit multiplication reconstructs the complete prepared original frame. -/
lemma nativeAction_prepared (modulus : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (x y : Fin (2 ^ modulus.size))
    (valid : (selectedInput coordinate x y).val < modulus) :
    nativeAction modulus.size (InPlaceTarget.modulusWord modulus) coefficient coordinate
        (preparedFrame modulus x y) =
      preparedUpdate modulus coordinate x y
        (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient
          (selectedInput coordinate x y)) := by
  apply (placement modulus.size coordinate).grouping.injective
  change (placement modulus.size coordinate).grouping
    ((placement modulus.size coordinate).grouping.symm _) = _
  rw [Equiv.apply_symm_apply, grouping_prepared_update]
  apply Prod.ext
  · have initial : ((placement modulus.size coordinate).grouping
        (preparedFrame modulus x y)).1 = ((selectedInput coordinate x y), 0) :=
      Prod.ext (grouping_prepared_coordinate modulus coordinate x y)
        (grouping_prepared_auxiliary modulus coordinate x y)
    exact (congrArg (Nat.FixedWidth.unitMultiplicationPairEquiv
      (InPlaceTarget.modulusWord modulus) coefficient) initial).trans
        (Nat.FixedWidth.unitMultiplicationPairEquiv_clean
          (InPlaceTarget.modulusWord modulus) positive coefficient _ valid)
  · rfl

/-- The placed program converts a canonical coordinate and restores all preparation. -/
lemma nativeProgram_prepared (modulus : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (x y : Fin (2 ^ modulus.size))
    (valid : (selectedInput coordinate x y).val < modulus) :
    (nativeProgram modulus.size (InPlaceTarget.modulusWord modulus) coefficient
      coordinate).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (ProductPlacement.frameEncoding modulus.size).width).basisEquiv.symm
              ((ProductPlacement.frameEncoding modulus.size).encode (preparedFrame modulus x y)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (ProductPlacement.frameEncoding modulus.size).width).basisEquiv.symm
          ((ProductPlacement.frameEncoding modulus.size).encode
            (preparedUpdate modulus coordinate x y
              (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive
                coefficient (selectedInput coordinate x y))))) := by
  have actual := (nativeProgram_realizes (environment := environment) modulus.size
    (InPlaceTarget.modulusWord modulus) coefficient coordinate).apply_encoded_ket
      (preparedFrame modulus x y)
  rw [nativeAction_prepared modulus positive coefficient coordinate x y valid] at actual
  exact actual

private lemma preparedFrame_runtime (modulus : Nat) (x y : Fin (2 ^ modulus.size)) :
    (NumeratorMeasurement.frameBasis modulus.size).symm
      ((ProductPlacement.frameEncoding modulus.size).encode (preparedFrame modulus x y)) =
        InPlaceTarget.preparedBasis modulus x y := by
  exact (congrArg (NumeratorMeasurement.frameBasis modulus.size).symm
    (InPlaceTarget.preparedBasis_frame modulus x y)).symm.trans
      ((NumeratorMeasurement.frameBasis modulus.size).symm_apply_apply _)

/-- The updated coordinate is assembled with precisely the original auxiliary preparation. -/
def preparedRuntimeUpdate (modulus : Nat) (coordinate : MeasuredPointAddition.Coordinate)
    (x y next : Fin (2 ^ modulus.size)) :
    (NumeratorMeasurement.context modulus.size).register.Index :=
  match coordinate with
  | .x => InPlaceTarget.preparedBasis modulus next y
  | .y => InPlaceTarget.preparedBasis modulus x next

private lemma preparedUpdate_runtime (modulus : Nat)
    (coordinate : MeasuredPointAddition.Coordinate) (x y next : Fin (2 ^ modulus.size)) :
    (NumeratorMeasurement.frameBasis modulus.size).symm
      ((ProductPlacement.frameEncoding modulus.size).encode
        (preparedUpdate modulus coordinate x y next)) =
      preparedRuntimeUpdate modulus coordinate x y next := by
  cases coordinate <;> exact preparedFrame_runtime _ _ _

/-- The actual runtime unitary restores the original prepared auxiliary and finite-cell context. -/
lemma runtimeProgram_prepared (modulus : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (x y : Fin (2 ^ modulus.size))
    (valid : (selectedInput coordinate x y).val < modulus) :
    (runtimeProgram modulus.size (InPlaceTarget.modulusWord modulus) coefficient
      coordinate).applyNormalized
        environment (NormalizedVector.ket (InPlaceTarget.preparedBasis modulus x y)) =
      NormalizedVector.ket (preparedRuntimeUpdate modulus coordinate x y
        (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient
          (selectedInput coordinate x y))) := by
  have actual := runtimeProgram_apply_ket (environment := environment) modulus.size
    (InPlaceTarget.modulusWord modulus) coefficient coordinate
    ((ProductPlacement.frameEncoding modulus.size).encode (preparedFrame modulus x y))
    ((ProductPlacement.frameEncoding modulus.size).encode
      (preparedUpdate modulus coordinate x y
        (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient
          (selectedInput coordinate x y))))
    (nativeProgram_prepared
      (environment := environment) modulus positive coefficient coordinate x y valid)
  rw [preparedFrame_runtime modulus x y,
    preparedUpdate_runtime modulus coordinate x y
      (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient
        (selectedInput coordinate x y))] at actual
  exact actual

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
