/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Semantic lifting for actual encoded circuits

The lemmas in this module transport proof-only `UnitaryCircuit.Realizes` facts across
semantic relabeling and product-register circuit constructors.  They never
package or recover a circuit from a semantic gate description.
-/

section

namespace QuantumAlg

noncomputable section

namespace UnitaryCircuit.Realizes

/-- A logical basis reindexing transports a basis-to-basis circuit action. -/
theorem applyNormalized_reindex_ket_of_eq {R S : Register}
    (equiv : R.Index ≃ S.Index) (program : UnitaryCircuit R) (input output : R.Index)
    (h : program.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    (UnitaryCircuit.reindex equiv program).applyNormalized
        (NormalizedVector.ket (equiv input)) =
      NormalizedVector.ket (equiv output) := by
  apply NormalizedVector.ext
  intro index
  have hindex := congrArg
    (fun state : NormalizedVector R => state (equiv.symm index)) h
  change program.applyVec
      (NormalizedVector.ket input : HilbertVector R) (equiv.symm index) =
    NormalizedVector.ket output (equiv.symm index) at hindex
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] at hindex
  change (UnitaryCircuit.reindex equiv program).applyVec
      (NormalizedVector.ket (equiv input) : HilbertVector S) index =
    NormalizedVector.ket (equiv output) index
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket,
    UnitaryCircuit.reindex_matrix, UnitaryOperator.coe_reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply,
    NormalizedVector.ket_apply]
  rw [equiv.symm_apply_apply, hindex]
  by_cases heq : equiv.symm index = output
  · have : index = equiv output := by
      rw [← heq, equiv.apply_symm_apply]
    simp [this]
  · have : index ≠ equiv output := by
      intro hindexOutput
      apply heq
      exact equiv.injective (by simpa using hindexOutput)
    simp [heq, this]

/-- Physical relabeling does not alter normalized-state semantics. -/
theorem applyNormalized_relabel {R : Register} (program : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling program.physical_idx newPhysicalIdx)
    (state : NormalizedVector R) :
    (UnitaryCircuit.relabel program relabeling).applyNormalized state =
      program.applyNormalized state := by
  apply NormalizedVector.ext
  intro index
  exact congrArg (fun vector : HilbertVector R => vector index)
    (UnitaryCircuit.relabel_applyVec program relabeling state)

/-- Transport only the semantic carrier of a realization proof. -/
theorem relabel {Data Other : Type} {encoding : BinaryLabelEncoding Data}
    {program : UnitaryCircuit (Qubits encoding.width)} {step : Data → Data}
    (layout : Other ≃ Data) (h : UnitaryCircuit.Realizes encoding program step) :
    UnitaryCircuit.Realizes (encoding.relabel layout) program
      (fun x => layout.symm (step (layout x))) where
  apply_encoded_ket := by
    intro x
    simpa [BinaryLabelEncoding.relabel] using h.apply_encoded_ket (layout x)

/-- Lift a realized program on the left component of a product encoding. -/
theorem prodLeft {Left Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    {program : UnitaryCircuit (Qubits left.width)} {step : Left → Left}
    (h : UnitaryCircuit.Realizes left program step) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod left right)
      (UnitaryCircuit.prodLeft (n := right.width) program)
      (fun x : Left × Right => (step x.1, x.2)) where
  apply_encoded_ket := by
    intro x
    rcases x with ⟨l, r⟩
    change
      (UnitaryCircuit.prodLeft (n := right.width) program).applyNormalized
          (NormalizedVector.ket (prodEquiv (left.encode l, right.encode r))) =
        NormalizedVector.ket
          (prodEquiv (left.encode (step l), right.encode r))
    rw [← NormalizedVector.tensor_ket]
    change
      ((UnitaryCircuit.prodLeft (n := right.width) program).matrix).apply
          ((NormalizedVector.ket (left.encode l)).tensor
            (NormalizedVector.ket (right.encode r))) = _
    rw [UnitaryCircuit.prodLeft, UnitaryCircuit.tensorQubits_matrix,
      UnitaryOperator.tensor_apply_tensor]
    change
      (program.applyNormalized (NormalizedVector.ket (left.encode l))).tensor
          ((UnitaryCircuit.identity (Qubits right.width) [] _).applyNormalized
            (NormalizedVector.ket (right.encode r))) = _
    rw [h.apply_encoded_ket,
      (UnitaryCircuit.Realizes.identity right).apply_encoded_ket r,
      NormalizedVector.tensor_ket]
    rfl

/-- Lift one proved left-register basis endpoint across an untouched encoded
right register, without requiring a total semantic step. -/
theorem prodLeft_applyNormalized_encoded_ket_of_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (program : UnitaryCircuit (Qubits left.width))
    (input output : Left) (rightValue : Right)
    (h : program.applyNormalized
        (NormalizedVector.ket (left.encode input)) =
      NormalizedVector.ket (left.encode output)) :
    (UnitaryCircuit.prodLeft (n := right.width) program).applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod left right).encode (input, rightValue))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod left right).encode
          (output, rightValue)) := by
  change
    (UnitaryCircuit.prodLeft (n := right.width) program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv (left.encode input, right.encode rightValue))) =
      NormalizedVector.ket
        (prodEquiv (left.encode output, right.encode rightValue))
  rw [← NormalizedVector.tensor_ket]
  change
    ((UnitaryCircuit.prodLeft (n := right.width) program).matrix).apply
        ((NormalizedVector.ket (left.encode input)).tensor
          (NormalizedVector.ket (right.encode rightValue))) = _
  rw [UnitaryCircuit.prodLeft, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_apply_tensor]
  change
    (program.applyNormalized
        (NormalizedVector.ket (left.encode input))).tensor
      ((UnitaryCircuit.identity (Qubits right.width) [] _).applyNormalized
        (NormalizedVector.ket (right.encode rightValue))) = _
  rw [h, (UnitaryCircuit.Realizes.identity right).apply_encoded_ket rightValue,
    NormalizedVector.tensor_ket]
  rfl

/-- Lift a realized program on the right component of a product encoding. -/
theorem prodRight {Left Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    {program : UnitaryCircuit (Qubits right.width)} {step : Right → Right}
    (h : UnitaryCircuit.Realizes right program step) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod left right)
      (UnitaryCircuit.prodRight (m := left.width) program)
      (fun x : Left × Right => (x.1, step x.2)) where
  apply_encoded_ket := by
    intro x
    rcases x with ⟨l, r⟩
    change
      (UnitaryCircuit.prodRight (m := left.width) program).applyNormalized
          (NormalizedVector.ket (prodEquiv (left.encode l, right.encode r))) =
        NormalizedVector.ket
          (prodEquiv (left.encode l, right.encode (step r)))
    rw [← NormalizedVector.tensor_ket]
    change
      ((UnitaryCircuit.prodRight (m := left.width) program).matrix).apply
          ((NormalizedVector.ket (left.encode l)).tensor
            (NormalizedVector.ket (right.encode r))) = _
    rw [UnitaryCircuit.prodRight, UnitaryCircuit.tensorQubits_matrix,
      UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_apply_tensor]
    change
      ((UnitaryCircuit.identity (Qubits left.width) [] _).applyNormalized
          (NormalizedVector.ket (left.encode l))).tensor
        (program.applyNormalized (NormalizedVector.ket (right.encode r))) = _
    rw [(UnitaryCircuit.Realizes.identity left).apply_encoded_ket l,
      h.apply_encoded_ket, NormalizedVector.tensor_ket]
    rfl

/-- Lift one proved right-register basis endpoint across an untouched encoded
left register, without requiring a total semantic step. -/
theorem prodRight_applyNormalized_encoded_ket_of_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (program : UnitaryCircuit (Qubits right.width))
    (leftValue : Left) (input output : Right)
    (h : program.applyNormalized
        (NormalizedVector.ket (right.encode input)) =
      NormalizedVector.ket (right.encode output)) :
    (UnitaryCircuit.prodRight (m := left.width) program).applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod left right).encode (leftValue, input))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod left right).encode (leftValue, output)) := by
  change
    (UnitaryCircuit.prodRight (m := left.width) program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv (left.encode leftValue, right.encode input))) =
      NormalizedVector.ket
        (prodEquiv (left.encode leftValue, right.encode output))
  rw [← NormalizedVector.tensor_ket]
  change
    ((UnitaryCircuit.prodRight (m := left.width) program).matrix).apply
        ((NormalizedVector.ket (left.encode leftValue)).tensor
          (NormalizedVector.ket (right.encode input))) = _
  rw [UnitaryCircuit.prodRight, UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_apply_tensor]
  change
    ((UnitaryCircuit.identity (Qubits left.width) [] _).applyNormalized
        (NormalizedVector.ket (left.encode leftValue))).tensor
      (program.applyNormalized
        (NormalizedVector.ket (right.encode input))) = _
  rw [(UnitaryCircuit.Realizes.identity left).apply_encoded_ket leftValue, h,
    NormalizedVector.tensor_ket]
  rfl

/-- Lift a realized update of an existing left/right pair across an untouched
middle component. -/
theorem insertMiddle {Left Middle Right : Type}
    {left : BinaryLabelEncoding Left}
    {middle : BinaryLabelEncoding Middle}
    {right : BinaryLabelEncoding Right}
    {program : UnitaryCircuit (Qubits (left.width + right.width))}
    {step : Left × Right → Left × Right}
    (h : UnitaryCircuit.Realizes (BinaryLabelEncoding.prod left right) program step) :
    UnitaryCircuit.Realizes
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.prod left middle) right)
      (UnitaryCircuit.insertMiddle
        (leftWidth := left.width) (middleWidth := middle.width)
        (rightWidth := right.width) program)
      (fun x : (Left × Middle) × Right =>
        let y := step (x.1.1, x.2)
        ((y.1, x.1.2), y.2)) where
  apply_encoded_ket := by
    intro x
    rcases x with ⟨⟨l, m⟩, r⟩
    let y := step (l, r)
    have hextended :=
      (UnitaryCircuit.Realizes.prodLeft (right := middle) h).apply_encoded_ket
        ((l, r), m)
    have hreindexed := applyNormalized_reindex_ket_of_eq
      (R := Qubits ((left.width + right.width) + middle.width))
      (S := Qubits ((left.width + middle.width) + right.width))
      (UnitaryCircuit.insertMiddleIndexEquiv left.width middle.width right.width)
      (UnitaryCircuit.prodLeft (n := middle.width) program)
      ((BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod left right) middle).encode ((l, r), m))
      ((BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod left right) middle).encode (y, m))
      (by simpa [y] using hextended)
    have hinput :
        UnitaryCircuit.insertMiddleIndexEquiv left.width middle.width right.width
            ((BinaryLabelEncoding.prod
              (BinaryLabelEncoding.prod left right) middle).encode ((l, r), m)) =
          (BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left middle) right).encode ((l, m), r) := by
      simp [UnitaryCircuit.insertMiddleIndexEquiv, BinaryLabelEncoding.prod]
    have houtput :
        UnitaryCircuit.insertMiddleIndexEquiv left.width middle.width right.width
            ((BinaryLabelEncoding.prod
              (BinaryLabelEncoding.prod left right) middle).encode (y, m)) =
          (BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left middle) right).encode
              ((y.1, m), y.2) := by
      rcases y with ⟨yl, yr⟩
      simp [UnitaryCircuit.insertMiddleIndexEquiv, BinaryLabelEncoding.prod]
    change
      (UnitaryCircuit.insertMiddle
          (leftWidth := left.width) (middleWidth := middle.width)
          (rightWidth := right.width) program).applyNormalized
          (NormalizedVector.ket
            ((BinaryLabelEncoding.prod
              (BinaryLabelEncoding.prod left middle) right).encode ((l, m), r))) =
        NormalizedVector.ket
          ((BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left middle) right).encode
              ((y.1, m), y.2))
    unfold UnitaryCircuit.insertMiddle
    rw [applyNormalized_relabel]
    rw [← hinput, ← houtput]
    exact hreindexed

/-- Lift one proved left/right basis endpoint across an untouched encoded
middle component, without requiring a total semantic step. -/
theorem insertMiddle_applyNormalized_encoded_ket_of_eq
    {Left Middle Right : Type}
    (left : BinaryLabelEncoding Left)
    (middle : BinaryLabelEncoding Middle)
    (right : BinaryLabelEncoding Right)
    (program : UnitaryCircuit (Qubits (left.width + right.width)))
    (leftValue : Left) (middleValue : Middle) (input output : Right)
    (h : program.applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod left right).encode (leftValue, input))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod left right).encode (leftValue, output))) :
    (UnitaryCircuit.insertMiddle
        (leftWidth := left.width) (middleWidth := middle.width)
        (rightWidth := right.width) program).applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left middle) right).encode
            ((leftValue, middleValue), input))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod left middle) right).encode
          ((leftValue, middleValue), output)) := by
  have hextended :=
    prodLeft_applyNormalized_encoded_ket_of_eq
      (BinaryLabelEncoding.prod left right) middle program
      (leftValue, input) (leftValue, output) middleValue h
  have hreindexed := applyNormalized_reindex_ket_of_eq
    (R := Qubits ((left.width + right.width) + middle.width))
    (S := Qubits ((left.width + middle.width) + right.width))
    (UnitaryCircuit.insertMiddleIndexEquiv left.width middle.width right.width)
    (UnitaryCircuit.prodLeft (n := middle.width) program)
    ((BinaryLabelEncoding.prod
      (BinaryLabelEncoding.prod left right) middle).encode
      ((leftValue, input), middleValue))
    ((BinaryLabelEncoding.prod
      (BinaryLabelEncoding.prod left right) middle).encode
      ((leftValue, output), middleValue))
    hextended
  have hinput :
      UnitaryCircuit.insertMiddleIndexEquiv left.width middle.width right.width
          ((BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left right) middle).encode
            ((leftValue, input), middleValue)) =
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod left middle) right).encode
          ((leftValue, middleValue), input) := by
    simp [UnitaryCircuit.insertMiddleIndexEquiv, BinaryLabelEncoding.prod]
  have houtput :
      UnitaryCircuit.insertMiddleIndexEquiv left.width middle.width right.width
          ((BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left right) middle).encode
            ((leftValue, output), middleValue)) =
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod left middle) right).encode
          ((leftValue, middleValue), output) := by
    simp [UnitaryCircuit.insertMiddleIndexEquiv, BinaryLabelEncoding.prod]
  unfold UnitaryCircuit.insertMiddle
  rw [applyNormalized_relabel]
  rw [← hinput, ← houtput]
  exact hreindexed

private theorem prodLeft_applyNormalized_ket_of_eq_aux
    {leftWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits leftWidth))
    (input output : Fin (2 ^ leftWidth))
    (rightLabel : Fin (2 ^ rightWidth))
    (h : program.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    (UnitaryCircuit.prodLeft (n := rightWidth) program).applyNormalized
        (NormalizedVector.ket (prodEquiv (input, rightLabel))) =
      NormalizedVector.ket (prodEquiv (output, rightLabel)) := by
  rw [← NormalizedVector.tensor_ket]
  change
    ((UnitaryCircuit.prodLeft (n := rightWidth) program).matrix).apply
        ((NormalizedVector.ket input).tensor
          (NormalizedVector.ket rightLabel)) = _
  rw [UnitaryCircuit.prodLeft, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_apply_tensor]
  change
    (program.applyNormalized (NormalizedVector.ket input)).tensor
        ((UnitaryCircuit.identity (Qubits rightWidth) [] _).applyNormalized
          (NormalizedVector.ket rightLabel)) = _
  rw [h, UnitaryCircuit.applyNormalized_identity,
    NormalizedVector.tensor_ket]

/-- Lift one raw basis endpoint across an untouched flat left register. -/
theorem prodRight_applyNormalized_ket_of_eq
    {leftWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits rightWidth))
    (leftLabel : Fin (2 ^ leftWidth))
    (input output : Fin (2 ^ rightWidth))
    (h : program.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    (UnitaryCircuit.prodRight (m := leftWidth) program).applyNormalized
        (NormalizedVector.ket (prodEquiv (leftLabel, input))) =
      NormalizedVector.ket (prodEquiv (leftLabel, output)) := by
  rw [← NormalizedVector.tensor_ket]
  change
    ((UnitaryCircuit.prodRight (m := leftWidth) program).matrix).apply
        ((NormalizedVector.ket leftLabel).tensor
          (NormalizedVector.ket input)) = _
  rw [UnitaryCircuit.prodRight, UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_apply_tensor]
  change
    ((UnitaryCircuit.identity (Qubits leftWidth) [] _).applyNormalized
        (NormalizedVector.ket leftLabel)).tensor
      (program.applyNormalized (NormalizedVector.ket input)) = _
  rw [UnitaryCircuit.applyNormalized_identity, h, NormalizedVector.tensor_ket]

/-- Lift one raw left/right basis endpoint across an untouched flat middle
register. -/
theorem insertMiddle_applyNormalized_ket_of_eq
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth)))
    (leftLabel : Fin (2 ^ leftWidth))
    (middleLabel : Fin (2 ^ middleWidth))
    (input output : Fin (2 ^ rightWidth))
    (h : program.applyNormalized
        (NormalizedVector.ket (prodEquiv (leftLabel, input))) =
      NormalizedVector.ket (prodEquiv (leftLabel, output))) :
    (UnitaryCircuit.insertMiddle
        (leftWidth := leftWidth) (middleWidth := middleWidth)
        (rightWidth := rightWidth) program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv (prodEquiv (leftLabel, middleLabel), input))) =
      NormalizedVector.ket
        (prodEquiv (prodEquiv (leftLabel, middleLabel), output)) := by
  have hextended := prodLeft_applyNormalized_ket_of_eq_aux
    program (prodEquiv (leftLabel, input))
    (prodEquiv (leftLabel, output)) middleLabel h
  have hreindexed := applyNormalized_reindex_ket_of_eq
    (R := Qubits ((leftWidth + rightWidth) + middleWidth))
    (S := Qubits ((leftWidth + middleWidth) + rightWidth))
    (UnitaryCircuit.insertMiddleIndexEquiv leftWidth middleWidth rightWidth)
    (UnitaryCircuit.prodLeft (n := middleWidth) program)
    (prodEquiv (prodEquiv (leftLabel, input), middleLabel))
    (prodEquiv (prodEquiv (leftLabel, output), middleLabel))
    hextended
  have hinput :
      UnitaryCircuit.insertMiddleIndexEquiv leftWidth middleWidth rightWidth
          (prodEquiv (prodEquiv (leftLabel, input), middleLabel)) =
        prodEquiv (prodEquiv (leftLabel, middleLabel), input) := by
    simp [UnitaryCircuit.insertMiddleIndexEquiv]
  have houtput :
      UnitaryCircuit.insertMiddleIndexEquiv leftWidth middleWidth rightWidth
          (prodEquiv (prodEquiv (leftLabel, output), middleLabel)) =
        prodEquiv (prodEquiv (leftLabel, middleLabel), output) := by
    simp [UnitaryCircuit.insertMiddleIndexEquiv]
  unfold UnitaryCircuit.insertMiddle
  rw [applyNormalized_relabel]
  rw [← hinput, ← houtput]
  exact hreindexed

end UnitaryCircuit.Realizes

end

end QuantumAlg

end
