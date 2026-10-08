/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Encoded.Circuit
public import QuantumAlg.Core.Base.Layout.Qubit
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Middle.Matrix
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Middle.Matrix

/-!
# Semantic lifting on canonical binary layouts

These lemmas lift actual model-relative circuits across canonical product
registers. The constructions preserve the original native events and oracle
permissions; the proofs transport only their encoded computational-basis
semantics.
-/

namespace QuantumAlg.UnitaryCircuit.Realizes

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}

public theorem applyNormalized_encoded_ket_of_binaryMatrix_eq {width : Nat}
    (program : UnitaryCircuit gates oracles
      (QubitLayout.canonical width).toQuantum)
    (input output : Fin (2 ^ width))
    (h : program.binaryMatrix.apply (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    program.applyNormalized
        (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm input)) =
      NormalizedVector.ket
        ((QubitLayout.canonical width).basisEquiv.symm output) := by
  apply NormalizedVector.ext
  intro physicalIndex
  have hindex := congrArg
    (fun state : NormalizedVector (Qubits width) =>
      state ((QubitLayout.canonical width).basisEquiv physicalIndex)) h
  change program.binaryMatrix.applyVec
      (NormalizedVector.ket input).vec
        ((QubitLayout.canonical width).basisEquiv physicalIndex) =
    NormalizedVector.ket output
      ((QubitLayout.canonical width).basisEquiv physicalIndex) at hindex
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at hindex
  change program.applyVec
      (NormalizedVector.ket
        ((QubitLayout.canonical width).basisEquiv.symm input)).vec
        physicalIndex =
    NormalizedVector.ket
      ((QubitLayout.canonical width).basisEquiv.symm output) physicalIndex
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket]
  convert hindex using 1 <;>
    simp [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      NormalizedVector.ket_apply, QubitLayout.basisEquiv,
      Equiv.eq_symm_apply]
  all_goals rfl

public theorem binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
    {width : Nat}
    (program : UnitaryCircuit gates oracles
      (QubitLayout.canonical width).toQuantum)
    (input output : Fin (2 ^ width))
    (h : program.applyNormalized
        (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm input)) =
      NormalizedVector.ket
        ((QubitLayout.canonical width).basisEquiv.symm output)) :
    program.binaryMatrix.apply (NormalizedVector.ket input) =
      NormalizedVector.ket output := by
  apply NormalizedVector.ext
  intro binaryIndex
  have hindex := congrArg
    (fun state : NormalizedVector
        (QubitLayout.canonical width).toQuantum.register =>
      state ((QubitLayout.canonical width).basisEquiv.symm binaryIndex)) h
  change program.applyVec
      (NormalizedVector.ket
        ((QubitLayout.canonical width).basisEquiv.symm input)).vec
        ((QubitLayout.canonical width).basisEquiv.symm binaryIndex) =
    NormalizedVector.ket
      ((QubitLayout.canonical width).basisEquiv.symm output)
        ((QubitLayout.canonical width).basisEquiv.symm binaryIndex) at hindex
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket] at hindex
  change program.binaryMatrix.applyVec
      (NormalizedVector.ket input).vec binaryIndex =
    NormalizedVector.ket output binaryIndex
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  convert hindex using 1 <;>
    simp [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      NormalizedVector.ket_apply, QubitLayout.basisEquiv]
  all_goals rfl

/-- Transport only the semantic labels of an actual-circuit realization. -/
theorem relabel {Data Other : Type} {encoding : BinaryLabelEncoding Data}
    {layout : QubitLayout encoding.width}
    {program : UnitaryCircuit gates oracles layout.toQuantum}
    {step : Data → Data} (equivalence : Other ≃ Data)
    (h : UnitaryCircuit.Realizes encoding program step) :
    UnitaryCircuit.Realizes (encoding.relabel equivalence) program
      (fun x => equivalence.symm (step (equivalence x))) where
  apply_encoded_ket := by
    intro x
    convert h.apply_encoded_ket (equivalence x) using 1 <;>
      simp [BinaryLabelEncoding.relabel] <;> rfl

/-- Execute a realized program on the left binary field while preserving the
complete existing right field. -/
theorem onBinaryPrefix {Left Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    {program : UnitaryCircuit gates oracles
      (QubitLayout.canonical left.width).toQuantum} {step : Left → Left}
    (h : UnitaryCircuit.Realizes left program step) :
    UnitaryCircuit.Realizes
      (layout := QubitLayout.canonical (left.width + right.width))
      (BinaryLabelEncoding.prod left right)
      (UnitaryCircuit.onBinaryPrefix right.width program)
      (fun x : Left × Right => (step x.1, x.2)) where
  apply_encoded_ket := by
    intro x
    apply applyNormalized_encoded_ket_of_binaryMatrix_eq
    rcases x with ⟨l, r⟩
    change
      (UnitaryCircuit.onBinaryPrefix right.width program).binaryMatrix.apply
          (NormalizedVector.ket (prodEquiv (left.encode l, right.encode r))) =
        NormalizedVector.ket
          (prodEquiv (left.encode (step l), right.encode r))
    rw [← NormalizedVector.tensor_ket,
      show (UnitaryCircuit.onBinaryPrefix right.width program).binaryMatrix =
        program.binaryMatrix.tensor (1 : UnitaryOperator (Qubits right.width)) from
        UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix right.width program,
      UnitaryOperator.tensor_apply_tensor]
    have hleft := h.apply_encoded_ket l
    have hleft := binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
      program (left.encode l) (left.encode (step l)) hleft
    rw [hleft]
    apply NormalizedVector.ext
    intro index
    rw [← NormalizedVector.tensor_ket]
    change HilbertVector.tensor _
      ((1 : UnitaryOperator (Qubits right.width)).applyVec
        (NormalizedVector.ket (right.encode r)).vec) index = _
    rw [UnitaryOperator.one_applyVec]
    rfl

/-- Lift one proved left-field basis endpoint while preserving a selected
encoded value in the complete existing right field. -/
theorem onBinaryPrefix_applyNormalized_encoded_ket_of_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (program : UnitaryCircuit gates oracles
      (QubitLayout.canonical left.width).toQuantum)
    (input output : Left) (rightValue : Right)
    (h : program.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical left.width).basisEquiv.symm
            (left.encode input))) =
      NormalizedVector.ket
        ((QubitLayout.canonical left.width).basisEquiv.symm
          (left.encode output))) :
    (UnitaryCircuit.onBinaryPrefix right.width program).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (left.width + right.width)).basisEquiv.symm
            ((BinaryLabelEncoding.prod left right).encode (input, rightValue)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (left.width + right.width)).basisEquiv.symm
          ((BinaryLabelEncoding.prod left right).encode (output, rightValue))) := by
  apply applyNormalized_encoded_ket_of_binaryMatrix_eq
  change
    (UnitaryCircuit.onBinaryPrefix right.width program).binaryMatrix.apply
        (NormalizedVector.ket (prodEquiv (left.encode input, right.encode rightValue))) =
      NormalizedVector.ket
        (prodEquiv (left.encode output, right.encode rightValue))
  rw [← NormalizedVector.tensor_ket,
    show (UnitaryCircuit.onBinaryPrefix right.width program).binaryMatrix =
      program.binaryMatrix.tensor (1 : UnitaryOperator (Qubits right.width)) from
      UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix right.width program,
    UnitaryOperator.tensor_apply_tensor]
  have hleft := binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
    program (left.encode input) (left.encode output) h
  rw [hleft]
  apply NormalizedVector.ext
  intro index
  rw [← NormalizedVector.tensor_ket]
  change HilbertVector.tensor _
    ((1 : UnitaryOperator (Qubits right.width)).applyVec
      (NormalizedVector.ket (right.encode rightValue)).vec) index = _
  rw [UnitaryOperator.one_applyVec]
  rfl

/-- Execute a realized program on the right binary field while preserving the
complete existing left field. -/
theorem onBinarySuffix {Left Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    {program : UnitaryCircuit gates oracles
      (QubitLayout.canonical right.width).toQuantum} {step : Right → Right}
    (h : UnitaryCircuit.Realizes right program step) :
    UnitaryCircuit.Realizes
      (layout := QubitLayout.canonical (left.width + right.width))
      (BinaryLabelEncoding.prod left right)
      (UnitaryCircuit.onCanonicalBinarySuffix left.width program)
      (fun x : Left × Right => (x.1, step x.2)) where
  apply_encoded_ket := by
    intro x
    apply applyNormalized_encoded_ket_of_binaryMatrix_eq
    rcases x with ⟨l, r⟩
    change
      (UnitaryCircuit.onCanonicalBinarySuffix left.width program).binaryMatrix.apply
          (NormalizedVector.ket (prodEquiv (left.encode l, right.encode r))) =
        NormalizedVector.ket
          (prodEquiv (left.encode l, right.encode (step r)))
    rw [← NormalizedVector.tensor_ket,
      show (UnitaryCircuit.onCanonicalBinarySuffix left.width program).binaryMatrix =
        (1 : UnitaryOperator (Qubits left.width)).tensor program.binaryMatrix from
        UnitaryCircuit.onCanonicalBinarySuffix_binaryMatrix left.width program,
      UnitaryOperator.tensor_apply_tensor]
    have hright := h.apply_encoded_ket r
    have hright := binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
      program (right.encode r) (right.encode (step r)) hright
    rw [hright]
    apply NormalizedVector.ext
    intro index
    rw [← NormalizedVector.tensor_ket]
    change HilbertVector.tensor
      ((1 : UnitaryOperator (Qubits left.width)).applyVec
        (NormalizedVector.ket (left.encode l)).vec) _ index = _
    rw [UnitaryOperator.one_applyVec]
    rfl

/-- Lift one proved right-field basis endpoint while preserving a selected
encoded value in the complete existing left field. -/
theorem onBinarySuffix_applyNormalized_encoded_ket_of_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (program : UnitaryCircuit gates oracles
      (QubitLayout.canonical right.width).toQuantum)
    (leftValue : Left) (input output : Right)
    (h : program.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical right.width).basisEquiv.symm
            (right.encode input))) =
      NormalizedVector.ket
        ((QubitLayout.canonical right.width).basisEquiv.symm
          (right.encode output))) :
    (UnitaryCircuit.onCanonicalBinarySuffix left.width program).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (left.width + right.width)).basisEquiv.symm
            ((BinaryLabelEncoding.prod left right).encode (leftValue, input)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (left.width + right.width)).basisEquiv.symm
          ((BinaryLabelEncoding.prod left right).encode (leftValue, output))) := by
  apply applyNormalized_encoded_ket_of_binaryMatrix_eq
  change
    (UnitaryCircuit.onCanonicalBinarySuffix left.width program).binaryMatrix.apply
        (NormalizedVector.ket (prodEquiv (left.encode leftValue, right.encode input))) =
      NormalizedVector.ket
        (prodEquiv (left.encode leftValue, right.encode output))
  rw [← NormalizedVector.tensor_ket,
    show (UnitaryCircuit.onCanonicalBinarySuffix left.width program).binaryMatrix =
      (1 : UnitaryOperator (Qubits left.width)).tensor program.binaryMatrix from
      UnitaryCircuit.onCanonicalBinarySuffix_binaryMatrix left.width program,
    UnitaryOperator.tensor_apply_tensor]
  have hright := binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
    program (right.encode input) (right.encode output) h
  rw [hright]
  apply NormalizedVector.ext
  intro index
  rw [← NormalizedVector.tensor_ket]
  change HilbertVector.tensor
    ((1 : UnitaryOperator (Qubits left.width)).applyVec
      (NormalizedVector.ket (left.encode leftValue)).vec) _ index = _
  rw [UnitaryOperator.one_applyVec]
  rfl

/-- Execute a realized update of the existing outer binary fields while
preserving the complete middle field. -/
theorem onBinaryMiddle {Left Middle Right : Type}
    {left : BinaryLabelEncoding Left}
    {middle : BinaryLabelEncoding Middle}
    {right : BinaryLabelEncoding Right}
    {program : UnitaryCircuit gates oracles
      (QubitLayout.canonical (left.width + right.width)).toQuantum}
    {step : Left × Right → Left × Right}
    (h : UnitaryCircuit.Realizes (BinaryLabelEncoding.prod left right)
      program step) :
    UnitaryCircuit.Realizes
      (layout := QubitLayout.canonical
        (left.width + middle.width + right.width))
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.prod left middle) right)
      (UnitaryCircuit.onBinaryMiddle middle.width program)
      (fun x : (Left × Middle) × Right =>
        let y := step (x.1.1, x.2)
        ((y.1, x.1.2), y.2)) where
  apply_encoded_ket := by
    intro x
    rcases x with ⟨⟨leftValue, middleValue⟩, rightValue⟩
    rcases outputEquation : step (leftValue, rightValue) with
      ⟨outputLeft, outputRight⟩
    apply applyNormalized_encoded_ket_of_binaryMatrix_eq
    change
      (UnitaryCircuit.onBinaryMiddle middle.width program).binaryMatrix.apply
          (NormalizedVector.ket
            (prodEquiv
              (prodEquiv (left.encode leftValue, middle.encode middleValue),
                right.encode rightValue))) =
        NormalizedVector.ket
          (prodEquiv
            (prodEquiv (left.encode outputLeft, middle.encode middleValue),
              right.encode outputRight))
    apply NormalizedVector.ext
    intro row
    rcases (prodEquiv (m := left.width + middle.width)
      (n := right.width)).surjective row with ⟨⟨rowLeftMiddle, rowRight⟩, rfl⟩
    rcases (prodEquiv (m := left.width) (n := middle.width)).surjective
      rowLeftMiddle with ⟨⟨rowLeft, rowMiddle⟩, rfl⟩
    change
      HilbertOperator.applyVec
          ((UnitaryCircuit.onBinaryMiddle middle.width program).binaryMatrix :
            HilbertOperator (Qubits (left.width + middle.width + right.width)))
          ((NormalizedVector.ket
              (prodEquiv
                (prodEquiv (left.encode leftValue, middle.encode middleValue),
                  right.encode rightValue)) :
              NormalizedVector
                (Qubits (left.width + middle.width + right.width))) :
            HilbertVector (Qubits (left.width + middle.width + right.width)))
          (prodEquiv (prodEquiv (rowLeft, rowMiddle), rowRight))
        =
        (NormalizedVector.ket
          (prodEquiv
            (prodEquiv (left.encode outputLeft, middle.encode middleValue),
              right.encode outputRight)) :
          NormalizedVector (Qubits (left.width + middle.width + right.width)))
          (prodEquiv (prodEquiv (rowLeft, rowMiddle), rowRight))
    rw [HilbertOperator.applyVec_ket]
    have middleEntry :
        (UnitaryCircuit.onBinaryMiddle middle.width program).binaryMatrix
            (prodEquiv (prodEquiv (rowLeft, rowMiddle), rowRight))
            (prodEquiv
              (prodEquiv (left.encode leftValue, middle.encode middleValue),
                right.encode rightValue)) =
          program.binaryMatrix
              (prodEquiv (rowLeft, rowRight))
              (prodEquiv (left.encode leftValue, right.encode rightValue)) *
            (if rowMiddle = middle.encode middleValue then 1 else 0) := by
      exact unitaryCircuit_onBinaryMiddle_binaryMatrix_entry program
        rowLeft (left.encode leftValue) rowMiddle (middle.encode middleValue)
        rowRight (right.encode rightValue)
    rw [middleEntry]
    have outerAction := h.apply_encoded_ket (leftValue, rightValue)
    rw [outputEquation] at outerAction
    have outerBinary := binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
      program
      (prodEquiv (left.encode leftValue, right.encode rightValue))
      (prodEquiv (left.encode outputLeft, right.encode outputRight))
      outerAction
    have outerEntry :
        program.binaryMatrix (prodEquiv (rowLeft, rowRight))
            (prodEquiv (left.encode leftValue, right.encode rightValue)) =
          (NormalizedVector.ket
            (prodEquiv (left.encode outputLeft, right.encode outputRight)) :
            NormalizedVector (Qubits (left.width + right.width)))
            (prodEquiv (rowLeft, rowRight)) := by
      have point := congrArg
        (fun state : NormalizedVector (Qubits (left.width + right.width)) =>
          state (prodEquiv (rowLeft, rowRight))) outerBinary
      change
        HilbertOperator.applyVec
            (program.binaryMatrix :
              HilbertOperator (Qubits (left.width + right.width)))
            ((NormalizedVector.ket
                (prodEquiv (left.encode leftValue, right.encode rightValue)) :
                NormalizedVector (Qubits (left.width + right.width))) :
              HilbertVector (Qubits (left.width + right.width)))
            (prodEquiv (rowLeft, rowRight)) = _ at point
      simpa only [HilbertOperator.applyVec_ket] using point
    rw [outerEntry]
    simp only [NormalizedVector.ket_apply]
    by_cases leftSame : rowLeft = left.encode outputLeft <;>
      by_cases middleSame : rowMiddle = middle.encode middleValue <;>
        by_cases rightSame : rowRight = right.encode outputRight <;>
          simp [leftSame, middleSame, rightSame]

end

end QuantumAlg.UnitaryCircuit.Realizes
