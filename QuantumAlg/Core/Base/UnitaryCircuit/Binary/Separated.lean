/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Middle.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
public import QuantumAlg.Core.Base.WireAddress
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Gate.SupportHybrid
public import QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Native execution on two separated binary wires

A two-qubit native word can be placed on any ordered pair of physical wires
by inserting the untouched middle field, then the untouched leading and
suffix.  The construction preserves the literal word and exposes its action
on arbitrary raw vectors split around the two active wires.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Execute a two-qubit word on two ordered physical wires of a canonical
binary register. -/
public def onBinarySeparated {gates : GateModel} {oracles : OracleModel}
    {width : Nat} (left right : Fin width) (before : left.val < right.val)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout :=
  castQubitWidth (by omega)
    (onBinaryPrefix (width - right.val - 1)
      (onBinarySuffix left.val
        (onBinaryMiddle (leftWidth := 1) (rightWidth := 1)
          (right.val - left.val - 1) body)))

/-- Assemble a raw register vector from the leading, the two active wires, the
middle field, and the suffix. -/
public def binarySeparatedVec {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (prefixState : HilbertVector (Qubits left.val))
    (active : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    HilbertVector (Qubits width) :=
  castQubitWidthVec (by omega)
    (HilbertVector.tensor
      (HilbertVector.tensor prefixState
        (binaryMiddleVec (leftWidth := 1) (rightWidth := 1) active middle)) suffix)

/-- Tensor form of a separated vector whose two active wires are themselves
given as an ordered tensor. -/
public theorem binarySeparatedVec_tensor {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (prefixState : HilbertVector (Qubits left.val))
    (first second : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    binarySeparatedVec left right before prefixState
        (HilbertVector.tensor first second) middle suffix =
      castQubitWidthVec (by omega)
        (HilbertVector.tensor
          (HilbertVector.tensor prefixState
            (HilbertVector.tensor
              (HilbertVector.tensor first middle) second)) suffix) := by
  unfold binarySeparatedVec
  rw [binaryMiddleVec_tensor]

/-- Tensor form of separated-vector assembly with source factor widths
transported to the exact physical leading, middle and suffix widths. -/
public theorem binarySeparatedVec_tensor_transport {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    {prefixWidth middleWidth suffixWidth : Nat}
    (prefixSame : prefixWidth = left.val)
    (middleSame : middleWidth = right.val - left.val - 1)
    (suffixSame : suffixWidth = width - right.val - 1)
    (prefixState : HilbertVector (Qubits prefixWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    binarySeparatedVec left right before
        (castQubitWidthVec prefixSame prefixState)
        (HilbertVector.tensor first second)
        (castQubitWidthVec middleSame middle)
        (castQubitWidthVec suffixSame suffix) =
      castQubitWidthVec (by
        omega : (prefixWidth + ((1 + middleWidth) + 1)) + suffixWidth = width)
        (HilbertVector.tensor
          (HilbertVector.tensor prefixState
            (HilbertVector.tensor (HilbertVector.tensor first middle) second))
          suffix) := by
  subst prefixWidth
  subst middleWidth
  subst suffixWidth
  simpa only [castQubitWidthVec_self] using
    (binarySeparatedVec_tensor left right before prefixState first second middle suffix)

/-- Concrete binary label of the five physical fields surrounding two
separated wires. -/
public def binarySeparatedBasisLabel {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) : Fin (2 ^ width) :=
  castQubitWidthIndex (by omega)
    (prodEquiv
      (m := left.val + ((1 + (right.val - left.val - 1)) + 1))
      (n := width - right.val - 1)
      (prodEquiv
        (m := left.val) (n := (1 + (right.val - left.val - 1)) + 1)
        (leading,
          prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
            (prodEquiv (m := 1) (n := right.val - left.val - 1)
              (first, middle), second)), suffix))

private theorem tensor_ket_vec {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :
    HilbertVector.tensor
        (NormalizedVector.ket (R := Qubits leftWidth) left :
          HilbertVector (Qubits leftWidth))
        (NormalizedVector.ket (R := Qubits rightWidth) right :
          HilbertVector (Qubits rightWidth)) =
      (NormalizedVector.ket (R := Qubits (leftWidth + rightWidth))
        (prodEquiv (m := leftWidth) (n := rightWidth) (left, right)) :
          HilbertVector (Qubits (leftWidth + rightWidth))) := by
  apply WithLp.ofLp_injective
  funext index
  obtain ⟨⟨leftIndex, rightIndex⟩, rfl⟩ :=
    (prodEquiv (m := leftWidth) (n := rightWidth)).surjective index
  rw [HilbertVector.tensor_apply_prod]
  simp only [NormalizedVector.ket_apply, Equiv.apply_eq_iff_eq]
  by_cases leftSame : leftIndex = left <;>
    by_cases rightSame : rightIndex = right <;>
    simp [leftSame, rightSame]

/-- A separated tensor of computational kets is the raw computational ket at
its concrete five-field binary label. -/
public theorem binarySeparatedVec_tensor_ket {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) :
    binarySeparatedVec left right before
        (NormalizedVector.ket (R := Qubits left.val) leading :
          HilbertVector (Qubits left.val))
        (HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits 1) first :
            HilbertVector (Qubits 1))
          (NormalizedVector.ket (R := Qubits 1) second :
            HilbertVector (Qubits 1)))
        (NormalizedVector.ket (R := Qubits (right.val - left.val - 1)) middle :
          HilbertVector (Qubits (right.val - left.val - 1)))
        (NormalizedVector.ket (R := Qubits (width - right.val - 1)) suffix :
          HilbertVector (Qubits (width - right.val - 1))) =
      (NormalizedVector.ket (R := Qubits width)
        (binarySeparatedBasisLabel left right before leading first middle second suffix) :
          HilbertVector (Qubits width)) := by
  rw [binarySeparatedVec_tensor]
  rw [tensor_ket_vec first middle, tensor_ket_vec _ second,
    tensor_ket_vec leading _, tensor_ket_vec _ suffix,
    castQubitWidthVec_ket]
  rfl

/-- Reading the first explicit one-qubit field of a separated label is the
physical bit at its left wire. -/
public theorem binarySeparatedBasisLabel_testBit_first {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) :
    (binarySeparatedBasisLabel left right before leading first middle second suffix).val.testBit
        (WireAddress.bitIndex left).val = first.val.testBit 0 := by
  let firstMiddle : Fin (2 ^ (1 + (right.val - left.val - 1))) :=
    prodEquiv (m := 1) (n := right.val - left.val - 1) (first, middle)
  let inside : Fin (2 ^ ((1 + (right.val - left.val - 1)) + 1)) :=
    prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
      (firstMiddle, second)
  let head : Fin (2 ^ (left.val + ((1 + (right.val - left.val - 1)) + 1))) :=
    prodEquiv (m := left.val) (n := (1 + (right.val - left.val - 1)) + 1)
      (leading, inside)
  let raw : Fin
      (2 ^ ((left.val + ((1 + (right.val - left.val - 1)) + 1)) +
        (width - right.val - 1))) :=
    prodEquiv
      (m := left.val + ((1 + (right.val - left.val - 1)) + 1))
      (n := width - right.val - 1) (head, suffix)
  have outer := prodEquiv_testBit_left head suffix
    ⟨right.val - left.val, by omega⟩
  have atHead := prodEquiv_testBit_right leading inside
    ⟨right.val - left.val, by omega⟩
  have atInside := prodEquiv_testBit_left firstMiddle second
    ⟨right.val - left.val - 1, by omega⟩
  have atFirst := prodEquiv_testBit_left first middle ⟨0, by omega⟩
  have firstIndex : width - 1 - left.val =
      (width - right.val - 1) + (right.val - left.val) := by omega
  have insideIndex : right.val - left.val =
      1 + (right.val - left.val - 1) := by omega
  have totalWidth :
      (left.val + ((1 + (right.val - left.val - 1)) + 1)) +
        (width - right.val - 1) = width := by omega
  unfold binarySeparatedBasisLabel
  rw [WireAddress.bitIndex_val]
  change (castQubitWidthIndex totalWidth raw).val.testBit
      (width - 1 - left.val) = first.val.testBit 0
  simp only [castQubitWidthIndex_val]
  calc
    raw.val.testBit (width - 1 - left.val) =
        head.val.testBit (right.val - left.val) := by
          simpa only [raw, firstIndex] using outer
    _ = inside.val.testBit (right.val - left.val) := by
          simpa only [head] using atHead
    _ = inside.val.testBit (1 + (right.val - left.val - 1)) := by
          exact congrArg (fun bit => inside.val.testBit bit) insideIndex
    _ = firstMiddle.val.testBit (right.val - left.val - 1) := by
          simpa only [inside] using atInside
    _ = first.val.testBit 0 := by
          simpa only [firstMiddle, Nat.add_zero] using atFirst

/-- Reading the second explicit one-qubit field of a separated label is the
physical bit at its right wire. -/
public theorem binarySeparatedBasisLabel_testBit_second {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) :
    (binarySeparatedBasisLabel left right before leading first middle second suffix).val.testBit
        (WireAddress.bitIndex right).val = second.val.testBit 0 := by
  let firstMiddle : Fin (2 ^ (1 + (right.val - left.val - 1))) :=
    prodEquiv (m := 1) (n := right.val - left.val - 1) (first, middle)
  let inside : Fin (2 ^ ((1 + (right.val - left.val - 1)) + 1)) :=
    prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
      (firstMiddle, second)
  let head : Fin (2 ^ (left.val + ((1 + (right.val - left.val - 1)) + 1))) :=
    prodEquiv (m := left.val) (n := (1 + (right.val - left.val - 1)) + 1)
      (leading, inside)
  let raw : Fin
      (2 ^ ((left.val + ((1 + (right.val - left.val - 1)) + 1)) +
        (width - right.val - 1))) :=
    prodEquiv
      (m := left.val + ((1 + (right.val - left.val - 1)) + 1))
      (n := width - right.val - 1) (head, suffix)
  have outer := prodEquiv_testBit_left head suffix ⟨0, by omega⟩
  have atHead := prodEquiv_testBit_right leading inside ⟨0, by omega⟩
  have atInside := prodEquiv_testBit_right firstMiddle second ⟨0, by omega⟩
  have secondIndex : width - 1 - right.val = width - right.val - 1 := by omega
  have totalWidth :
      (left.val + ((1 + (right.val - left.val - 1)) + 1)) +
        (width - right.val - 1) = width := by omega
  unfold binarySeparatedBasisLabel
  rw [WireAddress.bitIndex_val]
  change (castQubitWidthIndex totalWidth raw).val.testBit
      (width - 1 - right.val) = second.val.testBit 0
  simp only [castQubitWidthIndex_val]
  calc
    raw.val.testBit (width - 1 - right.val) = head.val.testBit 0 := by
      simpa only [raw, secondIndex, Nat.add_zero] using outer
    _ = inside.val.testBit 0 := by
      simpa only [head] using atHead
    _ = second.val.testBit 0 := by
      simpa only [inside] using atInside

/-- Every canonical binary address has a unique-shaped five-field split at
the two separated wires. -/
public theorem exists_binarySeparatedBasisLabel {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (index : Fin (2 ^ width)) :
    ∃ (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
      (middle : Fin (2 ^ (right.val - left.val - 1)))
      (second : Fin (2 ^ 1))
      (suffix : Fin (2 ^ (width - right.val - 1))),
      binarySeparatedBasisLabel left right before leading first middle second suffix =
        index := by
  let sourceWidth :=
    (left.val + ((1 + (right.val - left.val - 1)) + 1)) +
      (width - right.val - 1)
  have same : sourceWidth = width := by
    dsimp [sourceWidth]
    omega
  let sourceIndex : Fin (2 ^ sourceWidth) :=
    castQubitWidthIndex same.symm index
  obtain ⟨⟨head, suffix⟩, outer⟩ :=
    (prodEquiv
      (m := left.val + ((1 + (right.val - left.val - 1)) + 1))
      (n := width - right.val - 1)).surjective sourceIndex
  obtain ⟨⟨leading, inside⟩, atHead⟩ :=
    (prodEquiv (m := left.val)
      (n := (1 + (right.val - left.val - 1)) + 1)).surjective head
  obtain ⟨⟨firstMiddle, second⟩, atInside⟩ :=
    (prodEquiv (m := 1 + (right.val - left.val - 1))
      (n := 1)).surjective inside
  obtain ⟨⟨first, middle⟩, atFirstMiddle⟩ :=
    (prodEquiv (m := 1)
      (n := right.val - left.val - 1)).surjective firstMiddle
  refine ⟨leading, first, middle, second, suffix, ?_⟩
  unfold binarySeparatedBasisLabel
  change castQubitWidthIndex same
      (prodEquiv
        (m := left.val + ((1 + (right.val - left.val - 1)) + 1))
        (n := width - right.val - 1)
        (prodEquiv
          (m := left.val) (n := (1 + (right.val - left.val - 1)) + 1)
          (leading,
            prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
              (prodEquiv (m := 1) (n := right.val - left.val - 1)
                (first, middle), second)), suffix)) = index
  rw [atFirstMiddle, atInside, atHead, outer]
  exact castQubitWidthIndex_symm same index

/-- Separated-vector assembly is linear in its active two-wire state. -/
public theorem binarySeparatedVec_add_active {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (prefixState : HilbertVector (Qubits left.val))
    (first second : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    binarySeparatedVec left right before prefixState (first + second) middle suffix =
      binarySeparatedVec left right before prefixState first middle suffix +
        binarySeparatedVec left right before prefixState second middle suffix := by
  apply WithLp.ofLp_injective
  funext index
  simp [binarySeparatedVec, binaryMiddleVec, castQubitWidthVec_apply]
  ring

/-- Separated-vector assembly is linear in scalar multiples of its active
two-wire state. -/
public theorem binarySeparatedVec_smul_active {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (prefixState : HilbertVector (Qubits left.val))
    (scalar : ℂ) (active : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    binarySeparatedVec left right before prefixState (scalar • active) middle suffix =
      scalar • binarySeparatedVec left right before prefixState active middle suffix := by
  apply WithLp.ofLp_injective
  funext index
  simp [binarySeparatedVec, binaryMiddleVec, castQubitWidthVec_apply, smul_eq_mul]
  ring

/-- Separated placement applies the supplied word only to the two active
wires and fixes all three surrounding raw-vector fields. -/
public theorem unitaryCircuit_onBinarySeparated_applyVec
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout)
    (prefixState : HilbertVector (Qubits left.val))
    (active : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    (onBinarySeparated left right before body).binaryMatrix.applyVec
        (binarySeparatedVec left right before prefixState active middle suffix) =
      binarySeparatedVec left right before prefixState
        (body.binaryMatrix.applyVec active) middle suffix := by
  unfold onBinarySeparated binarySeparatedVec
  rw [castQubitWidth_binaryMatrix_applyVec,
    unitaryCircuit_onBinaryPrefix_applyVec_tensor,
    unitaryCircuit_onBinarySuffix_applyVec_tensor,
    unitaryCircuit_onBinaryMiddle_applyVec]

/-- Binary-coordinate spelling of separated-wire vector action. -/
public theorem onBinarySeparated_applyBinaryVec
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout)
    (prefixState : HilbertVector (Qubits left.val))
    (active : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    (onBinarySeparated left right before body).applyBinaryVec
        (binarySeparatedVec left right before prefixState active middle suffix) =
      binarySeparatedVec left right before prefixState
        (body.applyBinaryVec active) middle suffix := by
  exact unitaryCircuit_onBinarySeparated_applyVec left right before body
    prefixState active middle suffix

/-- A separated-wire circuit fixes any raw state whose nonzero computational
basis support is fixed by its two-wire body. -/
public theorem unitaryCircuit_onBinarySeparated_applyVec_eq_self_of_basis_support
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout)
    (state : HilbertVector (Qubits width))
    (bodyFixes : ∀ (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
      (middle : Fin (2 ^ (right.val - left.val - 1)))
      (second : Fin (2 ^ 1))
      (suffix : Fin (2 ^ (width - right.val - 1))),
      state (binarySeparatedBasisLabel left right before
        leading first middle second suffix) ≠ 0 →
      body.binaryMatrix.applyVec
          (HilbertVector.tensor
            (NormalizedVector.ket (R := Qubits 1) first :
              HilbertVector (Qubits 1))
            (NormalizedVector.ket (R := Qubits 1) second :
              HilbertVector (Qubits 1))) =
        HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits 1) first :
            HilbertVector (Qubits 1))
          (NormalizedVector.ket (R := Qubits 1) second :
            HilbertVector (Qubits 1))) :
    (onBinarySeparated left right before body).applyBinaryVec state = state := by
  classical
  let program := onBinarySeparated left right before body
  have stateExpansion :
      state = ∑ index : Fin (2 ^ width),
        state index •
          (NormalizedVector.ket (R := Qubits width) index :
            HilbertVector (Qubits width)) :=
    (HilbertVector.sum_amplitude_smul_ket state).symm
  calc
    program.applyBinaryVec state = program.applyBinaryVec
        (∑ index : Fin (2 ^ width),
          state index •
            (NormalizedVector.ket (R := Qubits width) index :
              HilbertVector (Qubits width))) := by
          exact congrArg program.applyBinaryVec stateExpansion
    _ = ∑ index : Fin (2 ^ width), program.applyBinaryVec
          (state index •
            (NormalizedVector.ket (R := Qubits width) index :
              HilbertVector (Qubits width))) := by
          unfold UnitaryCircuit.applyBinaryVec
          exact HilbertOperator.applyVec_sum
            (program.binaryMatrix : HilbertOperator (Qubits width)) _
    _ = ∑ index : Fin (2 ^ width), state index • program.applyBinaryVec
          (NormalizedVector.ket (R := Qubits width) index :
            HilbertVector (Qubits width)) := by
          apply Finset.sum_congr rfl
          intro index _
          rw [UnitaryCircuit.applyBinaryVec_smul]
    _ = ∑ index : Fin (2 ^ width), state index •
          (NormalizedVector.ket (R := Qubits width) index :
            HilbertVector (Qubits width)) := by
          apply Finset.sum_congr rfl
          intro index _
          obtain ⟨leading, first, middle, second, suffix, indexEq⟩ :=
            exists_binarySeparatedBasisLabel left right before index
          rw [← indexEq]
          by_cases zero : state
              (binarySeparatedBasisLabel left right before
                leading first middle second suffix) = 0
          · simp [zero]
          · have separated := binarySeparatedVec_tensor_ket left right before
              leading first middle second suffix
            have fixed : program.applyBinaryVec
                (NormalizedVector.ket (R := Qubits width)
                  (binarySeparatedBasisLabel left right before
                    leading first middle second suffix) :
                    HilbertVector (Qubits width)) =
                (NormalizedVector.ket (R := Qubits width)
                  (binarySeparatedBasisLabel left right before
                    leading first middle second suffix) :
                    HilbertVector (Qubits width)) := by
              rw [← separated]
              unfold program
              unfold UnitaryCircuit.applyBinaryVec
              rw [unitaryCircuit_onBinarySeparated_applyVec,
                bodyFixes leading first middle second suffix zero]
            exact congrArg
              (fun vector : HilbertVector (Qubits width) =>
                state (binarySeparatedBasisLabel left right before
                  leading first middle second suffix) • vector)
              fixed
    _ = state := HilbertVector.sum_amplitude_smul_ket state

/-- Separated placement preserves the complete ordered native-event trace. -/
public theorem unitaryCircuit_onBinarySeparated_eventTrace
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout) :
    (onBinarySeparated left right before body).eventTrace = body.eventTrace := by
  simp [onBinarySeparated, castQubitWidth_eventTrace,
    unitaryCircuit_onBinaryPrefix_eventTrace,
    unitaryCircuit_onBinarySuffix_eventTrace,
    unitaryCircuit_onBinaryMiddle_eventTrace]

/-- Separated placement preserves the exact native and oracle event pool. -/
public theorem unitaryCircuit_onBinarySeparated_eventCost
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout) :
    (onBinarySeparated left right before body).eventCost = body.eventCost := by
  rw [onBinarySeparated, castQubitWidth_eventCost,
    unitaryCircuit_onBinaryPrefix_eventCost,
    unitaryCircuit_onBinarySuffix_eventCost,
    unitaryCircuit_onBinaryMiddle_eventCost]

/-- Separated placement preserves dependency depth under every duration
assignment. -/
public theorem unitaryCircuit_onBinarySeparated_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits 2).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (onBinarySeparated left right before body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rw [onBinarySeparated, castQubitWidth_evaluatedEventDepth,
    unitaryCircuit_onBinaryPrefix_evaluatedEventDepth,
    unitaryCircuit_onBinarySuffix_evaluatedEventDepth,
    unitaryCircuit_onBinaryMiddle_evaluatedEventDepth]

end


end QuantumAlg.UnitaryCircuit
