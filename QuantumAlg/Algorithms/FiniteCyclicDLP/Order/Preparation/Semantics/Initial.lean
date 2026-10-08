/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Gap
public import QuantumAlg.Core.Base.UnitaryCircuit.Vector
public import QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Gap
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Primitives.WalshHadamard.Pipeline

/-!
# Literal native semantics of the positive-gap initial preparation

The addressed X prefix constructs the aligned base of the lowest source
block.  The actual low Walsh--Hadamard suffix then opens exactly its free low
bits.  These statements evaluate the same native words used by the intrinsic
resource ledger.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion

noncomputable section

open scoped BigOperators

variable {N : Nat}

/-- The computational-basis address reached by the literal initial X sweep. -/
public def initialXLabel (b : PositiveGapExpansion N) : Fin (2 ^ b.width) :=
  (List.ofFn fun gap : Fin b.gaps => b.wire gap.succ).foldl
    (fun label wire => WireAddress.flipBit wire label) 0

private theorem xor_two_pow_eq_add_of_lt {value bit : Nat}
    (below : value < 2 ^ bit) :
    value ^^^ 2 ^ bit = value + 2 ^ bit := by
  have asOr : 2 ^ bit + value = 2 ^ bit ||| value := by
    simpa using Nat.two_pow_add_eq_or_of_lt below 1
  rw [Nat.add_comm, asOr]
  apply Nat.eq_of_testBit_eq
  intro index
  rw [Nat.testBit_xor, Nat.testBit_or]
  by_cases same : index = bit
  · subst index
    simp [Nat.testBit_lt_two_pow below]
  · have powerZero : (2 ^ bit).testBit index = false :=
      Nat.testBit_two_pow_of_ne (Ne.symm same)
    simp [powerZero]

private theorem sum_pow_lt_pow_of_strictMono {count : Nat}
    (exponent : Fin count → Nat) (strict : StrictMono exponent)
    (upper : Nat) (bounded : ∀ index, exponent index < upper) :
    (∑ index, 2 ^ exponent index) < 2 ^ upper := by
  rw [← Finset.sum_image strict.injective.injOn]
  exact Nat.geomSum_lt (m := 2) (s := Finset.univ.image exponent)
    (n := upper) (by omega) (by
      intro current member
      rcases Finset.mem_image.mp member with ⟨index, -, rfl⟩
      exact bounded index)

private theorem foldl_xorPow_eq_sum_of_strictMono :
    ∀ (count : Nat) (exponent : Fin count → Nat), StrictMono exponent →
      (List.ofFn exponent).foldl (fun value bit => value ^^^ 2 ^ bit) 0 =
        ∑ index, 2 ^ exponent index := by
  intro count
  induction count with
  | zero =>
      intro exponent _
      simp
  | succ count induction =>
      intro exponent strict
      have prefixStrict :
          StrictMono (fun index : Fin count => exponent index.castSucc) := by
        intro left right less
        apply strict
        simpa using less
      have prefixBound :
          (∑ index : Fin count, 2 ^ exponent index.castSucc) <
            2 ^ exponent (Fin.last count) := by
        apply sum_pow_lt_pow_of_strictMono
          (fun index : Fin count => exponent index.castSucc) prefixStrict
          (exponent (Fin.last count))
        intro index
        apply strict
        change index.val < (Fin.last count).val
        simpa only [Fin.val_last] using index.isLt
      rw [List.ofFn_succ_last, List.foldl_append]
      simp only [List.foldl_cons]
      rw [induction _ prefixStrict, xor_two_pow_eq_add_of_lt prefixBound,
        Fin.sum_univ_castSucc]
      simp

private theorem foldl_flipBit_values (width : Nat) :
    ∀ (wires : List (Fin width)) (label : Fin (2 ^ width)),
      (wires.foldl (fun current wire => WireAddress.flipBit wire current) label).val =
        (wires.map fun wire => (WireAddress.bitIndex wire).val).foldl
          (fun current bit => current ^^^ 2 ^ bit) label.val := by
  intro wires label
  induction wires generalizing label with
  | nil => simp
  | cons wire wires induction =>
      rw [List.foldl_cons, List.map_cons, List.foldl_cons,
        induction (WireAddress.flipBit wire label)]
      rfl

/-- The literal X prefix reaches the aligned base address of source zero. -/
public theorem initialXLabel_val (b : PositiveGapExpansion N) :
    b.initialXLabel.val = b.tailMass 0 := by
  unfold initialXLabel
  rw [foldl_flipBit_values]
  have mapped :
      (List.ofFn fun gap : Fin b.gaps => b.wire gap.succ).map
          (fun wire => (WireAddress.bitIndex wire).val) =
        List.ofFn (fun gap : Fin b.gaps => b.ell gap.succ) := by
    simpa only [Function.comp_apply, b.bitIndex_wire] using
      (List.ofFn_comp' (fun gap : Fin b.gaps => b.wire gap.succ)
        (fun wire => (WireAddress.bitIndex wire).val)).symm
  rw [mapped]
  simp only [Fin.val_zero]
  have strict : StrictMono (fun gap : Fin b.gaps => b.ell gap.succ) := by
    intro left right less
    apply b.ell_strict
    simpa using less
  rw [foldl_xorPow_eq_sum_of_strictMono b.gaps
    (fun gap : Fin b.gaps => b.ell gap.succ) strict]
  unfold tailMass
  rw [Fin.sum_univ_succ]
  simp

public theorem initialXLabel_eq_tailMass (b : PositiveGapExpansion N) :
    b.initialXLabel =
      ⟨b.tailMass 0, b.tailMass_lt_pow_width 0⟩ := by
  apply Fin.ext
  exact b.initialXLabel_val

/-- One actual addressed native X flips its selected binary wire. -/
public theorem xAt_applyBinary_ket (oracles : OracleModel)
    (b : PositiveGapExpansion N) (wire : Fin b.width)
    (label : Fin (2 ^ b.width)) :
    (OrderPreparation.Intrinsic.xAt oracles b.asOrderExpansion wire).binaryMatrix.apply
        (NormalizedVector.ket label) =
      NormalizedVector.ket (WireAddress.flipBit wire label) := by
  change (QubitPrimitive.circuit (.x wire)
      (QubitLayout.canonical b.width) oracles).binaryMatrix.apply
        (NormalizedVector.ket label) =
    NormalizedVector.ket (WireAddress.flipBit wire label)
  rw [QubitPrimitive.circuit_canonical_binaryMatrix,
    QubitPrimitive.operator_apply_ket]
  rfl

/-- The actual intrinsic X sweep maps zero to its explicit folded address. -/
public theorem initialX_applyVec_zero (oracles : OracleModel)
    (b : PositiveGapExpansion N) :
    (OrderPreparation.Intrinsic.initialX oracles
      b.asOrderExpansion).applyBinaryVec
        (NormalizedVector.ket (R := Qubits b.width) 0 :
          HilbertVector (Qubits b.width)) =
      (NormalizedVector.ket (R := Qubits b.width) b.initialXLabel :
        HilbertVector (Qubits b.width)) := by
  rw [show OrderPreparation.Intrinsic.initialX oracles b.asOrderExpansion =
      UnitaryCircuit.indexedProduct "sv24-intrinsic-initial-x" b.gaps
        (.identity AlgorithmGate.model oracles
          (QuantumSignature.qubits b.width).canonicalPlacement.layout)
        (fun gap : Fin b.gaps => OrderPreparation.Intrinsic.xAt
          oracles b.asOrderExpansion (b.wire gap.succ)) by rfl]
  rw [UnitaryCircuit.applyBinaryVec_indexedProduct]
  have identityAction :
      (UnitaryCircuit.identity AlgorithmGate.model oracles
        (QuantumSignature.qubits b.width).canonicalPlacement.layout).applyBinaryVec
          (NormalizedVector.ket (R := Qubits b.width) 0 :
            HilbertVector (Qubits b.width)) =
        (NormalizedVector.ket (R := Qubits b.width) 0 :
          HilbertVector (Qubits b.width)) :=
    UnitaryCircuit.applyBinaryVec_identity _
  rw [identityAction]
  have foldAction : ∀ (wires : List (Fin b.width))
      (label : Fin (2 ^ b.width)),
      (wires.map (fun wire => OrderPreparation.Intrinsic.xAt
        oracles b.asOrderExpansion wire)).foldl
          (fun state circuit => circuit.applyBinaryVec state)
          (NormalizedVector.ket (R := Qubits b.width) label :
            HilbertVector (Qubits b.width)) =
        (NormalizedVector.ket (R := Qubits b.width)
          (wires.foldl
            (fun current wire => WireAddress.flipBit wire current) label) :
          HilbertVector (Qubits b.width)) := by
    intro wires label
    induction wires generalizing label with
    | nil => simp
    | cons wire wires induction =>
        simp only [List.map_cons, List.foldl_cons]
        have step := b.xAt_applyBinary_ket oracles wire label
        have raw := congrArg
          (fun state : NormalizedVector (Qubits b.width) =>
            (state : HilbertVector (Qubits b.width))) step
        have rawAction :
            (OrderPreparation.Intrinsic.xAt oracles
              b.asOrderExpansion wire).applyBinaryVec
                (NormalizedVector.ket (R := Qubits b.width) label :
                  HilbertVector (Qubits b.width)) =
              (NormalizedVector.ket (R := Qubits b.width)
                (WireAddress.flipBit wire label) :
                  HilbertVector (Qubits b.width)) := by
          simpa only [UnitaryOperator.apply_coe] using raw
        rw [rawAction]
        exact induction (WireAddress.flipBit wire label)
  have circuitList :
      List.ofFn (fun gap : Fin b.gaps =>
        OrderPreparation.Intrinsic.xAt oracles b.asOrderExpansion
          (b.wire gap.succ)) =
        (List.ofFn fun gap : Fin b.gaps => b.wire gap.succ).map
          (fun wire => OrderPreparation.Intrinsic.xAt oracles b.asOrderExpansion wire) := by
    exact List.ofFn_comp'
      (fun gap : Fin b.gaps => b.wire gap.succ)
      (fun wire => OrderPreparation.Intrinsic.xAt oracles b.asOrderExpansion wire)
  rw [circuitList]
  change ((List.ofFn fun gap : Fin b.gaps => b.wire gap.succ).map
      (fun wire => OrderPreparation.Intrinsic.xAt
        oracles b.asOrderExpansion wire)).foldl
        (fun state circuit => circuit.applyBinaryVec state)
        (NormalizedVector.ket (R := Qubits b.width) 0 :
          HilbertVector (Qubits b.width)) =
      (NormalizedVector.ket (R := Qubits b.width) b.initialXLabel :
        HilbertVector (Qubits b.width))
  simpa [initialXLabel] using
    foldAction (List.ofFn fun gap : Fin b.gaps => b.wire gap.succ) 0

private theorem initialXLabel_eq_tensorLabel (b : PositiveGapExpansion N) :
    b.initialXLabel =
      UnitaryCircuit.castQubitWidthIndex (by
        have upper : b.first < b.width := by
          simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
        omega : (b.width - b.first) + b.first = b.width)
        (prodEquiv (m := b.width - b.first) (n := b.first)
          (UnitaryCircuit.castQubitWidthIndex (by
            have upper : b.first < b.width := by
              simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
            omega : (b.width - b.first - 1) + 1 = b.width - b.first)
            (prodEquiv (m := b.width - b.first - 1) (n := 1)
              (b.residualHighLabel 0, 0)), 0)) := by
  apply Fin.ext
  rw [b.initialXLabel_val, b.tailMass_eq_residualHigh_mul 0]
  simp only [UnitaryCircuit.castQubitWidthIndex_val]
  rw [UnitaryCircuit.prodEquiv_value]
  simp only [UnitaryCircuit.castQubitWidthIndex_val]
  rw [UnitaryCircuit.prodEquiv_value]
  simp only [residualHighLabel_val,
    Fin.val_zero, Nat.zero_add]
  unfold first
  rw [pow_succ]
  ring

private theorem raw_tensor_ket {m n : Nat}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) :
    HilbertVector.tensor
        (NormalizedVector.ket (R := Qubits m) left : HilbertVector (Qubits m))
        (NormalizedVector.ket (R := Qubits n) right : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits (m + n))
        (prodEquiv (m := m) (n := n) (left, right)) :
          HilbertVector (Qubits (m + n))) := by
  apply WithLp.ofLp_injective
  funext index
  obtain ⟨⟨leftIndex, rightIndex⟩, rfl⟩ :=
    (prodEquiv (m := m) (n := n)).surjective index
  rw [HilbertVector.tensor_apply_prod]
  simp only [NormalizedVector.ket_apply, Equiv.apply_eq_iff_eq]
  by_cases leftSame : leftIndex = left <;>
    by_cases rightSame : rightIndex = right <;>
    simp [leftSame, rightSame]

private theorem initialXLabel_raw_tensor (b : PositiveGapExpansion N) :
    (NormalizedVector.ket (R := Qubits b.width) b.initialXLabel :
      HilbertVector (Qubits b.width)) =
      UnitaryCircuit.castQubitWidthVec (by
        have upper : b.first < b.width := by
          simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
        omega : (b.width - b.first) + b.first = b.width)
        (HilbertVector.tensor
          (UnitaryCircuit.castQubitWidthVec (by
            have upper : b.first < b.width := by
              simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
            omega : (b.width - b.first - 1) + 1 = b.width - b.first)
            (HilbertVector.tensor
              (basisKetVec (b.residualHighLabel 0))
              (NormalizedVector.ket0 : HilbertVector (Qubits 1))))
          (rawKetZero b.first)) := by
  change basisKetVec b.initialXLabel = _
  rw [b.initialXLabel_eq_tensorLabel]
  unfold rawKetZero basisKetVec
  rw [← basisKetVec_zero_one]
  rw [raw_tensor_ket, UnitaryCircuit.castQubitWidthVec_ket,
    raw_tensor_ket, UnitaryCircuit.castQubitWidthVec_ket]

private theorem lowHadamards_applyVec_tensor (oracles : OracleModel)
    (b : PositiveGapExpansion N)
    (high : HilbertVector (Qubits (b.width - b.first))) :
    (OrderPreparation.Intrinsic.lowHadamards oracles
      b.asOrderExpansion).applyBinaryVec
        (UnitaryCircuit.castQubitWidthVec (by
          have upper : b.first < b.width := by
            simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
          omega : (b.width - b.first) + b.first = b.width)
          (HilbertVector.tensor high (rawKetZero b.first))) =
      UnitaryCircuit.castQubitWidthVec (by
        have upper : b.first < b.width := by
          simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
        omega : (b.width - b.first) + b.first = b.width)
        (HilbertVector.tensor high
          (WalshHadamard.uniformState b.first :
            HilbertVector (Qubits b.first))) := by
  have zeroAction :
      (Gate.HadamardLayer.circuit oracles b.first).binaryMatrix.applyVec
          (rawKetZero b.first) =
        (WalshHadamard.uniformState b.first : HilbertVector (Qubits b.first)) := by
    change (WalshHadamard.Native.binaryOperator oracles b.first).applyVec
        (rawKetZero b.first) = _
    rw [WalshHadamard.Native.native_binary_matrix]
    unfold rawKetZero basisKetVec
    have normalized := congrArg
      (fun state : NormalizedVector (Qubits b.first) =>
        (state : HilbertVector (Qubits b.first)))
      (WalshHadamard.hadamardLayerOperator_apply_zero (n := b.first))
    simpa only [UnitaryOperator.apply_coe] using normalized
  have outer : b.width - b.first + b.first = b.width := by
    have upper : b.first < b.width := by
      simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
    omega
  rw [show OrderPreparation.Intrinsic.lowHadamards oracles b.asOrderExpansion =
      (UnitaryCircuit.onBinarySuffix (b.width - b.first)
        (Gate.HadamardLayer.circuit oracles b.first)).castQubitWidth outer by
    rfl]
  unfold UnitaryCircuit.applyBinaryVec
  rw [UnitaryCircuit.castQubitWidth_binaryMatrix_applyVec,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_applyVec_tensor, zeroAction]

/-- The literal initial X and low-Hadamard layers prepare residual block zero. -/
public theorem initialPreparation_applyVec_zero_eq_residualBlock_zero
    (oracles : OracleModel) (b : PositiveGapExpansion N) :
    ((OrderPreparation.Intrinsic.initialX oracles
      b.asOrderExpansion).seq
      (OrderPreparation.Intrinsic.lowHadamards oracles
        b.asOrderExpansion)).applyBinaryVec
        (NormalizedVector.ket (R := Qubits b.width) 0 :
          HilbertVector (Qubits b.width)) =
      b.residualBlock 0 := by
  let high := basisKetVec (b.residualHighLabel 0)
  let lowZero := rawKetZero b.first
  let lowUniform := (WalshHadamard.uniformState b.first :
    HilbertVector (Qubits b.first))
  have top : (b.width - b.first - 1) + 1 = b.width - b.first := by
    have upper : b.first < b.width := by
      simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
    omega
  have outer : (b.width - b.first) + b.first = b.width := by
    have upper : b.first < b.width := by
      simpa [first] using b.ell_lt_width (0 : Fin (b.gaps + 1))
    omega
  have left : ((b.width - b.first - 1) + 1) + b.first = b.width := by
    omega
  have assoc : ((b.width - b.first - 1) + 1) + b.first =
      (b.width - b.first - 1) + (1 + b.first) := by omega
  have residual : (b.width - b.first - 1) + (1 + b.first) = b.width := by
    omega
  rw [UnitaryCircuit.applyBinaryVec_seq, b.initialX_applyVec_zero oracles]
  rw [b.initialXLabel_raw_tensor]
  rw [b.lowHadamards_applyVec_tensor oracles]
  change UnitaryCircuit.castQubitWidthVec outer
      (HilbertVector.tensor
        (UnitaryCircuit.castQubitWidthVec top
          (HilbertVector.tensor high (NormalizedVector.ket0 : HilbertVector (Qubits 1))))
        lowUniform) = _
  rw [UnitaryCircuit.castQubitWidthVec_tensor_left top outer]
  calc
    UnitaryCircuit.castQubitWidthVec left
        (HilbertVector.tensor
          (HilbertVector.tensor high (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
          lowUniform) =
      UnitaryCircuit.castQubitWidthVec residual
        (UnitaryCircuit.castQubitWidthVec assoc
          (HilbertVector.tensor
            (HilbertVector.tensor high (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
            lowUniform)) := by
          rw [UnitaryCircuit.castQubitWidthVec_trans]
    _ = UnitaryCircuit.castQubitWidthVec residual
        (HilbertVector.tensor high
          (HilbertVector.tensor
            (NormalizedVector.ket0 : HilbertVector (Qubits 1)) lowUniform)) := by
          rw [UnitaryCircuit.castQubitWidthVec_tensor_assoc]
    _ = b.residualBlock 0 := by
          simpa [high, lowUniform, first] using
            (b.residualBlock_tensor_factor (0 : Fin (b.gaps + 1))).symm

end

end QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion
