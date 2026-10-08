/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Induction
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Induction
import all QuantumAlg.Primitives.WalshHadamard.Native

/-!
# Complete intrinsic range-preparation semantics

This file joins the one-set-bit and positive-gap cases.  The result covers
every positive represented order, including powers of two and `N = 1`, for
the literal intrinsic native circuit.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderPreparation.Intrinsic

noncomputable section

variable {N : Nat}

/-- Uniform raw range vector in the intrinsic active register. -/
@[expose] public def rangeVector (expansion : OrderExpansion N) :
    HilbertVector (Qubits (width expansion)) :=
  WithLp.toLp 2 fun address =>
    if address.val < N then OrderPreparation.invSqrtOrder N else 0

@[simp] public theorem rangeVector_apply (expansion : OrderExpansion N)
    (address : Fin (2 ^ width expansion)) :
    rangeVector expansion address =
      if address.val < N then OrderPreparation.invSqrtOrder N else 0 := by
  rfl

private theorem lowHadamards_applyVec_zero (oracles : OracleModel)
    (expansion : OrderExpansion N) :
    (lowHadamards oracles expansion).applyBinaryVec
        (NormalizedVector.ket (R := Qubits (width expansion)) 0 :
          HilbertVector (Qubits (width expansion))) =
      UnitaryCircuit.castQubitWidthVec (Nat.sub_add_cancel (by
        exact Nat.le_of_lt (ell_lt_width expansion
          ⟨0, expansion.count_pos⟩) : expansion.first ≤ width expansion))
        (HilbertVector.tensor
          (NormalizedVector.ket
            (R := Qubits (width expansion - expansion.first)) 0 :
            HilbertVector (Qubits (width expansion - expansion.first)))
          (WalshHadamard.uniformState expansion.first :
            HilbertVector (Qubits expansion.first))) := by
  have firstLe : expansion.first ≤ width expansion := by
    exact Nat.le_of_lt (ell_lt_width expansion
      ⟨0, expansion.count_pos⟩)
  let same := Nat.sub_add_cancel firstLe
  have zeroSplit :
      (NormalizedVector.ket (R := Qubits (width expansion)) 0 :
          HilbertVector (Qubits (width expansion))) =
        UnitaryCircuit.castQubitWidthVec same
          (HilbertVector.tensor
            (NormalizedVector.ket
              (R := Qubits (width expansion - expansion.first)) 0 :
              HilbertVector (Qubits (width expansion - expansion.first)))
            (NormalizedVector.ket (R := Qubits expansion.first) 0 :
              HilbertVector (Qubits expansion.first))) := by
    have tensorZero :
        HilbertVector.tensor
            (NormalizedVector.ket
              (R := Qubits (width expansion - expansion.first)) 0 :
              HilbertVector (Qubits (width expansion - expansion.first)))
            (NormalizedVector.ket (R := Qubits expansion.first) 0 :
              HilbertVector (Qubits expansion.first)) =
          (NormalizedVector.ket
            (R := Qubits ((width expansion - expansion.first) + expansion.first))
            (prodEquiv (m := width expansion - expansion.first)
              (n := expansion.first) (0, 0)) :
            HilbertVector
              (Qubits ((width expansion - expansion.first) + expansion.first))) := by
      simpa only [NormalizedVector.coe_tensor] using congrArg
        (fun state : NormalizedVector
            (Qubits ((width expansion - expansion.first) + expansion.first)) =>
          (state : HilbertVector
            (Qubits ((width expansion - expansion.first) + expansion.first))))
        (NormalizedVector.tensor_ket
          (0 : Fin (2 ^ (width expansion - expansion.first)))
          (0 : Fin (2 ^ expansion.first)))
    rw [tensorZero, UnitaryCircuit.castQubitWidthVec_ket]
    congr 2
  have zeroAction :
      (Gate.HadamardLayer.circuit oracles expansion.first).binaryMatrix.applyVec
          (NormalizedVector.ket (R := Qubits expansion.first) 0 :
            HilbertVector (Qubits expansion.first)) =
        (WalshHadamard.uniformState expansion.first :
          HilbertVector (Qubits expansion.first)) := by
    change (WalshHadamard.Native.binaryOperator oracles expansion.first).applyVec _ = _
    rw [WalshHadamard.Native.native_binary_matrix]
    have normalized := congrArg
      (fun state : NormalizedVector (Qubits expansion.first) =>
        (state : HilbertVector (Qubits expansion.first)))
      (WalshHadamard.hadamardLayerOperator_apply_zero (n := expansion.first))
    simpa only [UnitaryOperator.apply_coe] using normalized
  rw [zeroSplit]
  change (lowHadamards oracles expansion).binaryMatrix.applyVec _ = _
  unfold lowHadamards
  rw [UnitaryCircuit.castQubitWidth_binaryMatrix_applyVec,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_applyVec_tensor, zeroAction]

private theorem lowTarget_eq_rangeVector_of_count_eq_one
    (expansion : OrderExpansion N) (single : expansion.count = 1) :
    UnitaryCircuit.castQubitWidthVec (Nat.sub_add_cancel (by
      exact Nat.le_of_lt (ell_lt_width expansion
        ⟨0, expansion.count_pos⟩) : expansion.first ≤ width expansion))
      (HilbertVector.tensor
        (NormalizedVector.ket
          (R := Qubits (width expansion - expansion.first)) 0 :
          HilbertVector (Qubits (width expansion - expansion.first)))
        (WalshHadamard.uniformState expansion.first :
          HilbertVector (Qubits expansion.first))) =
      rangeVector expansion := by
  have firstLe : expansion.first ≤ width expansion := by
    exact Nat.le_of_lt (ell_lt_width expansion
      ⟨0, expansion.count_pos⟩)
  let same := Nat.sub_add_cancel firstLe
  have orderEq : N = 2 ^ expansion.first :=
    expansion.eq_pow_first_of_count_eq_one single
  apply WithLp.ofLp_injective
  funext index
  rw [UnitaryCircuit.castQubitWidthVec_apply]
  let equivalence := finCongr (congrArg (fun current => 2 ^ current) same)
  obtain ⟨⟨high, low⟩, sourceEq⟩ :=
    (prodEquiv (m := width expansion - expansion.first)
      (n := expansion.first)).surjective (equivalence.symm index)
  have indexEq : index = equivalence
      (prodEquiv (m := width expansion - expansion.first)
        (n := expansion.first) (high, low)) := by
    calc
      index = equivalence (equivalence.symm index) :=
        (equivalence.apply_symm_apply index).symm
      _ = equivalence (prodEquiv
          (m := width expansion - expansion.first)
          (n := expansion.first) (high, low)) :=
        congrArg equivalence sourceEq.symm
  change (HilbertVector.tensor
      (NormalizedVector.ket
        (R := Qubits (width expansion - expansion.first)) 0 :
        HilbertVector (Qubits (width expansion - expansion.first)))
      (WalshHadamard.uniformState expansion.first :
        HilbertVector (Qubits expansion.first))) (equivalence.symm index) = _
  rw [← sourceEq, HilbertVector.tensor_apply_prod, indexEq, rangeVector_apply]
  by_cases highZero : high = 0
  · subst high
    have belowOrder :
        (equivalence (prodEquiv
          (m := width expansion - expansion.first)
          (n := expansion.first) (0, low))).val < N := by
      calc
        _ = low.val := by
          simp [equivalence, prodEquiv, finProdFinEquiv]
        _ < 2 ^ expansion.first := low.isLt
        _ = N := orderEq.symm
    have amplitude : WalshHadamard.invSqrtCard expansion.first =
        OrderPreparation.invSqrtOrder N := by
      unfold WalshHadamard.invSqrtCard OrderPreparation.invSqrtOrder
      exact congrArg (fun cardinal : Nat =>
        (Real.sqrt (cardinal : Real) : Complex)⁻¹) orderEq.symm
    rw [if_pos belowOrder]
    simpa [NormalizedVector.ket_apply,
      WalshHadamard.uniformState_apply] using amplitude
  · have highVal : high.val ≠ 0 := by
      intro zero
      apply highZero
      exact Fin.ext zero
    have positive : 1 ≤ high.val := Nat.one_le_iff_ne_zero.mpr highVal
    have lowerBound : 2 ^ expansion.first ≤
        (equivalence (prodEquiv
          (m := width expansion - expansion.first)
          (n := expansion.first) (high, low))).val := by
      change 2 ^ expansion.first ≤
        low.val + 2 ^ expansion.first * high.val
      have scaled : 2 ^ expansion.first ≤ 2 ^ expansion.first * high.val := by
        simpa using Nat.mul_le_mul_left (2 ^ expansion.first) positive
      omega
    have notBelow : ¬(equivalence (prodEquiv
        (m := width expansion - expansion.first)
        (n := expansion.first) (high, low))).val < N := by
      intro smaller
      exact (Nat.not_lt_of_ge lowerBound) (lt_of_lt_of_eq smaller orderEq)
    simp [NormalizedVector.ket_apply, highZero, notBelow]

/-- The intrinsic native circuit prepares every one-set-bit order exactly,
including `N = 1`. -/
public theorem circuit_applyVec_zero_of_count_eq_one (oracles : OracleModel)
    (expansion : OrderExpansion N) (single : expansion.count = 1) :
    (circuit oracles expansion).applyBinaryVec
        (NormalizedVector.ket (R := Qubits (width expansion)) 0 :
          HilbertVector (Qubits (width expansion))) =
      rangeVector expansion := by
  have gapsZero : expansion.gaps = 0 := by
    simp [OrderExpansion.gaps, single]
  have initialIdentity :
      (initialX oracles expansion).applyBinaryVec
          (NormalizedVector.ket (R := Qubits (width expansion)) 0 :
            HilbertVector (Qubits (width expansion))) =
        (NormalizedVector.ket (R := Qubits (width expansion)) 0 :
          HilbertVector (Qubits (width expansion))) := by
    unfold initialX
    rw [UnitaryCircuit.applyBinaryVec_indexedProduct,
      UnitaryCircuit.applyBinaryVec_identity]
    have empty : List.ofFn (fun gap : Fin expansion.gaps =>
        (xAt oracles expansion (wire expansion
          (OrderPreparation.rightIndex expansion gap)))) = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using gapsZero
    rw [empty]
    simp only [List.foldl_nil]
  unfold circuit
  rw [UnitaryCircuit.applyBinaryVec_indexedProduct]
  have noStages : List.ofFn (fun gap : Fin expansion.gaps =>
      gapStage oracles expansion gap) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using gapsZero
  rw [noStages]
  simp only [List.foldl_nil]
  rw [UnitaryCircuit.applyBinaryVec_seq, initialIdentity,
    lowHadamards_applyVec_zero,
    lowTarget_eq_rangeVector_of_count_eq_one expansion single]

/-- The positive-gap range vector is the same pointwise intrinsic target as
the equivalent ordinary expansion. -/
private theorem positiveGap_rangeVector_eq
    (b : OrderExpansion.PositiveGapExpansion N) :
    b.rangeVector = rangeVector b.asOrderExpansion := by
  apply WithLp.ofLp_injective
  funext address
  rw [OrderExpansion.PositiveGapExpansion.rangeVector_apply,
    rangeVector_apply]

/-- The complete intrinsic word prepares the exact uniform range for every
positive order expansion. -/
public theorem circuit_applyVec_zero (oracles : OracleModel)
    (expansion : OrderExpansion N) (positive : 0 < N) :
    (circuit oracles expansion).applyBinaryVec
        (NormalizedVector.ket (R := Qubits (width expansion)) 0 :
          HilbertVector (Qubits (width expansion))) =
      rangeVector expansion := by
  by_cases single : expansion.count = 1
  · exact circuit_applyVec_zero_of_count_eq_one oracles expansion single
  · have multiple : 2 ≤ expansion.count := by
      have countPositive := expansion.count_pos
      omega
    let b := expansion.toPositiveGapExpansion multiple positive
    have recovered : b.asOrderExpansion = expansion :=
      OrderExpansion.PositiveGapExpansion.asOrderExpansion_toPositiveGapExpansion
        expansion multiple positive
    rw [← recovered]
    exact (b.intrinsicCircuit_applyVec_zero oracles).trans
      (positiveGap_rangeVector_eq b)

end

end QuantumAlg.FiniteCyclicDLP.OrderPreparation.Intrinsic
