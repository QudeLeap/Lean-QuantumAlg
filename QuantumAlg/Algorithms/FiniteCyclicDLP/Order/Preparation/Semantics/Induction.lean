/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Initial
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Stage
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Initial
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Stage

/-!
# Full positive-gap native preparation induction

The invariant is the finite sum of accepted aligned blocks plus the one
remaining block.  Each literal stage fixes the accepted part and splits the
remaining part with the proved source-angle coefficients.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion

noncomputable section

variable {N : Nat}

private def sourcePosition (b : PositiveGapExpansion N) (count : Nat) :
    Fin (b.gaps + 1) :=
  ⟨min count b.gaps, by omega⟩

private lemma sourcePosition_eq_of_le (b : PositiveGapExpansion N)
    {count : Nat} (bounded : count ≤ b.gaps) :
    b.sourcePosition count = ⟨count, by omega⟩ := by
  apply Fin.ext
  simp [sourcePosition, Nat.min_eq_left bounded]

private lemma sourcePosition_lt_of_lt (b : PositiveGapExpansion N)
    {left right : Nat} (rightBound : right ≤ b.gaps) (before : left < right) :
    (b.sourcePosition left).val < (b.sourcePosition right).val := by
  simp [sourcePosition,
    Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt before) rightBound),
    Nat.min_eq_left rightBound, before]

private def acceptedPrefix (b : PositiveGapExpansion N) (count : Nat) :
    HilbertVector (Qubits b.width) :=
  ∑ index ∈ Finset.range count,
    (b.blockWeight (b.sourcePosition index) : ℂ) •
      b.residualBlock (b.sourcePosition index)

private def prefixState (b : PositiveGapExpansion N) (count : Nat) :
    HilbertVector (Qubits b.width) :=
  b.acceptedPrefix count +
    (b.residualWeight (b.sourcePosition count) : ℂ) •
      b.residualBlock (b.sourcePosition count)

private lemma acceptedPrefix_succ (b : PositiveGapExpansion N) (count : Nat) :
    b.acceptedPrefix (count + 1) = b.acceptedPrefix count +
      (b.blockWeight (b.sourcePosition count) : ℂ) •
        b.residualBlock (b.sourcePosition count) := by
  unfold acceptedPrefix
  rw [Finset.sum_range_succ]

private lemma applyVec_finset_sum
    {gates : GateModel} {oracles : OracleModel}
    {environment : oracles.Interpretation} {width : Nat}
    (circuit : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    {ι : Type} (set : Finset ι)
    (term : ι → HilbertVector (Qubits width)) :
    (circuit.applyBinaryVec environment) (∑ index ∈ set, term index) =
      ∑ index ∈ set, (circuit.applyBinaryVec environment) (term index) := by
  classical
  induction set using Finset.induction_on with
  | empty =>
      have zero := UnitaryCircuit.applyBinaryVec_smul circuit (0 : ℂ)
        (0 : HilbertVector (Qubits width)) environment
      simpa using zero
  | @insert element set outside induction =>
      rw [Finset.sum_insert outside, Finset.sum_insert outside,
        UnitaryCircuit.applyBinaryVec_add, induction]

private lemma gapStage_applyVec_acceptedPrefix (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) (count : Nat) (notFinished : count < b.gaps) :
    ((b.gapStage oracles ⟨count, notFinished⟩).applyBinaryVec environment)
        (b.acceptedPrefix count) = b.acceptedPrefix count := by
  unfold acceptedPrefix
  rw [applyVec_finset_sum]
  apply Finset.sum_congr rfl
  intro index member
  rw [UnitaryCircuit.applyBinaryVec_smul]
  congr 1
  apply b.gapStage_applyVec_residual_eq_self oracles ⟨count, notFinished⟩
  have before := b.sourcePosition_lt_of_lt (Nat.le_of_lt notFinished)
    (Finset.mem_range.mp member)
  rw [b.sourcePosition_eq_of_le (Nat.le_of_lt notFinished)] at before
  simpa using before

private lemma gapStage_applyVec_prefixState (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) (count : Nat) (notFinished : count < b.gaps) :
    ((b.gapStage oracles ⟨count, notFinished⟩).applyBinaryVec environment) (b.prefixState count) =
      b.prefixState (count + 1) := by
  let gap : Fin b.gaps := ⟨count, notFinished⟩
  have current : b.sourcePosition count = gap.castSucc := by
    apply Fin.ext
    simp [sourcePosition, gap, Nat.min_eq_left (Nat.le_of_lt notFinished)]
  have next : b.sourcePosition (count + 1) = gap.succ := by
    apply Fin.ext
    simp [sourcePosition, gap,
      Nat.min_eq_left (by omega : count + 1 ≤ b.gaps)]
  have retained :
      (b.residualWeight gap.castSucc : ℂ) *
          (Real.cos (b.sourceAngle gap / 2) : ℂ) =
        (b.blockWeight gap.castSucc : ℂ) := by
    exact_mod_cast b.residualWeight_mul_cos_half_sourceAngle gap
  have opened :
      (b.residualWeight gap.castSucc : ℂ) *
          (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) =
        (b.residualWeight gap.succ : ℂ) := by
    exact_mod_cast b.residualWeight_mul_neg_sin_half_sourceAngle gap
  unfold prefixState
  rw [UnitaryCircuit.applyBinaryVec_add,
    b.gapStage_applyVec_acceptedPrefix oracles count notFinished,
    UnitaryCircuit.applyBinaryVec_smul, current,
    b.gapStage_applyVec_residual oracles gap]
  simp only [smul_add, smul_smul]
  rw [opened, retained, ← next, ← current, b.acceptedPrefix_succ count]
  abel

private lemma gapPrefix_foldl_applyVec (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) :
    ∀ (count : Nat) (bounded : count ≤ b.gaps),
      (List.ofFn (fun index : Fin count =>
        b.gapStage oracles (Fin.castLE bounded index))).foldl
          (fun state circuit => (circuit.applyBinaryVec environment) state)
          (b.residualBlock 0) = b.prefixState count := by
  intro count
  induction count with
  | zero =>
      intro _
      simp [prefixState, acceptedPrefix, sourcePosition,
        b.residualWeight_zero]
  | succ count induction =>
      intro bounded
      have previous : count ≤ b.gaps := Nat.le_of_succ_le bounded
      have step : count < b.gaps := by omega
      have leading :
          (List.ofFn (fun index : Fin count =>
            b.gapStage oracles (Fin.castLE bounded index.castSucc))).foldl
              (fun state circuit => (circuit.applyBinaryVec environment) state)
              (b.residualBlock 0) = b.prefixState count := by
        have castSame : ∀ index : Fin count,
            Fin.castLE bounded index.castSucc = Fin.castLE previous index := by
          intro index
          apply Fin.ext
          rfl
        simpa only [castSame] using induction previous
      have last : Fin.castLE bounded (Fin.last count) =
          (⟨count, step⟩ : Fin b.gaps) := by
        apply Fin.ext
        rfl
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat,
        leading, last]
      exact b.gapStage_applyVec_prefixState oracles count step

private lemma prefixState_last_eq_blockSum (b : PositiveGapExpansion N) :
    b.prefixState b.gaps =
      ∑ index : Fin (b.gaps + 1),
        (b.blockWeight index : ℂ) • b.residualBlock index := by
  have lastPosition : b.sourcePosition b.gaps = Fin.last b.gaps := by
    apply Fin.ext
    simp [sourcePosition]
  let penultimate : Fin b.gaps := ⟨b.gaps - 1, by
    have positive := b.gaps_pos
    omega⟩
  have nextIsLast : penultimate.succ = Fin.last b.gaps := by
    apply Fin.ext
    change (b.gaps - 1) + 1 = b.gaps
    have positive := b.gaps_pos
    omega
  have tail : b.tailMass penultimate.castSucc =
      2 ^ b.ell penultimate.succ := by
    have adjacent := b.tailMass_eq_pow_add_tailMass_succ penultimate
    have lastTail : b.tailMass penultimate.succ = 0 := by
      rw [nextIsLast, b.tailMass_last]
    rw [lastTail, Nat.add_zero] at adjacent
    exact adjacent
  have remaining : N - b.lowerMass (Fin.last b.gaps) =
      2 ^ b.ell (Fin.last b.gaps) := by
    calc
      N - b.lowerMass (Fin.last b.gaps) =
          N - b.lowerMass penultimate.succ := by rw [nextIsLast]
      _ = b.tailMass penultimate.castSucc :=
        b.N_sub_lowerMass_succ_eq_tailMass penultimate
      _ = 2 ^ b.ell penultimate.succ := tail
      _ = 2 ^ b.ell (Fin.last b.gaps) := by rw [nextIsLast]
  have weight : b.residualWeight (Fin.last b.gaps) =
      b.blockWeight (Fin.last b.gaps) := by
    unfold residualWeight blockWeight
    rw [remaining]
  have position (index : Fin b.gaps) :
      b.sourcePosition index.val = index.castSucc := by
    rw [b.sourcePosition_eq_of_le (Nat.le_of_lt index.isLt)]
    apply Fin.ext
    rfl
  have prefixSum :
      (∑ index : Fin b.gaps,
        (b.blockWeight index.castSucc : ℂ) • b.residualBlock index.castSucc) =
      ∑ index : Fin b.gaps,
        (b.blockWeight (b.sourcePosition index.val) : ℂ) •
          b.residualBlock (b.sourcePosition index.val) := by
    apply Finset.sum_congr rfl
    intro index _
    rw [position index]
  unfold prefixState acceptedPrefix
  rw [lastPosition, weight, Fin.sum_univ_castSucc]
  congr 1
  rw [prefixSum]
  exact (Fin.sum_univ_eq_sum_range (fun index =>
    (b.blockWeight (b.sourcePosition index) : ℂ) •
      b.residualBlock (b.sourcePosition index)) b.gaps).symm

private lemma intrinsic_gapStage_eq (oracles : OracleModel)
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    OrderPreparation.Intrinsic.gapStage oracles b.asOrderExpansion gap =
      b.gapStage oracles gap := by
  rfl

/-- The complete literal intrinsic schedule prepares the exact raw uniform
range vector for every expansion with at least one positive gap. -/
public lemma intrinsicCircuit_applyVec_zero (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) :
    ((OrderPreparation.Intrinsic.circuit oracles b.asOrderExpansion).applyBinaryVec environment)
        (NormalizedVector.ket (R := Qubits b.width) 0 :
          HilbertVector (Qubits b.width)) = b.rangeVector := by
  unfold OrderPreparation.Intrinsic.circuit
  rw [UnitaryCircuit.applyBinaryVec_indexedProduct,
    b.initialPreparation_applyVec_zero_eq_residualBlock_zero oracles]
  have stageFunction :
      OrderPreparation.Intrinsic.gapStage oracles b.asOrderExpansion =
      b.gapStage oracles := by
    funext gap
    exact intrinsic_gapStage_eq oracles b gap
  rw [stageFunction]
  have folded := b.gapPrefix_foldl_applyVec oracles (environment := environment)
    b.gaps (Nat.le_refl _)
  rw [b.prefixState_last_eq_blockSum, b.blockSum_eq_rangeVector] at folded
  exact folded

end

end QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion
