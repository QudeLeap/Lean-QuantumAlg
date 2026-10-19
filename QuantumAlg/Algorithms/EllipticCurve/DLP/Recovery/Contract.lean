/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.PreparedSupport
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Group
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.Circuit.Effect
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Values
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model.Bounds
import all QuantumAlg.Util.FinPow.BinaryBasis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selected-frequency recovery and finite success contract

The selected event, complete raw candidate condition, persistent selection
inclusion and packed-secret statements share this canonical owner. The prepared
exceptional mass has one mathematical owner. The statements apply to arbitrary
complete Store values and external Reference systems.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.FiniteCyclicDLP
open FiniteCyclicDLP Canonical.Probability ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
open scoped BigOperators ComplexOrder

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}



private lemma pairedBranch_bit (exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (index : Fin (2 * exponentWidth)) :
    (prodEquiv branch).val.testBit index.rev.val =
      ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index := by
  unfold ExceptionalOffsetAveraging.pairedBigEndianSelected
  split_ifs with first
  · have localLt : exponentWidth - 1 - index.val < exponentWidth := by omega
    have reversed : index.rev.val = exponentWidth + (exponentWidth - 1 - index.val) := by
      rw [Fin.val_rev]
      omega
    rw [reversed]
    exact prodEquiv_testBit_left branch.1 branch.2
      (⟨exponentWidth - 1 - index.val, localLt⟩ : Fin exponentWidth)
  · have localLt : exponentWidth - 1 - (index.val - exponentWidth) < exponentWidth := by omega
    have reversed : index.rev.val = exponentWidth - 1 - (index.val - exponentWidth) := by
      rw [Fin.val_rev]
      omega
    rw [reversed]
    exact prodEquiv_testBit_right branch.1 branch.2
      (⟨exponentWidth - 1 - (index.val - exponentWidth), localLt⟩ : Fin exponentWidth)

/-- The classical point checker uses exactly the original known-order group target. -/
lemma groupScalar_eq_target_iff [Fact p.Prime]
    (problem : KnownOrderProblem E.GroupPoint) (scalar : Nat) :
    scalar • problem.generator.toMathlib = problem.target.toMathlib ↔
      problem.generator ^ scalar = problem.target := by
  rw [← Canonical.Recovery.AttemptSoundness.groupPoint_pow_toMathlib
    E problem.generator scalar]
  constructor
  · intro equality
    apply (groupPointEquiv E).injective
    exact equality
  · intro equality
    exact congrArg GroupPoint.toMathlib equality

/-- A proof-side secret witness satisfies the same classical point check. -/
lemma secret_groupScalar_eq_target [Fact p.Prime]
    (problem : KnownOrderProblem E.GroupPoint)
    (input : FiniteCyclicDLP.Canonical.Probability.SecretInput problem) :
    input.secret.val • problem.generator.toMathlib = problem.target.toMathlib := by
  exact (groupScalar_eq_target_iff problem input.secret.val).mpr input.target_eq_generator_pow

/-- The original useful frequency pair selected by an invertible residue. -/
def selectedExponentFrequency (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (unit : (ZMod problem.order)ˣ) :
    Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem) :=
  (selectedIndex problem unit, selectedIndex problem (-input.secret * unit))

/-- Distinct units have distinct original left frequencies. -/
lemma selectedExponentFrequency_injective (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) :
    Function.Injective (selectedExponentFrequency problem input) := by
  intro left right same
  exact Units.ext (selectedIndex_injective problem (congrArg Prod.fst same))

/-- The useful raw event reads precisely the original paired big-endian exponent bits. -/
def selectedExponentEvent (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (bits : Fin (2 * orderWidth problem) → Bool) : Bool := by
  classical
  exact decide (∃ unit : (ZMod problem.order)ˣ,
    bits = ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
      (selectedExponentFrequency problem input unit))

/-- Every advertised source frequency lies in the same mathematical raw-bit event. -/
lemma selectedExponentEvent_selected (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (unit : (ZMod problem.order)ˣ) :
    selectedExponentEvent problem input
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
        (selectedExponentFrequency problem input unit)) = true := by
  classical
  exact decide_eq_true (by exact ⟨unit, rfl⟩)

/-- Original paired bits identify exactly the original frequency pair, including width zero. -/
private lemma originalPairedBits_injective (width : Nat) :
    Function.Injective (ExceptionalOffsetAveraging.pairedBigEndianSelected width) := by
  intro left right same
  apply (prodEquiv (m := width) (n := width)).injective
  let packedWidth : width + width = 2 * width := by omega
  let castPacked := finCongr (congrArg (fun count : Nat => 2 ^ count) packedWidth)
  apply castPacked.injective
  apply (BinaryBasis.bigEndianEquiv (2 * width)).symm.injective
  funext index
  rw [BinaryBasis.bigEndianEquiv_symm_value, BinaryBasis.bigEndianEquiv_symm_value]
  change finTwoEquiv.symm ((prodEquiv left).val.testBit index.rev.val) =
    finTwoEquiv.symm ((prodEquiv right).val.testBit index.rev.val)
  exact congrArg finTwoEquiv.symm ((pairedBranch_bit width left index).trans
    ((congrFun same index).trans (pairedBranch_bit width right index).symm))

/-- The raw event holds exactly on the original family of selected frequency pairs. -/
lemma selectedExponentEvent_pair_iff (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem)
    (frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) :
    selectedExponentEvent problem input
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) frequency) = true ↔
      ∃ unit : (ZMod problem.order)ˣ,
        frequency = selectedExponentFrequency problem input unit := by
  simp only [selectedExponentEvent, decide_eq_true_eq]
  constructor
  · rintro ⟨unit, same⟩
    exact ⟨unit, originalPairedBits_injective (orderWidth problem) same⟩
  · rintro ⟨unit, rfl⟩
    exact ⟨unit, rfl⟩

/-- Reinterpret the actual ordered mask in the original raw shape, without changing a bit. -/
def rawExponentInput (problem : KnownOrderProblem E.GroupPoint)
    (bits : Fin (2 * orderWidth problem) → Bool) :
    CShape.Value (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.InputShape
      (orderWidth problem)) :=
  .bits (fun index => bits (Fin.cast (by omega) index))

/-- The original packed pair and the actual mask agree at every physical bit. -/
lemma rawExponentInput_pair (problem : KnownOrderProblem E.GroupPoint)
    (frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) :
    rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) frequency) =
      .bits (Canonical.BornBridge.measurementOutcome problem (prodEquiv frequency)) := by
  apply congrArg CShape.Value.bits
  funext index
  change ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) frequency
    (Fin.cast (by omega) index) =
      (prodEquiv frequency).val.testBit
        (orderWidth problem + orderWidth problem - 1 - index.val)
  rw [← pairedBranch_bit]
  apply congrArg (prodEquiv frequency).val.testBit
  rw [Fin.val_rev, Fin.val_cast]
  omega

/-- A selected unit gives precisely the original selected raw recovery input. -/
lemma rawExponentInput_selected (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (unit : (ZMod problem.order)ˣ) :
    rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
        (selectedExponentFrequency problem input unit)) =
      RecoveryBridge.selectedRawInput problem input unit := by
  exact rawExponentInput_pair problem _

/-- Existing pure recovery computes the advertised secret on every original selected unit. -/
lemma outputOf_selectedExponentFrequency_recovers
    (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem)
    (unit : (ZMod problem.order)ˣ) (spec : ModulusSpec (orderWidth problem))
    (sameOrder : spec.modulus = problem.order) :
    ∃ output : ClassicalRoutines.FiniteCyclicDLP.Output spec,
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputOf spec
        (rawExponentInput problem
          (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            (selectedExponentFrequency problem input unit))) = some output ∧
      output.candidate.val = input.secret.val ∧ output.verified = true := by
  rw [rawExponentInput_selected]
  exact RecoveryBridge.outputOf_selectedRawInput_recovers problem input unit spec sameOrder

/-- Membership of the actual measured mask suffices for candidate recovery and verification. -/
lemma outputOf_selectedExponentEvent_recovers
    (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem)
    (bits : Fin (2 * orderWidth problem) → Bool)
    (selected : selectedExponentEvent problem input bits = true)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order) :
    ∃ output : ClassicalRoutines.FiniteCyclicDLP.Output spec,
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputOf spec
        (rawExponentInput problem bits) = some output ∧
      output.candidate.val = input.secret.val ∧ output.verified = true := by
  classical
  obtain ⟨unit, rfl⟩ := of_decide_eq_true selected
  exact outputOf_selectedExponentFrequency_recovers problem input unit spec sameOrder

/-- The original three-cell recovery model encodes success, the secret and reconstruction. -/
lemma outputCells_selectedExponentEvent
    (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem)
    (bits : Fin (2 * orderWidth problem) → Bool)
    (selected : selectedExponentEvent problem input bits = true)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order) :
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells spec
      (rawExponentInput problem bits) =
      .product (.bit true)
        (.product (CShape.wordOfNat (orderWidth problem) input.secret.val) (.bit true)) := by
  obtain ⟨output, success, candidate, verified⟩ :=
    outputOf_selectedExponentEvent_recovers problem input bits selected spec sameOrder
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_of_outputOf_some
    spec _ output success, candidate, verified]

/-- A nontrivial order yields the local fixed-width modulus required by the raw model. -/
def recoveryModulusSpec (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) : ModulusSpec (orderWidth problem) where
  modulus := problem.order
  two_le := nontrivial
  le_capacity := order_le_fourierModulus problem

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Structural reindexing preserves every actual finite measurement value and its bit order. -/
def rawRecoveryInput (problem : KnownOrderProblem E.GroupPoint)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2))) :
    CInputRef ctx (.fixedVector (orderWidth problem + orderWidth problem) (.finite 2)) :=
  .fixedVector fun index => .vectorGet measured (Fin.cast (by omega) index)

/-- The actual decoder input is exactly the original raw exponent mask at every bit. -/
lemma preparationInput_rawRecoveryInput (problem : KnownOrderProblem E.GroupPoint)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (store : Store ctx) :
    preparationInput (store.read (rawRecoveryInput problem measured)) =
      rawExponentInput problem (QubitReadouts.mask (store.read measured)) := rfl

section CandidateCondition

variable [Fact p.Prime]

/-- Within the original subgroup order, the public point equation identifies the unique secret. -/
lemma bounded_groupScalar_eq_target_iff (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (scalar : Nat) (bounded : scalar < problem.order) :
    scalar • problem.generator.toMathlib = problem.target.toMathlib ↔
      scalar = input.secret.val := by
  rw [groupScalar_eq_target_iff]
  constructor
  · intro accepted
    have sameResidue := pow_inj_mod.mp (accepted.trans input.target_eq_generator_pow.symm)
    have secretBound : input.secret.val < problem.order :=
      (residueIndex problem input.secret).isLt
    rw [← problem.order_eq_orderOf, Nat.mod_eq_of_lt bounded,
      Nat.mod_eq_of_lt secretBound] at sameResidue
    exact sameResidue
  · intro same
    rw [same]
    exact input.target_eq_generator_pow

/-- The actual raw candidate condition recognizes precisely the secret and original two flags. -/
lemma sampleAccepted_iff_secret (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (sample : CShape.Value (.fixedVector (orderWidth problem + orderWidth problem) (.finite 2))) :
    SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      problem.generator.toMathlib problem.target.toMathlib sample ↔
      let raw := ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells
        (recoveryModulusSpec problem nontrivial)
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput sample)
      raw.second.first.toNat = input.secret.val ∧
        raw.first.toBool = true ∧ raw.second.second.toBool = true := by
  dsimp only [SampleAccepted]
  exact and_congr (bounded_groupScalar_eq_target_iff problem input _
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_candidate_lt
      (recoveryModulusSpec problem nontrivial) _)) Iff.rfl

/-- Every original selected measured event meets the actual raw flags and public point equation. -/
lemma selectedExponentEvent_sampleAccepted (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (before : Store ctx)
    (selected : selectedExponentEvent problem input (QubitReadouts.mask (before.read measured)) =
      true) :
    SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      problem.generator.toMathlib problem.target.toMathlib
      (before.read (rawRecoveryInput problem measured)) := by
  have secretFits : input.secret.val < 2 ^ orderWidth problem :=
    lt_of_lt_of_le (residueIndex problem input.secret).isLt (order_le_fourierModulus problem)
  unfold SampleAccepted
  rw [preparationInput_rawRecoveryInput,
    outputCells_selectedExponentEvent problem input _ selected
      (recoveryModulusSpec problem nontrivial) rfl]
  change (input.secret.val % 2 ^ orderWidth problem) • problem.generator.toMathlib =
      problem.target.toMathlib ∧ true = true ∧ true = true
  rw [Nat.mod_eq_of_lt secretFits]
  exact ⟨secret_groupScalar_eq_target problem input, rfl, rfl⟩

end CandidateCondition

private lemma indicator_weight_mono {R : Register} (density : DensityOperator R)
    (first second : Prop) [Decidable first] [Decidable second] (included : first → second) :
    (if first then Effect.one R else Effect.zero R).weight density ≤
      (if second then Effect.one R else Effect.zero R).weight density := by
  by_cases selected : first
  · simp only [selected, included selected, if_true, le_refl]
  · by_cases eligible : second
    · simp only [selected, eligible, if_false, if_true, Effect.weight_one, Effect.weight_zero]
      exact density.mass_nonneg
    · simp only [selected, eligible, if_false, le_refl]

section PersistentSelection

variable [Fact p.Prime]

omit [Fact p.Prime] in
private lemma rawRecoveryInput_persistentInput (problem : KnownOrderProblem E.GroupPoint)
    (width : Nat)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2))) :
    persistentInput width (orderWidth problem) (rawRecoveryInput problem measured) =
      rawRecoveryInput problem (persistentInput width (orderWidth problem) measured) := rfl

/-- The actual lifted sample has the original flags and natural-scalar equation on selection. -/
lemma selectedExponentEvent_persistentSampleAccepted (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem) (width : Nat)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (before : Store (persistentCtx ctx width (orderWidth problem)))
    (selected : selectedExponentEvent problem input (QubitReadouts.mask
      (before.read (persistentInput width (orderWidth problem) measured))) = true) :
    SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      problem.generator.toMathlib problem.target.toMathlib
      (before.read (persistentInput width (orderWidth problem)
        (rawRecoveryInput problem measured))) := by
  rw [rawRecoveryInput_persistentInput]
  exact selectedExponentEvent_sampleAccepted problem nontrivial input
    (persistentInput width (orderWidth problem) measured) before selected

/-- Selected measurement mass is contained in the same original stored-candidate event. -/
lemma selectedPersistentSample_weight_le (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem) (width : Nat)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width (orderWidth problem)) Reference History) :
    state.effectWeight (fun record => if selectedExponentEvent problem input (QubitReadouts.mask
      (record.1.read (persistentInput width (orderWidth problem) measured))) = true then
        Effect.one ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)) ≤
      state.effectWeight (fun record =>
        if SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
            problem.generator.toMathlib problem.target.toMathlib
            (record.1.read (persistentInput width (orderWidth problem)
              (rawRecoveryInput problem measured))) then
          Effect.one ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)
        else Effect.zero
          ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro record _
  exact indicator_weight_mono (state.block record) _ _
    (selectedExponentEvent_persistentSampleAccepted problem nontrivial input width measured
      record.1)

end PersistentSelection

section PackedSecret

variable [Fact p.Prime]

private lemma selected_word_eq_secret (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (bounded : value.toNat < problem.order)
    (correct : value.toNat • problem.generator.toMathlib = problem.target.toMathlib) :
    value = CShape.wordOfNat (orderWidth problem) input.secret.val := by
  have decoded := (bounded_groupScalar_eq_target_iff problem input value.toNat bounded).mp correct
  have fits : input.secret.val < 2 ^ orderWidth problem :=
    lt_of_lt_of_le (residueIndex problem input.secret).isLt (order_le_fourierModulus problem)
  cases value with
  | unsignedWord word =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      change word.val = input.secret.val % 2 ^ orderWidth problem
      rw [Nat.mod_eq_of_lt fits]
      exact decoded

/-- Every actual returned word is the original secret when the established invariants hold. -/
lemma packBatchResult_supported_secret {model : ExecutionModel}
    {environment : model.Environment}
    {placement : RuntimeCtx model.kind}
    [BitWord.Selected model]
    (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx placement (Canonical.Layout.fieldWidth E) (orderWidth problem))
      Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted placement (Canonical.Layout.fieldWidth E)
        (orderWidth problem)).toCStorageRef)).toBool = true →
      let selected := entry.1.read (.storage (persistentSelected placement
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).toCStorageRef)
      selected.toNat < problem.order ∧
        selected.toNat • problem.generator.toMathlib = problem.target.toMathlib)
    (result : Store
      (batchResultCtx placement (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      (model.HiddenState ×
        (H × (packBatchResult placement (Canonical.Layout.fieldWidth E)
          (orderWidth problem)).Path)))
    (positive : 0 < (((packBatchResult placement (Canonical.Layout.fieldWidth E)
      (orderWidth problem)).execute environment Reference state).block result).mass)
    (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (output : result.1.read (batchResultRead placement (Canonical.Layout.fieldWidth E)
      (orderWidth problem)) = .optionSome value) :
    value = CShape.wordOfNat (orderWidth problem) input.secret.val := by
  refine packBatchResult_supported_property
    (fun value => value = CShape.wordOfNat (orderWidth problem) input.secret.val)
    state ?_ result positive value output
  intro entry present accepted
  have valid := holds entry present accepted
  exact selected_word_eq_secret problem input _ valid.1 valid.2

end PackedSecret

/-- The original selected floor with its complete exceptional error never exceeds one. -/
lemma samplingCandidateFloor_le_one (problem : KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    (problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed) ≤ 1 := by
  have orderBound : (problem.order : ℝ) ≤ (fourierModulus problem : ℝ) := by
    exact_mod_cast order_le_fourierModulus problem
  have totientBound : (Nat.totient problem.order : ℝ) ≤ (problem.order : ℝ) := by
    exact_mod_cast Nat.totient_le problem.order
  have modulusPositive : 0 < (fourierModulus problem : ℝ) := by
    unfold fourierModulus
    positivity
  have productBound : (problem.order : ℝ) * Nat.totient problem.order ≤
      (fourierModulus problem : ℝ) ^ 2 := by
    calc
      _ ≤ (problem.order : ℝ) * problem.order :=
        mul_le_mul_of_nonneg_left totientBound (Nat.cast_nonneg _)
      _ ≤ (fourierModulus problem : ℝ) * fourierModulus problem :=
        mul_self_le_mul_self (Nat.cast_nonneg _) orderBound
      _ = _ := by ring
  have numeratorBound : (problem.order : ℝ) * Nat.totient problem.order <
      4 * (fourierModulus problem : ℝ) ^ 2 := by
    nlinarith [sq_pos_of_pos modulusPositive]
  have selectedBound : (problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) < 1 :=
    (div_lt_one (by positivity)).mpr numeratorBound
  exact (sub_le_self _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).trans selectedBound.le

/-- The exact original failure coefficient can multiply inequalities in the actual loop. -/
lemma samplingFailureRatio_nonneg (problem : KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    0 ≤ 1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)) :=
  sub_nonneg.mpr (samplingCandidateFloor_le_one problem points seed)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Every physical affine addend represents its original big-endian public group power. -/
public def AddendEncoding (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E) : Prop :=
  (fun index => (points index).toGroupPoint) =
    ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth (ECDLP.Canonical.problem I))
      (ECDLP.Canonical.problem I).generator (ECDLP.Canonical.problem I).target

/-- The complete original exceptional error must fit the explicitly chosen finite retry budget. -/
public def RepetitionCondition (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (count : Nat) (failure : ℝ) : Prop :=
  (1 - (((I.subgroupOrder : ℝ) * Nat.totient I.subgroupOrder /
    (4 * (fourierModulus (ECDLP.Canonical.problem I) : ℝ) ^ 2)) -
      4 * Real.sqrt (preparedExceptionalMass (ECDLP.Canonical.problem I) points seed))) ^
        count ≤ failure

/-- Only a bounded scalar satisfying the original public group equation is accepted. -/
def AcceptedOutput (I : ECDLPInstance E)
    (output : CShape.Value (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I))))) :
    Prop :=
  ∃ scalar : ZMod I.subgroupOrder, I.CandidateScalar scalar ∧
    output = .optionSome (CShape.wordOfNat (orderWidth (ECDLP.Canonical.problem I)) scalar.val)

/-- The independent success requirement uses the explicitly allowed failure probability. -/
def successLowerBound (failure : ℝ) : ProbabilityLowerBound where
  value := 1 - ENNReal.ofReal failure
  le_one := tsub_le_self

end

end QuantumAlg.EllipticCurve.LogicalResources
