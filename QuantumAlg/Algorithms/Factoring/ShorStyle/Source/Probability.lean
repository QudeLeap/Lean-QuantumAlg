/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Distribution
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Analysis
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.SourceMass
import all QuantumAlg.Util.NumberTheory.EulerTotientBounds
import all QuantumAlg.Util.PMF
import all QuantumAlg.Util.NumberTheory.Factoring

/-!
# Source probability for the canonical Shor sample and Born law

This module contains only theorem-side sampling and amplification facts.
Semiprime factors occur solely in the source success event and its proof.
The original finite random sample remains correlated with its selected
member's Born outcome. Native execution must establish this source joint law
and its independent repetitions from actual stored results before applying
these bounds; this module supplies no execution or resource certificate.
The reduction to order finding and its measured recoverable outcomes follow
[Sho95, source.tex:1124-1169,1183-1300].
-/

section

namespace QuantumAlg
namespace Factoring
namespace ShorStyle
namespace Canonical
namespace Probability

open OrderFinding

noncomputable section

/-- Build the proof-only public input from a theorem-side semiprime model. -/
theorem Input.ofSemiprimeModel {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) : Input N where
  modulus_gt_one := model.modulus_gt_one

/-- Public postcondition for the bounded optional factor word. -/
def ReturnedDeclaredFactor {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) :
    CShape.Value (.option (.unsignedWord (modulusBits N))) → Prop
  | .optionSome candidate =>
      candidate.toNat = model.leftFactor ∨
        candidate.toNat = model.rightFactor
  | .optionNone => False

/-- Canonical natural representative of one internally sampled unit. -/
def sampledBase {N : Nat} (unit : (ZMod N)ˣ) : Nat :=
  (unit : ZMod N).val

/-- Mathematical order-finding input associated with one internal unit. -/
theorem sampledOrderInput {N : Nat} (input : Input N)
    (unit : (ZMod N)ˣ) :
    OrderFinding.Input N (sampledBase unit) (orderOf unit) := by
  let _ : NeZero N := input.neZero
  refine
    { modulus_ge_two := input.modulus_ge_two
      coprime := ZMod.val_coe_unit_coprime unit
      order_pos := orderOf_pos unit
      order_eq_one := ?_
      minimal := ?_ }
  · have hunit : unit ^ orderOf unit = 1 := pow_orderOf_eq_one unit
    have hvalue := congrArg (fun value : (ZMod N)ˣ => (value : ZMod N)) hunit
    have hbase : ((sampledBase unit : Nat) : ZMod N) = (unit : ZMod N) := by
      exact ZMod.natCast_zmod_val (unit : ZMod N)
    have hcast :
        (((sampledBase unit) ^ orderOf unit : Nat) : ZMod N) =
          ((1 : Nat) : ZMod N) := by
      rw [Nat.cast_pow, hbase]
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, Nat.cast_one]
        using hvalue
    have hmod : (sampledBase unit) ^ orderOf unit ≡ 1 [MOD N] :=
      (ZMod.natCast_eq_natCast_iff _ _ N).mp hcast
    rw [Nat.ModEq] at hmod
    simpa [Nat.mod_eq_of_lt input.modulus_gt_one] using hmod
  · intro exponent hexponent hreturn
    apply orderOf_le_of_pow_eq_one hexponent
    apply Units.ext
    have hmod : (sampledBase unit) ^ exponent ≡ 1 [MOD N] := by
      rw [Nat.ModEq]
      simpa [Nat.mod_eq_of_lt input.modulus_gt_one] using hreturn
    have hcast := (ZMod.natCast_eq_natCast_iff
      ((sampledBase unit) ^ exponent) 1 N).mpr hmod
    have hbase : ((sampledBase unit : Nat) : ZMod N) = (unit : ZMod N) := by
      exact ZMod.natCast_zmod_val (unit : ZMod N)
    change (unit : ZMod N) ^ exponent = (1 : ZMod N)
    rw [← hbase]
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast

/-- Runtime modular-exponentiation access for one proof-only sampled unit. -/
theorem sampledOracleAccess {N : Nat} (input : Input N) (unit : (ZMod N)ˣ) :
    ModExpOracleAccess N (sampledBase unit) (phaseBits N) (modulusBits N) where
  modulus_pos := input.modulus_pos
  register_fits := input.register_fits

/-- Reconstructing the unit from its canonical representative is exact. -/
@[simp] theorem unitOfCoprime_sampledBase_eq {N : Nat} (input : Input N)
    (unit : (ZMod N)ˣ) :
    ZMod.unitOfCoprime (sampledBase unit)
        (sampledOrderInput input unit).coprime = unit := by
  let _ : NeZero N := input.neZero
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime]
  exact ZMod.natCast_zmod_val (unit : ZMod N)

/-- Proof-only prepared residue corresponding to a fixed sampled unit. -/
def preparedUnit {N : Nat} (unit : (ZMod N)ˣ) : RSA.PreparedResidue N :=
  RSA.prepareResidue N (some (sampledBase unit))

@[simp] theorem preparedUnit_unit_eq {N : Nat} (input : Input N)
    (unit : (ZMod N)ˣ) : (preparedUnit unit).unit = unit := by
  unfold preparedUnit
  rw [RSA.prepareResidue_some_unit_of_coprime]
  exact unitOfCoprime_sampledBase_eq input unit

@[simp] theorem preparedUnit_earlyFactor_eq_none {N : Nat}
    (input : Input N) (unit : (ZMod N)ˣ) :
    (preparedUnit unit).earlyFactor = none := by
  unfold preparedUnit
  exact RSA.prepareResidue_some_earlyFactor_of_coprime _ _
    (sampledOrderInput input unit).coprime

/-- Fixed-width index of one sampled unit. -/
def sampledBaseIndex {N : Nat} (input : Input N) (unit : (ZMod N)ˣ) :
    Fin (2 ^ modulusBits N) := by
  letI : NeZero N := input.neZero
  exact ⟨sampledBase unit,
    lt_of_lt_of_le (ZMod.val_lt (unit : ZMod N)) input.register_fits⟩

theorem sampledBaseIndex_eligible {N : Nat} (input : Input N)
    (unit : (ZMod N)ˣ) :
    RSA.ResidueEligible N (sampledBaseIndex input unit).val := by
  let _ : Fact (1 < N) := ⟨input.modulus_gt_one⟩
  exact ⟨(ZMod.val_pos).mpr (Units.ne_zero unit),
    ZMod.val_lt (unit : ZMod N)⟩

/-- Canonical representatives distinguish sampled units. -/
theorem sampledBaseIndex_injective {N : Nat} (input : Input N) :
    Function.Injective (sampledBaseIndex input) := by
  let _ : NeZero N := input.neZero
  intro left right equal
  have values := congrArg Fin.val equal
  change sampledBase left = sampledBase right at values
  apply Units.ext
  exact ZMod.val_injective N values

/-- Runtime parameter encoding for a fixed proof-only unit. -/
def unitParameter {N : Nat} (input : Input N) (unit : (ZMod N)ˣ) :
    CShape.Value (ParameterShape (modulusBits N)) :=
  .product (.unsignedWord (sampledBaseIndex input unit))
    (.product (.bit false) (CShape.wordOfNat (modulusBits N) 0))

private theorem nativeSourcePMF_eq_of_base_eq
    {N x y t width : Nat} (baseEq : x = y)
    (left : ModExpOracleAccess N x t width)
    (right : ModExpOracleAccess N y t width) :
    OrderFinding.Native.sourceOutcomePMF left =
      OrderFinding.Native.sourceOutcomePMF right := by
  cases baseEq
  rfl

/-- A sample selecting one fixed unit has that unit's native source Born law. -/
theorem sampleOutcomePMF_eq_native_of_parameter_eq_unit
    {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (unit : (ZMod N)ˣ)
    (parameterEq : parameterValue input sample = unitParameter input unit) :
    sourceSampleOutcomePMF input sample =
      OrderFinding.Native.sourceOutcomePMF (sampledOracleAccess input unit) := by
  have hbase :
      (parameterValue input sample).first.toNat = sampledBase unit := by
    calc
      _ = (unitParameter input unit).first.toNat :=
        congrArg (fun value => value.first.toNat) parameterEq
      _ = sampledBase unit := rfl
  unfold sourceSampleOutcomePMF
  exact nativeSourcePMF_eq_of_base_eq hbase
    (sourceAccess input sample) (sampledOracleAccess input unit)

/-- Euler's elementary size bound turns the source recovery mass for any
sampled unit into the uniform `1 / (3n)` public-width floor. -/
theorem orderFindingFloor_ge_one_over_three_bitlength {N : Nat}
    (input : Input N) (unit : (ZMod N)ˣ) :
    (1 : Real) / (3 * (modulusBits N : Real)) ≤
      orderFindingOutputSuccessLowerBound (orderOf unit) := by
  have orderPositive : 0 < orderOf unit := orderOf_pos unit
  have orderLt : orderOf unit < N :=
    input_order_lt_modulus (sampledOrderInput input unit)
  have sizeBound : Nat.size (orderOf unit) ≤ modulusBits N := by
    rw [Nat.size_le]
    exact orderLt.trans_le input.register_fits
  have orderBound :
      orderOf unit ≤ Nat.totient (orderOf unit) * modulusBits N :=
    (NumberTheory.self_le_totient_mul_size (orderOf unit) orderPositive).trans
      (Nat.mul_le_mul_left _ sizeBound)
  have orderBoundReal :
      (orderOf unit : Real) ≤
        (Nat.totient (orderOf unit) : Real) * (modulusBits N : Real) := by
    exact_mod_cast orderBound
  have bitsPositive : (0 : Real) < modulusBits N := by
    exact_mod_cast input.modulusBits_pos
  have orderPositiveReal : (0 : Real) < orderOf unit := by
    exact_mod_cast orderPositive
  unfold orderFindingOutputSuccessLowerBound
  apply (div_le_div_iff₀ (mul_pos (by norm_num) bitsPositive)
    (mul_pos (by norm_num) orderPositiveReal)).2
  calc
    (1 : Real) * (3 * (orderOf unit : Real)) =
        3 * (orderOf unit : Real) := by ring
    _ ≤ 3 * ((Nat.totient (orderOf unit) : Real) *
        (modulusBits N : Real)) :=
      mul_le_mul_of_nonneg_left orderBoundReal (by norm_num)
    _ = (Nat.totient (orderOf unit) : Real) *
        (3 * (modulusBits N : Real)) := by ring

/-- For a fixed good-unit branch, the source selected-family Born law reaches
the source-certified recoverable-order event. -/
theorem sampleOutcomePMF_recoverable_ge_of_parameter_eq_unit
    {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (odd : ¬ Even N) (sample : Fin (2 ^ residueSamplingBits N))
    (unit : (ZMod N)ˣ)
    (parameterEq : parameterValue (Input.ofSemiprimeModel model) sample =
      unitParameter (Input.ofSemiprimeModel model) unit) :
    ENNReal.ofReal
        (orderFindingOutputSuccessLowerBound (orderOf unit)) ≤
      (sourceSampleOutcomePMF (Input.ofSemiprimeModel model) sample).toOuterMeasure
          {outcome |
            ShorSourceJoint.NativeRecoverableOutcome unit (orderOf unit) outcome} := by
  let input : Input N := Input.ofSemiprimeModel model
  let orderInput := sampledOrderInput input unit
  have registerBound : N ^ 2 ≤ 2 ^ phaseBits N := input.registerSquare_fits
  have scaledError :
      ((orderOf unit : Nat) : Real) ^ 2 < (2 : Real) ^ phaseBits N :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus orderInput) registerBound
  have modulusLarge : 12 ≤ N :=
    le_trans (by norm_num : 12 ≤ 15)
      (model.modulus_ge_fifteen_of_not_even odd)
  have largeRegister : 12 * orderOf unit ≤ 2 ^ phaseBits N :=
    largeRegister_of_publicRegisterBound_of_modulus_ge_twelve modulusLarge
      (input_order_lt_modulus orderInput) registerBound
  have sourceBound := ShorSourceJoint.SourceAnalysis.sourceOutputSuccessLowerBound_of_scaledError
    orderInput scaledError largeRegister
  rw [sampleOutcomePMF_eq_native_of_parameter_eq_unit
    input sample unit parameterEq]
  have bornEq :=
    ShorSourceJoint.SourceNativeEndpoint.nativeRecoverableMass_eq_sourceSuccessMass
    orderInput (sampledOracleAccess input unit)
  rw [unitOfCoprime_sampledBase_eq input unit] at sourceBound bornEq
  calc
    ENNReal.ofReal
        (orderFindingOutputSuccessLowerBound (orderOf unit)) ≤
        ENNReal.ofReal
          (orderFindingOutputSuccessMass unit
            (orderFindingPublicOutcomeProbability
              (phaseBits N) (orderOf unit))) :=
      ENNReal.ofReal_le_ofReal sourceBound
    _ = _ := bornEq.symm

/-- Fixed-sample recoverable-order mass in the public bit-length form used by
the sampler/Born product bound. -/
theorem sampleOutcomePMF_recoverable_ge_bitlength
    {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (odd : ¬ Even N) (sample : Fin (2 ^ residueSamplingBits N))
    (unit : (ZMod N)ˣ)
    (parameterEq : parameterValue (Input.ofSemiprimeModel model) sample =
      unitParameter (Input.ofSemiprimeModel model) unit) :
    ENNReal.ofReal ((1 : Real) / (3 * (modulusBits N : Real))) ≤
      (sourceSampleOutcomePMF (Input.ofSemiprimeModel model) sample).toOuterMeasure
          {outcome |
            ShorSourceJoint.NativeRecoverableOutcome unit (orderOf unit) outcome} := by
  refine (ENNReal.ofReal_le_ofReal
    (orderFindingFloor_ge_one_over_three_bitlength
      (Input.ofSemiprimeModel model) unit)).trans ?_
  exact sampleOutcomePMF_recoverable_ge_of_parameter_eq_unit
    model odd sample unit parameterEq

/-- Fixed-width representatives of the counted Shor good units. -/
noncomputable def goodResidueCandidates {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) :
    Finset (Fin (2 ^ modulusBits N)) :=
  model.goodEventUnits.image
    (sampledBaseIndex (Input.ofSemiprimeModel model))

@[simp] theorem goodResidueCandidates_card {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) :
    (goodResidueCandidates model).card = model.goodEventUnits.card := by
  unfold goodResidueCandidates
  exact Finset.card_image_of_injective _
    (sampledBaseIndex_injective (Input.ofSemiprimeModel model))

/-- Packed samples whose first proposal is a counted good unit. -/
noncomputable def firstProposalGoodBits {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) :
    Finset (Fin (2 ^ residueSamplingBits N)) :=
  Finset.univ.filter fun bits =>
    RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount bits
        (0 : Fin (15 + 1)) ∈ goodResidueCandidates model

/-- Exact cardinality of the first-good sampler cylinder. -/
theorem firstProposalGoodBits_card {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) :
    (firstProposalGoodBits model).card =
      (goodResidueCandidates model).card *
        (2 ^ modulusBits N) ^ 15 := by
  classical
  unfold firstProposalGoodBits
  change
    ((Finset.univ :
        Finset (Fin (2 ^ ((15 + 1) * modulusBits N)))).filter
      fun bits =>
        RSA.decodeFixedWidthWords (modulusBits N) (15 + 1) bits 0 ∈
          goodResidueCandidates model).card =
      (goodResidueCandidates model).card *
        (2 ^ modulusBits N) ^ 15
  exact RSA.card_filter_decodeFixedWidthWords_first_mem
    (modulusBits N) 15 (goodResidueCandidates model)

/-- Every first-good packed sample selects the represented good unit. -/
theorem exists_goodUnit_of_mem_firstProposalGoodBits {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    {bits : Fin (2 ^ residueSamplingBits N)}
    (member : bits ∈ firstProposalGoodBits model) :
    ∃ unit ∈ model.goodEventUnits,
      RSA.prepareResidueFromBits N (modulusBits N)
          residueProposalCount bits = preparedUnit unit := by
  let input : Input N := Input.ofSemiprimeModel model
  have firstMember :
      RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount bits
          (0 : Fin (15 + 1)) ∈ goodResidueCandidates model := by
    simpa [firstProposalGoodBits] using (Finset.mem_filter.mp member).2
  rcases Finset.mem_image.mp firstMember with ⟨unit, good, indexEq⟩
  refine ⟨unit, good, ?_⟩
  unfold RSA.prepareResidueFromBits preparedUnit
  congr 1
  have firstEq :
      RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount bits
          (0 : Fin (15 + 1)) = sampledBaseIndex input unit :=
    indexEq.symm
  have eligible :
      RSA.ResidueEligible N
        (RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount bits
          (0 : Fin (15 + 1))).val := by
    rw [firstEq]
    exact sampledBaseIndex_eligible input unit
  have selected := RSA.firstValidResidue_classify_eq_first
    (wordCount := 15) (modulus := N)
    (proposals := RSA.decodeFixedWidthWords
      (modulusBits N) residueProposalCount bits) eligible
  rw [firstEq] at selected
  exact selected

/-- On the counted cylinder, the semantic runtime parameter is the fixed
unit parameter used by the Born proof. -/
theorem parameterValue_eq_unitParameter_of_goodBits {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    {bits : Fin (2 ^ residueSamplingBits N)}
    (member : bits ∈ firstProposalGoodBits model) :
    ∃ unit ∈ model.goodEventUnits,
      parameterValue (Input.ofSemiprimeModel model) bits =
        unitParameter (Input.ofSemiprimeModel model) unit := by
  let _ : NeZero N := (Input.ofSemiprimeModel model).neZero
  obtain ⟨unit, good, prepared⟩ :=
    exists_goodUnit_of_mem_firstProposalGoodBits model member
  refine ⟨unit, good, ?_⟩
  have unitEq := preparedUnit_unit_eq (Input.ofSemiprimeModel model) unit
  have factorEq :=
    preparedUnit_earlyFactor_eq_none (Input.ofSemiprimeModel model) unit
  simp [parameterValue, unitParameter, prepared, unitEq, factorEq,
    sampledBaseIndex, sampledBase]
  rfl

/-- An odd semiprime is at most four times its Euler totient. -/
theorem modulus_le_four_totient_of_not_even {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (odd : ¬ Even N) :
    N ≤ 4 * Nat.totient N := by
  obtain ⟨leftGt, rightGt⟩ := model.factors_gt_two_of_not_even odd
  have leftLe : model.leftFactor ≤ 2 * (model.leftFactor - 1) := by omega
  have rightLe : model.rightFactor ≤ 2 * (model.rightFactor - 1) := by omega
  have totientEq :
      Nat.totient N =
        (model.leftFactor - 1) * (model.rightFactor - 1) := by
    calc
      Nat.totient N = Nat.totient
          (model.leftFactor * model.rightFactor) :=
        congrArg Nat.totient model.product_eq
      _ = Nat.totient model.leftFactor * Nat.totient model.rightFactor :=
        Nat.totient_mul model.leftRight_coprime
      _ = (model.leftFactor - 1) * (model.rightFactor - 1) := by
        rw [Nat.totient_prime model.left_prime,
          Nat.totient_prime model.right_prime]
  calc
    N = model.leftFactor * model.rightFactor := model.product_eq
    _ ≤ (2 * (model.leftFactor - 1)) *
        (2 * (model.rightFactor - 1)) :=
      Nat.mul_le_mul leftLe rightLe
    _ = 4 * ((model.leftFactor - 1) *
        (model.rightFactor - 1)) := by ring
    _ = 4 * Nat.totient N := by rw [totientEq]

/-- The proposal-cardinality power of two is below twice the modulus. -/
theorem registerCard_lt_twice_modulus {N : Nat} (input : Input N) :
    2 ^ modulusBits N < 2 * N := by
  have predBound := Nat.pow_pred_clog_lt_self
    (b := 2) (by norm_num : 1 < 2) input.modulus_gt_one
  have widthPositive : 0 < Nat.clog 2 N := by
    simpa [modulusBits] using input.modulusBits_pos
  change 2 ^ Nat.clog 2 N < 2 * N
  calc
    2 ^ Nat.clog 2 N = 2 ^ ((Nat.clog 2 N).pred + 1) := by
      apply congrArg (fun exponent : Nat => 2 ^ exponent)
      simpa [Nat.succ_eq_add_one] using
        (Nat.succ_pred_eq_of_pos widthPositive).symm
    _ = 2 ^ (Nat.clog 2 N).pred * 2 := by rw [pow_succ]
    _ < N * 2 :=
      (Nat.mul_lt_mul_right (by norm_num : 0 < 2)).2 predBound
    _ = 2 * N := Nat.mul_comm _ _

/-- The counted good residues occupy at least one sixteenth of a word. -/
theorem registerCard_le_sixteen_mul_goodResidueCandidates_card {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (odd : ¬ Even N) :
    2 ^ modulusBits N ≤ 16 * (goodResidueCandidates model).card := by
  let input : Input N := Input.ofSemiprimeModel model
  obtain ⟨leftGt, _rightGt⟩ := model.factors_gt_two_of_not_even odd
  have goodBound : Nat.totient N ≤ 2 * model.goodEventUnits.card := by
    simpa [model.card_goodEventUnits_eq_crtGoodBaseCount] using
      model.crtGoodBaseCount_atLeastHalf leftGt
  have modulusBound : N ≤ 8 * model.goodEventUnits.card := by
    calc
      N ≤ 4 * Nat.totient N := modulus_le_four_totient_of_not_even model odd
      _ ≤ 4 * (2 * model.goodEventUnits.card) :=
        Nat.mul_le_mul_left 4 goodBound
      _ = 8 * model.goodEventUnits.card := by ring
  rw [goodResidueCandidates_card]
  have registerBound := registerCard_lt_twice_modulus input
  omega

/-- Cross-multiplied form of the complete sampler-cylinder lower bound. -/
theorem samplerCard_le_sixteen_mul_firstProposalGoodBits_card {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (odd : ¬ Even N) :
    2 ^ residueSamplingBits N ≤
      16 * (firstProposalGoodBits model).card := by
  rw [firstProposalGoodBits_card]
  have registerBound :=
    registerCard_le_sixteen_mul_goodResidueCandidates_card model odd
  have scaled :
      (2 ^ modulusBits N) * (2 ^ modulusBits N) ^ 15 ≤
        (16 * (goodResidueCandidates model).card) *
          (2 ^ modulusBits N) ^ 15 :=
    Nat.mul_le_mul_right ((2 ^ modulusBits N) ^ 15) registerBound
  calc
    2 ^ residueSamplingBits N =
        (2 ^ modulusBits N) * (2 ^ modulusBits N) ^ 15 := by
      rw [residueSamplingBits, residueProposalCount]
      calc
        2 ^ (16 * modulusBits N) = 2 ^ (modulusBits N * 16) := by
          rw [Nat.mul_comm]
        _ = (2 ^ modulusBits N) ^ 16 := pow_mul 2 (modulusBits N) 16
        _ = (2 ^ modulusBits N) ^ 15 * (2 ^ modulusBits N) := by
          rw [show 16 = 15 + 1 by norm_num, pow_succ]
        _ = (2 ^ modulusBits N) * (2 ^ modulusBits N) ^ 15 :=
          Nat.mul_comm _ _
    _ ≤ (16 * (goodResidueCandidates model).card) *
        (2 ^ modulusBits N) ^ 15 := scaled
    _ = 16 * ((goodResidueCandidates model).card *
        (2 ^ modulusBits N) ^ 15) := Nat.mul_assoc _ _ _

/-- Under the actual internal uniform sampler, the complete first-good
cylinder has probability at least one sixteenth. -/
theorem firstProposalGoodMass_ge_oneSixteenth {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (odd : ¬ Even N) :
    (1 : ENNReal) / 16 ≤
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).toOuterMeasure
        (firstProposalGoodBits model) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have cardEq :
      Fintype.card
          ↥(firstProposalGoodBits model :
            Set (Fin (2 ^ residueSamplingBits N))) =
        (firstProposalGoodBits model).card := by
    rw [← Set.toFinset_card]
    simp
  rw [cardEq, Fintype.card_fin]
  change
    (1 : ENNReal) / 16 ≤
      ((firstProposalGoodBits model).card : ENNReal) /
        ((2 ^ residueSamplingBits N : Nat) : ENNReal)
  refine (ENNReal.le_div_iff_mul_le (Or.inl ?_) (Or.inl ?_)).2 ?_
  · positivity
  · finiteness
  have countNat := samplerCard_le_sixteen_mul_firstProposalGoodBits_card
    model odd
  have count :
      ((2 ^ residueSamplingBits N : Nat) : ENNReal) ≤
        ((firstProposalGoodBits model).card : ENNReal) * 16 := by
    exact_mod_cast (by simpa [Nat.mul_comm] using countNat)
  have divided :
      ((2 ^ residueSamplingBits N : Nat) : ENNReal) / 16 ≤
        ((firstProposalGoodBits model).card : ENNReal) :=
    ENNReal.div_le_of_le_mul count
  simpa [div_eq_mul_inv, mul_comm] using divided

/-- One semantic sampled-family outcome is good when the internally retained
sample selects a counted good unit and the measurement lies in that unit's
source-certified recoverable-order event. -/
def GoodAttemptOutcome {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) :
    SourceOutcome N → Prop :=
  fun outcome =>
    ∃ unit, unit ∈ model.goodEventUnits ∧
      parameterValue (Input.ofSemiprimeModel model) outcome.sample =
        unitParameter (Input.ofSemiprimeModel model) unit ∧
      ShorSourceJoint.NativeRecoverableOutcome unit (orderOf unit)
        outcome.measurement

/-- The one-attempt source floor represented as an extended nonnegative real
[Sho95, source.tex:1183-1300]. -/
def honestAttemptSuccessFloor (N : Nat) : ENNReal :=
  ENNReal.ofReal ((1 : Real) / (sourceSuccessDenominator N : Real))

/-- The sampler/Born product is the rational reciprocal used by the retry
budget. -/
theorem honestAttemptSuccessFloor_eq_product {N : Nat} (input : Input N) :
    honestAttemptSuccessFloor N =
      ((1 : ENNReal) / 16) *
        ENNReal.ofReal ((1 : Real) / (3 * (modulusBits N : Real))) := by
  have bitsPositive : (0 : Real) < modulusBits N := by
    exact_mod_cast input.modulusBits_pos
  have oneSixteenth :
      (1 : ENNReal) / 16 = ENNReal.ofReal ((1 : Real) / 16) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [oneSixteenth, ← ENNReal.ofReal_mul
    (by positivity : (0 : Real) ≤ (1 : Real) / 16)]
  apply congrArg ENNReal.ofReal
  unfold sourceSuccessDenominator
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [ne_of_gt bitsPositive]
  norm_num

/-- The source sample/Born joint law reaches a good sample
and its matching recoverable Born outcome with the certified one-attempt
floor. -/
theorem honestAttemptSuccessFloor_le_goodOutcomeProbability {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (odd : ¬ Even N) :
    honestAttemptSuccessFloor N ≤
      (sourceOutcomePMF (Input.ofSemiprimeModel model)).toOuterMeasure
        {outcome | GoodAttemptOutcome model outcome} := by
  let input : Input N := Input.ofSemiprimeModel model
  let branchFloor : ENNReal :=
    ENNReal.ofReal ((1 : Real) / (3 * (modulusBits N : Real)))
  have branches : ∀ sample,
      ¬ sample ∉ firstProposalGoodBits model →
      branchFloor ≤
        ((sourceSampleOutcomePMF input sample).map
          (fun measurement =>
            ({ sample := sample, measurement := measurement } :
              SourceOutcome N))).toOuterMeasure
          {outcome | GoodAttemptOutcome model outcome} := by
    intro sample notOutside
    have member : sample ∈ firstProposalGoodBits model := by simpa using notOutside
    obtain ⟨unit, good, parameterEq⟩ :=
      parameterValue_eq_unitParameter_of_goodBits model member
    rw [PMF.toOuterMeasure_map_apply]
    refine (sampleOutcomePMF_recoverable_ge_bitlength model odd sample unit
      parameterEq).trans ?_
    apply PMF.toOuterMeasure_mono
    rintro measurement ⟨recoverable, _support⟩
    exact ⟨unit, good, parameterEq, recoverable⟩
  have combined := PMF.bind_eventProbability_ge_goodMass_mul
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N)))
    (fun sample =>
      (sourceSampleOutcomePMF input sample).map fun measurement =>
        ({ sample := sample, measurement := measurement } :
          SourceOutcome N))
    (fun sample => sample ∉ firstProposalGoodBits model)
    (GoodAttemptOutcome model) branchFloor branches
  rw [honestAttemptSuccessFloor_eq_product input]
  refine (mul_le_mul_left
    (by simpa using firstProposalGoodMass_ge_oneSixteenth model odd)
    branchFloor).trans ?_
  simpa [sourceOutcomePMF, input, branchFloor] using combined

/-- The fixed source joint law amplifies through mathematical independent repetition. -/
private theorem sourceRepeat_containsEvent_probability_ge {N : Nat}
    (input : Input N) (event : SourceOutcome N → Prop)
    (count : Nat) (attemptFloor target : ENNReal)
    (attemptBound : attemptFloor ≤
      (sourceOutcomePMF input).toOuterMeasure {outcome | event outcome})
    (targetBound : target ≤ 1 - (1 - attemptFloor) ^ count) :
    target ≤ (PMF.independentReplicateVector (sourceOutcomePMF input) count).toOuterMeasure
      {samples | PMF.ContainsEvent event samples.toList} := by
  have amplified := PMF.independentReplicate_successProbability_ge
    (sourceOutcomePMF input) event count attemptFloor target attemptBound targetBound
  calc
    target ≤ (PMF.independentReplicate (sourceOutcomePMF input) count).toOuterMeasure
        {samples | PMF.ContainsEvent event samples} := amplified
    _ = ((PMF.independentReplicateVector (sourceOutcomePMF input) count).map
          List.Vector.toList).toOuterMeasure
        {samples | PMF.ContainsEvent event samples} := by
      rw [PMF.independentReplicateVector_toList]
    _ = (PMF.independentReplicateVector (sourceOutcomePMF input) count).toOuterMeasure
        {samples | PMF.ContainsEvent event samples.toList} := by
      rw [PMF.toOuterMeasure_map_apply]
      congr 1

/-- Real value of the rational complement used by the retry calculation. -/
theorem sourceFailureBudget_value {N : Nat} (input : Input N) :
    (sourceFailureBudget N).value =
      1 - (1 : Real) / (sourceSuccessDenominator N : Real) := by
  have oneLe : 1 ≤ sourceSuccessDenominator N := by
    have positive : 0 < sourceSuccessDenominator N := by
      unfold sourceSuccessDenominator
      exact Nat.mul_pos (by norm_num) input.modulusBits_pos
    omega
  have denominatorNe : (sourceSuccessDenominator N : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (Nat.lt_of_lt_of_le Nat.zero_lt_one oneLe)
  unfold sourceFailureBudget FailureBudget.value
  rw [Nat.cast_sub oneLe]
  norm_num only [Nat.cast_one]
  field_simp [denominatorNe]

/-- The ENNReal complement of the source floor is the retry failure base. -/
theorem one_sub_attemptFloor_eq_sourceFailure {N : Nat} (input : Input N) :
    1 - honestAttemptSuccessFloor N =
      ENNReal.ofReal (sourceFailureBudget N).value := by
  rw [sourceFailureBudget_value input]
  unfold honestAttemptSuccessFloor
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by positivity :
      (0 : Real) ≤ (1 : Real) / (sourceSuccessDenominator N : Real))]

/-- A concrete polynomial upper bound for the internally calibrated count. -/
def retryPolynomialBound (N : Nat) (budget : FailureBudget) : Nat :=
  max 1
    (sourceSuccessDenominator N *
      max (Nat.size budget.failureDenominator) 2)

private theorem one_div_sourceSuccessDenominator_le_logRatio
    {N : Nat} (input : Input N) :
    (1 : Real) / sourceSuccessDenominator N ≤
      Real.log
        (((sourceFailureBudget N).failureDenominator : Real) /
          (sourceFailureBudget N).failureNumerator) := by
  let denominator := sourceSuccessDenominator N
  have denominatorGtOne : 1 < denominator := by
    dsimp [denominator, sourceSuccessDenominator]
    have := input.modulusBits_pos
    omega
  have denominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.zero_lt_of_lt denominatorGtOne
  have predecessorPos : (0 : Real) < (denominator - 1 : Nat) := by
    exact_mod_cast Nat.sub_pos_of_lt denominatorGtOne
  change (1 : Real) / denominator ≤
    Real.log ((denominator : Real) / ((denominator - 1 : Nat) : Real))
  calc
    (1 : Real) / denominator =
        1 - ((denominator : Real) /
          ((denominator - 1 : Nat) : Real))⁻¹ := by
      rw [inv_div, Nat.cast_sub (Nat.one_le_of_lt denominatorGtOne)]
      field_simp [denominatorPos.ne']
      ring
    _ ≤ Real.log ((denominator : Real) /
        ((denominator - 1 : Nat) : Real)) :=
      Real.one_sub_inv_le_log_of_pos
        (div_pos denominatorPos predecessorPos)

private theorem retryExponentFor_le_sourceDenominator_mul_size
    {N : Nat} (input : Input N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    FailureBudget.retryExponentFor (sourceFailureBudget N) budget ≤
      (sourceSuccessDenominator N *
        Nat.size budget.failureDenominator : Nat) := by
  have sourceLogPos :
      0 < Real.log
        (((sourceFailureBudget N).failureDenominator : Real) /
          (sourceFailureBudget N).failureNumerator) := by
    have sourceWellFormed := sourceFailureBudget_strictlyWellFormed input
    have numeratorPos :
        (0 : Real) < (sourceFailureBudget N).failureNumerator := by
      exact_mod_cast sourceWellFormed.numerator_pos
    have numeratorLtDenominator :
        ((sourceFailureBudget N).failureNumerator : Real) <
          (sourceFailureBudget N).failureDenominator := by
      exact_mod_cast sourceWellFormed.numerator_lt_denominator
    exact Real.log_pos
      ((one_lt_div numeratorPos).2 numeratorLtDenominator)
  rw [FailureBudget.retryExponentFor, div_le_iff₀ sourceLogPos]
  calc
    Real.log
        ((budget.failureDenominator : Real) /
          budget.failureNumerator) ≤
        (Nat.size budget.failureDenominator : Real) :=
      FailureBudget.retryLogRatio_le_denominatorSize budget wellFormed
    _ =
        (sourceSuccessDenominator N *
          Nat.size budget.failureDenominator : Nat) *
          ((1 : Real) / sourceSuccessDenominator N) := by
      push_cast
      have denominatorNe : (sourceSuccessDenominator N : Real) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt
          (Nat.mul_pos (by norm_num) input.modulusBits_pos)
      field_simp [denominatorNe]
    _ ≤
        (sourceSuccessDenominator N *
          Nat.size budget.failureDenominator : Nat) *
          Real.log
            (((sourceFailureBudget N).failureDenominator : Real) /
              (sourceFailureBudget N).failureNumerator) :=
      mul_le_mul_of_nonneg_left
        (one_div_sourceSuccessDenominator_le_logRatio input)
        (by positivity)

/-- The exact retry count is polynomial in the modulus width and encoded
failure-budget denominator. -/
theorem retryCount_le_retryPolynomialBound {N : Nat} (input : Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    retryCount N budget ≤ retryPolynomialBound N budget := by
  let commonBound :=
    sourceSuccessDenominator N *
      max (Nat.size budget.failureDenominator) 2
  have commonPositive : 1 ≤ commonBound := by
    dsimp [commonBound]
    have denominatorPositive : 0 < sourceSuccessDenominator N := by
      unfold sourceSuccessDenominator
      exact Nat.mul_pos (by norm_num) input.modulusBits_pos
    have maxPositive :
        0 < max (Nat.size budget.failureDenominator) 2 :=
      lt_of_lt_of_le (by norm_num) (Nat.le_max_right _ _)
    have productPositive : 0 < commonBound :=
      Nat.mul_pos denominatorPositive maxPositive
    omega
  have budgetExponent :
      FailureBudget.retryExponentFor (sourceFailureBudget N) budget ≤
        (commonBound : Real) := by
    refine (retryExponentFor_le_sourceDenominator_mul_size
      input budget wellFormed).trans ?_
    exact_mod_cast Nat.mul_le_mul_left
      (sourceSuccessDenominator N)
      (Nat.le_max_left (Nat.size budget.failureDenominator) 2)
  unfold retryCount retryPolynomialBound
  exact (FailureBudget.retryCountFor_le_of_one_le_of_exponent_le
    (sourceFailureBudget N) budget commonPositive budgetExponent).trans
      (Nat.le_max_right 1 commonBound)

/-- The exact internally calibrated retry count has a logarithmic public
resource bound in the requested failure probability. -/
theorem retryCount_cast_le_97_mul_modulusBits_mul_max_one_log_one_div_value
    {N : Nat} (input : Input N) (budget : FailureBudget)
    (hbudget : budget.WellFormed) :
    (retryCount N budget : Real) ≤
      97 * (modulusBits N : Real) *
        max 1 (Real.log (1 / budget.value)) := by
  let M : Real := max 1 (Real.log (1 / budget.value))
  have hbitsNat : 1 ≤ modulusBits N := by
    have hbitsPos := input.modulusBits_pos
    omega
  have hbitsOne : (1 : Real) ≤ (modulusBits N : Real) := by
    exact_mod_cast hbitsNat
  have hbitsNonneg : (0 : Real) ≤ (modulusBits N : Real) := by
    linarith
  have hMOne : (1 : Real) ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hMNonneg : (0 : Real) ≤ M := by
    linarith
  have hwidthMOne : (1 : Real) ≤ (modulusBits N : Real) * M := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ ≤ (modulusBits N : Real) * 1 :=
        mul_le_mul_of_nonneg_right hbitsOne (by norm_num)
      _ ≤ (modulusBits N : Real) * M :=
        mul_le_mul_of_nonneg_left hMOne hbitsNonneg
  have hwidthMNonneg :
      (0 : Real) ≤ (modulusBits N : Real) * M := by
    linarith
  let sourceLog : Real :=
    Real.log
      (((sourceFailureBudget N).failureDenominator : Real) /
        (sourceFailureBudget N).failureNumerator)
  have hsourceLogPos : 0 < sourceLog := by
    dsimp [sourceLog]
    have sourceWellFormed := sourceFailureBudget_strictlyWellFormed input
    have numeratorPos :
        (0 : Real) < (sourceFailureBudget N).failureNumerator := by
      exact_mod_cast sourceWellFormed.numerator_pos
    have numeratorLtDenominator :
        ((sourceFailureBudget N).failureNumerator : Real) <
          (sourceFailureBudget N).failureDenominator := by
      exact_mod_cast sourceWellFormed.numerator_lt_denominator
    exact Real.log_pos
      ((one_lt_div numeratorPos).2 numeratorLtDenominator)
  have hsourceDenomPosNat : 0 < sourceSuccessDenominator N := by
    unfold sourceSuccessDenominator
    exact Nat.mul_pos (by norm_num) input.modulusBits_pos
  have hsourceDenomPos :
      (0 : Real) < (sourceSuccessDenominator N : Real) := by
    exact_mod_cast hsourceDenomPosNat
  have hsourceScale :
      (1 : Real) ≤ (sourceSuccessDenominator N : Real) * sourceLog := by
    calc
      (1 : Real) =
          (sourceSuccessDenominator N : Real) *
            ((1 : Real) / sourceSuccessDenominator N) := by
        field_simp [hsourceDenomPos.ne']
      _ ≤ (sourceSuccessDenominator N : Real) * sourceLog := by
        simpa [sourceLog] using
          mul_le_mul_of_nonneg_left
            (one_div_sourceSuccessDenominator_le_logRatio input)
            hsourceDenomPos.le
  have hsourceDenomEq :
      (sourceSuccessDenominator N : Real) =
        48 * (modulusBits N : Real) := by
    norm_num [sourceSuccessDenominator]
  have hwidthMLogNonneg :
      (0 : Real) ≤ ((modulusBits N : Real) * M) * sourceLog :=
    mul_nonneg hwidthMNonneg hsourceLogPos.le
  have hbudgetNumNe : (budget.failureNumerator : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hbudget.numerator_pos
  have hbudgetDenNe : (budget.failureDenominator : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hbudget.denominator_pos
  have hvalueInv :
      (1 : Real) / budget.value =
        (budget.failureDenominator : Real) / budget.failureNumerator := by
    unfold FailureBudget.value
    field_simp [hbudgetNumNe, hbudgetDenNe]
  have hbudgetLogEq :
      Real.log
          ((budget.failureDenominator : Real) / budget.failureNumerator) =
        Real.log (1 / budget.value) := by
    rw [hvalueInv]
  have hbudgetLogLeM :
      Real.log
          ((budget.failureDenominator : Real) / budget.failureNumerator) ≤ M := by
    rw [hbudgetLogEq]
    dsimp [M]
    exact le_max_right _ _
  let B : Real := 96 * (modulusBits N : Real) * M
  have hBOne : (1 : Real) ≤ B := by
    calc
      (1 : Real) ≤ 96 * 1 := by norm_num
      _ ≤ 96 * ((modulusBits N : Real) * M) :=
        mul_le_mul_of_nonneg_left hwidthMOne (by norm_num)
      _ = B := by
        dsimp [B]
        ring
  have hBNonneg : (0 : Real) ≤ B := by
    linarith
  have hbudgetExponent :
      FailureBudget.retryExponentFor (sourceFailureBudget N) budget ≤ B := by
    rw [FailureBudget.retryExponentFor]
    change
      Real.log
          ((budget.failureDenominator : Real) / budget.failureNumerator) /
          sourceLog ≤ B
    rw [div_le_iff₀ hsourceLogPos]
    calc
      Real.log
          ((budget.failureDenominator : Real) / budget.failureNumerator) ≤ M :=
        hbudgetLogLeM
      _ ≤ M * ((sourceSuccessDenominator N : Real) * sourceLog) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hsourceScale hMNonneg
      _ = (48 * (modulusBits N : Real) * M) * sourceLog := by
        rw [hsourceDenomEq]
        ring
      _ = 48 * ((modulusBits N : Real) * M * sourceLog) := by
        ring
      _ ≤ 96 * ((modulusBits N : Real) * M * sourceLog) :=
        mul_le_mul_of_nonneg_right (by norm_num) hwidthMLogNonneg
      _ = B * sourceLog := by
        dsimp [B]
        ring
  have hceilBOne : 1 ≤ Nat.ceil B := by
    have hcast : (1 : Real) ≤ (Nat.ceil B : Real) :=
      hBOne.trans (Nat.le_ceil B)
    exact_mod_cast hcast
  have hbudgetCount :
      FailureBudget.retryCountFor (sourceFailureBudget N) budget ≤ Nat.ceil B :=
    FailureBudget.retryCountFor_le_of_one_le_of_exponent_le
      (sourceFailureBudget N) budget hceilBOne
      (hbudgetExponent.trans (Nat.le_ceil B))
  have hretryNat : retryCount N budget ≤ Nat.ceil B := by
    unfold retryCount
    exact hbudgetCount
  have hretryReal :
      (retryCount N budget : Real) ≤ (Nat.ceil B : Real) := by
    exact_mod_cast hretryNat
  have hfinal :
      (retryCount N budget : Real) ≤
        97 * (modulusBits N : Real) * M := by
    apply le_of_lt
    calc
      (retryCount N budget : Real) ≤ (Nat.ceil B : Real) := hretryReal
      _ < B + 1 := Nat.ceil_lt_add_one hBNonneg
      _ = 96 * ((modulusBits N : Real) * M) + 1 := by
        dsimp [B]
        ring
      _ ≤ 97 * ((modulusBits N : Real) * M) := by
        nlinarith
      _ = 97 * (modulusBits N : Real) * M := by
        ring
  simpa [M] using hfinal

/-- The selected retry count meets the caller's failure target. -/
theorem retryFailurePower_le_target {N : Nat} (input : Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    (ENNReal.ofReal (sourceFailureBudget N).value) ^ retryCount N budget ≤
      ENNReal.ofReal budget.value := by
  apply FailureBudget.retryFailurePowerFor_le_of_count
    (sourceFailureBudget N) budget
    (sourceFailureBudget_strictlyWellFormed input) wellFormed
  unfold retryCount
  exact le_rfl

theorem successThreshold_le_one_sub_retryFailurePower {N : Nat}
    (input : Input N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    FailureBudget.successThreshold budget ≤
      1 - (ENNReal.ofReal (sourceFailureBudget N).value) ^
        retryCount N budget := by
  rw [FailureBudget.successThreshold,
    ENNReal.ofReal_sub _ (FailureBudget.value_nonneg budget wellFormed),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left
    (retryFailurePower_le_target input budget wellFormed) 1

/-- At the caller-calibrated count, the independent source Shor transcript
contains a good sample/recoverable-measurement pair at the requested success
threshold. -/
theorem repeatDistribution_goodOutcome_probability_ge {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (odd : ¬ Even N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    FailureBudget.successThreshold budget ≤
      (PMF.independentReplicateVector (sourceOutcomePMF (Input.ofSemiprimeModel model))
          (retryCount N budget)).toOuterMeasure
        {samples | PMF.ContainsEvent (GoodAttemptOutcome model) samples.toList} := by
  apply sourceRepeat_containsEvent_probability_ge
    (Input.ofSemiprimeModel model) (GoodAttemptOutcome model)
    (retryCount N budget) (honestAttemptSuccessFloor N)
  · exact honestAttemptSuccessFloor_le_goodOutcomeProbability model odd
  · rw [one_sub_attemptFloor_eq_sourceFailure
      (Input.ofSemiprimeModel model)]
    exact successThreshold_le_one_sub_retryFailurePower
      (Input.ofSemiprimeModel model) budget wellFormed

/-- Total source-transcript event for factor recovery. Even semiprimes use the
public-data shortcut; odd semiprimes require a source-certified good-unit/Born
pair. This distinction retains the original exceptional branch. -/
def SuccessfulSamples {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget)
    (samples : List.Vector
      (SourceOutcome N) (retryCount N budget)) : Prop :=
  if Even N then True
  else PMF.ContainsEvent (GoodAttemptOutcome model) samples.toList

/-- Independent source repetition reaches the recovery event at the requested target. -/
theorem repeatDistribution_successfulSamples_probability_ge {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    FailureBudget.successThreshold budget ≤
      (PMF.independentReplicateVector (sourceOutcomePMF (Input.ofSemiprimeModel model))
          (retryCount N budget)).toOuterMeasure
        {samples | SuccessfulSamples model budget samples} := by
  by_cases even : Even N
  · have thresholdLeOne : FailureBudget.successThreshold budget ≤ 1 := by
      unfold FailureBudget.successThreshold
      apply ENNReal.ofReal_le_one.mpr
      have nonnegative := FailureBudget.value_nonneg budget wellFormed
      linarith
    calc
      FailureBudget.successThreshold budget ≤ 1 := thresholdLeOne
      _ = (PMF.independentReplicateVector (sourceOutcomePMF (Input.ofSemiprimeModel model))
            (retryCount N budget)).toOuterMeasure Set.univ := by
        rw [PMF.toOuterMeasure_apply]
        simp
      _ = (PMF.independentReplicateVector (sourceOutcomePMF (Input.ofSemiprimeModel model))
            (retryCount N budget)).toOuterMeasure
          {samples | SuccessfulSamples model budget samples} := by
        congr 1
        ext samples
        simp [SuccessfulSamples, even]
  · simpa [SuccessfulSamples, even] using
      repeatDistribution_goodOutcome_probability_ge model even budget wellFormed

end

end Probability
end Canonical
end ShorStyle
end Factoring
end QuantumAlg

end
