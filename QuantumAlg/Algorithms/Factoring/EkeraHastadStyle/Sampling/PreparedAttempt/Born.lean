/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.PreparedAttempt
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Core.Algorithm.Probability.Minorization
import all QuantumAlg.Primitives.ShortDLP.BornProbability
import all QuantumAlg.Util.BinomialTail
import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Canonical Ekerå–Håstad fixed-sample Born minorization

The compiled member selected by one retained parameter has the original
short-DLP Born law. Its prepared residue, terminal PMF, pair embedding and
proof-side fractional mark use that same source sample. These mathematical
probabilities are the conditional law proved for the actual native batch.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical

noncomputable section

/-- Clean two-word unit encoding for the public canonical modulus input. -/
def compiledUnitEncoding {N : Nat} (input : Input N) :
    ShortDLP.UnitEncoding N (registerParameters N).workspaceBits where
  encode :=
    (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N
      input.modulus_gt_one (modulus_lt_arithmeticCapacity N)).encode
  encode_injective :=
    (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N
      input.modulus_gt_one (modulus_lt_arithmeticCapacity N)).encode_injective

/-- The canonical wrapper has exactly the raw compiled two-word encoding. -/
theorem compiledUnitEncoding_eq_raw {N : Nat} (input : Input N) :
    compiledUnitEncoding input =
      ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N
        input.modulus_gt_one (modulus_lt_arithmeticCapacity N) := by
  let raw := ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N
    input.modulus_gt_one (modulus_lt_arithmeticCapacity N)
  change
    ({ encode := raw.encode
       encode_injective := raw.encode_injective } :
        ShortDLP.UnitEncoding N
          (ShortDLP.CompiledMAU.workspaceBits (arithmeticBits N))) = raw
  cases raw
  rfl

/-- Attaching one fixed prepared residue preserves terminal-outcome equality. -/
theorem preparedSampleOfMeasurement_injective {N : Nat}
    (sample : Fin (2 ^ residueSamplingBits N)) :
    Function.Injective (preparedSampleOfMeasurement sample) := by
  intro left right h
  have hbits := congrArg (fun output : PreparedBatchSample N =>
    output.terminalBits) h
  simpa only [preparedSampleOfMeasurement, terminalBitsOfOutcome,
    measurementBits, ShortDLP.firstBits] using hbits

/-- Embed one source exponent-register pair into the terminal result of the
actual member selected by one raw sampler value. -/
def samplePairEmbedding (N : Nat)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    (Fin (2 ^ ShortDLP.firstBits (registerParameters N)) ×
      Fin (2 ^ (registerParameters N).ell)) ↪ PreparedBatchSample N where
  toFun := fun pair =>
    preparedSampleOfMeasurement sample
      (ShortDLP.BornProbability.shortDLPMeasurementOutcome
        (registerParameters N) (prodEquiv pair))
  inj' := by
    intro left right h
    apply prodEquiv.injective
    apply ShortDLP.BornProbability.shortDLPMeasurementOutcome_injective
      (registerParameters N)
    exact preparedSampleOfMeasurement_injective sample h

/-- Embed one exact-good first-register index through its principal pair into
the terminal result of the same selected member. -/
def sampleGoodFirstEmbedding (N secret : Nat)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    Fin (2 ^ ShortDLP.firstBits (registerParameters N)) ↪
      PreparedBatchSample N :=
  (ShortDLP.BornProbability.principalGoodPairEmbedding
    (registerParameters N) secret).trans (samplePairEmbedding N sample)

/-- The selected compiled-member Born law at one pair is the original workspace marginal. -/
theorem selectedOutcomePMF_pair_apply {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (pair : Fin (2 ^ ShortDLP.firstBits (registerParameters N)) ×
      Fin (2 ^ (registerParameters N).ell)) :
    selectedOutcomePMF (parameterValue input sample)
        (ShortDLP.BornProbability.shortDLPMeasurementOutcome
          (registerParameters N) (prodEquiv pair)) =
      ShortDLP.BornProbability.pairBornProbability
        (compiledUnitEncoding input) (preparedResidue sample).unit
        (RSA.targetUnit (preparedResidue sample).unit) pair := by
  unfold selectedOutcomePMF
  rw [parameterUnit_parameterValue, parameterTarget_parameterValue]
  rw [ShortDLP.CompiledMAU.outcomePMF_eq_ideal
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (preparedResidue sample).unit (RSA.targetUnit (preparedResidue sample).unit)
    input.modulus_gt_one (modulus_lt_arithmeticCapacity N)]
  rw [compiledUnitEncoding_eq_raw input]
  exact ShortDLP.BornProbability.shortDLPBornOutcomeProbability_eq_pairBornProbability
    (params := registerParameters N)
    (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N
      input.modulus_gt_one (modulus_lt_arithmeticCapacity N))
    (preparedResidue sample).unit (RSA.targetUnit (preparedResidue sample).unit) pair

/-- The fixed-sample prepared-output PMF has the same point mass at the
embedded pair as the actual selected member's terminal PMF. -/
theorem fixedPreparedSamplePMF_samplePairEmbedding_apply {N : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (pair : Fin (2 ^ ShortDLP.firstBits (registerParameters N)) ×
      Fin (2 ^ (registerParameters N).ell)) :
    fixedPreparedSamplePMF input sample (samplePairEmbedding N sample pair) =
      ShortDLP.BornProbability.pairBornProbability
        (compiledUnitEncoding input) (preparedResidue sample).unit
        (RSA.targetUnit (preparedResidue sample).unit) pair := by
  classical
  change
    ((selectedOutcomePMF (parameterValue input sample)).map
        (preparedSampleOfMeasurement sample))
      (preparedSampleOfMeasurement sample
        (ShortDLP.BornProbability.shortDLPMeasurementOutcome
          (registerParameters N) (prodEquiv pair))) =
      _
  rw [PMF.map_apply_of_injective (selectedOutcomePMF (parameterValue input sample))
    (preparedSampleOfMeasurement sample)
    (preparedSampleOfMeasurement_injective sample)]
  exact selectedOutcomePMF_pair_apply input sample pair

/-- The exact source-sized narrow-good core embedded in one selected prepared
terminal output. -/
noncomputable def exactNarrowGoodSampleCore (N secret : Nat)
    (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m) :
    Finset (PreparedBatchSample N) :=
  (ShortDLP.BornProbability.exactNarrowGoodFirstIndices
    secret hm hsecretPos hsecretLt).map
      (sampleGoodFirstEmbedding N secret sample)

/-- The selected narrow-good core retains the exact source cardinality. -/
theorem exactNarrowGoodSampleCore_card (N secret : Nat)
    (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m) :
    (exactNarrowGoodSampleCore N secret sample hm hsecretPos hsecretLt).card =
      2 ^ (ShortDLP.firstBits (registerParameters N) - 1) := by
  rw [exactNarrowGoodSampleCore, Finset.card_map,
    ShortDLP.BornProbability.exactNarrowGoodFirstIndices_card]

/-- Common actual-PMF floor split from every selected narrow-good atom. -/
def exactNarrowGoodAtomFloor (N : Nat) : ENNReal :=
  ENNReal.ofReal
    (((2 : Real) ^ ((registerParameters N).m +
      (registerParameters N).ell + 2))⁻¹)

/-- Every atom in the selected core receives the source-derived Fourier floor
from the PMF of that same selected member. -/
theorem fixedPreparedSamplePMF_exactNarrowGoodSampleCore_apply_ge {N : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (secret : Nat) (hm : 2 ≤ (registerParameters N).m)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (horder : ShortDLP.oracleFiberSpan (registerParameters N) secret ≤
      orderOf (preparedResidue sample).unit)
    {outcome : PreparedBatchSample N}
    (houtcome : outcome ∈
      exactNarrowGoodSampleCore N secret sample hm hsecretPos hsecretLt) :
    exactNarrowGoodAtomFloor N ≤ fixedPreparedSamplePMF input sample outcome := by
  classical
  rw [exactNarrowGoodSampleCore, Finset.mem_map] at houtcome
  rcases houtcome with ⟨j, hj, rfl⟩
  let pair := ShortDLP.BornProbability.principalGoodPairEmbedding
    (registerParameters N) secret j
  have hpair : pair ∈ ShortDLP.BornProbability.exactNarrowGoodCore
      secret hm hsecretPos hsecretLt := by
    rw [ShortDLP.BornProbability.exactNarrowGoodCore, Finset.mem_map]
    exact ⟨j, hj, rfl⟩
  change exactNarrowGoodAtomFloor N ≤
    fixedPreparedSamplePMF input sample (samplePairEmbedding N sample pair)
  rw [fixedPreparedSamplePMF_samplePairEmbedding_apply]
  rw [ShortDLP.BornProbability.pairBornProbability_eq_ofReal_pairSourceWeight
    (compiledUnitEncoding input) (preparedResidue sample).unit
    (RSA.targetUnit (preparedResidue sample).unit) secret pair.1 pair.2
    htarget horder]
  exact ENNReal.ofReal_le_ofReal
    (ShortDLP.BornProbability.exactNarrowGoodCore_pairSourceWeight_ge
      secret hm hsecretPos hsecretLt hpair)

/-- Boolean-marked coupling for the fixed-sample actual PMF. -/
noncomputable def fixedPreparedSampleMinorization {N : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (secret : Nat) (hm : 2 ≤ (registerParameters N).m)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (horder : ShortDLP.oracleFiberSpan (registerParameters N) secret ≤
      orderOf (preparedResidue sample).unit) :
    PMF (PreparedBatchSample N × Bool) := by
  classical
  exact PMF.fractionalMarking (fixedPreparedSamplePMF input sample)
    (exactNarrowGoodSampleCore N secret sample hm hsecretPos hsecretLt)
    (exactNarrowGoodAtomFloor N)
    (fun outcome houtcome =>
      fixedPreparedSamplePMF_exactNarrowGoodSampleCore_apply_ge
        input sample secret hm hsecretPos hsecretLt htarget horder houtcome)

/-- Forgetting the proof-side mark recovers the exact selected-member PMF. -/
theorem fixedPreparedSampleMinorization_map_fst {N : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (secret : Nat) (hm : 2 ≤ (registerParameters N).m)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (horder : ShortDLP.oracleFiberSpan (registerParameters N) secret ≤
      orderOf (preparedResidue sample).unit) :
    (fixedPreparedSampleMinorization input sample secret hm hsecretPos
      hsecretLt htarget horder).map Prod.fst =
        fixedPreparedSamplePMF input sample := by
  classical
  exact PMF.fractionalMarking_map_fst (fixedPreparedSamplePMF input sample)
    (exactNarrowGoodSampleCore N secret sample hm hsecretPos hsecretLt)
    (exactNarrowGoodAtomFloor N)
    (fun outcome houtcome =>
      fixedPreparedSamplePMF_exactNarrowGoodSampleCore_apply_ge
        input sample secret hm hsecretPos hsecretLt htarget horder houtcome)

/-- The literal source floor marks exactly one eighth of the fixed-sample
actual PMF. -/
theorem fixedPreparedSampleMinorization_markedMass {N : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (secret : Nat) (hm : 2 ≤ (registerParameters N).m)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (horder : ShortDLP.oracleFiberSpan (registerParameters N) secret ≤
      orderOf (preparedResidue sample).unit) :
    (fixedPreparedSampleMinorization input sample secret hm hsecretPos
      hsecretLt htarget horder).toOuterMeasure {outcome | outcome.2} =
        ENNReal.ofReal (1 / 8 : Real) := by
  classical
  rw [fixedPreparedSampleMinorization,
    PMF.fractionalMarking_markedMass,
    exactNarrowGoodSampleCore_card]
  unfold exactNarrowGoodAtomFloor ShortDLP.firstBits
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity :
      0 ≤ (((2 ^ ((registerParameters N).ell +
        (registerParameters N).m - 1) : Nat) : Real)))]
  apply congrArg ENNReal.ofReal
  norm_cast
  have hexponent :
      (registerParameters N).m + (registerParameters N).ell + 2 =
        ((registerParameters N).ell + (registerParameters N).m - 1) + 3 := by
    omega
  rw [hexponent, pow_add]
  field_simp
  norm_num

/-- Decode the two short-DLP registers from one actual fixed-sample terminal
outcome through the batch's canonical terminal-bit decoder. -/
def fixedPreparedDecodedSample (N : Nat) (outcome : PreparedBatchSample N) :
    RSA.ShortLogSample (registerParameters N).m (registerParameters N).ell :=
  BatchRecovery.decodeTerminalSample (registerParameters N).m
    (registerParameters N).ell outcome.terminalBits

/-- The first measured exponent-register index carried by an actual prepared
batch sample. -/
def fixedPreparedFirstRegisterIndex (N : Nat) (outcome : PreparedBatchSample N) :
    Fin (2 ^ ((registerParameters N).ell + (registerParameters N).m)) :=
  (fixedPreparedDecodedSample N outcome).1

/-- Decoding an embedded source pair recovers that pair through the same
terminal-bit representation used by the fixed batch. -/
@[simp] theorem fixedPreparedDecodedSample_samplePairEmbedding
    (N : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (pair : Fin (2 ^ ShortDLP.firstBits (registerParameters N)) ×
      Fin (2 ^ (registerParameters N).ell)) :
    fixedPreparedDecodedSample N (samplePairEmbedding N sample pair) = pair := by
  change ShortDLP.decodeOutcome (registerParameters N)
    (ShortDLP.BornProbability.shortDLPMeasurementOutcome
      (registerParameters N) (prodEquiv pair)) = pair
  simp only [ShortDLP.BornProbability.decodeOutcome_shortDLPMeasurementOutcome,
    Equiv.symm_apply_apply]

/-- The selected exact-good embedding preserves its source first-register
index after the canonical fixed-batch decoder. -/
@[simp] theorem fixedPreparedFirstRegisterIndex_sampleGoodFirstEmbedding
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (j : Fin (2 ^ ShortDLP.firstBits (registerParameters N))) :
    fixedPreparedFirstRegisterIndex N
        (sampleGoodFirstEmbedding N secret sample j) = j := by
  change fixedPreparedFirstRegisterIndex N
      (samplePairEmbedding N sample
        (ShortDLP.BornProbability.principalGoodPairEmbedding
          (registerParameters N) secret j)) = j
  unfold fixedPreparedFirstRegisterIndex
  rw [fixedPreparedDecodedSample_samplePairEmbedding]
  rfl

/-- An actual prepared sample is source-narrow-good and retains the exact
prepared residue selected by the same raw sampler value. -/
def FixedPreparedNarrowGoodSample (N secret : Nat)
    (sample : Fin (2 ^ residueSamplingBits N))
    (outcome : PreparedBatchSample N) : Prop :=
  outcome.prepared = preparedResidue sample ∧
    ShortDLP.BornProbability.NarrowGoodPair (registerParameters N) secret
      (fixedPreparedDecodedSample N outcome)

/-- Every atom of the fixed selected core is an actual narrow-good terminal
sample tagged with its own selected prepared residue. -/
theorem exactNarrowGoodSampleCore_mem_fixedPreparedNarrowGoodSample
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    {outcome : PreparedBatchSample N}
    (houtcome : outcome ∈ exactNarrowGoodSampleCore N secret sample hm
      hsecretPos hsecretLt) :
    FixedPreparedNarrowGoodSample N secret sample outcome := by
  classical
  rw [exactNarrowGoodSampleCore, Finset.mem_map] at houtcome
  rcases houtcome with ⟨j, hj, rfl⟩
  constructor
  · rfl
  · have hpair :
        ShortDLP.BornProbability.principalGoodPairEmbedding
            (registerParameters N) secret j ∈
          ShortDLP.BornProbability.exactNarrowGoodCore secret hm
            hsecretPos hsecretLt := by
      rw [ShortDLP.BornProbability.exactNarrowGoodCore, Finset.mem_map]
      exact ⟨j, hj, rfl⟩
    have hgood :=
      ShortDLP.BornProbability.exactNarrowGoodCore_mem_narrowGoodPairs
        secret hm hsecretPos hsecretLt hpair
    change ShortDLP.BornProbability.NarrowGoodPair
      (registerParameters N) secret
        (fixedPreparedDecodedSample N
          (samplePairEmbedding N sample
            (ShortDLP.BornProbability.principalGoodPairEmbedding
              (registerParameters N) secret j)))
    rw [fixedPreparedDecodedSample_samplePairEmbedding]
    exact (Finset.mem_filter.mp hgood).2

/-- The finite obstruction event on two actual prepared batch samples. -/
def fixedPreparedTinyMultiplierObstructionPair (N : Nat)
    (pair : PreparedBatchSample N × PreparedBatchSample N) : Prop :=
  RSA.ShortLogTinyMultiplierObstruction (registerParameters N).m
    (registerParameters N).ell
    (fixedPreparedFirstRegisterIndex N pair.1,
      fixedPreparedFirstRegisterIndex N pair.2)

/-- Obstructed ordered first-register pairs inside the exact selected core. -/
noncomputable def exactNarrowGoodSampleObstructionIndexPairs
    (N secret : Nat)
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m) :
    Finset (Fin (2 ^ ShortDLP.firstBits (registerParameters N)) ×
      Fin (2 ^ ShortDLP.firstBits (registerParameters N))) := by
  classical
  let selected := ShortDLP.BornProbability.exactNarrowGoodFirstIndices
    secret hm hsecretPos hsecretLt
  exact (selected ×ˢ selected).filter fun indices =>
    RSA.ShortLogTinyMultiplierObstruction (registerParameters N).m
      (registerParameters N).ell indices

/-- The exact finite obstruction carrier embedded into two actual outputs of
one fixed selected member. -/
noncomputable def exactNarrowGoodSampleObstructionPairs
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m) :
    Finset (PreparedBatchSample N × PreparedBatchSample N) :=
  (exactNarrowGoodSampleObstructionIndexPairs N secret hm hsecretPos
    hsecretLt).map
      ((sampleGoodFirstEmbedding N secret sample).prodMap
        (sampleGoodFirstEmbedding N secret sample))

/-- The fixed selected obstruction carrier injects into the global pure-RSA
first-index obstruction carrier. -/
theorem exactNarrowGoodSampleObstructionPairs_card_le
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m) :
    (exactNarrowGoodSampleObstructionPairs N secret sample hm
      hsecretPos hsecretLt).card ≤
      (RSA.shortLogTinyMultiplierObstructionPairs
        (registerParameters N).m (registerParameters N).ell).card := by
  classical
  rw [exactNarrowGoodSampleObstructionPairs, Finset.card_map]
  apply Finset.card_le_card
  intro indices hindices
  rw [exactNarrowGoodSampleObstructionIndexPairs, Finset.mem_filter] at hindices
  exact RSA.mem_shortLogTinyMultiplierObstructionPairs_iff.mpr hindices.2

/-- Every pair in the fixed selected obstruction carrier has both coordinates
inside the same selected exact-good core. -/
theorem exactNarrowGoodSampleObstructionPairs_mem_core
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    {pair : PreparedBatchSample N × PreparedBatchSample N}
    (hpair : pair ∈ exactNarrowGoodSampleObstructionPairs N secret sample hm
      hsecretPos hsecretLt) :
    pair.1 ∈ exactNarrowGoodSampleCore N secret sample hm
        hsecretPos hsecretLt ∧
      pair.2 ∈ exactNarrowGoodSampleCore N secret sample hm
        hsecretPos hsecretLt := by
  classical
  rw [exactNarrowGoodSampleObstructionPairs, Finset.mem_map] at hpair
  rcases hpair with ⟨indices, hindices, rfl⟩
  rw [exactNarrowGoodSampleObstructionIndexPairs, Finset.mem_filter] at hindices
  have hselected := Finset.mem_product.mp hindices.1
  constructor
  · rw [exactNarrowGoodSampleCore, Finset.mem_map]
    exact ⟨indices.1, hselected.1, rfl⟩
  · rw [exactNarrowGoodSampleCore, Finset.mem_map]
    exact ⟨indices.2, hselected.2, rfl⟩

/-- Two selected core atoms enter the finite obstruction carrier whenever
their decoded first indices form a tiny-multiplier obstruction. -/
theorem exactNarrowGoodSampleObstructionPairs_mem_of_core_of_obstruction
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    {pair : PreparedBatchSample N × PreparedBatchSample N}
    (hfirst : pair.1 ∈ exactNarrowGoodSampleCore N secret sample hm
      hsecretPos hsecretLt)
    (hsecond : pair.2 ∈ exactNarrowGoodSampleCore N secret sample hm
      hsecretPos hsecretLt)
    (hobstruction : fixedPreparedTinyMultiplierObstructionPair N pair) :
    pair ∈ exactNarrowGoodSampleObstructionPairs N secret sample hm
      hsecretPos hsecretLt := by
  classical
  rcases pair with ⟨first, second⟩
  rw [exactNarrowGoodSampleCore, Finset.mem_map] at hfirst hsecond
  rcases hfirst with ⟨firstIndex, hfirstIndex, hfirst⟩
  rcases hsecond with ⟨secondIndex, hsecondIndex, hsecond⟩
  change (sampleGoodFirstEmbedding N secret sample) firstIndex = first at hfirst
  change (sampleGoodFirstEmbedding N secret sample) secondIndex = second at hsecond
  subst first
  subst second
  rw [exactNarrowGoodSampleObstructionPairs, Finset.mem_map]
  refine ⟨(firstIndex, secondIndex), ?_, rfl⟩
  rw [exactNarrowGoodSampleObstructionIndexPairs, Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨hfirstIndex, hsecondIndex⟩, ?_⟩
  unfold fixedPreparedTinyMultiplierObstructionPair at hobstruction
  rw [fixedPreparedFirstRegisterIndex_sampleGoodFirstEmbedding,
    fixedPreparedFirstRegisterIndex_sampleGoodFirstEmbedding] at hobstruction
  exact hobstruction

/-- The marked branch restricted to the actual fixed selected core has the
same literal one-eighth mass as the full mark event. -/
theorem fixedPreparedSampleMinorization_markedCoreMass {N : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (secret : Nat) (hm : 2 ≤ (registerParameters N).m)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (horder : ShortDLP.oracleFiberSpan (registerParameters N) secret ≤
      orderOf (preparedResidue sample).unit) :
    (fixedPreparedSampleMinorization input sample secret hm hsecretPos
      hsecretLt htarget horder).toOuterMeasure
        {outcome | outcome.2 ∧ outcome.1 ∈
          exactNarrowGoodSampleCore N secret sample hm hsecretPos hsecretLt} =
      ENNReal.ofReal (1 / 8 : Real) := by
  classical
  rw [fixedPreparedSampleMinorization,
    PMF.fractionalMarking_markedCoreMass]
  have hmarked := fixedPreparedSampleMinorization_markedMass
    input sample secret hm hsecretPos hsecretLt htarget horder
  rw [fixedPreparedSampleMinorization,
    PMF.fractionalMarking_markedMass] at hmarked
  exact hmarked

/-- Two independent marked draws hit the finite fixed-sample obstruction
carrier with probability at most `1/2048`.  The bound is the global pure-RSA
carrier count scaled by the literal selected-atom floor. -/
theorem fixedPreparedSampleMinorization_markedObstructionMass_le_oneOver2048
    {N : Nat} (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (secret : Nat) (hm : 3 ≤ (registerParameters N).m)
    (htradeoff : (registerParameters N).m ≤
      2 * (registerParameters N).ell)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (horder : ShortDLP.oracleFiberSpan (registerParameters N) secret ≤
      orderOf (preparedResidue sample).unit) :
    (PMF.independentPair
      (fixedPreparedSampleMinorization input sample secret (by omega)
        hsecretPos hsecretLt htarget horder)).toOuterMeasure
        (PMF.markedPairCarrier
          (exactNarrowGoodSampleObstructionPairs N secret sample (by omega)
            hsecretPos hsecretLt)) ≤
      ENNReal.ofReal (1 / 2048 : Real) := by
  classical
  let core := exactNarrowGoodSampleCore N secret sample (by omega)
    hsecretPos hsecretLt
  let bad := exactNarrowGoodSampleObstructionPairs N secret sample
    (by omega) hsecretPos hsecretLt
  let floor := exactNarrowGoodAtomFloor N
  have hfloor : ∀ outcome ∈ core,
      floor ≤ fixedPreparedSamplePMF input sample outcome := by
    intro outcome houtcome
    exact fixedPreparedSamplePMF_exactNarrowGoodSampleCore_apply_ge
      input sample secret (by omega) hsecretPos hsecretLt htarget horder houtcome
  have hbadCore : ∀ pair ∈ bad, pair.1 ∈ core ∧ pair.2 ∈ core := by
    intro pair hpair
    exact exactNarrowGoodSampleObstructionPairs_mem_core
      N secret sample (by omega) hsecretPos hsecretLt hpair
  have hmass :
      (PMF.independentPair
        (fixedPreparedSampleMinorization input sample secret (by omega)
          hsecretPos hsecretLt htarget horder)).toOuterMeasure
          (PMF.markedPairCarrier bad) =
        bad.card * floor ^ 2 := by
    change (PMF.independentPair
      (PMF.fractionalMarking (fixedPreparedSamplePMF input sample) core floor
        hfloor)).toOuterMeasure (PMF.markedPairCarrier bad) = _
    exact PMF.independentPair_fractionalMarking_markedBadMass
      (fixedPreparedSamplePMF input sample) core floor hfloor bad hbadCore
  rw [hmass]
  let badCard : Nat := bad.card
  let spaceCard : Nat := 2 ^ ((registerParameters N).ell +
    (registerParameters N).m)
  have hbadCard : badCard ≤
      (RSA.shortLogTinyMultiplierObstructionPairs
        (registerParameters N).m (registerParameters N).ell).card := by
    exact exactNarrowGoodSampleObstructionPairs_card_le
      N secret sample (by omega) hsecretPos hsecretLt
  have hcountNat : badCard * 128 ≤ spaceCard ^ 2 := by
    exact (Nat.mul_le_mul_right 128 hbadCard).trans
      (RSA.card_shortLogTinyMultiplierObstructionPairs_mul_128_le_square
        hm htradeoff)
  have hcount : (badCard : ENNReal) * 128 ≤
      (spaceCard : ENNReal) * (spaceCard : ENNReal) := by
    have hcountPow : (badCard : ENNReal) * 128 ≤
        (spaceCard : ENNReal) ^ 2 := by
      exact_mod_cast hcountNat
    simpa [pow_two] using hcountPow
  have hfloorEq : floor =
      (4 : ENNReal)⁻¹ * (spaceCard : ENNReal)⁻¹ := by
    dsimp [floor, exactNarrowGoodAtomFloor]
    rw [ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : Real) ≤ 2)]
    have hexponent :
        (registerParameters N).m + (registerParameters N).ell + 2 =
          2 + ((registerParameters N).ell + (registerParameters N).m) := by
      omega
    rw [hexponent, pow_add,
      ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
    norm_num [spaceCard]
  have hspaceZero : (spaceCard : ENNReal) ≠ 0 := by
    simp [spaceCard]
  have hspaceTop : (spaceCard : ENNReal) ≠ ⊤ := by finiteness
  change (badCard : ENNReal) * floor ^ 2 ≤ _
  rw [hfloorEq]
  rw [show ENNReal.ofReal (1 / 2048 : Real) = (2048 : ENNReal)⁻¹ by
    rw [show (1 / 2048 : Real) = (2048 : Real)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num]
  rw [ENNReal.le_inv_iff_mul_le]
  rw [pow_two, show (2048 : ENNReal) = 128 * 16 by norm_num]
  calc
    (badCard : ENNReal) *
          ((4 : ENNReal)⁻¹ * (spaceCard : ENNReal)⁻¹ *
            ((4 : ENNReal)⁻¹ * (spaceCard : ENNReal)⁻¹)) *
          (128 * 16) =
        ((badCard : ENNReal) * 128) *
          ((spaceCard : ENNReal)⁻¹ * (spaceCard : ENNReal)⁻¹) *
          (((4 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹) * 16) := by
      ac_rfl
    _ ≤ ((spaceCard : ENNReal) * (spaceCard : ENNReal)) *
          ((spaceCard : ENNReal)⁻¹ * (spaceCard : ENNReal)⁻¹) *
          (((4 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹) * 16) := by
      gcongr
    _ = 1 := by
      rw [show ((spaceCard : ENNReal) * (spaceCard : ENNReal)) *
          ((spaceCard : ENNReal)⁻¹ * (spaceCard : ENNReal)⁻¹) =
        ((spaceCard : ENNReal) * (spaceCard : ENNReal)⁻¹) *
          ((spaceCard : ENNReal) * (spaceCard : ENNReal)⁻¹) by ac_rfl,
        ENNReal.mul_inv_cancel hspaceZero hspaceTop]
      rw [show (16 : ENNReal) = 4 * 4 by norm_num,
        show (4 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹ * (4 * 4) =
          ((4 : ENNReal)⁻¹ * 4) * ((4 : ENNReal)⁻¹ * 4) by ac_rfl,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      norm_num

/-- Two actual prepared terminal samples are feasible when both are
narrow-good for the same fixed residue and their first indices avoid the
finite tiny-multiplier obstruction. -/
def FixedPreparedFeasibleNarrowGoodPair (N secret : Nat)
    (sample : Fin (2 ^ residueSamplingBits N))
    (pair : PreparedBatchSample N × PreparedBatchSample N) : Prop :=
  FixedPreparedNarrowGoodSample N secret sample pair.1 ∧
    FixedPreparedNarrowGoodSample N secret sample pair.2 ∧
    ¬ fixedPreparedTinyMultiplierObstructionPair N pair

/-- A marked fixed-sample transcript with two selected core atoms and no
marked obstruction pair projects to a transcript containing an actual
feasible narrow-good pair. -/
theorem hasFixedPreparedFeasibleNarrowGoodPair_map_fst_of_markedCore
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (hm : 2 ≤ (registerParameters N).m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (samples : List (PreparedBatchSample N × Bool))
    (htwo : PMF.AtLeastTwoEvents
      (fun outcome => outcome.2 ∧ outcome.1 ∈
        exactNarrowGoodSampleCore N secret sample hm hsecretPos
          hsecretLt) samples)
    (hclear : ¬ PMF.HasPair
      (fun pair => pair ∈ PMF.markedPairCarrier
        (exactNarrowGoodSampleObstructionPairs N secret sample hm
          hsecretPos hsecretLt)) samples) :
    PMF.HasPair (FixedPreparedFeasibleNarrowGoodPair N secret sample)
      (samples.map Prod.fst) := by
  classical
  rcases PMF.hasPair_sameEvent_of_atLeastTwo
      (fun outcome => outcome.2 ∧ outcome.1 ∈
        exactNarrowGoodSampleCore N secret sample hm hsecretPos
          hsecretLt) samples htwo with
    ⟨markedPair, hmarkedPair, hfirst, hsecond⟩
  refine ⟨(markedPair.1.1, markedPair.2.1), ?_, ?_⟩
  · rw [List.unorderedPairs_map]
    exact List.mem_map.mpr ⟨markedPair, hmarkedPair, rfl⟩
  · refine ⟨
      exactNarrowGoodSampleCore_mem_fixedPreparedNarrowGoodSample
        N secret sample hm hsecretPos hsecretLt hfirst.2,
      exactNarrowGoodSampleCore_mem_fixedPreparedNarrowGoodSample
        N secret sample hm hsecretPos hsecretLt hsecond.2, ?_⟩
    intro hobstruction
    apply hclear
    refine ⟨markedPair, hmarkedPair, ?_⟩
    change markedPair ∈ PMF.markedPairCarrier
      (exactNarrowGoodSampleObstructionPairs N secret sample hm
        hsecretPos hsecretLt)
    rw [PMF.mem_markedPairCarrier_iff]
    exact ⟨hfirst.1, hsecond.1,
      exactNarrowGoodSampleObstructionPairs_mem_of_core_of_obstruction
        N secret sample hm hsecretPos hsecretLt hfirst.2 hsecond.2
          hobstruction⟩

/-- Sixteen independent terminal measurements of one fixed selected residue
contain a feasible narrow-good pair with the source-shaped batch floor.  All
sixteen draws use the same raw residue sampler value; only their terminal
measurements are independent. -/
theorem fixedPreparedSample_sixteen_hasFeasibleNarrowGoodPair_ge
    {N : Nat} (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (secret : Nat) (hm : 3 ≤ (registerParameters N).m)
    (htradeoff : (registerParameters N).m ≤
      2 * (registerParameters N).ell)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (horder : ShortDLP.oracleFiberSpan (registerParameters N) secret ≤
      orderOf (preparedResidue sample).unit) :
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : Real) ≤
      ((PMF.independentReplicate
        (fixedPreparedSamplePMF input sample) 16).toOuterMeasure
          {samples | PMF.HasPair
            (FixedPreparedFeasibleNarrowGoodPair N secret sample) samples}) := by
  classical
  let hmTwo : 2 ≤ (registerParameters N).m := by omega
  let core := exactNarrowGoodSampleCore N secret sample hmTwo
    hsecretPos hsecretLt
  let coupling := fixedPreparedSampleMinorization input sample secret hmTwo
    hsecretPos hsecretLt htarget horder
  let markedCore := fun outcome : PreparedBatchSample N × Bool =>
    outcome.2 ∧ outcome.1 ∈ core
  let bad := exactNarrowGoodSampleObstructionPairs N secret sample hmTwo
    hsecretPos hsecretLt
  let markedBad := fun pair :
      (PreparedBatchSample N × Bool) × (PreparedBatchSample N × Bool) =>
    pair ∈ PMF.markedPairCarrier bad
  let transcripts := PMF.independentReplicate coupling 16
  let atLeastTwoSet : Set (List (PreparedBatchSample N × Bool)) :=
    {samples | PMF.AtLeastTwoEvents markedCore samples}
  let badTranscriptSet : Set (List (PreparedBatchSample N × Bool)) :=
    {samples | PMF.HasPair markedBad samples}
  have hmarked : coupling.toOuterMeasure
      {outcome | markedCore outcome} = ENNReal.ofReal (1 / 8 : Real) := by
    simpa [coupling, markedCore, core] using
      fixedPreparedSampleMinorization_markedCoreMass
        input sample secret hmTwo hsecretPos hsecretLt htarget horder
  have hunmarked : coupling.toOuterMeasure
      {outcome | ¬ markedCore outcome} = ENNReal.ofReal (7 / 8 : Real) := by
    rw [PMF.eventProbability_eq_one_sub_complement coupling
      (fun outcome => ¬ markedCore outcome)]
    simp only [not_not]
    rw [hmarked]
    calc
      1 - ENNReal.ofReal (1 / 8 : Real) =
          ENNReal.ofReal (1 - 1 / 8 : Real) := by
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub (1 : Real) (by positivity)]
      _ = ENNReal.ofReal (7 / 8 : Real) := by norm_num
  have hatLeastTwo : transcripts.toOuterMeasure atLeastTwoSet =
      ENNReal.ofReal (BinomialTail.atLeastTwoOfSixteenAtOneEighth : Real) := by
    dsimp only [transcripts, atLeastTwoSet]
    rw [PMF.independentReplicate_atLeastTwoProbability_eq,
      hmarked, hunmarked]
    have hinner :
        ENNReal.ofReal (7 / 8 : Real) ^ 16 +
            16 * ENNReal.ofReal (1 / 8 : Real) *
              ENNReal.ofReal (7 / 8 : Real) ^ 15 =
          ENNReal.ofReal
            ((7 / 8 : Real) ^ 16 +
              16 * (1 / 8 : Real) * (7 / 8 : Real) ^ 15) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_pow (by positivity : (0 : Real) ≤ 7 / 8),
        ENNReal.ofReal_mul
          (by positivity : (0 : Real) ≤ 16 * (1 / 8 : Real)),
        ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 16),
        ENNReal.ofReal_pow (by positivity : (0 : Real) ≤ 7 / 8)]
      norm_num
    change 1 - (ENNReal.ofReal (7 / 8 : Real) ^ 16 +
        16 * ENNReal.ofReal (1 / 8 : Real) *
          ENNReal.ofReal (7 / 8 : Real) ^ 15) = _
    rw [hinner]
    calc
      1 - ENNReal.ofReal
          ((7 / 8 : Real) ^ 16 +
            16 * (1 / 8 : Real) * (7 / 8 : Real) ^ 15) =
          ENNReal.ofReal
            (1 - ((7 / 8 : Real) ^ 16 +
              16 * (1 / 8 : Real) * (7 / 8 : Real) ^ 15)) := by
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub (1 : Real) (by positivity)]
      _ = ENNReal.ofReal
          (BinomialTail.atLeastTwoOfSixteenAtOneEighth : Real) := by
        congr 1
        norm_num [BinomialTail.atLeastTwoOfSixteenAtOneEighth]
  have hbadPair :
      (PMF.independentPair coupling).toOuterMeasure
          {pair | markedBad pair} ≤ ENNReal.ofReal (1 / 2048 : Real) := by
    change (PMF.independentPair coupling).toOuterMeasure
      (↑(PMF.markedPairCarrier bad) : Set _) ≤
        ENNReal.ofReal (1 / 2048 : Real)
    simpa only [coupling, bad] using
      fixedPreparedSampleMinorization_markedObstructionMass_le_oneOver2048
        input sample secret hm htradeoff hsecretPos hsecretLt htarget horder
  have hbadTranscript : transcripts.toOuterMeasure badTranscriptSet ≤
      ENNReal.ofReal (1 / 8 : Real) := by
    calc
      transcripts.toOuterMeasure badTranscriptSet ≤
          (Nat.choose 16 2 : ENNReal) *
            ((PMF.independentPair coupling).toOuterMeasure
              {pair | markedBad pair}) := by
        exact PMF.independentReplicate_hasPairProbability_le
          coupling markedBad 16
      _ ≤ (Nat.choose 16 2 : ENNReal) *
          ENNReal.ofReal (1 / 2048 : Real) := by
        simpa [mul_comm] using mul_le_mul_right hbadPair (Nat.choose 16 2 : ENNReal)
      _ = ENNReal.ofReal ((120 : Real) * (1 / 2048 : Real)) := by
        rw [show Nat.choose 16 2 = 120 by norm_num [Nat.choose],
          ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 120)]
        norm_num
      _ ≤ ENNReal.ofReal (1 / 8 : Real) :=
        ENNReal.ofReal_le_ofReal (by norm_num)
  have hdiff :
      transcripts.toOuterMeasure atLeastTwoSet -
          transcripts.toOuterMeasure badTranscriptSet ≤
        transcripts.toOuterMeasure (atLeastTwoSet \ badTranscriptSet) := by
    apply tsub_le_iff_left.mpr
    calc
      transcripts.toOuterMeasure atLeastTwoSet ≤
          transcripts.toOuterMeasure (atLeastTwoSet ∩ badTranscriptSet) +
            transcripts.toOuterMeasure
              (atLeastTwoSet \ badTranscriptSet) :=
        MeasureTheory.measure_le_inter_add_sdiff _ _ _
      _ ≤ transcripts.toOuterMeasure badTranscriptSet +
            transcripts.toOuterMeasure
              (atLeastTwoSet \ badTranscriptSet) := by
        gcongr
        exact Set.inter_subset_right
  have hgood : ENNReal.ofReal
        (BinomialTail.sixteenSampleBatchFloor : Real) ≤
      transcripts.toOuterMeasure (atLeastTwoSet \ badTranscriptSet) := by
    calc
      ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : Real) =
          ENNReal.ofReal
            ((BinomialTail.atLeastTwoOfSixteenAtOneEighth : Real) -
              1 / 8) := by
        congr 1
        norm_num [BinomialTail.sixteenSampleBatchFloor]
      _ = ENNReal.ofReal
            (BinomialTail.atLeastTwoOfSixteenAtOneEighth : Real) -
          ENNReal.ofReal (1 / 8 : Real) := by
        rw [ENNReal.ofReal_sub]
        norm_num
      _ ≤ transcripts.toOuterMeasure atLeastTwoSet -
          transcripts.toOuterMeasure badTranscriptSet :=
        tsub_le_tsub hatLeastTwo.ge hbadTranscript
      _ ≤ transcripts.toOuterMeasure
          (atLeastTwoSet \ badTranscriptSet) := hdiff
  have hprojects : atLeastTwoSet \ badTranscriptSet ⊆
      List.map Prod.fst ⁻¹'
        {samples | PMF.HasPair
          (FixedPreparedFeasibleNarrowGoodPair N secret sample) samples} := by
    intro outputs houtputs
    change PMF.HasPair
      (FixedPreparedFeasibleNarrowGoodPair N secret sample)
        (outputs.map Prod.fst)
    exact hasFixedPreparedFeasibleNarrowGoodPair_map_fst_of_markedCore
      N secret sample hmTwo hsecretPos hsecretLt outputs
        houtputs.1 houtputs.2
  calc
    ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : Real) ≤
        transcripts.toOuterMeasure (atLeastTwoSet \ badTranscriptSet) := hgood
    _ ≤ transcripts.toOuterMeasure
        (List.map Prod.fst ⁻¹'
          {samples | PMF.HasPair
            (FixedPreparedFeasibleNarrowGoodPair N secret sample) samples}) :=
      transcripts.toOuterMeasure_mono (fun _ houtputs => hprojects houtputs.1)
    _ = (transcripts.map (List.map Prod.fst)).toOuterMeasure
        {samples | PMF.HasPair
          (FixedPreparedFeasibleNarrowGoodPair N secret sample) samples} := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = ((PMF.independentReplicate
      (fixedPreparedSamplePMF input sample) 16).toOuterMeasure
        {samples | PMF.HasPair
          (FixedPreparedFeasibleNarrowGoodPair N secret sample) samples}) := by
      dsimp only [transcripts]
      rw [PMF.independentReplicate_map,
        fixedPreparedSampleMinorization_map_fst]

/-- The pure lattice-feasibility predicate for two terminal results held by
actual prepared batch samples. -/
def fixedPreparedPairFeasible (N : Nat)
    (pair : PreparedBatchSample N × PreparedBatchSample N) : Prop :=
  RSA.ShortLogRecoveryFeasible (registerParameters N).m
    (registerParameters N).ell
    (fixedPreparedDecodedSample N pair.1,
      fixedPreparedDecodedSample N pair.2)

/-- Excluding the actual fixed-sample obstruction supplies the pure RSA
lattice-feasibility certificate for its decoded terminal pair. -/
theorem fixedPreparedPairFeasible_of_noTinyMultiplierObstruction
    (N : Nat) (pair : PreparedBatchSample N × PreparedBatchSample N)
    (hm : 3 ≤ (registerParameters N).m)
    (hclear : ¬ fixedPreparedTinyMultiplierObstructionPair N pair) :
    fixedPreparedPairFeasible N pair := by
  apply RSA.shortLogRecoveryFeasible_of_noTinyVector hm
  apply RSA.shortLogNoTinyVector_of_noTinyMultiplierObstruction _ hm
  simpa only [fixedPreparedTinyMultiplierObstructionPair,
    fixedPreparedFirstRegisterIndex] using hclear

/-- Every fixed-sample feasible narrow-good pair carries the exact pure RSA
feasibility certificate consumed by the canonical batch recovery. -/
theorem fixedPreparedFeasibleNarrowGoodPair_feasible
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (pair : PreparedBatchSample N × PreparedBatchSample N)
    (hm : 3 ≤ (registerParameters N).m)
    (hpair : FixedPreparedFeasibleNarrowGoodPair N secret sample pair) :
    fixedPreparedPairFeasible N pair :=
  fixedPreparedPairFeasible_of_noTinyMultiplierObstruction N pair hm hpair.2.2

/-- The source narrow-good predicate on one canonical terminal decoder is
definitionally the pure RSA short-log good-sample predicate. -/
theorem fixedPreparedNarrowGood_iff_shortLogGoodSample
    (N secret : Nat) (outcome : PreparedBatchSample N) :
    ShortDLP.BornProbability.NarrowGoodPair (registerParameters N) secret
      (fixedPreparedDecodedSample N outcome) ↔
      RSA.ShortLogGoodSample (registerParameters N).m
        (registerParameters N).ell secret
        (fixedPreparedDecodedSample N outcome) := by
  unfold ShortDLP.BornProbability.NarrowGoodPair
  unfold RSA.ShortLogGoodSample RSA.shortLogCenteredDistance
  unfold ShortDLP.BornProbability.centeredPhaseFrequency
    ShortDLP.BornProbability.phaseFrequencyNat
  rw [NumberTheory.natAbs_centeredResidue (by positivity)]
  simp only [ShortDLP.firstBits]

/-- Two actual narrow-good terminal samples of the same fixed prepared
residue admit the hidden short logarithm as a pure RSA recovery candidate. -/
theorem fixedPreparedShortLogPairCandidate_of_narrowGood
    (N secret : Nat) (sample : Fin (2 ^ residueSamplingBits N))
    (first second : PreparedBatchSample N)
    (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ (registerParameters N).m)
    (htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ secret)
    (hfirst : FixedPreparedNarrowGoodSample N secret sample first)
    (hsecond : FixedPreparedNarrowGoodSample N secret sample second) :
    RSA.ShortLogPairCandidate (registerParameters N).m
      (registerParameters N).ell (preparedResidue sample).unit
      (fixedPreparedDecodedSample N first,
        fixedPreparedDecodedSample N second) secret := by
  refine ⟨hsecretPos, hsecretLt, htarget.symm, ?_, ?_⟩
  · exact (fixedPreparedNarrowGood_iff_shortLogGoodSample
      N secret first).mp hfirst.2
  · exact (fixedPreparedNarrowGood_iff_shortLogGoodSample
      N secret second).mp hsecond.2

/-- A feasible fixed-sample pair makes the canonical pair recovery return
some factor.  If preparation exposed an early factor it is retained; otherwise
the pure RSA short-log recovery returns one of the declared factors. -/
theorem recoverPreparedPair_some_of_fixedPreparedFeasibleNarrowGoodPair
    {p q : Nat} (sample : Fin (2 ^ residueSamplingBits (p * q)))
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpOdd : Odd p) (hqOdd : Odd q)
    (hm : 3 ≤ (registerParameters (p * q)).m)
    (hsecretPos : 0 < RSA.shortLogSecret p q)
    (hsecretLt : RSA.shortLogSecret p q <
      2 ^ (registerParameters (p * q)).m)
    (horder : ShortDLP.oracleFiberSpan (registerParameters (p * q))
        (RSA.shortLogSecret p q) ≤
      orderOf (preparedResidue sample).unit)
    {pair : PreparedBatchSample (p * q) × PreparedBatchSample (p * q)}
    (hpair : FixedPreparedFeasibleNarrowGoodPair (p * q)
      (RSA.shortLogSecret p q) sample pair) :
    ∃ factor, BatchRecovery.recoverPreparedPair (p * q)
      (registerParameters (p * q)).m (registerParameters (p * q)).ell pair =
        some factor := by
  have hfeasible := fixedPreparedFeasibleNarrowGoodPair_feasible
    (p * q) (RSA.shortLogSecret p q) sample pair hm hpair
  have htarget : RSA.targetUnit (preparedResidue sample).unit =
      (preparedResidue sample).unit ^ RSA.shortLogSecret p q :=
    RSA.targetUnit_eq_shortLog hp hq hpq hpOdd hqOdd
      (preparedResidue sample).unit
  have hcandidate := fixedPreparedShortLogPairCandidate_of_narrowGood
    (p * q) (RSA.shortLogSecret p q) sample pair.1 pair.2
      hsecretPos hsecretLt htarget hpair.1 hpair.2.1
  have hpowLeSpan : 2 ^ (registerParameters (p * q)).m ≤
      ShortDLP.oracleFiberSpan (registerParameters (p * q))
        (RSA.shortLogSecret p q) := by
    unfold ShortDLP.oracleFiberSpan ShortDLP.firstBits
    have hpow : 2 ^ (registerParameters (p * q)).m ≤
        2 ^ ((registerParameters (p * q)).ell +
          (registerParameters (p * q)).m) := by
      rw [pow_add]
      simpa [mul_comm] using
        Nat.le_mul_of_pos_left (2 ^ (registerParameters (p * q)).m)
          (by positivity : 0 < 2 ^ (registerParameters (p * q)).ell)
    omega
  have hsuccess := RSA.recoverFactorFromShortLogPair_shortLogSecret
    hp hq hpOdd hqOdd hfeasible (hpowLeSpan.trans horder) hcandidate
  rcases pair with ⟨first, second⟩
  rcases first with ⟨firstPrepared, firstBits⟩
  rcases second with ⟨secondPrepared, secondBits⟩
  rcases hpair with ⟨hfirst, hsecond, hclear⟩
  rcases hfirst with ⟨hfirstPrepared, hfirstGood⟩
  rcases hsecond with ⟨hsecondPrepared, hsecondGood⟩
  change firstPrepared = preparedResidue sample at hfirstPrepared
  change secondPrepared = preparedResidue sample at hsecondPrepared
  subst firstPrepared
  subst secondPrepared
  rw [BatchRecovery.recoverPreparedPair_same_prepared]
  cases hearly : (preparedResidue sample).earlyFactor with
  | some factor =>
      exact ⟨factor, by simp only [Option.orElse_some]⟩
  | none =>
      rcases hsuccess with hsuccess | hsuccess
      · exact ⟨p, by
          simpa only [hearly, Option.orElse_none,
            fixedPreparedDecodedSample] using hsuccess⟩
      · exact ⟨q, by
          simpa only [hearly, Option.orElse_none,
            fixedPreparedDecodedSample] using hsuccess⟩

/-- One feasible narrow-good pair among the 120 ordered recovery inputs makes
the canonical fixed sixteen-sample batch value return some factor. -/
theorem batchValue_eq_some_of_fixedPreparedFeasibleNarrowGoodPair
    {p q : Nat} (sample : Fin (2 ^ residueSamplingBits (p * q)))
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpOdd : Odd p) (hqOdd : Odd q)
    (hm : 3 ≤ (registerParameters (p * q)).m)
    (hsecretPos : 0 < RSA.shortLogSecret p q)
    (hsecretLt : RSA.shortLogSecret p q <
      2 ^ (registerParameters (p * q)).m)
    (horder : ShortDLP.oracleFiberSpan (registerParameters (p * q))
        (RSA.shortLogSecret p q) ≤
      orderOf (preparedResidue sample).unit)
    (inputs : List.Vector (PreparedBatchSample (p * q)) 16)
    (hpairExists : PMF.HasPair
      (FixedPreparedFeasibleNarrowGoodPair (p * q)
        (RSA.shortLogSecret p q) sample) inputs.toList) :
    ∃ factor, BatchRecovery.batchValue (p * q)
      (registerParameters (p * q)).m (registerParameters (p * q)).ell inputs =
        some factor := by
  rcases hpairExists with ⟨pair, hpairMember, hpair⟩
  obtain ⟨factor, hresult⟩ :=
    recoverPreparedPair_some_of_fixedPreparedFeasibleNarrowGoodPair
      sample hp hq hpq hpOdd hqOdd hm hsecretPos hsecretLt horder hpair
  apply BatchRecovery.batchValue_eq_some_of_exists
  refine ⟨factor, ?_⟩
  rw [BatchRecovery.batchPairValues_eq_list]
  exact List.mem_map.mpr ⟨pair, hpairMember, hresult⟩

end

end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
