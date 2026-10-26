/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Fourier
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution
import all QuantumAlg.Primitives.WalshHadamard.Native

/-!
# The complete same-partner source weight is the original terminal Born probability

The shared Fourier contraction has the declared source's exact double-sum
amplitude on every encoded unit. All other workspace amplitudes vanish.
Injectivity identifies the sums without retaining an old arithmetic backend
or identifying different physical registers [GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open QuantumFourierTransform.Semiclassical
open scoped BigOperators

private lemma measured_hadamard_normalization (bits : Nat) :
    WalshHadamard.invSqrtCard bits = NormalizedVector.invSqrt2 ^ bits := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (WalshHadamard.Native.normalization_product bits).symm

private lemma measuredFourierRow_entry (bits : Nat) (frequency input : Fin (2 ^ bits)) :
    Partner.fullRows true bits frequency ((binaryEquiv bits).symm input) =
      star (invSqrtN bits * ω bits ^ (input.val * frequency.val)) := by
  simp only [Partner.fullRows, if_true, Equiv.apply_symm_apply,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix]
  rfl

variable (m ell width : Nat) (modulus : BitVec width) [NeZero modulus.toNat]
  (generator target : (ZMod modulus.toNat)ˣ)
  (encoding : UnitEncoding modulus.toNat (workspaceBits width))

/-- Every source unit-one column equals the declared original encoded group-value amplitude. -/
lemma memberFourierKraus_source_amplitude
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (row : (Recycling.Carrier.units modulus.toNat).Index) :
    memberFourierKraus m ell width modulus generator target first second row 1 =
      BornProbability.circuitAmplitude (params := registerParameters m ell width) encoding generator
        target first second (encoding.encode row) := by
  rw [memberFourierKraus_seed_entry]
  unfold BornProbability.circuitAmplitude
  apply Finset.sum_congr rfl
  intro sourceFirst _
  apply Finset.sum_congr rfl
  intro sourceSecond _
  rw [measuredFourierRow_entry, measuredFourierRow_entry]
  rw [← measured_hadamard_normalization, ← measured_hadamard_normalization]
  change _ = _ * _ * (if encoding.encode row =
    encoding.encode (oracleValue generator target sourceFirst.val sourceSecond.val) then _ else 0)
  by_cases same : row = oracleValue generator target sourceFirst.val sourceSecond.val
  · have encodedSame := congrArg encoding.encode same
    rw [if_pos same, if_pos encodedSame]
    dsimp only [registerParameters, firstBits]
    ring
  · have encodedDifferent : encoding.encode row ≠
        encoding.encode (oracleValue generator target sourceFirst.val sourceSecond.val) :=
      fun hit => same (encoding.encode_injective hit)
    rw [if_neg same, if_neg encodedDifferent]
    ring

omit [NeZero modulus.toNat] in
/-- The declared source has no amplitude outside the same original injective unit encoding. -/
lemma memberSourceAmplitude_outside
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (workspace : Fin (2 ^ workspaceBits width)) (outside : workspace ∉ Set.range encoding.encode) :
    BornProbability.circuitAmplitude (params := registerParameters m ell width) encoding generator
      target first second workspace = 0 := by
  unfold BornProbability.circuitAmplitude
  apply Finset.sum_eq_zero
  intro sourceFirst _
  apply Finset.sum_eq_zero
  intro sourceSecond _
  have different : workspace ≠
      encodeUnit (params := registerParameters m ell width) encoding
        (oracleValue generator target sourceFirst.val sourceSecond.val) := by
    intro same
    exact outside ⟨oracleValue generator target sourceFirst.val sourceSecond.val, same.symm⟩
  rw [if_neg different, mul_zero]

/-- Squared norm of the canonical unit-one column, retaining all source unit outputs. -/
def memberFourierWeight (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) : ℝ :=
  ∑ row : (Recycling.Carrier.units modulus.toNat).Index,
    ‖memberFourierKraus m ell width modulus generator target first second row 1‖ ^ 2

/-- The full source unit sum is exactly the original declared workspace marginal. -/
lemma memberFourierWeight_workspace
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    memberFourierWeight m ell width modulus generator target first second =
      ∑ workspace : Fin (2 ^ workspaceBits width),
        ‖BornProbability.circuitAmplitude (params := registerParameters m ell width) encoding
          generator target first second workspace‖ ^ 2 := by
  let amplitude (workspace : Fin (2 ^ workspaceBits width)) :=
    ‖BornProbability.circuitAmplitude (params := registerParameters m ell width) encoding generator
      target first second workspace‖ ^ 2
  calc
    _ = ∑ row : (Recycling.Carrier.units modulus.toNat).Index, amplitude (encoding.encode row) := by
      apply Finset.sum_congr rfl
      intro row _
      rw [memberFourierKraus_source_amplitude m ell width modulus generator target encoding]
    _ = ∑ workspace ∈ Finset.univ.image encoding.encode, amplitude workspace := by
      rw [Finset.sum_image]
      intro first _ second _ same
      exact encoding.encode_injective same
    _ = ∑ workspace, amplitude workspace := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro workspace _ outside
      have notRange : workspace ∉ Set.range encoding.encode := by
        rintro ⟨row, rfl⟩
        exact outside (Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩)
      change ‖BornProbability.circuitAmplitude (params := registerParameters m ell width) encoding
        generator target first second workspace‖ ^ 2 = 0
      rw [memberSourceAmplitude_outside m ell width modulus generator target encoding first second
        workspace notRange, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The complete same-partner source weight is the unchanged original terminal Born PMF. -/
lemma memberFourierWeight_ideal
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    memberFourierWeight m ell width modulus generator target first second =
      (((measurement (registerParameters m ell width)).outcomePMF
        (BornProbability.evolvedState encoding generator target))
        (BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
          (prodEquiv (first, second)))).toReal := by
  rw [BornProbability.shortDLPBornOutcomeProbability_eq_workspaceMarginal,
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]
  exact memberFourierWeight_workspace m ell width modulus generator target encoding first second

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
