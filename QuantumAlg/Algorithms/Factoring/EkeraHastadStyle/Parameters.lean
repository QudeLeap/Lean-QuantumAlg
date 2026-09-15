/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.RSA.FixedWidthSampling
import all QuantumAlg.Util.RSA.ResidueSampling
import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Public widths and deterministic residue parameters for Ekerå--Håstad factoring

The public modulus determines every exponent and arithmetic width. The
classical parameter uses the shared exact RSA residue decoder, while total
unit selection is fixed internally. This module introduces no random draw,
classical evaluator, quantum instruction, or hidden execution callback.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical

noncomputable section

/-! ## Public widths and executable assumptions -/

/-- Binary width of the known RSA modulus. -/
@[implicit_reducible] public def modulusBits (N : Nat) : Nat :=
  ShorStyle.Canonical.modulusBits N

/-- Public arithmetic width that strictly contains the modulus. The actual
compiler uses this width exactly, including its proved small-width branches. -/
def arithmeticBits (N : Nat) : Nat := Nat.clog 2 (N + 1)

/-- Fixed number of residue proposals decoded before one short-DLP batch. -/
@[implicit_reducible] def residueProposalCount : Nat :=
  ShorStyle.Canonical.residueProposalCount

/-- Exact number of internally sampled proposal bits. -/
@[implicit_reducible] def residueSamplingBits (N : Nat) : Nat :=
  ShorStyle.Canonical.residueSamplingBits N

/-- Width of either prime in a same-bit RSA modulus. -/
def factorBits (N : Nat) : Nat := modulusBits N / 2

/-- Source upper-bound width for the short logarithm. -/
def shortLogBits (N : Nat) : Nat := factorBits N + 1

/-- Source tradeoff width for the fixed choice `s = 2`. -/
def tradeoffBits (N : Nat) : Nat := (shortLogBits N + 1) / 2

/-- An exact same-bit RSA modulus exposes twice the source prime width. -/
theorem modulusBits_sameBit {b : Nat} (pair : RSA.RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    modulusBits pair.modulus = 2 * b := by
  exact RSA.FixedWidthSampling.modulus_clog_eq_two_mul pair hb

/-- The strict arithmetic word also has twice the source prime width on the
same-bit distribution. -/
theorem arithmeticBits_sameBit {b : Nat} (pair : RSA.RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    arithmeticBits pair.modulus = 2 * b := by
  unfold arithmeticBits
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow (Nat.succ_le_of_lt pair.modulus_bits.2)
  · have strict : 2 ^ (2 * b - 1) < pair.modulus + 1 :=
      lt_of_le_of_lt pair.modulus_bits.1 (Nat.lt_succ_self pair.modulus)
    have pred_lt : 2 * b - 1 < Nat.clog 2 (pair.modulus + 1) :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).2 strict
    omega

/-- The modulus-derived factor width agrees with the source prime width. -/
theorem factorBits_sameBit {b : Nat} (pair : RSA.RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    factorBits pair.modulus = b := by
  rw [factorBits, modulusBits_sameBit pair hb]
  omega

/-- The executable short-log width is the source width `b + 1`. -/
theorem shortLogBits_sameBit {b : Nat} (pair : RSA.RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    shortLogBits pair.modulus = RSA.GeneratorOrder.m b := by
  rw [shortLogBits, factorBits_sameBit pair hb]
  rfl

/-- The executable tradeoff width is the source choice `ceil((b + 1) / 2)`. -/
theorem tradeoffBits_sameBit {b : Nat} (pair : RSA.RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    tradeoffBits pair.modulus = RSA.GeneratorOrder.ell b := by
  rw [tradeoffBits, shortLogBits_sameBit pair hb]
  rfl

/-- Public executable assumptions for a known nontrivial modulus. -/
public structure Input (N : Nat) : Prop where
  modulus_gt_one : 1 < N

theorem Input.modulus_pos {N : Nat} (input : Input N) : 0 < N :=
  Nat.zero_lt_of_lt input.modulus_gt_one

theorem Input.neZero {N : Nat} (input : Input N) : NeZero N :=
  ⟨Nat.ne_of_gt input.modulus_pos⟩

theorem Input.modulusBits_pos {N : Nat} (input : Input N) :
    0 < modulusBits N :=
  Nat.clog_pos (by norm_num : 1 < 2) input.modulus_gt_one

/-- The public modulus fits strictly inside its derived arithmetic word. -/
theorem modulus_lt_arithmeticCapacity (N : Nat) :
    N < 2 ^ arithmeticBits N := by
  exact lt_of_lt_of_le (Nat.lt_succ_self N)
    (Nat.le_pow_clog (by norm_num : 1 < 2) (N + 1))

theorem shortLogBits_le_modulusBits_add_one (N : Nat) :
    shortLogBits N ≤ modulusBits N + 1 := by
  unfold shortLogBits factorBits
  omega

theorem tradeoffBits_le_modulusBits_add_one (N : Nat) :
    tradeoffBits N ≤ modulusBits N + 1 := by
  unfold tradeoffBits
  have := shortLogBits_le_modulusBits_add_one N
  omega

theorem arithmeticBits_le_modulusBits_add_one (N : Nat) [NeZero N] :
    arithmeticBits N ≤ modulusBits N + 1 := by
  have modulusPositive : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have capacity : N ≤ 2 ^ modulusBits N :=
    Nat.le_pow_clog (by norm_num : 1 < 2) N
  unfold arithmeticBits modulusBits
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  calc
    N + 1 ≤ 2 * N := by omega
    _ ≤ 2 * 2 ^ Nat.clog 2 N := Nat.mul_le_mul_left 2 capacity
    _ = 2 ^ Nat.clog 2 N * 2 := by ring

/-- Actual short-DLP register parameters derived only from `N`. The two
exponent registers reuse the same power and zero auxiliary words. -/
@[implicit_reducible]
def registerParameters (N : Nat) : ShortDLP.RegisterParameters :=
  ShortDLP.CompiledMAU.registerParameters
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)

/-- Number of measured bits in one terminal short-DLP outcome. -/
@[implicit_reducible] def measurementBits (N : Nat) : Nat :=
  ShortDLP.firstBits (registerParameters N) + (registerParameters N).ell

theorem measurementBits_pos (N : Nat) : 0 < measurementBits N := by
  unfold measurementBits registerParameters
  simp only [ShortDLP.CompiledMAU.registerParameters, ShortDLP.firstBits,
    shortLogBits]
  omega

/-! ## Internally sampled parameter -/

/-- Runtime shape shared with the counted RSA residue sampler. -/
abbrev ParameterShape (N : Nat) : CShape :=
  ShorStyle.Canonical.ParameterShape (modulusBits N)

/-- The Shor sampler assumptions induced by an Ekerå–Håstad input. -/
theorem Input.samplerInput {N : Nat} (input : Input N) :
    ShorStyle.Canonical.Input N :=
  ⟨input.modulus_gt_one⟩

/-- Shaped parameter computed by the actual fixed-cost residue sampler. -/
def parameterValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    CShape.Value (ParameterShape N) :=
  ShorStyle.Canonical.parameterValue input.samplerInput sample

/-- Proof-side prepared residue represented by one sampler output. -/
def preparedResidue {N : Nat} (sample : Fin (2 ^ residueSamplingBits N)) :
    RSA.PreparedResidue N :=
  RSA.prepareResidueFromBits N (modulusBits N) residueProposalCount sample

@[simp] theorem parameterValue_unit_toNat {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    (parameterValue input sample).first.toNat =
      ((preparedResidue sample).unit : ZMod N).val := by
  exact ShorStyle.Canonical.parameterValue_unit_toNat
    input.samplerInput sample

/-- Total unit selected by one shaped parameter.

Sampler-produced parameters take the coprime branch.  Keeping the fallback
inside this closed definition makes the executable circuit family total without
turning coprimality into a caller proof. -/
def parameterUnit {N : Nat} (parameter : CShape.Value (ParameterShape N)) :
    (ZMod N)ˣ :=
  if coprime : Nat.Coprime parameter.first.toNat N then
    ZMod.unitOfCoprime parameter.first.toNat coprime
  else
    1

/-- A sampler-produced parameter selects exactly its prepared unit. -/
@[simp] theorem parameterUnit_parameterValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    parameterUnit (parameterValue input sample) =
      (preparedResidue sample).unit := by
  let _ : NeZero N := input.neZero
  have valueEq := parameterValue_unit_toNat input sample
  have coprime : Nat.Coprime (parameterValue input sample).first.toNat N := by
    rw [valueEq]
    exact ZMod.val_coe_unit_coprime (preparedResidue sample).unit
  unfold parameterUnit
  rw [dif_pos coprime]
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, valueEq]
  exact ZMod.natCast_zmod_val ((preparedResidue sample).unit : ZMod N)

/-- Public-data target paired with the internally selected generator. -/
def parameterTarget {N : Nat} (parameter : CShape.Value (ParameterShape N)) :
    (ZMod N)ˣ :=
  RSA.targetUnit (parameterUnit parameter)

/-- A sampler-produced parameter selects the target paired with its prepared
unit. -/
@[simp] theorem parameterTarget_parameterValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    parameterTarget (parameterValue input sample) =
      RSA.targetUnit (preparedResidue sample).unit := by
  unfold parameterTarget
  rw [parameterUnit_parameterValue]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
