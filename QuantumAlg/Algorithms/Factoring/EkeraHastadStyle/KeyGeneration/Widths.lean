/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics

/-!
# Original short-log width conditions supplied by the proof-side RSA key

The executable widths depend only on the public modulus. These mathematical
equations relate them to the same-width prime-pair model used by conditional
probability proofs. They derive the short-log domain internally and keep the
key factors out of the actual program's inputs.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.GoodKeyModel

noncomputable section

variable {N : Nat} (model : GoodKeyModel N)

/-- The existing effective-key hypothesis supplies positive prime width. -/
theorem bitWidth_pos : 1 ≤ model.bitWidth := by
  have effective := model.effective
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  omega

/-- The public modulus encoding has exactly twice the model's prime width. -/
theorem modulusBits_eq : modulusBits N = 2 * model.bitWidth :=
  (congrArg modulusBits model.modulus_eq).trans
    (RSA.FixedWidthSampling.modulus_clog_eq_two_mul model.pair model.bitWidth_pos)

/-- The public short-log width equals the original generator-order parameter. -/
theorem shortLogBits_eq : shortLogBits N = RSA.GeneratorOrder.m model.bitWidth :=
  (congrArg shortLogBits model.modulus_eq).trans
    (shortLogBits_sameBit model.pair model.bitWidth_pos)

/-- The public tradeoff width equals the original generator-order parameter. -/
theorem tradeoffBits_eq : tradeoffBits N = RSA.GeneratorOrder.ell model.bitWidth :=
  (congrArg tradeoffBits model.modulus_eq).trans
    (tradeoffBits_sameBit model.pair model.bitWidth_pos)

include model in
/-- Every effective key lies inside the original fixed-source Born bound's width domain. -/
theorem shortLog_atLeastThree : 3 ≤ (registerParameters N).m := by
  change 3 ≤ shortLogBits N
  rw [model.shortLogBits_eq]
  have effective := model.effective
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  unfold RSA.GeneratorOrder.m
  omega

/-- The public tradeoff choice meets the original two-register batch condition. -/
theorem tradeoff_sufficient : (registerParameters N).m ≤ 2 * (registerParameters N).ell := by
  change shortLogBits N ≤ 2 * tradeoffBits N
  unfold tradeoffBits
  omega

/-- The proof-side logarithm is positive for the original distinct-prime input domain. -/
theorem shortLogSecret_pos : 0 < RSA.shortLogSecret model.pair.p model.pair.q := by
  unfold RSA.shortLogSecret
  apply Nat.div_pos
  · have left := model.pair.p_prime.one_lt
    have right := model.pair.q_prime.one_lt
    omega
  · norm_num

/-- The original short logarithm fits the public first-register width. -/
theorem shortLogSecret_lt :
    RSA.shortLogSecret model.pair.p model.pair.q < 2 ^ (registerParameters N).m := by
  change RSA.shortLogSecret model.pair.p model.pair.q < 2 ^ shortLogBits N
  rw [model.shortLogBits_eq]
  exact RSA.GeneratorOrder.RSAKeyPairBits.shortLogSecret_lt_two_pow_m model.pair

/-- Original generator-order sufficiency covers the actual compiled oracle fiber span. -/
theorem orderSufficient_runtimeFiberSpan (secret order : Nat)
    (sufficient : RSA.GeneratorOrder.OrderSufficient model.bitWidth secret order) :
    ShortDLP.oracleFiberSpan (registerParameters N) secret ≤ order := by
  unfold ShortDLP.oracleFiberSpan ShortDLP.firstBits registerParameters
  simp only [ShortDLP.CompiledMAU.registerParameters, model.shortLogBits_eq,
    model.tradeoffBits_eq]
  apply le_trans _ sufficient
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right secret (Nat.sub_le _ _)) _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.GoodKeyModel
