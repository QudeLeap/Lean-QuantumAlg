/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Space
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout

/-!
# The simultaneous reset fits the independent sampler-stage allowance

The reset genuinely allocates a result cell per bank wire. Those cells need
not coincide with the source sampler's earlier workspace. Their later stage
fits the same independent allowance because the earlier preparation peak
already reserves enough capacity beside the sampler's retained results.
The width inequality includes the total zero-modulus specialization.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open ShortDLP.CompiledMAU

/-- The actual compiled bank width fits within the source sampler's temporary allowance. -/
lemma nativeBatch_reset_width_le (N : Nat) :
    ShortDLP.totalQubits
      (registerParameters (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) ≤
      9 * modulusBits N + 14 := by
  rw [totalQubits_eq]
  by_cases empty : N = 0
  · subst N
    norm_num [shortLogBits, factorBits, tradeoffBits, arithmeticBits,
      modulusBits, ShorStyle.Canonical.modulusBits]
  · let : NeZero N := ⟨empty⟩
    have first := shortLogBits_le_modulusBits_add_one N
    have second := tradeoffBits_le_modulusBits_add_one N
    have arithmetic := arithmeticBits_le_modulusBits_add_one N
    omega

/-- The exact reset scratch and retained source cells fit the unchanged sampler allowance. -/
lemma nativeBatch_reset_retained_le_sampler (N : Nat) :
    RuntimeRound.resetSpace (shortLogBits N) (tradeoffBits N) (arithmeticBits N) +
      ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N) ≤
        ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  have width := nativeBatch_reset_width_le N
  have bitSize : Nat.clog 2 2 = 1 := by decide
  intro axis
  cases axis with
  | classicalBits =>
      change ShortDLP.totalQubits
          (registerParameters (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) *
            Nat.clog 2 2 + (18 * modulusBits N + 1) ≤ 27 * modulusBits N + 15
      rw [bitSize]
      omega
  | quantumSystems dimension =>
      simp [RuntimeRound.resetSpace, ShorStyle.Canonical.Sampler.Retained.resultSpace,
        ShorStyle.Canonical.Sampler.Retained.additionalSpace, SpacePool.ofShape]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
