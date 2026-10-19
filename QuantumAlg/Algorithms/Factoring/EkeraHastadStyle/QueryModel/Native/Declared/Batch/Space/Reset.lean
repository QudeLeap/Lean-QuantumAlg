/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters

/-!
# Actual declared-bank reset scratch within the independent sampler allowance

The simultaneous reset genuinely allocates one classical result cell per
original bank wire. Its later stage fits the earlier source sampler allowance.
The old scalar allowance therefore remains sufficient without interpreting
it as the exact reset peak or claiming reuse of already released sampler cells.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

noncomputable section

/-- The original oracle bank, including its target, fits the sampler's temporary capacity. -/
lemma declaredBatch_reset_width_le (N : Nat) :
    ShortDLP.totalQubits (Native.parameters N) ≤ 9 * modulusBits N + 14 := by
  change tradeoffBits N + shortLogBits N + tradeoffBits N + modulusBits N ≤ _
  by_cases empty : N = 0
  · subst N
    norm_num [shortLogBits, factorBits, tradeoffBits,
      modulusBits, ShorStyle.Canonical.modulusBits]
  · let : NeZero N := ⟨empty⟩
    have first := shortLogBits_le_modulusBits_add_one N
    have second := tradeoffBits_le_modulusBits_add_one N
    omega

/-- Every actually allocated reset cell is covered by the independent source scratch bound. -/
lemma declaredBatch_resetSpace_le_sampler (N : Nat) :
    resetSpace N ≤
      ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N) := by
  have width := declaredBatch_reset_width_le N
  have bitSize : Nat.clog 2 2 = 1 := by decide
  intro axis
  cases axis with
  | classicalBits =>
      change ShortDLP.totalQubits (Native.parameters N) * Nat.clog 2 2 ≤
        9 * modulusBits N + 14
      rwa [bitSize, Nat.mul_one]
  | quantumSystems dimension =>
      simp [resetSpace, ShorStyle.Canonical.Sampler.Program.additionalSpace, SpacePool.ofShape]

/-- The sequential maximum has the same independent scalar allowance after the real change. -/
lemma declaredBatch_scratchSpace_eq_sampler (N : Nat) :
    scratchSpace N =
      ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N) :=
  SpacePool.max_eq_left (declaredBatch_resetSpace_le_sampler N)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
