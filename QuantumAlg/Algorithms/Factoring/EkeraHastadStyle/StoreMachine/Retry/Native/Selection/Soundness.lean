/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability

/-!
# Every supported actual selected word is a nontrivial divisor

The chronological selector returns one supported original batch factor.
The existing batch support theorem bounds that factor strictly below the
modulus, whose original input certificate fits the output word. Its actual
word encoding therefore does not truncate. No good-key, factorization or
caller-state assumption is introduced.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection

noncomputable section

open Execution ShortDLP.CompiledMAU ClassicalRoutines.FirstAccepted.Direct

/-- Every supported typed batch word decodes to its original checked nontrivial factor. -/
theorem batch_outputValue_some_sound {N : Nat} (specification : Input N)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [PMF.mem_support_map_iff] at supported
  rcases supported with ⟨value, member, encoded⟩
  cases value with
  | none => cases encoded
  | some factor =>
      have wordEq : CShape.wordOfNat (modulusBits N) factor = word :=
        CShape.Value.optionSome.inj encoded
      have sound := sampledBatchOutputPMF_some_sound specification member
      have capacity : factor < CShape.wordModulus (modulusBits N) :=
        sound.2.2.trans_le specification.samplerInput.register_fits
      have decoded : word.toNat = factor := by
        rw [← wordEq, CShape.wordOfNat_val, Nat.mod_eq_of_lt capacity]
      exact decoded.symm ▸ sound

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every populated actual selected output word represents a checked nontrivial divisor. -/
theorem run_some_sound (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((run base noQuantum specification count).outputDistribution input).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [run_selectedDistribution] at supported
  exact batch_outputValue_some_sound specification word
    (Optional.Distribution.selectedDistribution_some_support _ (count + 1) word supported)

/-- Natural observation of any supported populated actual result is the same nontrivial divisor. -/
theorem run_decoded_some_sound (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference) (factor : Nat)
    (supported : some factor ∈
      (((run base noQuantum specification count).outputDistribution input).map
        decodeFactor).support) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  rw [PMF.mem_support_map_iff] at supported
  rcases supported with ⟨value, member, decoded⟩
  cases value with
  | optionNone => cases decoded
  | optionSome word =>
      have valueEq : word.toNat = factor := Option.some.inj decoded
      exact valueEq ▸ run_some_sound base noQuantum specification count input word member

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection
