/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Sampled

/-!
# Correctness and conditional success of a complete declared EH batch

The physical factor cell is populated only by a certified nontrivial divisor.
For a good key, its empty-result probability obeys the original single-batch
floor, both for the first preparation and a later full redraw and reuse.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma map_point_of_singleton_fiber {Source Target : Type}
    (distribution : PMF Source) (read : Source → Target) (source : Source) (target : Target)
    (fiber : ∀ value, target = read value ↔ value = source) :
    distribution.map read target = distribution source := by
  rw [PMF.map_apply]
  calc
    (∑' value, if target = read value then distribution value else 0) =
        ∑' value, if value = source then distribution value else 0 := by
      apply tsum_congr
      intro value
      by_cases equal : target = read value
      · have same := (fiber value).mp equal
        simp [equal, same]
      · have different : value ≠ source := fun same => equal ((fiber value).mpr same)
        simp [equal, different]
    _ = distribution source := tsum_ite_eq source distribution

/-- Encoding the independent recovered source as an optional word preserves
the exact empty-result probability. -/
lemma packed_none {N : Nat} (input : Input N) :
    ((sampledBatchOutputPMF input).map
      (LatticeBatchRecoveryOutput.outputValue (N := N))) .optionNone =
        sampledBatchOutputPMF input none := by
  apply map_point_of_singleton_fiber (sampledBatchOutputPMF input)
    (LatticeBatchRecoveryOutput.outputValue (N := N)) none .optionNone
  intro value
  cases value <;> simp [LatticeBatchRecoveryOutput.outputValue]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- A populated value supported by the independently sampled and encoded
one-batch source law is a checked nontrivial factor. -/
lemma sourceOutput_some_sound (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      (((sampledBatchOutputPMF input).map
        LatticeBatchRecoveryOutput.outputValue).support)) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [PMF.mem_support_map_iff] at supported
  rcases supported with ⟨value, member, encoded⟩
  cases value with
  | none => cases encoded
  | some factor =>
      have wordEq : CShape.wordOfNat (modulusBits N) factor = word :=
        CShape.Value.optionSome.inj encoded
      have sound := sampledBatchOutputPMF_some_sound input member
      have capacity : factor < CShape.wordModulus (modulusBits N) :=
        sound.2.2.trans_le input.samplerInput.register_fits
      have decoded : word.toNat = factor := by
        rw [← wordEq, CShape.wordOfNat_val, Nat.mod_eq_of_lt capacity]
      exact decoded.symm ▸ sound

lemma run_some_sound {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((run base noQuantum N input).outputDistribution (sourceEnvironment input)
        original).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [run_outputDistribution] at supported
  exact sourceOutput_some_sound N input word supported

lemma nextRun_some_sound {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles
      (Batch.context base noQuantum N) Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((nextRun base noQuantum N input).outputDistribution (sourceEnvironment input)
        original).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [nextRun_outputDistribution] at supported
  exact sourceOutput_some_sound N input word supported

lemma run_none {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (run base noQuantum N input).outputDistribution (sourceEnvironment input) original .optionNone =
      sampledBatchOutputPMF input none := by
  rw [run_outputDistribution, packed_none]

lemma nextRun_none {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles
      (Batch.context base noQuantum N) Reference) :
    (nextRun base noQuantum N input).outputDistribution (sourceEnvironment input) original
      .optionNone =
      sampledBatchOutputPMF input none := by
  rw [nextRun_outputDistribution, packed_none]

lemma run_none_le (good : GoodKeyModel N) {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (run base noQuantum N good.input).outputDistribution (sourceEnvironment good.input)
      original .optionNone ≤
      1 - NativeBatchSuccess.successFloor good.bitWidth := by
  rw [run_none]
  exact NativeBatchSuccess.sampled_none_le good

lemma nextRun_none_le (good : GoodKeyModel N) {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles
      (Batch.context base noQuantum N) Reference) :
    (nextRun base noQuantum N good.input).outputDistribution (sourceEnvironment good.input)
      original .optionNone ≤
      1 - NativeBatchSuccess.successFloor good.bitWidth := by
  rw [nextRun_none]
  exact NativeBatchSuccess.sampled_none_le good

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery
