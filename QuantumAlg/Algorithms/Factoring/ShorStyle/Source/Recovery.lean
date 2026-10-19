/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Mathematics

/-!
# Original source success survives the native factor selection order

The semantic recovery input associated with each retained source tuple is
the same original unit and terminal outcome used by the source theorem.
Every present source result is a proper divisor, so an earlier successful
sample cannot replace a source-good result with an invalid factor. The
actual left-priority fold therefore preserves the original retry event,
including its separate even-modulus route and positive retry count.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

noncomputable section

private lemma sampledSemanticInput_eq_good {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (outcome : SourceOutcome N)
    (unit : (ZMod N)ˣ)
    (parameterEq : parameterValue (Probability.Input.ofSemiprimeModel model) outcome.sample =
      Probability.unitParameter (Probability.Input.ofSemiprimeModel model) unit) :
    FactorRecovery.sampledSemanticInput (Probability.Input.ofSemiprimeModel model)
        outcome.sample outcome.measurement =
      FactorRecovery.goodAttemptSemanticInput model unit outcome := by
  let source := Probability.Input.ofSemiprimeModel model
  let : NeZero N := source.neZero
  have baseValue : (FactorRecovery.sampledSemanticInput source
      outcome.sample outcome.measurement).base.val =
        (FactorRecovery.goodAttemptSemanticInput model unit outcome).base.val := by
    calc
      _ = (parameterValue source outcome.sample).first.toNat :=
        (parameterValue_unit_toNat source outcome.sample).symm
      _ = (Probability.unitParameter source unit).first.toNat :=
        congrArg (fun value => value.first.toNat) parameterEq
      _ = _ := (Nat.mod_eq_of_lt (ZMod.val_lt (unit : ZMod N))).symm
  have baseEqual := Fin.ext baseValue
  have terminalEqual : (FactorRecovery.sampledSemanticInput source
      outcome.sample outcome.measurement).terminalBits =
        (FactorRecovery.goodAttemptSemanticInput model unit outcome).terminalBits := rfl
  have sameInput
      (left right : ClassicalAlgorithms.OrderRecovery.Input
        (FactorRecovery.recoverySpec source))
      (sameBase : left.base = right.base) (sameBits : left.terminalBits = right.terminalBits) :
      left = right := by
    cases left
    cases right
    cases sameBase
    cases sameBits
    rfl
  exact sameInput _ _ baseEqual terminalEqual

/-- Every present source result is a declared factor; no earlier candidate can be spurious. -/
lemma sourceResult_declared_or_none {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (outcome : SourceOutcome N) :
    Probability.ReturnedDeclaredFactor model
        (sourceResult (Probability.Input.ofSemiprimeModel model) outcome) ∨
      sourceResult (Probability.Input.ofSemiprimeModel model) outcome = .optionNone := by
  let source := Probability.Input.ofSemiprimeModel model
  let recovered := ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
    (FactorRecovery.recoverySpec source)
    (FactorRecovery.sampledSemanticInput source outcome.sample outcome.measurement)
  cases selected : FactorRecovery.outputOfRecovered
      (parameterValue source outcome.sample) recovered with
  | none => exact Or.inr (congrArg FactorRecovery.encodeOutput selected)
  | some factor =>
      have sound := FactorRecovery.outputOfRecovered_parameterValue_some_sound
        source outcome.sample recovered selected
      have declared := model.nontrivial_factor_eq_declared sound.1 sound.2.1 sound.2.2
      apply Or.inl
      change Probability.ReturnedDeclaredFactor model
        (FactorRecovery.encodeOutput
          (FactorRecovery.outputOfRecovered (parameterValue source outcome.sample) recovered))
      rw [selected]
      change (CShape.wordOfNat (modulusBits N) factor).toNat = model.leftFactor ∨
        (CShape.wordOfNat (modulusBits N) factor).toNat = model.rightFactor
      rw [FactorRecovery.encodeOutput_some_payload_toNat source sound.2.2]
      exact declared

/-- The source-good unit and Born event refer to the same input recovered by the native tail. -/
lemma sourceResult_good {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (outcome : SourceOutcome N) (good : Probability.GoodAttemptOutcome model outcome) :
    Probability.ReturnedDeclaredFactor model
      (sourceResult (Probability.Input.ofSemiprimeModel model) outcome) := by
  rcases good with ⟨unit, unitMember, parameterEq, recoverable⟩
  obtain ⟨factor, actual, declared⟩ :=
    FactorRecovery.outputOfRecovered_unitOutcome_declared model outcome unit
      unitMember parameterEq recoverable
  let source := Probability.Input.ofSemiprimeModel model
  have semantic := sampledSemanticInput_eq_good model outcome unit parameterEq
  have result : FactorRecovery.outputOfRecovered (parameterValue source outcome.sample)
      (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
        (FactorRecovery.recoverySpec source)
        (FactorRecovery.sampledSemanticInput source outcome.sample outcome.measurement)) =
      some factor := by
    rw [semantic]
    exact actual
  have sound := FactorRecovery.outputOfRecovered_parameterValue_some_sound
    source outcome.sample _ result
  change Probability.ReturnedDeclaredFactor model
    (FactorRecovery.encodeOutput
      (FactorRecovery.outputOfRecovered (parameterValue source outcome.sample) _))
  rw [result]
  change (CShape.wordOfNat (modulusBits N) factor).toNat = model.leftFactor ∨
    (CShape.wordOfNat (modulusBits N) factor).toNat = model.rightFactor
  rw [FactorRecovery.encodeOutput_some_payload_toNat source sound.2.2]
  exact declared

private lemma firstPresent_of_declared {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (first later : CShape.Value (.option (.unsignedWord (modulusBits N))))
    (declared : Probability.ReturnedDeclaredFactor model first) :
    firstPresent first later = first := by
  cases first with
  | optionNone => exact False.elim declared
  | optionSome value => rfl

/-- Earlier present results are valid, so the first-present fold preserves any source-good visit. -/
lemma sourceResults_of_contains_good {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (outcomes : List (SourceOutcome N))
    (good : PMF.ContainsEvent (Probability.GoodAttemptOutcome model) outcomes) :
    Probability.ReturnedDeclaredFactor model
      (sourceResults (Probability.Input.ofSemiprimeModel model) outcomes) := by
  induction outcomes with
  | nil =>
      obtain ⟨outcome, member, _⟩ := good
      exact False.elim (List.not_mem_nil member)
  | cons head rest ih =>
      rcases sourceResult_declared_or_none model head with declared | absent
      · rw [sourceResults, firstPresent_of_declared model _ _ declared]
        exact declared
      · have later : PMF.ContainsEvent (Probability.GoodAttemptOutcome model) rest := by
          obtain ⟨outcome, member, accepted⟩ := good
          rcases List.mem_cons.mp member with same | member
          · subst outcome
            have impossible := sourceResult_good model head accepted
            rw [absent] at impossible
            exact False.elim impossible
          · exact ⟨outcome, member, accepted⟩
        change Probability.ReturnedDeclaredFactor model (firstPresent _ _)
        rw [absent]
        exact ih later

/-- A positive number of actual source visits preserves the original total even-modulus route. -/
lemma sourceResults_of_even {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (even : Even N)
    (head : SourceOutcome N) (rest : List (SourceOutcome N)) :
    Probability.ReturnedDeclaredFactor model
      (sourceResults (Probability.Input.ofSemiprimeModel model) (head :: rest)) := by
  have actual : sourceResult (Probability.Input.ofSemiprimeModel model) head =
      FactorRecovery.encodeOutput (N := N) (some 2) :=
    congrArg FactorRecovery.encodeOutput
      (FactorRecovery.outputOfRecovered_eq_some_two_of_even model even _ _)
  have declared : Probability.ReturnedDeclaredFactor model
      (sourceResult (Probability.Input.ofSemiprimeModel model) head) := by
    rcases sourceResult_declared_or_none model head with result | absent
    · exact result
    · rw [actual] at absent
      contradiction
  rw [sourceResults, firstPresent_of_declared model _ _ declared]
  exact declared

/-- The original source retry event is contained in success of the native first-present result. -/
lemma sourceResults_successfulSamples {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (samples : List.Vector (SourceOutcome N) (retryCount N budget))
    (successful : Probability.SuccessfulSamples model budget samples) :
    Probability.ReturnedDeclaredFactor model
      (sourceResults (Probability.Input.ofSemiprimeModel model) samples.toList) := by
  by_cases even : Even N
  · have nonempty : samples.toList ≠ [] := by
      intro empty
      have length := samples.2
      change samples.toList.length = retryCount N budget at length
      rw [empty] at length
      have positive := retryCount_pos N budget
      simp only [List.length_nil] at length
      omega
    cases listed : samples.toList with
    | nil => exact False.elim (nonempty listed)
    | cons head rest => exact sourceResults_of_even model even head rest
  · apply sourceResults_of_contains_good model samples.toList
    simpa only [Probability.SuccessfulSamples, if_neg even] using successful

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
