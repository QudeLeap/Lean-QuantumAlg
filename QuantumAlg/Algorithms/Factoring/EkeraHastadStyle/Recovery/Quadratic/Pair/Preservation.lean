/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Pair

/-!
# Full borrowed restoration of both checks and left-priority selection

The six native instructions in each check and the two actual selector
executions restore every borrowed classical-quantum-reference correlation.
No absence of borrowed quantum wires or initial scratch value is assumed.
The proofs follow the actual sequence syntax, including both stored branches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines.NumberTheory

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma three_classical_restore {input₀ output₀ input₁ output₁ input₂ output₂ : CShape}
    (first : ClassicalOp input₀ output₀ ctx ctx) (second : ClassicalOp input₁ output₁ ctx ctx)
    (third : ClassicalOp input₂ output₂ ctx ctx) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (BitWord.instruction (execution := model) first) (.seq (BitWord.instruction
      (execution := model) second) (BitWord.instruction (execution := model)
      third))).BorrowedRestored
      Reference state
      ((Circuit.seq (BitWord.instruction (execution := model) first) (.seq (BitWord.instruction
        (execution := model) second) (BitWord.instruction (execution := model) third))).execute
          environment
        Reference state) :=
  Circuit.borrowedRestored_seq
    (environment := environment) (BitWord.instruction (execution := model) first) (.seq
    (BitWord.instruction (execution := model) second) (BitWord.instruction (execution := model)
    third))
    state (Circuit.borrowedRestored_classical (environment := environment) _ state)
    (Circuit.borrowedRestored_seq
      (environment := environment) (BitWord.instruction (execution := model) second)
      (BitWord.instruction (execution := model) third) _
      (Circuit.borrowedRestored_classical
        (environment := environment) _ _) (Circuit.borrowedRestored_classical (environment :=
        environment) _ _))

/-- Both complete range and divisibility blocks restore the original full borrowed interface. -/
lemma nativeQuadratic_check_borrowedRestored (refs : Check.Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Check.code (model := model) refs).BorrowedRestored Reference state
      ((Check.code (model := model) refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq
    (environment := environment) (FactorRange.code (model := model) (Check.rangeRefs refs))
    (Divisibility.code (model := model) refs.divisor) state
    (three_classical_restore (FactorRange.lowerOp (Check.rangeRefs refs))
      (FactorRange.upperOp (Check.rangeRefs refs)) (FactorRange.combineOp (Check.rangeRefs refs))
      Reference state)
    (three_classical_restore (Divisibility.remainderOp refs.divisor)
      (Divisibility.equalityOp refs.divisor) (Divisibility.combineOp refs.divisor) Reference _)

/-- Complete candidate-pair checking and selection returns every borrowed joint state exactly. -/
lemma nativeQuadratic_pair_borrowedRestored (refs : Pair.Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Pair.code (model := model) refs).BorrowedRestored Reference state
      ((Pair.code (model := model) refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) (Check.code (model := model) refs.first)
    (.seq (Check.code (model := model) refs.second)
      (Selection.code (model := model) (Pair.selectedInputs refs.first) (Pair.selectedInputs
        refs.second)
        refs.selection)) state
    (nativeQuadratic_check_borrowedRestored refs.first Reference state)
    (Circuit.borrowedRestored_seq
      (environment := environment) (Check.code (model := model) refs.second)
      (Selection.code (model := model) (Pair.selectedInputs refs.first) (Pair.selectedInputs
        refs.second)
        refs.selection) _
      (nativeQuadratic_check_borrowedRestored refs.second Reference _)
      (Selection.nativeQuadratic_selection_borrowedRestored
        (Pair.selectedInputs refs.first) (Pair.selectedInputs refs.second)
        refs.selection Reference _))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
