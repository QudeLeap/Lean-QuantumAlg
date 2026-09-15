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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem three_classical_restore {input₀ output₀ input₁ output₁ input₂ output₂ : CShape}
    (first : ClassicalOp input₀ output₀ ctx ctx) (second : ClassicalOp input₁ output₁ ctx ctx)
    (third : ClassicalOp input₂ output₂ ctx ctx) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (.classical first) (.seq (.classical second) (.classical third))).BorrowedRestored
      Reference state
      ((Circuit.seq (.classical first) (.seq (.classical second) (.classical third))).execute
        Reference state) :=
  Circuit.borrowedRestored_seq (.classical first) (.seq (.classical second) (.classical third))
    state (Circuit.borrowedRestored_classical first state)
    (Circuit.borrowedRestored_seq (.classical second) (.classical third) _
      (Circuit.borrowedRestored_classical second _) (Circuit.borrowedRestored_classical third _))

/-- Both complete range and divisibility blocks restore the original full borrowed interface. -/
theorem nativeQuadratic_check_borrowedRestored (refs : Check.Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Check.code refs).BorrowedRestored Reference state
      ((Check.code refs).execute Reference state) :=
  Circuit.borrowedRestored_seq (FactorRange.code (Check.rangeRefs refs))
    (Divisibility.code refs.divisor) state
    (three_classical_restore (FactorRange.lowerOp (Check.rangeRefs refs))
      (FactorRange.upperOp (Check.rangeRefs refs)) (FactorRange.combineOp (Check.rangeRefs refs))
      Reference state)
    (three_classical_restore (Divisibility.remainderOp refs.divisor)
      (Divisibility.equalityOp refs.divisor) (Divisibility.combineOp refs.divisor) Reference _)

/-- Complete candidate-pair checking and selection returns every borrowed joint state exactly. -/
theorem nativeQuadratic_pair_borrowedRestored (refs : Pair.Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Pair.code refs).BorrowedRestored Reference state
      ((Pair.code refs).execute Reference state) :=
  Circuit.borrowedRestored_seq (Check.code refs.first)
    (.seq (Check.code refs.second)
      (Selection.code (Pair.selectedInputs refs.first) (Pair.selectedInputs refs.second)
        refs.selection)) state
    (nativeQuadratic_check_borrowedRestored refs.first Reference state)
    (Circuit.borrowedRestored_seq (Check.code refs.second)
      (Selection.code (Pair.selectedInputs refs.first) (Pair.selectedInputs refs.second)
        refs.selection) _
      (nativeQuadratic_check_borrowedRestored refs.second Reference _)
      (Selection.nativeQuadratic_selection_borrowedRestored
        (Pair.selectedInputs refs.first) (Pair.selectedInputs refs.second)
        refs.selection Reference _))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
