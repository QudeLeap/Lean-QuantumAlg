/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Candidate.Prefix
import all QuantumAlg.Util.Classical.OrderRecovery

/-!
# Exact arithmetic of the actual Euclidean candidate prefix

Both total division outputs fit their original numerator width. The two
continuant operations implement the declared wrapping recurrence exactly;
the existing source cursor's candidate bound removes that wrapping on real
continued-fraction visits. No mathematical cursor is a runtime instruction.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

/-- A quotient cannot overflow the original numerator width. -/
theorem nativeCursorDivision_first_exact {width : Nat}
    (numerator denominator : CShape.Word width) :
    (CShape.divRem width width (.product numerator denominator)).first.toNat =
      numerator.toNat / denominator.toNat := by
  change (numerator.toNat / denominator.toNat) % 2 ^ width = _
  exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt numerator.toNat_lt)

/-- A total remainder also fits that width, including the interpreter's zero-divisor case. -/
theorem nativeCursorDivision_second_exact {width : Nat}
    (numerator denominator : CShape.Word width) :
    (CShape.divRem width width (.product numerator denominator)).second.toNat =
      numerator.toNat % denominator.toNat := by
  change (numerator.toNat % denominator.toNat) % 2 ^ width = _
  exact Nat.mod_eq_of_lt ((Nat.mod_le _ _).trans_lt numerator.toNat_lt)

/-- The actual multiply and addition implement precisely one wrapped continuant recurrence. -/
theorem nativeContinuant_value_toNat {width : Nat}
    (quotient previous older : CShape.Word width) :
    (continuantValue quotient previous older).toNat =
      (quotient.toNat * previous.toNat + older.toNat) % 2 ^ width := by
  change ((quotient.toNat * previous.toNat) % 2 ^ width + older.toNat) % 2 ^ width = _
  exact Nat.mod_add_mod _ _ _

/-- A source-proved fitted continuant is represented without truncation by those same operations. -/
theorem nativeContinuant_value_exact {width : Nat}
    (quotient previous older : CShape.Word width)
    (fits : quotient.toNat * previous.toNat + older.toNat < 2 ^ width) :
    (continuantValue quotient previous older).toNat =
      quotient.toNat * previous.toNat + older.toNat := by
  rw [nativeContinuant_value_toNat]
  exact Nat.mod_eq_of_lt fits

/-- The stored quotient and predecessors materialize the same source cursor candidate. -/
theorem nativeCandidatePrefix_cursor {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (previousFree : division.key ∉ previous.storageKeys)
    (olderFree : division.key ∉ older.storageKeys) (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (numeratorEq : (store.read numerator).toNat = cursor.numerator)
    (denominatorEq : (store.read denominator).toNat = cursor.denominator)
    (previousEq : (store.read previous).toNat = cursor.previous.denominator)
    (olderEq : (store.read older).toNat = cursor.older.denominator)
    (candidateFits : cursor.candidate.denominator < 2 ^ width) :
    (((candidatePrefixStep numerator denominator previous older division candidate store).1).read
      (cellRead candidate)).toNat = cursor.candidate.denominator := by
  rw [nativeCandidatePrefix_result _ _ _ _ _ _ previousFree olderFree,
    nativeContinuant_value_toNat, nativeCursorDivision_first_exact,
    numeratorEq, denominatorEq, previousEq, olderEq]
  exact Nat.mod_eq_of_lt candidateFits

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
