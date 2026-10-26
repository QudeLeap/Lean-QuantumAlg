/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic

/-!
# Kernel checks of exact and approximate rotation certificates

The thirty-letter example is a coarse numerical calibration at index three,
not a high-precision synthesis result. The singleton T example is deliberately
rejected because the target retains both half-angle phases.
-/

@[expose] public section

namespace QuantumAlg.CliffordT

/-- A nonempty thirty-letter identity word for exercising the numerical branch. -/
def checkerThirtyWord : List Letter := List.replicate 16 .t ++ List.replicate 14 .h

lemma checkerThirtyWord_length : checkerThirtyWord.length = 30 := by decide +kernel

lemma check_rejects_single_t : check [.t] 3 (1 / 1000) = false := by decide +kernel

lemma check_rejects_negative_tolerance : check [] 3 (-1) = false := by decide +kernel

lemma check_accepts_exact_two : check [.h, .s, .s, .s, .h, .s, .s, .s, .h] 2 0 = true := by
  decide +kernel

lemma check_accepts_thirty_word : check checkerThirtyWord 3 (3 / 5) = true := by decide +kernel

end QuantumAlg.CliffordT
