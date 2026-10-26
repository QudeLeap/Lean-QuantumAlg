/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Construction
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Pool
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Primitives.ZReset.Resources

/-!
# Independent complete allowances for the actual measured recycling schedule

The native coordinates are separate width-only formulas. Every arithmetic
vent, paid H/reset/Z and retained control measurement is charged. The two
exponent streams remain sequential and retain all prior feedback
opportunities [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources

noncomputable section

open Execution

/-- One existing single-qubit native coordinate in the actual BitWord execution model. -/
def oneQubit : ResourcePool model := ResourcePool.singleton (.gate .singleQubit)

/-- One actual physical control measurement into its retained output cell. -/
def oneMeasurement : ResourcePool model := ResourcePool.singleton (.measurement (2 : ℕ+))

/-- Independent complete native allowance for one actual measured modular multiplication. -/
def arithmeticBudget (width : Nat) : ResourcePool model :=
  MAU.Multiplication.Gidney.Measured.Layout.multiplicationBudget .empty BitWord.model .empty width

/-- Two actual H gates, possible control-reset X and actual MZ accompany the measured arithmetic. -/
def baseBudget (width : Nat) : ResourcePool model :=
  arithmeticBudget width + 2 • oneQubit + oneQubit + oneMeasurement

/-- A chronological stage additionally pays at most one phase for each earlier stored result. -/
def stageBudget (width position : Nat) : ResourcePool model :=
  baseBudget width + position • oneQubit

/-- Every preceding-bit feedback opportunity in the original chronological suffix. -/
def feedbackWork (remaining position : Nat) : Nat :=
  remaining * position + remaining.choose 2

/-- Width-only complete native allowance for the original source suffix. -/
def suffixBudget (width remaining position : Nat) : ResourcePool model :=
  remaining • baseBudget width + feedbackWork remaining position • oneQubit

/-- Both original exponent streams retain every measured stage and triangular feedback charge. -/
def memberBudget (m ell width : Nat) : ResourcePool model :=
  resultBits m ell • baseBudget width + ((ell + m).choose 2 + ell.choose 2) • oneQubit

/-- Default quantum duration charges native arithmetic and three control gates per stage. -/
def stageTime (width position : Nat) : Nat :=
  (160 * width ^ 2 - 255 * width) + 3 + position

def suffixTime (width remaining position : Nat) : Nat :=
  remaining * ((160 * width ^ 2 - 255 * width) + 3) + feedbackWork remaining position

def memberTime (m ell width : Nat) : Nat :=
  resultBits m ell * ((160 * width ^ 2 - 255 * width) + 3) +
    ((ell + m).choose 2 + ell.choose 2)

/-- The suffix recurrence retains each actual preceding-bit feedback opportunity. -/
lemma measuredFeedbackWork_succ (remaining position : Nat) :
    feedbackWork (remaining + 1) position = position + feedbackWork remaining (position + 1) := by
  have choose : (remaining + 1).choose 2 = remaining + remaining.choose 2 := by
    simpa using Nat.choose_succ_succ remaining 1
  simp only [feedbackWork, choose, Nat.succ_mul, Nat.mul_add, Nat.mul_one]
  omega

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources
