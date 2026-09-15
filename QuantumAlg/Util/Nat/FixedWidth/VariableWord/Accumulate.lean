/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Accumulate

/-!
# Three-word variable modular accumulation

Binary selection on the first input chooses full binary MACs of the second
input with compile-time coefficients `2^i`. The resulting bit-pair sum is
the product of both original inputs. This purely finite arithmetic uses
the controlled-add recurrence [VBE95, 9511018.tex:333-367] and has no parity,
unit-input or extra clean-word premise.
-/

namespace QuantumAlg.Nat.FixedWidth

open QuantumAlg.Nat.FixedWidth.ModularAccumulate

/-- One first-input bit selects a complete second-input MAC. -/
def variableWordStep {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) (index : Nat) : Fin (2 ^ width) :=
  if first.val.testBit index then
    accumulateWordPrefix modulus (2 ^ index) second target width else target

/-- The increasing-bit arithmetic prefix on the unchanged two inputs. -/
def variableWordPrefix {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) : Nat → Fin (2 ^ width)
  | 0 => target
  | count + 1 => variableWordStep modulus first second
      (variableWordPrefix modulus first second target count) count

theorem variableWordStep_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) (index : Nat)
    (valid : target.val < modulus.val) :
    (variableWordStep modulus first second target index).val < modulus.val := by
  unfold variableWordStep
  split_ifs
  · exact accumulateWordPrefix_valid modulus (2 ^ index) second target valid width
  · exact valid

theorem variableWordPrefix_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) (count : Nat)
    (valid : target.val < modulus.val) :
    (variableWordPrefix modulus first second target count).val < modulus.val := by
  induction count with
  | zero => exact valid
  | succ count inductionHypothesis =>
      exact variableWordStep_valid modulus first second _ count inductionHypothesis

theorem variableWordPrefix_val {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) (count : Nat)
    (valid : target.val < modulus.val) :
    (variableWordPrefix modulus first second target count).val =
      accumulateSelected modulus.val second.val first.val target.val count := by
  induction count with
  | zero => exact (Nat.mod_eq_of_lt valid).symm
  | succ count inductionHypothesis =>
      have canonical := variableWordPrefix_valid modulus first second target count valid
      change (variableWordStep modulus first second
        (variableWordPrefix modulus first second target count) count).val = _
      rw [accumulateSelected_succ, selectedBitContribution_eq_if]
      by_cases selected : first.val.testBit count = true
      · rw [variableWordStep, if_pos selected, if_pos selected,
          accumulateWordPrefix_full modulus (2 ^ count) second _ canonical,
          inductionHypothesis, stageConstantResidue]
        simp only [Nat.add_mod, Nat.mod_mod, Nat.mul_comm]
      · rw [variableWordStep, if_neg selected, if_neg selected, Nat.add_zero,
          ← inductionHypothesis, Nat.mod_eq_of_lt canonical]

/-- The full bit-pair sum is the modular product of the two original inputs. -/
theorem variableWordPrefix_full {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) (valid : target.val < modulus.val) :
    (variableWordPrefix modulus first second target width).val =
      (target.val + first.val * second.val) % modulus.val := by
  rw [variableWordPrefix_val modulus first second target width valid,
    accumulateSelected_eq_add_mul_mod_of_lt_two_pow first.isLt, Nat.mul_comm second.val]

/-- All noncanonical target labels are fixed, independently of both inputs. -/
theorem variableWordPrefix_outside {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) (count : Nat)
    (outside : modulus.val ≤ target.val) :
    variableWordPrefix modulus first second target count = target := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [variableWordPrefix, inductionHypothesis]
      unfold variableWordStep
      split_ifs
      · exact accumulateWordPrefix_outside modulus (2 ^ count) second target outside width
      · rfl

end QuantumAlg.Nat.FixedWidth
