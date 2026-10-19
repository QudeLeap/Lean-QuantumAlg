/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow
import all QuantumAlg.Primitives.QFT.Mathematics.PhaseFactors
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# Binary exponents in the ordered QPE query ladder

Summing the original little-endian binary weights recovers each phase label
[Lin22, phaseestimation.tex:514-523].
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

/-- Exponent contributed by one repeated binary-weight stage on one phase
basis label. -/
def stageExponent {t : Nat} (stage : Fin t) (a : Fin (2 ^ t)) : Nat :=
  2 ^ stage.val * (a.val.testBit stage.val).toNat

/-- Pointwise exponent accumulator matching the right-fold execution order of
the indexed circuit product. -/
def stageExponentFold {t : Nat} (stages : List (Fin t))
    (initial : Fin (2 ^ t) → Nat) : Fin (2 ^ t) → Nat :=
  stages.foldl
    (fun accumulated stage a => stageExponent stage a + accumulated a)
    initial

lemma stageExponentFold_apply {t : Nat} (stages : List (Fin t))
    (initial : Fin (2 ^ t) → Nat) (a : Fin (2 ^ t)) :
    stageExponentFold stages initial a =
      initial a + (stages.map (fun stage => stageExponent stage a)).sum := by
  induction stages generalizing initial with
  | nil => simp [stageExponentFold]
  | cons stage stages ih =>
      rw [stageExponentFold, List.foldl_cons]
      change stageExponentFold stages
          (fun a => stageExponent stage a + initial a) a = _
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm]

lemma stageExponentFold_all {t : Nat} (a : Fin (2 ^ t)) :
    stageExponentFold (List.ofFn fun stage : Fin t => stage)
        (fun _ => 0) a = a.val := by
  rw [stageExponentFold_apply]
  simp only [zero_add]
  rw [show
      (List.ofFn fun stage : Fin t => stage).map
          (fun stage => stageExponent stage a) =
        List.ofFn (fun stage : Fin t => stageExponent stage a) by
    exact (List.ofFn_comp' (fun stage : Fin t => stage)
      (fun stage => stageExponent stage a)).symm]
  rw [List.sum_ofFn]
  simp_rw [stageExponent, Nat.mul_comm]
  rw [← natOfBits_eq_sum]
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt a.isLt]

end QuantumAlg.QuantumPhaseEstimation.Native
