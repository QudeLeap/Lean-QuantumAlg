/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Diagonal

/-!
# Full diagonal semantics of the native three-bit parity-phase word

Seven phase factors combine to one phase on the all-one branch. Every
computational coordinate is restored by the six actual CNOT occurrences.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

/-- The complete native parity word is an exact three-bit controlled phase. -/
theorem toffoliExpansion_phaseWord_matrix (oracles : OracleModel) (angle : ℝ) :
    ((phaseWord oracles angle).matrix : HilbertOperator layout.register) =
      Matrix.diagonal (fun basis =>
        if bits basis 0 = 1 ∧ bits basis 1 = 1 ∧ bits basis 2 = 1 then
          Complex.exp (((4 * angle : ℝ) : ℂ) * Complex.I) else 1) := by
  simp only [phaseWord, UnitaryCircuit.seq_matrix, Submonoid.coe_mul,
    phase_weighted, cnot_weighted]
  repeat rw [weighted_mul]
  refine (weighted_eq_diagonal _ _ ?_).trans ?_
  · intro basis
    simp only [Equiv.trans_apply, Equiv.refl_apply]
    rw [permutation_involutive, target_permutations_commute,
      permutation_involutive, permutation_involutive]
  · apply congrArg Matrix.diagonal
    funext row
    simp only [Equiv.trans_apply, Equiv.refl_apply, word_permutations_cancel]
    repeat rw [permutation_apply]
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
      Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2), one_mul, mul_one]
    generalize bits row 0 = a
    generalize bits row 1 = b
    generalize bits row 2 = c
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [weight, ← Complex.exp_add]
    all_goals congr 1; ring_nf

end
end QuantumAlg.Gate.Toffoli
