/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.Complex

/-!
# Mathematical addressed controlled phase

The original computational-basis operator fixes the phase on the selected
wire values independently of the native realization and its accounting.
It supplies the target for an actual default-model gate expansion.
-/

namespace QuantumAlg

noncomputable section

/-- Computational-basis phase contributed by one addressed controlled-phase
rotation.  The phase is present exactly when both addressed wires are set. -/
public def qftControlledPhaseFactor {n : Nat} (control target : Fin n)
    (angle : Real) (basis : Fin (2 ^ n)) : Complex :=
  if basis.val.testBit (WireAddress.bitIndex control).val &&
      basis.val.testBit (WireAddress.bitIndex target).val then
    Complex.exp (angle * Complex.I)
  else 1

/-- Certified addressed controlled-phase operator. -/
public def qftControlledPhaseOperator {n : Nat} (control target : Fin n)
    (angle : Real) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofMatrix
    (Matrix.diagonal (qftControlledPhaseFactor control target angle)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl]
        simp only [Matrix.star_apply]
        rw [Finset.sum_eq_single i]
        · simp only [Matrix.diagonal_apply_eq]
          by_cases hphase :
              i.val.testBit (WireAddress.bitIndex control).val &&
                i.val.testBit (WireAddress.bitIndex target).val
          · simp only [qftControlledPhaseFactor, hphase, if_pos]
            change Complex.exp ((angle : Complex) * Complex.I) *
                starRingEnd Complex
                  (Complex.exp ((angle : Complex) * Complex.I)) = 1
            rw [conj_exp_I, exp_I_mul_exp_neg_I]
          · simp [qftControlledPhaseFactor, hphase]
        · intro k _ hki
          rw [Matrix.diagonal_apply_ne _ (Ne.symm hki), zero_mul]
        · simp
      · rw [Matrix.mul_apply, Matrix.one_apply, if_neg hij]
        simp only [Matrix.star_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hik : i = k
        · subst k
          rw [Matrix.diagonal_apply_eq,
            Matrix.diagonal_apply_ne _ (Ne.symm hij)]
          simp
        · rw [Matrix.diagonal_apply_ne _ hik, zero_mul])

end

end QuantumAlg
