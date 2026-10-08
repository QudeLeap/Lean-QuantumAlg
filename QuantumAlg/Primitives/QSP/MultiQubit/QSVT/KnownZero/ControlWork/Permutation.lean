/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork
import all QuantumAlg.Components.QubitPrimitive.Basis

/-!
# Full permutation of the restored final-control flip

The two X masks restore the final original control. Only the phase coordinate
is toggled, and only when that control was zero. Every other coordinate is
preserved without assumptions on its value or correlations.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

private def physical (k n : Nat) : QubitLayout (1 + (k + (1 + n))) :=
  ⟨Fin.val, Fin.val_injective⟩

private def maskPermutation (k n : Nat) : Equiv.Perm (layout k n).Basis :=
  QubitPrimitive.nativeAmbientPermutation (physical k n) (.x (lastControl k n))

private def cnotPermutation (k n : Nat) : Equiv.Perm (layout k n).Basis :=
  QubitPrimitive.nativeAmbientPermutation (physical k n)
    (.cnot (lastControl k n) (0 : Fin (1 + (k + (1 + n)))) (lastControl_ne_phase k n))

/-- Row permutation of the three actual native gates. -/
def lastPermutation (k n : Nat) : Equiv.Perm (layout k n).Basis :=
  ((maskPermutation k n).trans (cnotPermutation k n)).trans (maskPermutation k n)

/-- The complete native operator is the permutation of its addressed X, CNOT and X word. -/
theorem controlWork_lastFlip_matrix (k n : Nat) (oracles : OracleModel) :
    (lastFlip k n oracles).matrix = UnitaryOperator.ofPerm (lastPermutation k n) := by
  rw [lastFlip, UnitaryCircuit.seq_matrix, UnitaryCircuit.seq_matrix]
  change (QubitPrimitive.nativeApplication (physical k n) (.x (lastControl k n))).operator *
    ((QubitPrimitive.nativeApplication (physical k n)
      (.cnot (lastControl k n) (0 : Fin (1 + (k + (1 + n))))
        (lastControl_ne_phase k n))).operator *
      (QubitPrimitive.nativeApplication (physical k n) (.x (lastControl k n))).operator) = _
  repeat rw [QubitPrimitive.nativeApplication_operator_ofPerm]
  rw [UnitaryOperator.ofPerm_mul, UnitaryOperator.ofPerm_mul]
  rfl

/-- The masks restore the last control and toggle only the phase coordinate on its zero branch. -/
theorem controlWork_lastPermutation_coordinates (k n : Nat)
    (basis : Fin (1 + (k + (1 + n))) → Fin 2) :
    lastPermutation k n basis = Function.update basis 0
      (if basis (lastControl k n) = 0 then Fin.add (n := 2) (basis 0) 1 else basis 0) := by
  change QubitPrimitive.nativeAmbientPermutation (physical k n) (.x (lastControl k n))
    (QubitPrimitive.nativeAmbientPermutation (physical k n)
      (.cnot (lastControl k n) (0 : Fin (1 + (k + (1 + n)))) (lastControl_ne_phase k n))
      (QubitPrimitive.nativeAmbientPermutation (physical k n) (.x (lastControl k n)) basis)) = _
  repeat rw [QubitPrimitive.nativeAmbientPermutation_apply]
  simp only [QubitPrimitive.basisAction]
  funext index
  have distinct := lastControl_ne_phase k n
  by_cases phase : index = (0 : Fin (1 + (k + (1 + n))))
  · subst index
    simp only [Function.update_self, Function.update_of_ne distinct.symm,
      Function.update_of_ne distinct]
    generalize basis (lastControl k n) = control
    generalize basis 0 = target
    fin_cases control <;> fin_cases target <;> rfl
  · by_cases control : index = lastControl k n
    · subst index
      simp only [Function.update_self, Function.update_of_ne distinct]
      generalize basis (lastControl k n) = value
      fin_cases value <;> rfl
    · simp [Function.update_of_ne, phase, control]

private def bits (k n : Nat) (basis : (layout k n).Basis) :
    Fin (1 + (k + (1 + n))) → Fin 2 := basis

private theorem bits_injective (k n : Nat) : Function.Injective (bits k n) := by
  intro left right same
  exact same

private theorem lastPermutation_bits (k n : Nat) (basis : (layout k n).Basis) :
    bits k n (lastPermutation k n basis) = Function.update (bits k n basis) 0
      (if bits k n basis (lastControl k n) = 0 then
        Fin.add (n := 2) (bits k n basis 0) 1 else bits k n basis 0) :=
  controlWork_lastPermutation_coordinates k n basis

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
