/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Construction
import all QuantumAlg.Components.QubitPrimitive.Basis

/-!
# Exact addressed permutations in the Toffoli phase word

The CNOTs preserve both original controls, except for the explicitly restored
control-pair parity computation. The two target-parity permutations commute.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

private def physical : QubitLayout 3 := ⟨Fin.val, Fin.val_injective⟩

private def permutation (control target : Fin 3) (distinct : control ≠ target) :
    Equiv.Perm layout.register.Index :=
  QubitPrimitive.nativeAmbientPermutation physical (.cnot control target distinct)

private lemma cnot_matrix (oracles : OracleModel) (control target : Fin 3)
    (distinct : control ≠ target) (environment : oracles.Interpretation) :
    ((cnot oracles control target distinct).matrix environment) =
      UnitaryOperator.ofPerm (permutation control target distinct) := by
  change (QubitPrimitive.nativeApplication physical (.cnot control target distinct)).operator = _
  exact QubitPrimitive.nativeApplication_operator_ofPerm physical (.cnot control target distinct)

private def bits (basis : layout.register.Index) : Fin 3 → Fin 2 := basis

private lemma bits_injective : Function.Injective bits := fun _ _ same => same

private lemma permutation_apply (control target : Fin 3) (distinct : control ≠ target)
    (basis : layout.register.Index) :
    bits (permutation control target distinct basis) =
      Function.update (bits basis) target (bits basis control + bits basis target) :=
  QubitPrimitive.nativeAmbientPermutation_apply physical (.cnot control target distinct) basis

private lemma permutation_involutive (control target : Fin 3) (distinct : control ≠ target) :
    Function.Involutive (permutation control target distinct) := by
  intro basis
  apply bits_injective
  rw [permutation_apply, permutation_apply]
  funext index
  by_cases same : index = target
  · subst index
    simp only [Function.update_self, Function.update_of_ne distinct]
    generalize bits basis control = first
    generalize bits basis target = second
    fin_cases first <;> fin_cases second <;> rfl
  · simp [Function.update_of_ne, same]

private lemma target_permutations_commute (basis : layout.register.Index) :
    permutation 0 2 (by decide) (permutation 1 2 (by decide) basis) =
      permutation 1 2 (by decide) (permutation 0 2 (by decide) basis) := by
  apply bits_injective
  repeat rw [permutation_apply]
  funext index
  by_cases same : index = (2 : Fin 3)
  · subst index
    simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
      Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
    exact add_left_comm _ _ _
  · simp [Function.update_of_ne, same]

private lemma word_permutations_cancel (basis : layout.register.Index) :
    permutation 0 1 (by decide) (permutation 0 1 (by decide)
      (permutation 0 2 (by decide) (permutation 1 2 (by decide)
        (permutation 0 2 (by decide) (permutation 1 2 (by decide) basis))))) = basis := by
  rw [permutation_involutive, target_permutations_commute,
    permutation_involutive, permutation_involutive]

end
end QuantumAlg.Gate.Toffoli
