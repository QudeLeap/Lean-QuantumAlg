/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Independent modular translation on a finite qubit word

This metadata-free operator is specified by finite addition alone. Exact
constant adders realize the same phase-sensitive target regardless of their
choice of gates or borrowed storage [D00, paper.tex:352-365].
-/

namespace QuantumAlg.MAU.Addition

noncomputable section

private def translationPermutation (width constant : Nat) : Equiv.Perm (Fin (2 ^ width)) :=
  letI : NeZero (2 ^ width) := ⟨Nat.ne_of_gt (Nat.two_pow_pos width)⟩
  Equiv.addRight (⟨constant % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩ : Fin (2 ^ width))

private theorem translationPermutation_apply (width constant : Nat) (input : Fin (2 ^ width)) :
    translationPermutation width constant input =
      ⟨(input.val + constant) % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩ := by
  apply Fin.ext
  change (input.val + constant % 2 ^ width) % 2 ^ width =
    (input.val + constant) % 2 ^ width
  exact Nat.add_mod_mod _ _ _

/-- Exact finite-word translation without circuit, layout or resource metadata. -/
public def wordTranslation (width constant : Nat) : UnitaryOperator (Qubits width) :=
  UnitaryOperator.ofPerm (translationPermutation width constant).symm

/-- Exact arithmetic basis action; its phase is preserved before coherent control. -/
public theorem wordTranslation_ket (width constant : Nat) (input : Fin (2 ^ width)) :
    (wordTranslation width constant).apply (NormalizedVector.ket input) =
      NormalizedVector.ket (R := Qubits width)
        ⟨(input.val + constant) % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩ := by
  rw [wordTranslation, UnitaryOperator.ofPerm_apply_ket]
  exact congrArg NormalizedVector.ket (translationPermutation_apply width constant input)

end

end QuantumAlg.MAU.Addition
