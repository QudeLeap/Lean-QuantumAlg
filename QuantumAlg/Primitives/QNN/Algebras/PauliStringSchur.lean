/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra
public import QuantumAlg.Primitives.QNN.Interface.SchurGeneric
public import QuantumAlg.Primitives.QNN.Algebras.PauliSchurFamily

/-!
# The Schur identity `(g⊗g)^g = span{C}` for `su(2ⁿ)`

Discharges the Schur one-dimensionality hypothesis (H2) for the full `n`-qubit Pauli-string algebra
`su(2ⁿ)` through the parametrized Pauli-family solver (`SchurSolver`): the family's string set is
all non-identity labels, so the four bespoke solver inputs are immediate — the identity is excluded
by definition, the product of an anticommuting pair is nonzero, separation is the full symplectic
non-degeneracy, and connectivity is the unrestricted anticommutation-graph constancy. The
closed-form adjoint matrix, its diagonal square, the separating eigenvalue, and the assembly into
`(g⊗g)^g = span{C}` are all supplied family-independently by `PauliSchurFamily.schur`.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### The Schur identity for `su(2ⁿ)` -/

/-- **The `su(2ⁿ)` family as a `PauliSchurFamily`.** The string set is all non-identity labels,
so the four bespoke inputs are immediate: the set excludes the identity by definition, the
product of an anticommuting pair is nonzero (anticommuting strings are distinct), separation is
the full symplectic non-degeneracy, and connectivity is the unrestricted anticommutation-graph
constancy. -/
noncomputable def suSchurFamily (n : ℕ) : PauliSchurFamily n (suHermBasis n) where
  mem s := s ≠ 0
  equiv := nzEquiv n
  B_eq _ := rfl
  not_mem_zero h := h rfl
  xor_closed := by
    intro a c ha hc hω he
    have hac : a = c := by
      have hh := pauliXor_self_inv a c
      rw [he, pauliXor_zero_right] at hh
      exact hh
    rw [hac, pauliOmega_self_zero] at hω
    exact one_ne_zero hω.symm
  sep_witness := by
    intro a c _ _ hac
    have hd : pauliXor a c ≠ 0 := fun he => hac (by
      have hh := pauliXor_self_inv a c
      rw [he, pauliXor_zero_right] at hh
      exact hh)
    obtain ⟨s, hs⟩ := pauliOmega_nondeg hd
    exact ⟨s, fun h0 => one_ne_zero (by rw [h0, pauliOmega_zero_left] at hs; exact hs.symm), hs⟩
  conn_const := by
    intro T h x y hx hy
    refine pauliAnticomm_const (fun a c hac => ?_) hx hy
    have ha0 : a ≠ 0 := fun h0 => one_ne_zero (by
      rw [h0, pauliOmega_zero_left] at hac; exact hac.symm)
    have hc0 : c ≠ 0 := fun h0 => one_ne_zero (by
      rw [h0, pauliOmega_comm, pauliOmega_zero_left] at hac; exact hac.symm)
    exact h a c ha0 hc0 hac

/-- **The Schur identity `(g⊗g)^g = span{C}` for `su(2ⁿ)`** (general `n`). Discharges the Schur
hypothesis (H2) for the full `n`-qubit Pauli-string algebra: the hard inclusion `(g⊗g)^g ≤ span{C}`
is genuinely proved from the symplectic Pauli structure, with `gTensorGInvariant` the genuine
`adCommutantGG ⊓ gTensorG`. [RBS+23] -/
theorem suHermBasis_schur (n : ℕ) :
    gTensorGInvariant (suHermBasis n) = Submodule.span ℂ {(suHermBasis n).casimir} :=
  (suSchurFamily n).schur

/-- **Schur-discharged consistency witness for `su(2ⁿ)`.** With the Schur identity (H2) discharged
by `suHermBasis_schur`, the diagonal witness sequence has exponentially vanishing variance. The
finite-group twirl hypothesis (H1) is not discharged here. [MBS+18, maintext.tex:148] -/
theorem suN_hasBarrenPlateau_schurDischarged :
    HasBarrenPlateau (fun n => (suSM n (suHermBasis_schur (n + 1))).variance) :=
  suN_hasBarrenPlateau_ofSchur (fun n => suHermBasis_schur (n + 1))

end QuantumAlg
