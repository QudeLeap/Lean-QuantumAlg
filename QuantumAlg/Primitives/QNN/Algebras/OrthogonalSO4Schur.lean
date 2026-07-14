/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.OrthogonalSO4

/-!
# The two-Casimir invariant space for reductive `so(4)`

This module turns the exceptional `so(4) = su(2) ⊕ su(2)` case into a concrete
invariant-space theorem.  The full six-element basis is ordered as the `A` Pauli
triangle followed by the commuting `B` triangle.  Its doubled-adjoint invariant
space is exactly the span of the two per-ideal Casimirs, so it has complex
finrank `2`; consequently the single-Casimir Schur identity for the full
reductive algebra is false.
-/

@[expose] public section

namespace QuantumAlg
open Matrix
open scoped Kronecker
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The ordered six two-qubit Pauli labels for the two `so(4)` ideals. -/
def so4Label : Fin 6 → (Fin 2 → Fin 4) :=
  ![so4A.t 0, so4A.t 1, so4A.t 2, so4B.t 0, so4B.t 1, so4B.t 2]

/-- The normalized Hermitian matrices associated with the six `so(4)` labels. -/
noncomputable def so4B6 (i : Fin 6) : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  rtNinv 2 • pauliMat (so4Label i)

theorem so4Label_inj : Function.Injective so4Label := by decide

/-- The concrete generator set given by the range of the six normalized matrices. -/
noncomputable def so4FullGens : Set (Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ) :=
  Set.range so4B6

theorem so4B6_mem_span (i : Fin 6) :
    so4B6 i ∈ Submodule.span ℂ (Set.range so4B6) :=
  Submodule.subset_span ⟨i, rfl⟩

theorem so4Label_xor_mem_of_anticomm {i j : Fin 6}
    (hω : pauliOmega (so4Label i) (so4Label j) = 1) :
    ∃ k : Fin 6, pauliXor (so4Label i) (so4Label j) = so4Label k := by
  revert hω
  fin_cases i <;> fin_cases j <;> decide

theorem so4B6_lie_mem_span (i j : Fin 6) :
    ⁅so4B6 i, so4B6 j⁆ ∈ Submodule.span ℂ (Set.range so4B6) := by
  rw [so4B6, so4B6, smul_lie, lie_smul, pauliMat_bracket_closed]
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide)
      (pauliOmega (so4Label i) (so4Label j)) with hcomm | hanti
  · rw [pauliPhase_sub_eq_zero hcomm, zero_smul, smul_zero]
    simp
  · obtain ⟨k, hk⟩ := so4Label_xor_mem_of_anticomm hanti
    rw [hk]
    have hpm : pauliMat (so4Label k) = (rtNinv 2)⁻¹ • so4B6 k := by
      rw [so4B6, smul_smul, inv_mul_cancel₀ (rtNinv_ne_zero 2), one_smul]
    have hpmem : pauliMat (so4Label k) ∈ Submodule.span ℂ (Set.range so4B6) := by
      rw [hpm]
      exact Submodule.smul_mem _ _ (so4B6_mem_span k)
    have hphase : (pauliPhase (so4Label i) (so4Label j)
          - pauliPhase (so4Label j) (so4Label i)) • pauliMat (so4Label k)
        ∈ Submodule.span ℂ (Set.range so4B6) :=
      Submodule.smul_mem _ _ hpmem
    have hrt : rtNinv 2 • ((pauliPhase (so4Label i) (so4Label j)
          - pauliPhase (so4Label j) (so4Label i)) • pauliMat (so4Label k))
        ∈ Submodule.span ℂ (Set.range so4B6) :=
      Submodule.smul_mem _ _ hphase
    exact Submodule.smul_mem _ _ hrt

end QuantumAlg

namespace QuantumAlg

open Matrix
open scoped Kronecker
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Lie subalgebra spanned by the concrete six-element `so(4)` family. -/
noncomputable def so4FullLie : LieSubalgebra ℂ (Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ) where
  toSubmodule := Submodule.span ℂ (Set.range so4B6)
  lie_mem' := by
    intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy =>
        rcases hx with ⟨i, rfl⟩
        rcases hy with ⟨j, rfl⟩
        exact so4B6_lie_mem_span i j
      | zero => rw [lie_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [lie_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy => rw [lie_smul]; exact Submodule.smul_mem _ _ hy
    | zero => rw [zero_lie]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [smul_lie]; exact Submodule.smul_mem _ _ hx

/-- The concrete six-element Hermitian orthonormal basis of the full `so(4)` algebra. -/
noncomputable def so4HermBasis : DLAHermBasis so4FullGens where
  dim := 6
  B := so4B6
  herm := by
    intro i
    rw [so4B6, conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]
  ortho := by
    intro i j
    rw [so4B6, so4B6, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply,
      rtNinv_conj, ← mul_assoc, rtNinv_mul_self, pauliMat_hsInner]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, one_div,
        inv_mul_cancel₀ (pow_ne_zero 2 (by norm_num : (2 : ℂ) ≠ 0))]
    · rw [if_neg h, if_neg (fun he => h (by
        exact so4Label_inj he)), mul_zero]
  span_eq := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      exact LieSubalgebra.subset_lieSpan ⟨i, rfl⟩
    · intro x hx
      exact dynamicalLieAlgebra_minimal so4FullGens
        (show so4FullGens ⊆ (so4FullLie : Set (Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ)) from by
          rintro _ ⟨i, rfl⟩
          change so4B6 i ∈ Submodule.span ℂ (Set.range so4B6)
          exact Submodule.subset_span ⟨i, rfl⟩) hx

/-- The six explicit `so(4)` labels are exactly the two-qubit odd-`#Y` labels. -/
theorem so4Label_odd (i : Fin 6) : Odd (yCount (so4Label i)) := by
  fin_cases i <;> decide

/-- Every two-qubit odd-`#Y` Pauli label appears in the explicit `so(4)` list. -/
theorem so4Label_complete_odd {s : Fin 2 → Fin 4} (hs : Odd (yCount s)) :
    ∃ i : Fin 6, s = so4Label i := by
  revert s
  decide

/-- The family `soHermBasis 2` and the concrete six-element `so(4)` basis have the
same basis range. -/
theorem soB_two_range_so4B6 :
    Set.range (soB 2) = Set.range so4B6 := by
  ext A
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := so4Label_complete_odd (soEquiv 2 i).2
    refine ⟨j, ?_⟩
    rw [soB, so4B6, hj]
  · rintro ⟨j, rfl⟩
    refine ⟨(soEquiv 2).symm ⟨so4Label j, so4Label_odd j⟩, ?_⟩
    simp only [soB, so4B6, Equiv.apply_symm_apply]

/-- The concrete six-element `so(4)` Pauli basis spans Mathlib's `so(4, ℂ)`. -/
theorem so4B6_span_orthogonalSo :
    Submodule.span ℂ (Set.range so4B6) =
      (LieAlgebra.Orthogonal.so (Fin (2 ^ 2)) ℂ).toSubmodule := by
  rw [← soB_two_range_so4B6, soB_span_orthogonal_so]

/-- The normalized `A ⊕ B` triangle basis as one nondependent six-element family. -/
noncomputable def so4ABB (p : Fin 2 × Fin 3) : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  if p.1 = 0 then so4A.basis.B p.2 else so4B.basis.B p.2

/-- The normalized `A ⊕ B` triangle basis has the same range as `so4B6`. -/
theorem so4ABB_range_so4B6 :
    Set.range so4ABB = Set.range so4B6 := by
  ext A
  constructor
  · rintro ⟨p, rfl⟩
    rcases p with ⟨j, k⟩
    fin_cases j <;> fin_cases k
    · exact ⟨0, by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨1, by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨2, by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨3, by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨4, by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨5, by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨(0, 0), by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨(0, 1), by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨(0, 2), by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨(1, 0), by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨(1, 1), by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩
    · exact ⟨(1, 2), by simp [so4ABB, so4B6, so4Label, PauliTriangle.basis, PauliTriangle.triB]⟩

/-- The `A ⊕ B` triangle basis spans Mathlib's `so(4, ℂ)`. -/
theorem so4AB_span_orthogonalSo :
    Submodule.span ℂ (Set.range so4ABB) =
      (LieAlgebra.Orthogonal.so (Fin (2 ^ 2)) ℂ).toSubmodule := by
  rw [so4ABB_range_so4B6, so4B6_span_orthogonalSo]

theorem gTensorG_eq_of_B_range_eq {N : ℕ}
    {gens₁ gens₂ : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : DLAHermBasis gens₁) (c : DLAHermBasis gens₂)
    (hB : Set.range b.B = Set.range c.B) : gTensorG b = gTensorG c := by
  rw [gTensorG, gTensorG]
  apply congrArg (Submodule.span ℂ)
  ext X
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, c.B i = b.B p.1 := by
      have : b.B p.1 ∈ Set.range c.B := by
        rw [← hB]
        exact ⟨p.1, rfl⟩
      simpa only [Set.mem_range] using this
    obtain ⟨j, hj⟩ : ∃ j, c.B j = b.B p.2 := by
      have : b.B p.2 ∈ Set.range c.B := by
        rw [← hB]
        exact ⟨p.2, rfl⟩
      simpa only [Set.mem_range] using this
    exact ⟨(i, j), by
      change c.B i ⊗ₖ c.B j = b.B p.1 ⊗ₖ b.B p.2
      rw [hi, hj]⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, b.B i = c.B p.1 := by
      have : c.B p.1 ∈ Set.range b.B := by
        rw [hB]
        exact ⟨p.1, rfl⟩
      simpa only [Set.mem_range] using this
    obtain ⟨j, hj⟩ : ∃ j, b.B j = c.B p.2 := by
      have : c.B p.2 ∈ Set.range b.B := by
        rw [hB]
        exact ⟨p.2, rfl⟩
      simpa only [Set.mem_range] using this
    exact ⟨(i, j), by
      change b.B i ⊗ₖ b.B j = c.B p.1 ⊗ₖ c.B p.2
      rw [hi, hj]⟩

theorem adCommutantGG_eq_of_B_range_eq {N : ℕ}
    {gens₁ gens₂ : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : DLAHermBasis gens₁) (c : DLAHermBasis gens₂)
    (hB : Set.range b.B = Set.range c.B) : adCommutantGG b = adCommutantGG c := by
  ext X
  rw [adCommutantGG, adCommutantGG]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h j
    obtain ⟨i, hi⟩ : ∃ i, b.B i = c.B j := by
      have : c.B j ∈ Set.range b.B := by
        rw [hB]
        exact ⟨j, rfl⟩
      simpa only [Set.mem_range] using this
    simpa [hi] using h i
  · intro h i
    obtain ⟨j, hj⟩ : ∃ j, c.B j = b.B i := by
      have : b.B i ∈ Set.range c.B := by
        rw [← hB]
        exact ⟨i, rfl⟩
      simpa only [Set.mem_range] using this
    simpa [hj] using h j

theorem gTensorGInvariant_eq_of_B_range_eq {N : ℕ}
    {gens₁ gens₂ : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : DLAHermBasis gens₁) (c : DLAHermBasis gens₂)
    (hB : Set.range b.B = Set.range c.B) :
    gTensorGInvariant b = gTensorGInvariant c := by
  rw [gTensorGInvariant, gTensorGInvariant, adCommutantGG_eq_of_B_range_eq b c hB,
    gTensorG_eq_of_B_range_eq b c hB]

/-- The invariant-space carrier for `soHermBasis 2` is the concrete `so(4)` carrier. -/
theorem soHermBasis_two_gTensorGInvariant_eq_so4 :
    gTensorGInvariant (soHermBasis 2) = gTensorGInvariant so4HermBasis :=
  gTensorGInvariant_eq_of_B_range_eq (soHermBasis 2) so4HermBasis (by
    change Set.range (soB 2) = Set.range so4B6
    exact soB_two_range_so4B6)

theorem adMatrix_so4_apply (k a i : Fin 6) :
    adMatrix so4HermBasis k a i
      = rtNinv 2 * rtNinv 2 * rtNinv 2 *
          (pauliPhase (so4Label k) (so4Label i)
            - pauliPhase (so4Label i) (so4Label k)) *
          (if so4Label a = pauliXor (so4Label k) (so4Label i) then (2 ^ 2 : ℂ) else 0) := by
  rw [adMatrix, Matrix.of_apply]
  change hsInner (so4B6 a) ⁅so4B6 k, so4B6 i⁆ = _
  rw [so4B6, so4B6, so4B6, smul_lie, lie_smul, pauliMat_bracket_closed,
    hsInner_smul_left, hsInner_smul_right, hsInner_smul_right, hsInner_smul_right,
    starRingEnd_apply, rtNinv_conj, pauliMat_hsInner]
  ring

theorem adMatrix_so4_eq_zero {k a i : Fin 6}
    (h : so4Label a ≠ pauliXor (so4Label k) (so4Label i)) :
    adMatrix so4HermBasis k a i = 0 := by
  rw [adMatrix_so4_apply, if_neg h, mul_zero]

theorem adMatrix_so4_ne_zero {k a i : Fin 6}
    (hsupp : so4Label a = pauliXor (so4Label k) (so4Label i))
    (hanti : pauliOmega (so4Label k) (so4Label i) = 1) :
    adMatrix so4HermBasis k a i ≠ 0 := by
  rw [adMatrix_so4_apply, if_pos hsupp]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · exact rtNinv_ne_zero 2
  · exact rtNinv_ne_zero 2
  · exact rtNinv_ne_zero 2
  · exact pauliPhase_sub_ne_zero hanti
  · norm_num

/-- The diagonal of the square of the `k`th concrete adjoint matrix. -/
noncomputable def so4Mu6 (k a : Fin 6) : ℂ :=
  (adMatrix so4HermBasis k * adMatrix so4HermBasis k) a a

theorem adMatrix_so4_sq_diagonal (k : Fin 6) :
    adMatrix so4HermBasis k * adMatrix so4HermBasis k = Matrix.diagonal (so4Mu6 k) := by
  ext a a'
  by_cases ha : a = a'
  · subst ha; rw [Matrix.diagonal_apply_eq, so4Mu6]
  · rw [show Matrix.diagonal (so4Mu6 k) a a' = 0 from Matrix.diagonal_apply_ne _ ha,
      Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : so4Label a = pauliXor (so4Label k) (so4Label i)
    · have h2 : so4Label i ≠ pauliXor (so4Label k) (so4Label a') := fun hi =>
        ha (so4Label_inj (by rw [h1, hi, pauliXor_self_inv]))
      rw [adMatrix_so4_eq_zero h2, mul_zero]
    · rw [adMatrix_so4_eq_zero h1, zero_mul]

theorem adMatrix_so4_eq_zero_of_comm {k a i : Fin 6}
    (h : pauliOmega (so4Label k) (so4Label i) = 0) :
    adMatrix so4HermBasis k a i = 0 := by
  rw [adMatrix_so4_apply, pauliPhase_sub_eq_zero h, mul_zero, zero_mul]

theorem so4Mu6_eq_zero_iff (k a : Fin 6) :
    so4Mu6 k a = 0 ↔ pauliOmega (so4Label k) (so4Label a) = 0 := by
  constructor
  · intro h
    by_contra hω
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide)
        (pauliOmega (so4Label k) (so4Label a)) with h0 | h1
    · exact hω h0
    · obtain ⟨i₀, hxor⟩ := so4Label_xor_mem_of_anticomm h1
      have hsupp : so4Label a = pauliXor (so4Label k) (so4Label i₀) := by
        rw [← hxor, pauliXor_self_inv]
      have hanti : pauliOmega (so4Label k) (so4Label i₀) = 1 := by
        rw [← hxor, pauliOmega_xor_right, pauliOmega_self_zero, zero_add, h1]
      have hσi₀ : so4Label i₀ = pauliXor (so4Label k) (so4Label a) := hxor.symm
      have hμ : so4Mu6 k a = adMatrix so4HermBasis k a i₀ * adMatrix so4HermBasis k i₀ a := by
        rw [so4Mu6, Matrix.mul_apply]
        refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun he => absurd (Finset.mem_univ i₀) he)
        by_cases h1s : so4Label a = pauliXor (so4Label k) (so4Label i)
        · refine absurd (so4Label_inj ?_) hi
          have hii : so4Label i = pauliXor (so4Label k) (so4Label a) := by
            have hsi := pauliXor_self_inv (so4Label k) (so4Label i)
            rw [← h1s] at hsi
            exact hsi.symm
          exact hii.trans hσi₀.symm
        · rw [adMatrix_so4_eq_zero h1s, zero_mul]
      rw [hμ] at h
      rcases mul_eq_zero.mp h with hz | hz
      · exact adMatrix_so4_ne_zero hsupp hanti hz
      · exact adMatrix_so4_ne_zero hσi₀ h1 hz
  · intro h
    rw [so4Mu6, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : so4Label a = pauliXor (so4Label k) (so4Label i)
    · have hi0 : so4Label i = pauliXor (so4Label k) (so4Label a) := by
        have hsi := pauliXor_self_inv (so4Label k) (so4Label i)
        rw [← h1] at hsi
        exact hsi.symm
      have hcomm : pauliOmega (so4Label k) (so4Label i) = 0 := by
        rw [hi0, pauliOmega_xor_right, pauliOmega_self_zero, zero_add, h]
      rw [adMatrix_so4_eq_zero_of_comm hcomm, zero_mul]
    · rw [adMatrix_so4_eq_zero h1, zero_mul]

theorem so4Label_omega_sep {a a' : Fin 6} (ha : a ≠ a') :
    ∃ k, pauliOmega (so4Label k) (so4Label a)
        ≠ pauliOmega (so4Label k) (so4Label a') := by
  revert ha
  fin_cases a <;> fin_cases a' <;> decide

theorem so4Mu6_sep {a a' : Fin 6} (ha : a ≠ a') : ∃ k, so4Mu6 k a ≠ so4Mu6 k a' := by
  obtain ⟨k, hω⟩ := so4Label_omega_sep ha
  by_cases hka : pauliOmega (so4Label k) (so4Label a) = 0
  · have hka' : pauliOmega (so4Label k) (so4Label a') ≠ 0 := fun h => hω (hka.trans h.symm)
    have hmu : so4Mu6 k a = 0 := (so4Mu6_eq_zero_iff k a).mpr hka
    have hmu' : so4Mu6 k a' ≠ 0 := (so4Mu6_eq_zero_iff k a').not.mpr hka'
    refine ⟨k, ?_⟩
    rw [hmu]
    exact Ne.symm hmu'
  · have hmu : so4Mu6 k a ≠ 0 := (so4Mu6_eq_zero_iff k a).not.mpr hka
    have hka' : pauliOmega (so4Label k) (so4Label a') = 0 := by
      rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide)
          (pauliOmega (so4Label k) (so4Label a')) with h0 | h1
      · exact h0
      · exfalso
        rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide)
            (pauliOmega (so4Label k) (so4Label a)) with ha0 | ha1
        · exact hka ha0
        · exact hω (ha1.trans h1.symm)
    have hmu' : so4Mu6 k a' = 0 := (so4Mu6_eq_zero_iff k a').mpr hka'
    refine ⟨k, ?_⟩
    rw [hmu']
    exact hmu

private theorem coeffMatrix_diag_eq_of_so4_ad_ne_zero
    {X : Matrix (Fin (2 ^ 2) × Fin (2 ^ 2)) (Fin (2 ^ 2) × Fin (2 ^ 2)) ℂ}
    (hX : X ∈ gTensorGInvariant so4HermBasis)
    (hoff : ∀ a a' : Fin so4HermBasis.dim, a ≠ a' → coeffMatrix so4HermBasis X a a' = 0)
    {x y : Fin so4HermBasis.dim} (hxy : ∃ k, adMatrix so4HermBasis k x y ≠ 0) :
    coeffMatrix so4HermBasis X x x = coeffMatrix so4HermBasis X y y := by
  obtain ⟨k, hk⟩ := hxy
  have hcomm := gTensorGInvariant_commute so4HermBasis hX k
  have he := congrFun (congrFun hcomm x) y
  have hL : (adMatrix so4HermBasis k * coeffMatrix so4HermBasis X) x y =
      adMatrix so4HermBasis k x y * coeffMatrix so4HermBasis X y y := by
    rw [Matrix.mul_apply, Finset.sum_eq_single y
      (fun i _ hiy => by rw [hoff i y hiy, mul_zero])
      (fun h => absurd (Finset.mem_univ y) h)]
  have hR : (coeffMatrix so4HermBasis X * adMatrix so4HermBasis k) x y =
      coeffMatrix so4HermBasis X x x * adMatrix so4HermBasis k x y := by
    rw [Matrix.mul_apply, Finset.sum_eq_single x
      (fun j _ hjx => by rw [hoff x j (Ne.symm hjx), zero_mul])
      (fun h => absurd (Finset.mem_univ x) h)]
  rw [hL, hR] at he
  have hs : adMatrix so4HermBasis k x y *
      (coeffMatrix so4HermBasis X y y - coeffMatrix so4HermBasis X x x) = 0 := by
    rw [mul_sub, he]
    ring
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left hk)).symm

private theorem so4_ad_ne_zero_201 :
    adMatrix so4HermBasis (2 : Fin 6) (0 : Fin 6) (1 : Fin 6) ≠ 0 := by
  exact adMatrix_so4_ne_zero (by decide) (by decide)

private theorem so4_ad_ne_zero_012 :
    adMatrix so4HermBasis (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) ≠ 0 := by
  exact adMatrix_so4_ne_zero (by decide) (by decide)

private theorem so4_ad_ne_zero_534 :
    adMatrix so4HermBasis (5 : Fin 6) (3 : Fin 6) (4 : Fin 6) ≠ 0 := by
  exact adMatrix_so4_ne_zero (by decide) (by decide)

private theorem so4_ad_ne_zero_345 :
    adMatrix so4HermBasis (3 : Fin 6) (4 : Fin 6) (5 : Fin 6) ≠ 0 := by
  exact adMatrix_so4_ne_zero (by decide) (by decide)

/-- The quadratic Casimir of the `A` ideal in the concrete six-element basis. -/
noncomputable def so4ACasimir :
    Matrix (Fin (2 ^ 2) × Fin (2 ^ 2)) (Fin (2 ^ 2) × Fin (2 ^ 2)) ℂ :=
  so4B6 0 ⊗ₖ so4B6 0 + so4B6 1 ⊗ₖ so4B6 1 + so4B6 2 ⊗ₖ so4B6 2

/-- The quadratic Casimir of the `B` ideal in the concrete six-element basis. -/
noncomputable def so4BCasimir :
    Matrix (Fin (2 ^ 2) × Fin (2 ^ 2)) (Fin (2 ^ 2) × Fin (2 ^ 2)) ℂ :=
  so4B6 3 ⊗ₖ so4B6 3 + so4B6 4 ⊗ₖ so4B6 4 + so4B6 5 ⊗ₖ so4B6 5

/-- The two-element family containing the `A`- and `B`-ideal Casimirs. -/
noncomputable def so4IdealCasimir :
    Fin 2 → Matrix (Fin (2 ^ 2) × Fin (2 ^ 2)) (Fin (2 ^ 2) × Fin (2 ^ 2)) ℂ :=
  ![so4ACasimir, so4BCasimir]

set_option maxHeartbeats 800000 in
-- Expanding and normalizing the complete six-by-six coefficient system needs extra heartbeats.
theorem so4_gTensorGInvariant_le_span_twoCasimir :
    gTensorGInvariant so4HermBasis ≤ Submodule.span ℂ (Set.range so4IdealCasimir) := by
  intro X hX
  have hoff : ∀ a a' : Fin so4HermBasis.dim, a ≠ a' → coeffMatrix so4HermBasis X a a' = 0 :=
    fun a a' ha => coeffMatrix_offdiag_zero so4HermBasis hX so4Mu6
      adMatrix_so4_sq_diagonal (fun a a' h => so4Mu6_sep h) ha
  have h01 : coeffMatrix so4HermBasis X (0 : Fin 6) (0 : Fin 6) =
      coeffMatrix so4HermBasis X (1 : Fin 6) (1 : Fin 6) :=
    coeffMatrix_diag_eq_of_so4_ad_ne_zero hX hoff ⟨(2 : Fin 6), so4_ad_ne_zero_201⟩
  have h12 : coeffMatrix so4HermBasis X (1 : Fin 6) (1 : Fin 6) =
      coeffMatrix so4HermBasis X (2 : Fin 6) (2 : Fin 6) :=
    coeffMatrix_diag_eq_of_so4_ad_ne_zero hX hoff ⟨(0 : Fin 6), so4_ad_ne_zero_012⟩
  have h34 : coeffMatrix so4HermBasis X (3 : Fin 6) (3 : Fin 6) =
      coeffMatrix so4HermBasis X (4 : Fin 6) (4 : Fin 6) :=
    coeffMatrix_diag_eq_of_so4_ad_ne_zero hX hoff ⟨(5 : Fin 6), so4_ad_ne_zero_534⟩
  have h45 : coeffMatrix so4HermBasis X (4 : Fin 6) (4 : Fin 6) =
      coeffMatrix so4HermBasis X (5 : Fin 6) (5 : Fin 6) :=
    coeffMatrix_diag_eq_of_so4_ad_ne_zero hX hoff ⟨(3 : Fin 6), so4_ad_ne_zero_345⟩
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun r : Fin 2 => if r = 0 then hsInner (so4B6 0 ⊗ₖ so4B6 0) X
      else hsInner (so4B6 3 ⊗ₖ so4B6 3) X, ?_⟩
  have hcoord := gTensorG_coord so4HermBasis hX.2
  change X = ∑ i : Fin 6, ∑ j : Fin 6,
      hsInner (so4B6 i ⊗ₖ so4B6 j) X • (so4B6 i ⊗ₖ so4B6 j) at hcoord
  have hoff6 : ∀ a a' : Fin 6, a ≠ a' →
      hsInner (so4B6 a ⊗ₖ so4B6 a') X = 0 := by
    intro a a' ha
    have h := hoff a a' ha
    change hsInner (so4B6 a ⊗ₖ so4B6 a') X = 0 at h
    exact h
  have h01c : hsInner (so4B6 0 ⊗ₖ so4B6 0) X =
      hsInner (so4B6 1 ⊗ₖ so4B6 1) X := by
    have h := h01
    change hsInner (so4B6 0 ⊗ₖ so4B6 0) X =
      hsInner (so4B6 1 ⊗ₖ so4B6 1) X at h
    exact h
  have h12c : hsInner (so4B6 1 ⊗ₖ so4B6 1) X =
      hsInner (so4B6 2 ⊗ₖ so4B6 2) X := by
    have h := h12
    change hsInner (so4B6 1 ⊗ₖ so4B6 1) X =
      hsInner (so4B6 2 ⊗ₖ so4B6 2) X at h
    exact h
  have h34c : hsInner (so4B6 3 ⊗ₖ so4B6 3) X =
      hsInner (so4B6 4 ⊗ₖ so4B6 4) X := by
    have h := h34
    change hsInner (so4B6 3 ⊗ₖ so4B6 3) X =
      hsInner (so4B6 4 ⊗ₖ so4B6 4) X at h
    exact h
  have h45c : hsInner (so4B6 4 ⊗ₖ so4B6 4) X =
      hsInner (so4B6 5 ⊗ₖ so4B6 5) X := by
    have h := h45
    change hsInner (so4B6 4 ⊗ₖ so4B6 4) X =
      hsInner (so4B6 5 ⊗ₖ so4B6 5) X at h
    exact h
  conv_rhs => rw [hcoord]
  simp only [Fin.sum_univ_two, Fin.sum_univ_six, so4IdealCasimir, so4ACasimir,
    so4BCasimir]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, if_true, Fin.isValue, if_false,
    Fin.reduceEq]
  rw [hoff6 (0 : Fin 6) (1 : Fin 6) (by decide),
    hoff6 (0 : Fin 6) (2 : Fin 6) (by decide),
    hoff6 (0 : Fin 6) (3 : Fin 6) (by decide),
    hoff6 (0 : Fin 6) (4 : Fin 6) (by decide),
    hoff6 (0 : Fin 6) (5 : Fin 6) (by decide),
    hoff6 (1 : Fin 6) (0 : Fin 6) (by decide),
    hoff6 (1 : Fin 6) (2 : Fin 6) (by decide),
    hoff6 (1 : Fin 6) (3 : Fin 6) (by decide),
    hoff6 (1 : Fin 6) (4 : Fin 6) (by decide),
    hoff6 (1 : Fin 6) (5 : Fin 6) (by decide),
    hoff6 (2 : Fin 6) (0 : Fin 6) (by decide),
    hoff6 (2 : Fin 6) (1 : Fin 6) (by decide),
    hoff6 (2 : Fin 6) (3 : Fin 6) (by decide),
    hoff6 (2 : Fin 6) (4 : Fin 6) (by decide),
    hoff6 (2 : Fin 6) (5 : Fin 6) (by decide),
    hoff6 (3 : Fin 6) (0 : Fin 6) (by decide),
    hoff6 (3 : Fin 6) (1 : Fin 6) (by decide),
    hoff6 (3 : Fin 6) (2 : Fin 6) (by decide),
    hoff6 (3 : Fin 6) (4 : Fin 6) (by decide),
    hoff6 (3 : Fin 6) (5 : Fin 6) (by decide),
    hoff6 (4 : Fin 6) (0 : Fin 6) (by decide),
    hoff6 (4 : Fin 6) (1 : Fin 6) (by decide),
    hoff6 (4 : Fin 6) (2 : Fin 6) (by decide),
    hoff6 (4 : Fin 6) (3 : Fin 6) (by decide),
    hoff6 (4 : Fin 6) (5 : Fin 6) (by decide),
    hoff6 (5 : Fin 6) (0 : Fin 6) (by decide),
    hoff6 (5 : Fin 6) (1 : Fin 6) (by decide),
    hoff6 (5 : Fin 6) (2 : Fin 6) (by decide),
    hoff6 (5 : Fin 6) (3 : Fin 6) (by decide),
    hoff6 (5 : Fin 6) (4 : Fin 6) (by decide)]
  simp only [zero_smul, add_zero, zero_add]
  rw [← h12c, ← h01c, ← h45c, ← h34c]
  simp only [smul_add]
  abel_nf

theorem so4ACasimir_eq : so4ACasimir = so4A.basis.casimir := by
  rw [so4ACasimir, DLAHermBasis.casimir]
  change so4B6 0 ⊗ₖ so4B6 0 + so4B6 1 ⊗ₖ so4B6 1 +
      so4B6 2 ⊗ₖ so4B6 2 = ∑ j : Fin 3, so4A.basis.B j ⊗ₖ so4A.basis.B j
  rw [Fin.sum_univ_three]
  rfl

theorem so4BCasimir_eq : so4BCasimir = so4B.basis.casimir := by
  rw [so4BCasimir, DLAHermBasis.casimir]
  change so4B6 3 ⊗ₖ so4B6 3 + so4B6 4 ⊗ₖ so4B6 4 +
      so4B6 5 ⊗ₖ so4B6 5 = ∑ j : Fin 3, so4B.basis.B j ⊗ₖ so4B.basis.B j
  rw [Fin.sum_univ_three]
  rfl

theorem so4ACasimir_mem_gTensorG : so4ACasimir ∈ gTensorG so4HermBasis := by
  rw [so4ACasimir, gTensorG]
  change so4B6 0 ⊗ₖ so4B6 0 + so4B6 1 ⊗ₖ so4B6 1 + so4B6 2 ⊗ₖ so4B6 2 ∈
    Submodule.span ℂ (Set.range fun p : Fin 6 × Fin 6 => so4B6 p.1 ⊗ₖ so4B6 p.2)
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.subset_span ⟨((0 : Fin 6), (0 : Fin 6)), rfl⟩)
      (Submodule.subset_span ⟨((1 : Fin 6), (1 : Fin 6)), rfl⟩))
    (Submodule.subset_span ⟨((2 : Fin 6), (2 : Fin 6)), rfl⟩)

theorem so4BCasimir_mem_gTensorG : so4BCasimir ∈ gTensorG so4HermBasis := by
  rw [so4BCasimir, gTensorG]
  change so4B6 3 ⊗ₖ so4B6 3 + so4B6 4 ⊗ₖ so4B6 4 + so4B6 5 ⊗ₖ so4B6 5 ∈
    Submodule.span ℂ (Set.range fun p : Fin 6 × Fin 6 => so4B6 p.1 ⊗ₖ so4B6 p.2)
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.subset_span ⟨((3 : Fin 6), (3 : Fin 6)), rfl⟩)
      (Submodule.subset_span ⟨((4 : Fin 6), (4 : Fin 6)), rfl⟩))
    (Submodule.subset_span ⟨((5 : Fin 6), (5 : Fin 6)), rfl⟩)

theorem so4_cross_lie_zero_basis
    (i : Fin so4A.basis.dim) (j : Fin so4B.basis.dim) : ⁅so4A.basis.B i, so4B.basis.B j⁆ = 0 := by
  rw [PauliTriangle.basis_B, PauliTriangle.basis_B, PauliTriangle.triB, PauliTriangle.triB,
    smul_lie, lie_smul, pauliMat_bracket_closed]
  have hcomm : pauliOmega (so4A.t i) (so4B.t j) = 0 := by
    fin_cases i <;> fin_cases j <;> decide
  rw [pauliPhase_sub_eq_zero hcomm, zero_smul, smul_zero]
  simp

theorem so4_cross_lie_zero_BA
    (i : Fin so4A.basis.dim) (j : Fin so4B.basis.dim) : ⁅so4B.basis.B j, so4A.basis.B i⁆ = 0 := by
  have hskew : ⁅so4B.basis.B j, so4A.basis.B i⁆ = -⁅so4A.basis.B i, so4B.basis.B j⁆ := by
    rw [← neg_inj]
    simp [lie_skew (so4A.basis.B i) (so4B.basis.B j)]
  rw [hskew, so4_cross_lie_zero_basis i j, neg_zero]

theorem doubledAd_B_on_so4ACasimir (k : Fin 3) :
    doubledAd (so4B.basis.B k) so4ACasimir = 0 := by
  rw [so4ACasimir_eq, DLAHermBasis.casimir]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [doubledAd_kron, so4_cross_lie_zero_BA i k]
  simp

theorem doubledAd_A_on_so4BCasimir (k : Fin 3) :
    doubledAd (so4A.basis.B k) so4BCasimir = 0 := by
  rw [so4BCasimir_eq, DLAHermBasis.casimir]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [doubledAd_kron, so4_cross_lie_zero_basis k i]
  simp

theorem so4ACasimir_mem_adCommutant : so4ACasimir ∈ adCommutantGG so4HermBasis := by
  rw [adCommutantGG, Submodule.mem_iInf]
  intro k
  rw [LinearMap.mem_ker]
  fin_cases k
  · have h := casimir_mem_adCommutantGG so4A.basis
    rw [adCommutantGG, Submodule.mem_iInf] at h
    have hk := LinearMap.mem_ker.mp (h (0 : Fin 3))
    change doubledAd (so4A.basis.B (0 : Fin 3)) so4ACasimir = 0
    rw [so4ACasimir_eq]
    exact hk
  · have h := casimir_mem_adCommutantGG so4A.basis
    rw [adCommutantGG, Submodule.mem_iInf] at h
    have hk := LinearMap.mem_ker.mp (h (1 : Fin 3))
    change doubledAd (so4A.basis.B (1 : Fin 3)) so4ACasimir = 0
    rw [so4ACasimir_eq]
    exact hk
  · have h := casimir_mem_adCommutantGG so4A.basis
    rw [adCommutantGG, Submodule.mem_iInf] at h
    have hk := LinearMap.mem_ker.mp (h (2 : Fin 3))
    change doubledAd (so4A.basis.B (2 : Fin 3)) so4ACasimir = 0
    rw [so4ACasimir_eq]
    exact hk
  · exact doubledAd_B_on_so4ACasimir 0
  · exact doubledAd_B_on_so4ACasimir 1
  · exact doubledAd_B_on_so4ACasimir 2

theorem so4BCasimir_mem_adCommutant : so4BCasimir ∈ adCommutantGG so4HermBasis := by
  rw [adCommutantGG, Submodule.mem_iInf]
  intro k
  rw [LinearMap.mem_ker]
  fin_cases k
  · exact doubledAd_A_on_so4BCasimir 0
  · exact doubledAd_A_on_so4BCasimir 1
  · exact doubledAd_A_on_so4BCasimir 2
  · have h := casimir_mem_adCommutantGG so4B.basis
    rw [adCommutantGG, Submodule.mem_iInf] at h
    have hk := LinearMap.mem_ker.mp (h (0 : Fin 3))
    change doubledAd (so4B.basis.B (0 : Fin 3)) so4BCasimir = 0
    rw [so4BCasimir_eq]
    exact hk
  · have h := casimir_mem_adCommutantGG so4B.basis
    rw [adCommutantGG, Submodule.mem_iInf] at h
    have hk := LinearMap.mem_ker.mp (h (1 : Fin 3))
    change doubledAd (so4B.basis.B (1 : Fin 3)) so4BCasimir = 0
    rw [so4BCasimir_eq]
    exact hk
  · have h := casimir_mem_adCommutantGG so4B.basis
    rw [adCommutantGG, Submodule.mem_iInf] at h
    have hk := LinearMap.mem_ker.mp (h (2 : Fin 3))
    change doubledAd (so4B.basis.B (2 : Fin 3)) so4BCasimir = 0
    rw [so4BCasimir_eq]
    exact hk

theorem so4ACasimir_mem_invariant : so4ACasimir ∈ gTensorGInvariant so4HermBasis := by
  rw [gTensorGInvariant]
  exact Submodule.mem_inf.mpr ⟨so4ACasimir_mem_adCommutant, so4ACasimir_mem_gTensorG⟩

theorem so4BCasimir_mem_invariant : so4BCasimir ∈ gTensorGInvariant so4HermBasis := by
  rw [gTensorGInvariant]
  exact Submodule.mem_inf.mpr ⟨so4BCasimir_mem_adCommutant, so4BCasimir_mem_gTensorG⟩

theorem span_twoCasimir_le_so4_gTensorGInvariant :
    Submodule.span ℂ (Set.range so4IdealCasimir) ≤ gTensorGInvariant so4HermBasis := by
  rw [Submodule.span_le, Set.range_subset_iff]
  intro j
  fin_cases j
  · simpa [so4IdealCasimir] using so4ACasimir_mem_invariant
  · simpa [so4IdealCasimir] using so4BCasimir_mem_invariant

theorem so4_gTensorGInvariant_eq_span_twoCasimir :
    gTensorGInvariant so4HermBasis = Submodule.span ℂ (Set.range so4IdealCasimir) :=
  le_antisymm so4_gTensorGInvariant_le_span_twoCasimir span_twoCasimir_le_so4_gTensorGInvariant

theorem so4ACasimir_hsInner_self : hsInner so4ACasimir so4ACasimir = 3 := by
  rw [so4ACasimir_eq, so4A.basis.casimir_hsInner_self, PauliTriangle.basis_dim]
  norm_num

theorem so4BCasimir_hsInner_self : hsInner so4BCasimir so4BCasimir = 3 := by
  rw [so4BCasimir_eq, so4B.basis.casimir_hsInner_self, PauliTriangle.basis_dim]
  norm_num

theorem so4ACasimir_hsInner_B : hsInner so4ACasimir so4BCasimir = 0 := by
  rw [so4ACasimir_eq, so4BCasimir_eq]
  have h := casimir_cross_aux so4Basis so4_cross_ortho (0 : Fin 2) (1 : Fin 2)
  change hsInner so4A.basis.casimir so4B.basis.casimir = 0
  exact h

theorem so4BCasimir_hsInner_A : hsInner so4BCasimir so4ACasimir = 0 := by
  rw [so4ACasimir_eq, so4BCasimir_eq]
  have h := casimir_cross_aux so4Basis so4_cross_ortho (1 : Fin 2) (0 : Fin 2)
  change hsInner so4B.basis.casimir so4A.basis.casimir = 0
  exact h

theorem so4IdealCasimir_linearIndependent : LinearIndependent ℂ so4IdealCasimir := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  fin_cases j
  · have hinner : hsInner so4ACasimir (∑ j, c j • so4IdealCasimir j) = c 0 * 3 := by
      rw [Fin.sum_univ_two, so4IdealCasimir]
      change hsInner so4ACasimir (c 0 • so4ACasimir + c 1 • so4BCasimir) = c 0 * 3
      rw [hsInner_add_right, hsInner_smul_right, hsInner_smul_right,
        so4ACasimir_hsInner_self, so4ACasimir_hsInner_B]
      ring
    rw [hc, hsInner_zero_right] at hinner
    exact (mul_eq_zero.mp hinner.symm).resolve_right (by norm_num : (3 : ℂ) ≠ 0)
  · have hinner : hsInner so4BCasimir (∑ j, c j • so4IdealCasimir j) = c 1 * 3 := by
      rw [Fin.sum_univ_two, so4IdealCasimir]
      change hsInner so4BCasimir (c 0 • so4ACasimir + c 1 • so4BCasimir) = c 1 * 3
      rw [hsInner_add_right, hsInner_smul_right, hsInner_smul_right,
        so4BCasimir_hsInner_A, so4BCasimir_hsInner_self]
      ring
    rw [hc, hsInner_zero_right] at hinner
    exact (mul_eq_zero.mp hinner.symm).resolve_right (by norm_num : (3 : ℂ) ≠ 0)

/-- The span of the two per-ideal `so(4)` Casimirs is two-dimensional. -/
theorem so4_span_twoCasimir_finrank :
    Module.finrank ℂ (Submodule.span ℂ (Set.range so4IdealCasimir)) = 2 := by
  rw [finrank_span_eq_card so4IdealCasimir_linearIndependent, Fintype.card_fin]

/-- The full doubled-adjoint invariant space for reductive `so(4)` has dimension exactly two. -/
theorem so4_gTensorGInvariant_finrank :
    Module.finrank ℂ (gTensorGInvariant so4HermBasis) = 2 := by
  rw [so4_gTensorGInvariant_eq_span_twoCasimir, so4_span_twoCasimir_finrank]

/-- The `m = 2` member of the orthogonal family has a two-dimensional invariant space. -/
theorem soHermBasis_two_gTensorGInvariant_finrank :
    Module.finrank ℂ (gTensorGInvariant (soHermBasis 2)) = 2 := by
  rw [soHermBasis_two_gTensorGInvariant_eq_so4, so4_gTensorGInvariant_finrank]

theorem so4HermBasis_casimir_ne_zero : so4HermBasis.casimir ≠ 0 := by
  intro hzero
  have hinner : hsInner so4HermBasis.casimir so4HermBasis.casimir = (6 : ℂ) := by
    rw [so4HermBasis.casimir_hsInner_self]
    rfl
  rw [hzero, hsInner_zero_right] at hinner
  norm_num at hinner

theorem soHermBasis_two_casimir_ne_zero : (soHermBasis 2).casimir ≠ 0 := by
  intro hzero
  have hinner : hsInner (soHermBasis 2).casimir (soHermBasis 2).casimir = (6 : ℂ) := by
    rw [(soHermBasis 2).casimir_hsInner_self, soHermBasis_dim_closedForm]
    norm_num
  rw [hzero, hsInner_zero_right] at hinner
  norm_num at hinner

/-- The full reductive `so(4)` invariant space is not the span of the single split Casimir. -/
theorem so4_singleCasimir_schur_false :
    gTensorGInvariant so4HermBasis ≠ Submodule.span ℂ {so4HermBasis.casimir} := by
  intro h
  have hfin : Module.finrank ℂ (gTensorGInvariant so4HermBasis) =
      Module.finrank ℂ (Submodule.span ℂ {so4HermBasis.casimir}) := by
    rw [h]
  have hsingle : Module.finrank ℂ (Submodule.span ℂ {so4HermBasis.casimir}) = 1 := by
    simpa using finrank_span_singleton (K := ℂ) (v := so4HermBasis.casimir)
      so4HermBasis_casimir_ne_zero
  rw [so4_gTensorGInvariant_finrank, hsingle] at hfin
  norm_num at hfin

/-- The `m = 2` orthogonal family member is not single-Casimir Schur. -/
theorem soHermBasis_two_singleCasimir_schur_false :
    gTensorGInvariant (soHermBasis 2) ≠ Submodule.span ℂ {(soHermBasis 2).casimir} := by
  intro h
  have hfin : Module.finrank ℂ (gTensorGInvariant (soHermBasis 2)) =
      Module.finrank ℂ (Submodule.span ℂ {(soHermBasis 2).casimir}) := by
    rw [h]
  have hsingle : Module.finrank ℂ (Submodule.span ℂ {(soHermBasis 2).casimir}) = 1 := by
    simpa using finrank_span_singleton (K := ℂ) (v := (soHermBasis 2).casimir)
      soHermBasis_two_casimir_ne_zero
  rw [soHermBasis_two_gTensorGInvariant_finrank, hsingle] at hfin
  norm_num at hfin

end QuantumAlg
