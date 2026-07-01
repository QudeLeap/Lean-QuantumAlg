/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Core.Components.Oracle.BlockEncoding
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Linear combination of unitaries (LCU)

The LCU primitive block-encodes a linear combination of unitaries into a larger
operator acting on an ancilla control register tensored with the system
[Lin22, hermfunc.tex:531].

The raw SELECT sum is a `HilbertOperator`; its unitary SELECT wrapper and the
walk carrier are `Gate`s.  Projected-block algebra still works in the
`HilbertOperator` layer because the public `main` statement is the
block-encoding identity itself.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

variable {a n : ℕ}

/-- The control-basis projector `|i><i|` on the `a`-qubit control register. -/
def lcuProj (i : Fin (2 ^ a)) : HilbertOperator (Qubits a) :=
  Matrix.of fun r c => (if r = i then (1 : ℂ) else 0) * (if c = i then (1 : ℂ) else 0)

/-- Raw select operator `SELECT = sum_i |i><i| ⊗ U_i` [Lin22, hermfunc.tex:492]. -/
def lcuSelectOp (U : Fin (2 ^ a) → Gate (Qubits n)) : HilbertOperator (Qubits (a + n)) :=
  ∑ i, HilbertOperator.tensor (lcuProj i) (U i : HilbertOperator (Qubits n))

theorem lcuSelectOp_apply (U : Fin (2 ^ a) → Gate (Qubits n))
    (x x' : Fin (2 ^ a)) (y y' : Fin (2 ^ n)) :
    lcuSelectOp U (prodEquiv (x, y)) (prodEquiv (x', y'))
      = (if x = x' then U x y y' else 0) := by
  unfold lcuSelectOp
  rw [Matrix.sum_apply]
  by_cases h : x = x'
  · subst x'
    simp [HilbertOperator.tensor_apply, lcuProj]
  · simp [HilbertOperator.tensor_apply, lcuProj, h]

theorem lcuSelectOp_mem_unitaryGroup (U : Fin (2 ^ a) → Gate (Qubits n)) :
    lcuSelectOp U ∈ Matrix.unitaryGroup (Fin (2 ^ (a + n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext r c
  rcases (prodEquiv (m := a) (n := n)).surjective r with ⟨⟨x, y⟩, rfl⟩
  rcases (prodEquiv (m := a) (n := n)).surjective c with ⟨⟨x', y'⟩, rfl⟩
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  change (∑ p : Fin (2 ^ a) × Fin (2 ^ n),
      lcuSelectOp U (prodEquiv (x, y)) (prodEquiv p) *
        star (lcuSelectOp U (prodEquiv (x', y')) (prodEquiv p))) =
    (1 : HilbertOperator (Qubits (a + n))) (prodEquiv (x, y)) (prodEquiv (x', y'))
  by_cases hxx : x = x'
  · subst x'
    have hU := (U x).unitary
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU
    have hentry := congrFun (congrFun hU y) y'
    rw [Matrix.mul_apply] at hentry
    rw [Fintype.sum_prod_type]
    simpa [lcuSelectOp_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hentry
  · rw [Fintype.sum_prod_type]
    simp [lcuSelectOp_apply, hxx, eq_comm]

/-- The select operator as a unitary gate. -/
def lcuSelect (U : Fin (2 ^ a) → Gate (Qubits n)) : Gate (Qubits (a + n)) :=
  Gate.ofUnitary (lcuSelectOp U) (lcuSelectOp_mem_unitaryGroup U)

/-- The coefficient 1-norm `lambda = sum_i alpha_i` for nonnegative coefficients. -/
def lcuNorm (alpha : Fin (2 ^ a) → ℝ) : ℝ := ∑ i, alpha i

/-- The system operator `A = sum_i alpha_i U_i` encoded by the LCU walk. -/
def lcuCombination (alpha : Fin (2 ^ a) → ℝ) (U : Fin (2 ^ a) → Gate (Qubits n)) :
    HilbertOperator (Qubits n) :=
  ∑ i, ((alpha i : ℝ) : ℂ) • (U i : HilbertOperator (Qubits n))

/-- The LCU walk gate `W = (V† ⊗ I) · SELECT · (V ⊗ I)`. -/
def lcuWalk (V : Gate (Qubits a)) (U : Fin (2 ^ a) → Gate (Qubits n)) : Gate (Qubits (a + n)) :=
  Gate.tensor V.conjTranspose (1 : Gate (Qubits n)) *
    lcuSelect U * Gate.tensor V (1 : Gate (Qubits n))

/-- Sandwiching a control projector between `V†` and `V` and reading the
`(0, 0)` entry leaves the squared first-column amplitude. -/
private theorem lcuProj_sandwich (V : Gate (Qubits a)) (i : Fin (2 ^ a)) :
    (((V.conjTranspose : HilbertOperator (Qubits a)) * lcuProj i *
        (V : HilbertOperator (Qubits a))) 0 0)
      = star (V i 0) * V i 0 := by
  change
      ((((V : HilbertOperator (Qubits a)).conjTranspose * lcuProj i *
          (V : HilbertOperator (Qubits a))) 0 0)) =
        star (V i 0) * V i 0
  have hsum : (∑ k, star (V k 0) * (if k = i then (1 : ℂ) else 0)) = star (V i 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    exact Fintype.sum_ite_eq' i (fun k => star (V k 0))
  have hsum2 : (∑ c, (if c = i then (1 : ℂ) else 0) * V c 0) = V i 0 := by
    simp only [ite_mul, one_mul, zero_mul]
    exact Fintype.sum_ite_eq' i (fun c => V c 0)
  have key : ∀ c, ((V : HilbertOperator (Qubits a)).conjTranspose * lcuProj i) 0 c
      = star (V i 0) * (if c = i then (1 : ℂ) else 0) := by
    intro c
    rw [Matrix.mul_apply]
    simp only [lcuProj, Matrix.of_apply, Matrix.conjTranspose_apply, ← mul_assoc]
    rw [← Finset.sum_mul, hsum]
  rw [Matrix.mul_apply]
  calc
    ∑ c, (((V : HilbertOperator (Qubits a)).conjTranspose * lcuProj i) 0 c) * V c 0
        = ∑ c, (star (V i 0) * (if c = i then (1 : ℂ) else 0)) * V c 0 := by
          refine Finset.sum_congr rfl fun c _ => by rw [key c]
    _ = ∑ c, star (V i 0) * ((if c = i then (1 : ℂ) else 0) * V c 0) := by
          refine Finset.sum_congr rfl fun c _ => by ring
    _ = star (V i 0) * (∑ c, (if c = i then (1 : ℂ) else 0) * V c 0) := by
          rw [Finset.mul_sum]
    _ = star (V i 0) * V i 0 := by rw [hsum2]

/-- The LCU walk operator expands into a control-block sum. -/
theorem lcuWalk_eq_sum (V : Gate (Qubits a)) (U : Fin (2 ^ a) → Gate (Qubits n)) :
    (lcuWalk V U : HilbertOperator (Qubits (a + n)))
      = ∑ i, HilbertOperator.tensor
          ((V.conjTranspose : HilbertOperator (Qubits a)) * lcuProj i *
            (V : HilbertOperator (Qubits a)))
          (U i : HilbertOperator (Qubits n)) := by
  unfold lcuWalk lcuSelect
  change
      HilbertOperator.tensor (V.conjTranspose : HilbertOperator (Qubits a))
        (1 : HilbertOperator (Qubits n))
      * lcuSelectOp U
      * HilbertOperator.tensor (V : HilbertOperator (Qubits a)) (1 : HilbertOperator (Qubits n))
      = ∑ i, HilbertOperator.tensor
          ((V.conjTranspose : HilbertOperator (Qubits a)) * lcuProj i *
            (V : HilbertOperator (Qubits a)))
          (U i : HilbertOperator (Qubits n))
  unfold lcuSelectOp
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor]
  simp

/-- The projected LCU block, entry by entry [Lin22, hermfunc.tex:531]. -/
theorem lcuWalk_projected_entry (V : Gate (Qubits a)) (U : Fin (2 ^ a) → Gate (Qubits n))
    (alpha : Fin (2 ^ a) → ℝ) (halpha : ∀ i, 0 ≤ alpha i) (hlam : 0 < lcuNorm alpha)
    (hV : ∀ i, V i 0 = ((Real.sqrt (alpha i / lcuNorm alpha) : ℝ) : ℂ))
    (s t : Fin (2 ^ n)) :
    projectedBlock a n (lcuWalk V U : HilbertOperator (Qubits (a + n))) s t
      = ((lcuNorm alpha : ℂ))⁻¹ * ∑ i, ((alpha i : ℝ) : ℂ) * U i s t := by
  have tprod :
      ∀ (G : HilbertOperator (Qubits a)) (K : HilbertOperator (Qubits n))
        (x x' : Fin (2 ^ a)) (y y' : Fin (2 ^ n)),
      (HilbertOperator.tensor G K) (prodEquiv (x, y)) (prodEquiv (x', y'))
        = G x x' * K y y' := by
    intro G K x x' y y'
    rw [HilbertOperator.tensor_apply]
    simp only [Equiv.symm_apply_apply]
  unfold projectedBlock
  rw [lcuWalk_eq_sum, Matrix.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tprod, lcuProj_sandwich]
  have hnn : (0 : ℝ) ≤ alpha i / lcuNorm alpha := div_nonneg (halpha i) hlam.le
  rw [hV i, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hnn, Complex.ofReal_div]
  ring

/-- **LCU block encoding** [Lin22, hermfunc.tex:531]. -/
theorem LinearCombinationOfUnitaries.main (V : Gate (Qubits a)) (U : Fin (2 ^ a) → Gate (Qubits n))
    (alpha : Fin (2 ^ a) → ℝ) (halpha : ∀ i, 0 ≤ alpha i) (hlam : 0 < lcuNorm alpha)
    (hV : ∀ i, V i 0 = ((Real.sqrt (alpha i / lcuNorm alpha) : ℝ) : ℂ)) :
    ExactBlockEncoding a n (lcuWalk V U)
      (((lcuNorm alpha : ℂ))⁻¹ • lcuCombination alpha U) := by
  constructor
  intro s t
  rw [lcuWalk_projected_entry V U alpha halpha hlam hV]
  change ((lcuNorm alpha : ℂ))⁻¹ * ∑ i, ((alpha i : ℝ) : ℂ) * U i s t
    = ((lcuNorm alpha : ℂ))⁻¹ * (lcuCombination alpha U s t)
  unfold lcuCombination
  simp [Matrix.sum_apply, Finset.mul_sum]

end

end QuantumAlg
