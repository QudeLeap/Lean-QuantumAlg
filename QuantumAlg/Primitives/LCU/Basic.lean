/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified
public import QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Components.Oracle.BlockEncoding
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Linear combination of unitaries (LCU)

The LCU primitive block-encodes a linear combination of unitaries into a larger
operator acting on an ancilla control register tensored with the system
[Lin22, hermfunc.tex:531].

The SELECT carrier and complete walk are metadata-free `UnitaryOperator`s.
Their private raw matrix formulas prove the projected-block theorem.  The
executable realization is supplied separately under explicit preparation,
inverse-preparation and SELECT access, with resources derived from actual calls.
-/

section

namespace QuantumAlg

noncomputable section

variable {a n : ℕ}

/-- The coefficient 1-norm `lambda = sum_i alpha_i` for nonnegative coefficients. -/
public def lcuNorm (α : Fin (2 ^ a) → ℝ) : ℝ := ∑ i, α i

/-- The system operator `A = sum_i alpha_i U_i` encoded by the LCU walk. -/
public def lcuCombination (α : Fin (2 ^ a) → ℝ)
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    HilbertOperator (Qubits n) :=
  ∑ i, ((α i : ℝ) : ℂ) • (U i : HilbertOperator (Qubits n))

/-- Metadata-free LCU walk
`W = (V† ⊗ I) · SELECT · (V ⊗ I)`. -/
public def lcuWalk (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    UnitaryOperator (Qubits (a + n)) :=
  (V.tensor (1 : UnitaryOperator (Qubits n))).dagger *
    (lcuSelectOp U * V.tensor (1 : UnitaryOperator (Qubits n)))





/-- Sandwiching a control projector between `V†` and `V` and reading the
`(0, 0)` entry leaves the squared first-column amplitude. -/
private theorem lcuProj_sandwich (V : UnitaryOperator (Qubits a))
    (i : Fin (2 ^ a)) :
    (((V : HilbertOperator (Qubits a)).conjTranspose * lcuProj i *
        (V : HilbertOperator (Qubits a))) 0 0)
      = star (V i 0) * V i 0 := by
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

/-- The metadata-free LCU walk expands into a control-block sum. -/
theorem lcuWalk_eq_sum (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (lcuWalk V U : HilbertOperator (Qubits (a + n)))
      = ∑ i, HilbertOperator.tensor
          ((V : HilbertOperator (Qubits a)).conjTranspose * lcuProj i *
            (V : HilbertOperator (Qubits a)))
          (U i : HilbertOperator (Qubits n)) := by
  rw [lcuWalk]
  change
    ((V.tensor (1 : UnitaryOperator (Qubits n))).dagger :
        HilbertOperator (Qubits (a + n))) *
      ((lcuSelectOp U : HilbertOperator (Qubits (a + n))) *
        (V.tensor (1 : UnitaryOperator (Qubits n)) :
          HilbertOperator (Qubits (a + n)))) =
      ∑ i, HilbertOperator.tensor
      ((V : HilbertOperator (Qubits a)).conjTranspose * lcuProj i *
        (V : HilbertOperator (Qubits a)))
      (U i : HilbertOperator (Qubits n))
  rw [UnitaryOperator.coe_dagger, UnitaryOperator.coe_tensor,
    HilbertOperator.conjTranspose_tensor]
  simp only [lcuSelectOp, UnitaryOperator.coe_ofMatrix]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mul_assoc, HilbertOperator.tensor_mul_tensor,
    HilbertOperator.tensor_mul_tensor]
  simp

/-- The projected LCU block, entry by entry [Lin22, hermfunc.tex:531]. -/
theorem lcuWalk_projected_entry (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))
    (α : Fin (2 ^ a) → ℝ) (halpha : ∀ i, 0 ≤ α i) (hlam : 0 < lcuNorm α)
    (hV : ∀ i, V i 0 = ((Real.sqrt (α i / lcuNorm α) : ℝ) : ℂ))
    (s t : Fin (2 ^ n)) :
    projectedBlock a n
        (lcuWalk V U : HilbertOperator (Qubits (a + n))) s t
      = ((lcuNorm α : ℂ))⁻¹ * ∑ i, ((α i : ℝ) : ℂ) * U i s t := by
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
  have hnn : (0 : ℝ) ≤ α i / lcuNorm α := div_nonneg (halpha i) hlam.le
  rw [hV i, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hnn, Complex.ofReal_div]
  ring

/-- **LCU block encoding** [Lin22, hermfunc.tex:531]. -/
public theorem lcuWalk_exactBlockEncoding (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))
    (α : Fin (2 ^ a) → ℝ) (halpha : ∀ i, 0 ≤ α i) (hlam : 0 < lcuNorm α)
    (hV : ∀ i, V i 0 = ((Real.sqrt (α i / lcuNorm α) : ℝ) : ℂ)) :
    ExactBlockEncoding a n (lcuWalk V U)
      (((lcuNorm α : ℂ))⁻¹ • lcuCombination α U) := by
  constructor
  intro s t
  rw [lcuWalk_projected_entry V U α halpha hlam hV]
  change ((lcuNorm α : ℂ))⁻¹ * ∑ i, ((α i : ℝ) : ℂ) * U i s t
    = ((lcuNorm α : ℂ))⁻¹ * (lcuCombination α U s t)
  unfold lcuCombination
  simp [Matrix.sum_apply, Finset.mul_sum]

end

end QuantumAlg

end
