/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Util.FinPow

/-!
# Block encodings

Components-layer predicates for exact and approximate block encodings. Following
the standard `(alpha, a, epsilon)` convention, the carrier `U` is a metadata-free
`UnitaryOperator`, while the encoded target `A` is a possibly non-unitary
`HilbertOperator`. The ancilla convention is explicit: the block is obtained by
projecting the ancilla register onto the computational-basis state `0^a` on both
sides, with system basis labels carried by `QuantumAlg.prodEquiv`.
-/

section

namespace QuantumAlg

noncomputable section

/-- The top-left projected system block
`(<0^a| ⊗ I) U (|0^a> ⊗ I)` as a Hilbert operator on the system register. -/
public def projectedBlock (a n : Nat) (U : HilbertOperator (Qubits (a + n))) :
    HilbertOperator (Qubits n) :=
  fun i j =>
    U (prodEquiv ((0 : Fin (2 ^ a)), i)) (prodEquiv ((0 : Fin (2 ^ a)), j))

/-- A finite-dimensional squared error for the projected block.  This records
the norm-style `epsilon` convention without committing the base Core layer to a
heavier operator-norm API. -/
public def blockEncodingErrorSq (a n : Nat) (α : ℝ)
    (U : UnitaryOperator (Qubits (a + n)))
    (A : HilbertOperator (Qubits n)) : ℝ :=
  ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ n),
    Complex.normSq
      (A i j - (α : ℂ) * projectedBlock a n (U : HilbertOperator (Qubits (a + n))) i j)

/-- An `(alpha, a, epsilon)` block encoding: after scaling the top-left
projected block by `alpha`, the result is within `epsilon` of `A`. -/
public structure BlockEncoding (α : ℝ) (a n : Nat) (ε : ℝ)
    (U : UnitaryOperator (Qubits (a + n))) (A : HilbertOperator (Qubits n)) : Prop where
  alpha_pos : 0 < α
  epsilon_nonneg : 0 <= ε
  block_error : blockEncodingErrorSq a n α U A <= ε ^ 2

/-- Exact block encoding with ancilla size `a`: the `0^a` projected block of
the unitary carrier `U` is exactly the system operator `A`.  This is the
`alpha = 1`, `epsilon = 0` special case of `BlockEncoding`, witnessed by
`ExactBlockEncoding.toBlockEncoding`. -/
public structure ExactBlockEncoding (a n : Nat) (U : UnitaryOperator (Qubits (a + n)))
    (A : HilbertOperator (Qubits n)) : Prop where
  block_eq : ∀ i j : Fin (2 ^ n),
    projectedBlock a n (U : HilbertOperator (Qubits (a + n))) i j = A i j

theorem ExactBlockEncoding.projected_block_eq {a n : Nat}
    {U : UnitaryOperator (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (h : ExactBlockEncoding a n U A) :
    projectedBlock a n (U : HilbertOperator (Qubits (a + n))) = A := by
  ext i j
  exact h.block_eq i j

theorem ExactBlockEncoding.block_entry {a n : Nat}
    {U : UnitaryOperator (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (h : ExactBlockEncoding a n U A) (i j : Fin (2 ^ n)) :
    (U : HilbertOperator (Qubits (a + n)))
      (prodEquiv ((0 : Fin (2 ^ a)), i)) (prodEquiv ((0 : Fin (2 ^ a)), j))
      = A i j :=
  h.block_eq i j

theorem exactBlockEncoding_iff_projectedBlock {a n : Nat}
    {U : UnitaryOperator (Qubits (a + n))} {A : HilbertOperator (Qubits n)} :
    ExactBlockEncoding a n U A ↔
      projectedBlock a n (U : HilbertOperator (Qubits (a + n))) = A := by
  constructor
  · intro h
    exact h.projected_block_eq
  · intro h
    exact ⟨by intro i j; rw [h]⟩

theorem ExactBlockEncoding.toBlockEncoding {a n : Nat}
    {U : UnitaryOperator (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (h : ExactBlockEncoding a n U A) :
    BlockEncoding 1 a n 0 U A := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simp [blockEncodingErrorSq, h.block_eq]

/-- If the projected block exactly equals `alpha⁻¹ A`, then the same carrier is
an exact `(alpha, a, 0)` block encoding of `A`. -/
theorem ExactBlockEncoding.toScaledBlockEncoding {α : ℝ} (halpha : 0 < α)
    {a n : Nat} {U : UnitaryOperator (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)}
    (h : ExactBlockEncoding a n U ((α : ℂ)⁻¹ • A)) :
    BlockEncoding α a n 0 U A := by
  refine ⟨halpha, by norm_num, ?_⟩
  have halphaC : ((α : ℂ) ≠ 0) := by
    exact_mod_cast ne_of_gt halpha
  have hmulC : (α : ℂ) * (α : ℂ)⁻¹ = 1 := by
    exact mul_inv_cancel₀ halphaC
  have hentry : ∀ i j : Fin (2 ^ n),
      A i j - (α : ℂ) * ((α : ℂ)⁻¹ * A i j) = 0 := by
    intro i j
    rw [← mul_assoc, hmulC, one_mul, sub_self]
  rw [show blockEncodingErrorSq a n α U A = 0 by
    simp [blockEncodingErrorSq, h.block_eq, hentry]]
  norm_num

/-! ## LCU SELECT declarations -/

variable {a n : ℕ}

/-- The control-basis projector `|i><i|` on the `a`-qubit control register. -/
def lcuProj (i : Fin (2 ^ a)) : HilbertOperator (Qubits a) :=
  Matrix.of fun r c =>
    (if r = i then (1 : ℂ) else 0) * (if c = i then (1 : ℂ) else 0)

private theorem lcuSelectFormula_apply
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))
    (x x' : Fin (2 ^ a)) (y y' : Fin (2 ^ n)) :
    (∑ i, HilbertOperator.tensor (lcuProj i)
        (U i : HilbertOperator (Qubits n)))
        (prodEquiv (x, y)) (prodEquiv (x', y'))
      = (if x = x' then U x y y' else 0) := by
  rw [Matrix.sum_apply]
  by_cases h : x = x'
  · subst x'
    simp [HilbertOperator.tensor_apply, lcuProj]
  · simp [HilbertOperator.tensor_apply, lcuProj, h]

/-- Metadata-free SELECT carrier [Lin22, hermfunc.tex:492]. -/
def lcuSelectOp (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    UnitaryOperator (Qubits (a + n)) :=
  UnitaryOperator.ofMatrix
    (∑ i, HilbertOperator.tensor (lcuProj i)
      (U i : HilbertOperator (Qubits n))) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext r c
    rcases (prodEquiv (m := a) (n := n)).surjective r with ⟨⟨x, y⟩, rfl⟩
    rcases (prodEquiv (m := a) (n := n)).surjective c with ⟨⟨x', y'⟩, rfl⟩
    rw [Matrix.mul_apply]
    rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
    change (∑ p : Fin (2 ^ a) × Fin (2 ^ n),
        (∑ i, HilbertOperator.tensor (lcuProj i)
          (U i : HilbertOperator (Qubits n)))
            (prodEquiv (x, y)) (prodEquiv p) *
          star ((∑ i, HilbertOperator.tensor (lcuProj i)
            (U i : HilbertOperator (Qubits n)))
              (prodEquiv (x', y')) (prodEquiv p))) =
      (1 : HilbertOperator (Qubits (a + n)))
        (prodEquiv (x, y)) (prodEquiv (x', y'))
    by_cases hxx : x = x'
    · subst x'
      have hU := (U x).property
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU
      have hentry := congrFun (congrFun hU y) y'
      rw [Matrix.mul_apply] at hentry
      rw [Fintype.sum_prod_type]
      simpa [lcuSelectFormula_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply] using hentry
    · rw [Fintype.sum_prod_type]
      simp [lcuSelectFormula_apply, hxx, eq_comm])

theorem lcuSelectOp_apply (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))
    (x x' : Fin (2 ^ a)) (y y' : Fin (2 ^ n)) :
    lcuSelectOp U (prodEquiv (x, y)) (prodEquiv (x', y'))
      = (if x = x' then U x y y' else 0) := by
  change (∑ i, HilbertOperator.tensor (lcuProj i)
      (U i : HilbertOperator (Qubits n)))
      (prodEquiv (x, y)) (prodEquiv (x', y')) = _
  exact lcuSelectFormula_apply U x x' y y'

/-- Stable opaque-subroutine label for the `a`-control, `n`-system SELECT
family. -/
def lcuSelectSubroutineLabel (a n : Nat) : Resource.SubroutineLabel where
  family := "lcu"
  name := "lcu-select"
  parameters := [a, n]



/-- Literal strict event for one LCU SELECT query. -/
def lcuSelectEvent (a n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (lcuSelectSubroutineLabel a n).quantum

variable (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))

/-- Declared SELECT member at a caller-supplied physical placement. Its fixed
label and operator family are owned by this component. -/
def lcuSelectLeafAt (systemIdx : List Nat) : UnitaryLeaf (Qubits (a + n)) :=
  UnitaryLeaf.subroutine (lcuSelectSubroutineLabel a n) systemIdx (lcuSelectOp U)

/-- Declared SELECT leaf on the canonical joint layout. -/
def lcuSelectLeaf : UnitaryLeaf (Qubits (a + n)) :=
  lcuSelectLeafAt U (List.range (a + n))

end

end QuantumAlg

end
