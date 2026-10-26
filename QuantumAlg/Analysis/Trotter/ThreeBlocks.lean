/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.Trotter.SecondOrder

/-!
# Three-block second-order commutator estimates

The finite three-entry expansion uses the nested-commutator normalization of
[CST+21, prefactor.tex:105-114]. The norm-only polynomial below is a coarse
algebraic consequence of the triangle inequality and submultiplicativity.
It is not a model-specific or sharp commutator estimate.
-/

@[expose] public section

namespace QuantumAlg.Trotter

open HilbertOperator

noncomputable section

/-- Exact three-entry expansion, including both half-weighted self-nested terms. -/
lemma secondOrderCommutatorSum_three {R : Register} (I P G : Hamiltonian R) :
    secondOrderCommutatorSum ![I, P, G] =
      opNorm (⁅(P : HilbertOperator R) + (G : HilbertOperator R),
        ⁅(P : HilbertOperator R) + (G : HilbertOperator R),
        (I : HilbertOperator R)⁆⁆) +
      (1 / 2 : ℝ) * opNorm (⁅(I : HilbertOperator R), ⁅(I : HilbertOperator R),
        (P : HilbertOperator R) + (G : HilbertOperator R)⁆⁆) +
      opNorm (⁅(G : HilbertOperator R), ⁅(G : HilbertOperator R),
        (P : HilbertOperator R)⁆⁆) +
      (1 / 2 : ℝ) * opNorm (⁅(P : HilbertOperator R), ⁅(P : HilbertOperator R),
        (G : HilbertOperator R)⁆⁆) := by
  simp [secondOrderCommutatorSum, Fin.sum_univ_succ, Ring.lie_def]
  ring

private lemma central_nested_shift {R : Register} (I C T : HilbertOperator R)
    (hCI : Commute C I) (hCT : Commute C T) :
    ⁅I + C, ⁅I + C, T⁆⁆ = ⁅I, ⁅I, T⁆⁆ := by
  have hinner : ⁅I + C, T⁆ = ⁅I, T⁆ := by
    simp only [Ring.lie_def, add_mul, mul_add]
    rw [hCT.eq]
    abel
  have houter : Commute C ⁅I, T⁆ := by
    simpa only [Ring.lie_def] using (hCI.mul_right hCT).sub_right (hCT.mul_right hCI)
  rw [hinner]
  change (I + C) * ⁅I, T⁆ - ⁅I, T⁆ * (I + C) = _
  rw [add_mul, mul_add, houter.eq]
  change I * ⁅I, T⁆ + ⁅I, T⁆ * C - (⁅I, T⁆ * I + ⁅I, T⁆ * C) =
    I * ⁅I, T⁆ - ⁅I, T⁆ * I
  abel

/-- A central shift of the first block preserves the actual weighted sum.
Commutation with the first block removes the repeated-self cross term. -/
lemma secondOrderCommutatorSum_three_centralShift {R : Register}
    (I C P G : Hamiltonian R)
    (hCI : Commute (C : HilbertOperator R) (I : HilbertOperator R))
    (hCP : Commute (C : HilbertOperator R) (P : HilbertOperator R))
    (hCG : Commute (C : HilbertOperator R) (G : HilbertOperator R)) :
    secondOrderCommutatorSum ![I + C, P, G] = secondOrderCommutatorSum ![I, P, G] := by
  have hCT := hCP.add_right hCG
  have htail : ⁅(P : HilbertOperator R) + (G : HilbertOperator R),
      (I : HilbertOperator R) + (C : HilbertOperator R)⁆ =
      ⁅(P : HilbertOperator R) + (G : HilbertOperator R), (I : HilbertOperator R)⁆ := by
    simp only [Ring.lie_def, mul_add, add_mul]
    rw [hCP.eq, hCG.eq]
    abel
  rw [secondOrderCommutatorSum_three, secondOrderCommutatorSum_three]
  simp only [Hamiltonian.coe_hAdd, htail, central_nested_shift _ _ _ hCI hCT]

private lemma commutator_opNorm_le {R : Register} (X Y : HilbertOperator R) :
    opNorm ⁅X, Y⁆ ≤ 2 * opNorm X * opNorm Y := by
  calc
    _ ≤ opNorm (X * Y) + opNorm (Y * X) := opNorm_sub_le _ _
    _ ≤ opNorm X * opNorm Y + opNorm Y * opNorm X :=
      add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
    _ = _ := by ring

private lemma nested_opNorm_le {R : Register} (X Y : HilbertOperator R)
    (x y : ℝ) (hx : opNorm X ≤ x) (hy : opNorm Y ≤ y) (hx0 : 0 ≤ x) :
    opNorm ⁅X, ⁅X, Y⁆⁆ ≤ 4 * x ^ 2 * y := by
  have hxy : opNorm ⁅X, Y⁆ ≤ 2 * x * y :=
    (commutator_opNorm_le X Y).trans (by
      gcongr
      exact opNorm_nonneg Y)
  calc
    _ ≤ 2 * opNorm X * opNorm ⁅X, Y⁆ := commutator_opNorm_le _ _
    _ ≤ 2 * x * (2 * x * y) := by
      gcongr
      exact opNorm_nonneg ⁅X, Y⁆
    _ = _ := by ring

/-- A norm-only coarse bound on the actual three-block weighted sum. -/
lemma secondOrderCommutatorSum_three_le {R : Register} (I P G : Hamiltonian R)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : I.opNorm ≤ a) (hP : P.opNorm ≤ b) (hG : G.opNorm ≤ b) :
    secondOrderCommutatorSum ![I, P, G] ≤ 16 * a * b ^ 2 + 4 * a ^ 2 * b + 6 * b ^ 3 := by
  have hT : opNorm ((P : HilbertOperator R) + (G : HilbertOperator R)) ≤ 2 * b :=
    (opNorm_add_le _ _).trans (by change P.opNorm + G.opNorm ≤ _; linarith)
  have hTI := nested_opNorm_le ((P : HilbertOperator R) + (G : HilbertOperator R)) I (2 * b) a hT hI
    (by positivity)
  have hIT := nested_opNorm_le (I : HilbertOperator R)
    ((P : HilbertOperator R) + (G : HilbertOperator R))
    a (2 * b) hI hT ha
  have hGP := nested_opNorm_le (G : HilbertOperator R) P b b hG hP hb
  have hPG := nested_opNorm_le (P : HilbertOperator R) G b b hP hG hb
  rw [secondOrderCommutatorSum_three]
  nlinarith

/-- The coarse bound depends on the unshifted first block when the shift is central. -/
lemma secondOrderCommutatorSum_three_centralShift_le {R : Register}
    (I C P G : Hamiltonian R)
    (hCI : Commute (C : HilbertOperator R) (I : HilbertOperator R))
    (hCP : Commute (C : HilbertOperator R) (P : HilbertOperator R))
    (hCG : Commute (C : HilbertOperator R) (G : HilbertOperator R))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : I.opNorm ≤ a) (hP : P.opNorm ≤ b) (hG : G.opNorm ≤ b) :
    secondOrderCommutatorSum ![I + C, P, G] ≤
      16 * a * b ^ 2 + 4 * a ^ 2 * b + 6 * b ^ 3 := by
  rw [secondOrderCommutatorSum_three_centralShift I C P G hCI hCP hCG]
  exact secondOrderCommutatorSum_three_le I P G a b ha hb hI hP hG

end

end QuantumAlg.Trotter
