/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.QKernel.DiscreteLogConcept
import all QuantumAlg.Primitives.QKernel.DiscreteLogConcept
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Conditional quantum-kernel learning advantage

The source proves a conditional learning separation for a discrete-log concept
class over a prime-field multiplicative group [LAT21, arxiv.tex:263-287,332-334].
This file abstracts its reduction strategy to a finite cyclic group under
named hardness, reduction, and quantum-accuracy hypotheses. The classical
accuracy ceiling follows by contrapositive using the proved secret-homogeneity
`acc_shift` in `QuantumAlg.Primitives.QKernel.DiscreteLogConcept`, corresponding
to the source's shift-of-concept reduction [LAT21, arxiv.tex:431-455].
The hardness proposition and quantum accuracy floor are supplied data; this
structure does not itself construct the source learner or prove its efficiency.

The expressivity (density-matrix EQK realization) half lives in
`QuantumAlg.Primitives.QKernel.Expressivity`; the fidelity-kernel PSD foundation is in
`QuantumAlg.Primitives.QKernel.Fidelity`.

Source: Liu, Arunachalam & Temme (2021), *A rigorous and robust quantum speed-up in supervised
machine learning* [LAT21, arxiv.tex:283-287,332-336].
-/

section

namespace QuantumAlg

/-- **Conditional quantum-kernel learning advantage**, abstracting the source
separation [LAT21, arxiv.tex:263-287,332-334] to a finite cyclic group `G` under
explicit hypotheses. The classical ceiling is derived by contrapositive using
`acc_shift`: a predictor beating `1/2 + ε`, transported to the fixed concept
`f_1`, implies the supplied proposition `ClassicalSolvesDLP` through
`singleConceptReduction`.

The named fields model classical DLP hardness, the learning-to-DLP reduction
[LAT21, arxiv.tex:431-455], and the SVM-QKE accuracy guarantee
[LAT21, arxiv.tex:332-334]. Their concrete algorithmic and complexity content
remains an input to this structure; the algebraic shift step is proved by
`dlogConcept_reduction`. -/
public structure QuantumKernelAdvantage (G : Type*) [Group G] [Fintype G] [IsCyclic G] where
  /-- A generator of the cyclic group. -/
  g : G
  /-- `g` generates `G`. -/
  hg : ∀ x, x ∈ Subgroup.zpowers g
  /-- The classical advantage gap above chance that is provably unreachable. -/
  ε : ℝ
  /-- The gap is positive. -/
  hε : 0 < ε
  /-- The chance ceiling stays strictly below the quantum floor. -/
  hε_lt : 1 / 2 + ε < 99 / 100
  /-- An opaque proposition standing for "the discrete-log problem is classically easy". -/
  ClassicalSolvesDLP : Prop
  /-- **DLP hardness** ([LAT21, arxiv.tex:284] assumption): no efficient classical DLP solver. -/
  dlpHard : ¬ ClassicalSolvesDLP
  /-- The classical learner under scrutiny. -/
  classicalPredictor : G → Bool
  /-- The secret labelling the learner targets. -/
  classicalSecret : ZMod (Nat.card G)
  /-- The learner's (uniform) test accuracy. -/
  classicalAcc : ℝ
  /-- The accuracy is the uniform agreement with the concept `f_{classicalSecret}`. -/
  classicalAcc_def : classicalAcc = acc g hg classicalPredictor classicalSecret
  /-- **The reduction** ([LAT21, arxiv.tex:284]): an above-chance learner for
  the fixed concept `f_1` yields an efficient DLP solver. Its algebraic step is
  `dlogConcept_reduction`. -/
  singleConceptReduction :
    (1 / 2 + ε <
      acc g hg (fun y => classicalPredictor (y * gpow g hg (classicalSecret - 1))) 1)
      → ClassicalSolvesDLP
  /-- The quantum-kernel SVM's accuracy. -/
  quantumAcc : ℝ
  /-- **Quantum floor** ([LAT21, arxiv.tex:333]): the SVM with quantum-kernel estimation is highly
  accurate (margin generalization). -/
  quantumFloor : (99 : ℝ) / 100 ≤ quantumAcc

/-- Genuine **classical accuracy ceiling**: under DLP hardness, the classical learner cannot
beat `1/2 + ε`. The proof transports the learner to the fixed concept via `acc_shift` and
applies the reduction, contradicting hardness. -/
lemma QuantumKernelAdvantage.classical_ceiling {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (M : QuantumKernelAdvantage G) : M.classicalAcc ≤ 1 / 2 + M.ε := by
  by_contra h
  push Not at h
  refine M.dlpHard (M.singleConceptReduction ?_)
  rw [acc_shift, ← M.classicalAcc_def]
  exact h

/-- Under the supplied hardness, reduction, and quantum-floor hypotheses, the
quantum accuracy exceeds the accuracy of the classical predictor in `M`. -/
public theorem QuantumKernelAdvantage.main {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (M : QuantumKernelAdvantage G) : M.classicalAcc < M.quantumAcc :=
  lt_of_le_of_lt M.classical_ceiling (lt_of_lt_of_le M.hε_lt M.quantumFloor)

/-- The conditional-separation hypotheses are jointly satisfiable (not vacuous): a concrete
`QuantumKernelAdvantage` on the order-2 cyclic group, with an always-wrong classical predictor
(`acc = 0`), so the reduction's premise is false and the bundle is consistent with `dlpHard`. -/
private lemma qka_nonempty : Nonempty (QuantumKernelAdvantage (Multiplicative (ZMod 2))) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Multiplicative (ZMod 2))
  refine ⟨{
    g := g, hg := hg, ε := 1 / 100, hε := by norm_num, hε_lt := by norm_num
    ClassicalSolvesDLP := False, dlpHard := not_false
    classicalPredictor := fun x => !(dlogConcept g hg 1 x)
    classicalSecret := 1
    classicalAcc := acc g hg (fun x => !(dlogConcept g hg 1 x)) 1
    classicalAcc_def := rfl
    singleConceptReduction := ?_
    quantumAcc := 1, quantumFloor := by norm_num }⟩
  intro h
  -- the shift `1 - 1 = 0` makes `gpow … = 1`, so the shifted predictor is the original
  simp only [sub_self, gpow_zero, mul_one] at h
  have hfilt : (Finset.univ.filter
      (fun x => (!(dlogConcept g hg 1 x)) = dlogConcept g hg 1 x)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun x _ => by cases dlogConcept g hg 1 x <;> simp)
  have hz : acc g hg (fun x => !(dlogConcept g hg 1 x)) 1 = 0 := by
    simp only [acc, hfilt, Finset.card_empty, Nat.cast_zero, zero_div]
  rw [hz] at h
  norm_num at h

end QuantumAlg

end
