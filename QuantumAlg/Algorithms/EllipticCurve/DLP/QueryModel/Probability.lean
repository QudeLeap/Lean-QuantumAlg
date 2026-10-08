/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.FourierLaw
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.State

/-!
# Original hidden-line amplitude floor for intrinsic declared ECDLP

The actual intrinsic point labels are injective. Their Fourier amplitudes
equal the original finite-cyclic hidden-line sums and inherit the existing
backend-independent floor. A secret witness appears only in the proof of
which outcomes are useful [PZ03, ecc.tex:1531-1666].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] problem

open FiniteCyclicDLP.Canonical.Probability

/-- Intrinsic point label of one original generator-power fiber. -/
@[expose] public def selectedPointLabel (I : ECDLPInstance E) (index : Fin I.subgroupOrder) :
    Fin (2 ^ Layout.pointWidth E) :=
  pointLabel ((problem I).generator ^ index.val)

/-- Distinct original generator powers occupy distinct physical point labels. -/
public theorem selectedPointLabel_injective (I : ECDLPInstance E) :
    Function.Injective (selectedPointLabel I) := by
  intro left right same
  have powers := pointLabel_injective same
  apply Fin.ext
  have remainders := (pow_inj_mod).mp powers
  have orderIdentity : (problem I).order = I.subgroupOrder := rfl
  rw [← (problem I).order_eq_orderOf, orderIdentity,
    Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt] at remainders
  exact remainders

private theorem postQueryCoefficient_selectedPointLabel (I : ECDLPInstance E)
    (input : SecretInput (problem I))
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (index : Fin I.subgroupOrder) :
    postQueryCoefficient I left right (selectedPointLabel I index) =
      if inRange : right.val < I.subgroupOrder then
        if left.val = (fiberLeft (problem I) input index ⟨right.val, inRange⟩).val then
          FiniteCyclicDLP.OrderPreparation.invSqrtOrder I.subgroupOrder *
            FiniteCyclicDLP.OrderPreparation.invSqrtOrder I.subgroupOrder
        else 0
      else 0 := by
  classical
  unfold postQueryCoefficient
  by_cases rightRange : right.val < I.subgroupOrder
  · simp only [rightRange, if_true, dite_true]
    by_cases leftRange : left.val < I.subgroupOrder
    · simp only [leftRange, if_true]
      have pointEquality :
          selectedPointLabel I index =
            pointLabel ((problem I).toSourceScope.oracleMultiplier left.val right.val) ↔
          left.val = (fiberLeft (problem I) input index ⟨right.val, rightRange⟩).val := by
        constructor
        · intro same
          have powers := pointLabel_injective same
          exact congrArg Fin.val
            ((oracleMultiplier_eq_generator_pow_iff (problem I) input
              ⟨left.val, leftRange⟩ ⟨right.val, rightRange⟩ index).mp powers.symm)
        · intro same
          have sameFin : (⟨left.val, leftRange⟩ : Fin I.subgroupOrder) =
              fiberLeft (problem I) input index ⟨right.val, rightRange⟩ := Fin.ext same
          have multiplier :
              (problem I).toSourceScope.oracleMultiplier left.val right.val =
                (problem I).generator ^ index.val :=
            (oracleMultiplier_eq_generator_pow_iff (problem I) input
              ⟨left.val, leftRange⟩ ⟨right.val, rightRange⟩ index).mpr sameFin
          exact congrArg pointLabel multiplier.symm
      rw [if_congr pointEquality rfl rfl]
    · have different :
          left.val ≠ (fiberLeft (problem I) input index ⟨right.val, rightRange⟩).val := by
        intro same
        exact leftRange (same ▸
          (fiberLeft (problem I) input index ⟨right.val, rightRange⟩).isLt)
      simp only [leftRange, if_false, different]
  · simp only [rightRange, if_false, dite_false]

/-- The intrinsic source amplitude is the original hidden-line fiber sum. -/
public theorem sourceAmplitude_selectedPointLabel_eq_sum (I : ECDLPInstance E)
    (input : SecretInput (problem I))
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (index : Fin I.subgroupOrder) :
    sourceAmplitude I left right (selectedPointLabel I index) =
      ∑ sourceRight : Fin I.subgroupOrder,
        selectedFiberTerm input left right index sourceRight := by
  classical
  unfold sourceAmplitude
  rw [Finset.sum_comm]
  calc
    _ = ∑ sourceRight : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)),
        if inRange : sourceRight.val < I.subgroupOrder then
          selectedFiberTerm input left right index ⟨sourceRight.val, inRange⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro sourceRight _
      simp_rw [postQueryCoefficient_selectedPointLabel I input]
      by_cases inRange : sourceRight.val < I.subgroupOrder
      · simp only [inRange, dite_true]
        simp_rw [mul_ite, mul_zero]
        let selected : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)) :=
          ⟨(fiberLeft (problem I) input index ⟨sourceRight.val, inRange⟩).val,
            (fiberLeft (problem I) input index ⟨sourceRight.val, inRange⟩).isLt.trans_le
              (FiniteCyclicDLP.order_le_fourierModulus (problem I))⟩
        rw [Fintype.sum_eq_single selected]
        · simp [selected, selectedFiberTerm, FiniteCyclicDLP.OrderPreparation.invSqrtOrder,
            FiniteCyclicDLP.invSqrtOrder, problem]
        · intro other different
          have differentValue :
              other.val ≠ (fiberLeft (problem I) input index ⟨sourceRight.val, inRange⟩).val := by
            intro same
            exact different (Fin.ext same)
          simp [differentValue]
      · simp [inRange]
    _ = _ := sum_fin_fourierModulus_if_sourceRange (problem I)
      (selectedFiberTerm input left right index)

/-- The actual declared-query state retains the original selected amplitude floor. -/
public theorem sourceState_selectedPointLabel_amplitude_floor (I : ECDLPInstance E)
    (A : Access I) (input : SecretInput (problem I))
    (unit : (ZMod (problem I).order)ˣ) (index : Fin I.subgroupOrder) :
    1 / (2 * (FiniteCyclicDLP.fourierModulus (problem I) : ℝ)) ≤
      ‖sourceState I A (rawBasis I
        (selectedIndex (problem I) (unit : ZMod (problem I).order))
        (selectedIndex (problem I) (-input.secret * (unit : ZMod (problem I).order)))
        (selectedPointLabel I index))‖ := by
  rw [sourceState_rawBasis, sourceAmplitude_selectedPointLabel_eq_sum I input]
  exact one_div_two_fourierModulus_le_norm_sum_selectedFiberTerm (problem I) input unit index

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
