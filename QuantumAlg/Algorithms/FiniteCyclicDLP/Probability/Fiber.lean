/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.QFT.Construction
public import QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Primitives.QFT.Mathematics
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import QuantumAlg.Util.Complex
import all QuantumAlg.Util.Complex
public import QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Util.FiniteCyclicDLP
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Pure hidden-line Fourier fibers

The original known-order frequency selection and fiber phase estimates use
the unchanged twelve-fold oversampling. Their source sums and amplitude
factorization are mathematical statements independent of any oracle access,
runtime encoding, terminal-measurement backend, or recovery implementation.

The secret is a proof-side witness identifying useful Fourier frequencies.
It is not an executable program parameter. The bounds require neither a
prime group order nor a finite enumeration of the ambient group.
-/

section

namespace QuantumAlg

open scoped BigOperators

noncomputable section

namespace FiniteCyclicDLP
namespace Canonical
namespace Probability

universe u

variable {G : Type u} [Group G]

/-- The secret witness needed to identify the useful raw Fourier outcomes.
No classical recovery result is included in this input. -/
public structure SecretInput (P : KnownOrderProblem G) where
  /-- Advertised discrete logarithm modulo the known generator order. -/
  secret : ZMod P.order
  /-- The advertised scalar generates the problem target. -/
  target_eq_generator_pow : P.generator ^ secret.val = P.target

/-- The source-scoped target membership and known finite generator order
supply a bounded secret witness for the probability proof. This is a proof
parameter, not an executable input or an enumeration of group elements. -/
public noncomputable def SecretInput.ofKnownOrderProblem
    (P : KnownOrderProblem G) : SecretInput P := by
  classical
  have finiteGenerator : IsOfFinOrder P.generator :=
    orderOf_ne_zero_iff.mp (by
      rw [← P.order_eq_orderOf]
      exact P.order_ne_zero)
  have existsN : ∃ n : Nat, n ∈ Finset.range (orderOf P.generator) ∧
      P.generator ^ n = P.target := Finset.mem_image.mp
    (finiteGenerator.mem_zpowers_iff_mem_range_orderOf.mp P.target_mem_zpowers)
  let n := Classical.choose existsN
  have ⟨nRange, hpow⟩ := Classical.choose_spec existsN
  have bounded : n < P.order := by
    rw [P.order_eq_orderOf]
    exact Finset.mem_range.mp nRange
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  exact ⟨(n : ZMod P.order), by
    simpa only [ZMod.val_natCast_of_lt bounded] using hpow⟩

/-- The canonical bounded natural representative of a residue modulo the
problem order. -/
@[expose] public def residueIndex (P : KnownOrderProblem G) (value : ZMod P.order) :
    Fin P.order :=
  ⟨value.val, by
    let _ : NeZero P.order := ⟨P.order_ne_zero⟩
    exact ZMod.val_lt value⟩

/-- The oversampled Fourier index selected by a residue modulo the problem
order. -/
@[expose] public def selectedIndex (P : KnownOrderProblem G) (value : ZMod P.order) :
    Fin (2 ^ orderWidth P) :=
  selectedRawFrequency P (residueIndex P value)

public theorem selectedIndex_injective (P : KnownOrderProblem G) :
    Function.Injective (selectedIndex P) := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  intro left right h
  apply ZMod.val_injective P.order
  have hscaled := congrArg
    (fun index : Fin (2 ^ orderWidth P) =>
      index.val * P.order / fourierModulus P) h
  simpa [selectedIndex, residueIndex, selectedRawFrequency_scale] using hscaled


/-- Left source index in the fibre determined by a hidden-line sample. -/
@[expose] public def fiberLeft (P : KnownOrderProblem G) (input : SecretInput P)
    (k b : Fin P.order) : Fin P.order :=
  ⟨(k.val + input.secret.val * b.val) % P.order,
    Nat.mod_lt _ P.order_pos⟩

public theorem oracleMultiplier_fiber (P : KnownOrderProblem G)
    (input : SecretInput P) (k b : Fin P.order) :
    P.toSourceScope.oracleMultiplier (fiberLeft P input k b).val b.val =
      P.generator ^ k.val := by
  have horder : orderOf P.generator = P.order := P.order_eq_orderOf.symm
  have hleft :
      P.generator ^ (fiberLeft P input k b).val =
        P.generator ^ (k.val + input.secret.val * b.val) := by
    simpa [fiberLeft, horder] using
      (pow_mod_orderOf P.generator (k.val + input.secret.val * b.val))
  unfold SourceScope.oracleMultiplier
  rw [← input.target_eq_generator_pow, ← pow_mul, hleft, pow_add]
  simp [mul_assoc]

public theorem oracleMultiplier_eq_generator_pow_iff
    (P : KnownOrderProblem G) (input : SecretInput P)
    (a b k : Fin P.order) :
    P.toSourceScope.oracleMultiplier a.val b.val = P.generator ^ k.val ↔
      a = fiberLeft P input k b := by
  constructor
  · intro h
    have hmultiplier :
        P.generator ^ a.val *
            (P.generator ^ (input.secret.val * b.val))⁻¹ =
          P.generator ^ k.val := by
      unfold SourceScope.oracleMultiplier at h
      rw [← input.target_eq_generator_pow, ← pow_mul] at h
      exact h
    have hpower :
        P.generator ^ a.val =
          P.generator ^ (k.val + input.secret.val * b.val) := by
      calc
        P.generator ^ a.val =
            (P.generator ^ a.val *
                (P.generator ^ (input.secret.val * b.val))⁻¹) *
              P.generator ^ (input.secret.val * b.val) := by simp
        _ = P.generator ^ k.val *
              P.generator ^ (input.secret.val * b.val) := by rw [hmultiplier]
        _ = P.generator ^ (k.val + input.secret.val * b.val) :=
          (pow_add _ _ _).symm
    have hmod := (pow_inj_mod).mp hpower
    apply Fin.ext
    simpa [fiberLeft, P.order_eq_orderOf.symm,
      Nat.mod_eq_of_lt a.isLt] using hmod
  · rintro rfl
    exact oracleMultiplier_fiber P input k b


public theorem sum_fin_fourierModulus_if_sourceRange
    (P : KnownOrderProblem G) (f : Fin P.order → ℂ) :
    (∑ i : Fin (2 ^ orderWidth P),
      if hi : i.val < P.order then f ⟨i.val, hi⟩ else 0) =
      ∑ i : Fin P.order, f i := by
  classical
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  have hclean :
      (∑ i ∈ Finset.range (2 ^ orderWidth P),
        if hq : i < 2 ^ orderWidth P then
          if hi : i < P.order then f ⟨i, hi⟩ else 0
        else
          0) =
        ∑ i ∈ Finset.range (2 ^ orderWidth P),
          if hi : i < P.order then f ⟨i, hi⟩ else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hclean]
  symm
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr
      ((Finset.mem_range.mp hi).trans_le (order_le_fourierModulus P))
  · intro i _hi hnot
    have hge : ¬i < P.order := by
      intro hlt
      exact hnot (Finset.mem_range.mpr hlt)
    simp [hge]

/-- Complex contribution of one source pair to a selected Fourier fibre. -/
@[expose] public def selectedFiberTerm {P : KnownOrderProblem G}
    (input : SecretInput P) (left right : Fin (2 ^ orderWidth P))
    (k b : Fin P.order) : ℂ :=
  star (invSqrtN (orderWidth P) *
      ω (orderWidth P) ^ ((fiberLeft P input k b).val * left.val)) *
    star (invSqrtN (orderWidth P) *
      ω (orderWidth P) ^ (b.val * right.val)) *
    (invSqrtOrder P.order * invSqrtOrder P.order)

private def selectedError (P : KnownOrderProblem G) (residue : Fin P.order) :
    Nat :=
  (selectedRawFrequency P residue).val * P.order -
    residue.val * fourierModulus P

private theorem selectedRawFrequency_mul_order (P : KnownOrderProblem G)
    (residue : Fin P.order) :
    (selectedRawFrequency P residue).val * P.order =
      residue.val * fourierModulus P + selectedError P residue := by
  have hlower :
      residue.val * fourierModulus P ≤
        (selectedRawFrequency P residue).val * P.order :=
    QuantumAlg.Nat.le_ceilDiv_mul
      (num := residue.val * fourierModulus P) P.order_pos
  unfold selectedError
  omega

private def selectedLeftResidue (P : KnownOrderProblem G)
    (unit : (ZMod P.order)ˣ) : Fin P.order :=
  residueIndex P (unit : ZMod P.order)

private def selectedRightResidue (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ) : Fin P.order :=
  residueIndex P (-input.secret * (unit : ZMod P.order))

private def balanceQuotient (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ) : Nat :=
  (input.secret.val * (selectedLeftResidue P unit).val +
      (selectedRightResidue P input unit).val) / P.order

private theorem secret_mul_left_add_right_eq_order_mul_balanceQuotient
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) :
    input.secret.val * (selectedLeftResidue P unit).val +
        (selectedRightResidue P input unit).val =
      P.order * balanceQuotient P input unit := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  have hleft :
      ((selectedLeftResidue P unit).val : ZMod P.order) =
        (unit : ZMod P.order) :=
    ZMod.natCast_zmod_val (unit : ZMod P.order)
  have hright :
      ((selectedRightResidue P input unit).val : ZMod P.order) =
        -input.secret * (unit : ZMod P.order) :=
    ZMod.natCast_zmod_val (-input.secret * (unit : ZMod P.order))
  have hsecret : (input.secret.val : ZMod P.order) = input.secret :=
    ZMod.natCast_zmod_val input.secret
  have hzero :
      ((input.secret.val * (selectedLeftResidue P unit).val +
        (selectedRightResidue P input unit).val : Nat) : ZMod P.order) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hsecret, hleft, hright]
    ring
  have hdvd :
      P.order ∣
        input.secret.val * (selectedLeftResidue P unit).val +
          (selectedRightResidue P input unit).val :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  calc
    input.secret.val * (selectedLeftResidue P unit).val +
        (selectedRightResidue P input unit).val =
      (input.secret.val * (selectedLeftResidue P unit).val +
          (selectedRightResidue P input unit).val) / P.order * P.order :=
        (Nat.div_mul_cancel hdvd).symm
    _ = P.order * balanceQuotient P input unit := by
      rw [Nat.mul_comm]
      rfl

private def fiberQuotient (P : KnownOrderProblem G) (input : SecretInput P)
    (tail b : Fin P.order) : Nat :=
  (tail.val + input.secret.val * b.val) / P.order

private theorem fiber_mod_add_order_mul_quotient
    (P : KnownOrderProblem G) (input : SecretInput P)
    (tail b : Fin P.order) :
    (fiberLeft P input tail b).val +
        P.order * fiberQuotient P input tail b =
      tail.val + input.secret.val * b.val := by
  simpa [fiberLeft, fiberQuotient] using
    (Nat.mod_add_div (tail.val + input.secret.val * b.val) P.order)

/-- Integer phase residual appearing in the public selected-fiber phase law. -/
public def phaseError (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail b : Fin P.order) : Nat :=
  (fiberLeft P input tail b).val *
      ((selectedRawFrequency P
          (residueIndex P (unit : ZMod P.order))).val * P.order -
        (residueIndex P (unit : ZMod P.order)).val * fourierModulus P) +
    b.val *
      ((selectedRawFrequency P
          (residueIndex P (-input.secret * (unit : ZMod P.order)))).val *
            P.order -
        (residueIndex P (-input.secret * (unit : ZMod P.order))).val *
          fourierModulus P)

private theorem phaseError_eq_selectedErrors
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail b : Fin P.order) :
    phaseError P input unit tail b =
      (fiberLeft P input tail b).val *
          selectedError P (selectedLeftResidue P unit) +
        b.val * selectedError P (selectedRightResidue P input unit) := by
  rfl

private theorem hiddenLine_phase_nat_identity
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail b : Fin P.order) :
    P.order *
          ((fiberLeft P input tail b).val *
              (selectedIndex P (unit : ZMod P.order)).val +
            b.val *
              (selectedIndex P
                (-input.secret * (unit : ZMod P.order))).val) +
        fourierModulus P * P.order *
          (fiberQuotient P input tail b *
            (selectedLeftResidue P unit).val) =
      fourierModulus P *
          (tail.val * (selectedLeftResidue P unit).val) +
        fourierModulus P * P.order *
          (b.val * balanceQuotient P input unit) +
        phaseError P input unit tail b := by
  have hleft := selectedRawFrequency_mul_order P
    (selectedLeftResidue P unit)
  have hright := selectedRawFrequency_mul_order P
    (selectedRightResidue P input unit)
  have hbalance :=
    secret_mul_left_add_right_eq_order_mul_balanceQuotient P input unit
  have hfiber := fiber_mod_add_order_mul_quotient P input tail b
  change
    P.order *
          ((fiberLeft P input tail b).val *
              (selectedRawFrequency P (selectedLeftResidue P unit)).val +
            b.val *
              (selectedRawFrequency P
                (selectedRightResidue P input unit)).val) +
        fourierModulus P * P.order *
          (fiberQuotient P input tail b *
            (selectedLeftResidue P unit).val) = _
  calc
    P.order *
          ((fiberLeft P input tail b).val *
              (selectedRawFrequency P (selectedLeftResidue P unit)).val +
            b.val *
              (selectedRawFrequency P
                (selectedRightResidue P input unit)).val) +
        fourierModulus P * P.order *
          (fiberQuotient P input tail b *
            (selectedLeftResidue P unit).val) =
      (fiberLeft P input tail b).val *
          ((selectedRawFrequency P (selectedLeftResidue P unit)).val * P.order) +
        b.val *
          ((selectedRawFrequency P
            (selectedRightResidue P input unit)).val * P.order) +
        fourierModulus P * P.order *
          (fiberQuotient P input tail b *
            (selectedLeftResidue P unit).val) := by ring
    _ = (fiberLeft P input tail b).val *
          ((selectedLeftResidue P unit).val * fourierModulus P +
            selectedError P (selectedLeftResidue P unit)) +
        b.val *
          ((selectedRightResidue P input unit).val * fourierModulus P +
            selectedError P (selectedRightResidue P input unit)) +
        fourierModulus P * P.order *
          (fiberQuotient P input tail b *
            (selectedLeftResidue P unit).val) := by
      rw [hleft, hright]
    _ = fourierModulus P *
          (((fiberLeft P input tail b).val +
              P.order * fiberQuotient P input tail b) *
                (selectedLeftResidue P unit).val +
            b.val * (selectedRightResidue P input unit).val) +
        phaseError P input unit tail b := by
      rw [phaseError_eq_selectedErrors]
      ring
    _ = fourierModulus P *
          (tail.val * (selectedLeftResidue P unit).val +
            b.val *
              (input.secret.val * (selectedLeftResidue P unit).val +
                (selectedRightResidue P input unit).val)) +
        phaseError P input unit tail b := by
      rw [hfiber]
      ring
    _ = fourierModulus P *
          (tail.val * (selectedLeftResidue P unit).val) +
        fourierModulus P * P.order *
          (b.val * balanceQuotient P input unit) +
        phaseError P input unit tail b := by
      rw [hbalance]
      ring

/-- Unit-modulus phase attached to one selected Fourier-fibre term. -/
@[expose] public def selectedFiberPhase (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (tail b : Fin P.order) : ℂ :=
  star (ω (orderWidth P) ^
    ((fiberLeft P input tail b).val *
        (selectedIndex P (unit : ZMod P.order)).val +
      b.val *
        (selectedIndex P
          (-input.secret * (unit : ZMod P.order))).val))

/-- Common unit-modulus phase contributed by the observed group-element tail.
It is independent of the source summation variable and hence does not affect
the selected outcome probability.  [Sho95, source.tex:1742-1775] -/
@[expose] public def selectedTailPhase (P : KnownOrderProblem G)
    (unit : (ZMod P.order)ˣ) (tail : Fin P.order) : ℂ :=
  Complex.exp
    (-(2 * Real.pi *
      (((tail.val * (residueIndex P (unit : ZMod P.order)).val : Nat) : ℝ) /
        (P.order : ℝ))) * Complex.I)

/-- Residual selected-fibre phase after removing the common tail phase. -/
@[expose] public def selectedErrorPhase (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (tail b : Fin P.order) : ℂ :=
  Complex.exp
    (-(2 * Real.pi * ((phaseError P input unit tail b : Nat) : ℝ) /
      ((P.order : ℝ) * (fourierModulus P : ℝ))) * Complex.I)

theorem selectedFiberPhase_eq_tail_mul_error
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail b : Fin P.order) :
    selectedFiberPhase P input unit tail b =
      selectedTailPhase P unit tail *
        selectedErrorPhase P input unit tail b := by
  have hphase := hiddenLine_phase_nat_identity P input unit tail b
  have horderR : (P.order : ℝ) ≠ 0 := by
    exact_mod_cast P.order_ne_zero
  have hqR : (fourierModulus P : ℝ) ≠ 0 := by
    unfold fourierModulus
    positivity
  have hphaseR :
      (P.order : ℝ) *
            (((fiberLeft P input tail b).val : ℝ) *
                ((selectedIndex P (unit : ZMod P.order)).val : ℝ) +
              (b.val : ℝ) *
                ((selectedIndex P
                  (-input.secret * (unit : ZMod P.order))).val : ℝ)) +
          (fourierModulus P : ℝ) * (P.order : ℝ) *
            (((fiberQuotient P input tail b : Nat) : ℝ) *
              ((selectedLeftResidue P unit).val : ℝ)) =
        (fourierModulus P : ℝ) *
            ((tail.val : ℝ) * ((selectedLeftResidue P unit).val : ℝ)) +
          (fourierModulus P : ℝ) * (P.order : ℝ) *
            ((b.val : ℝ) * ((balanceQuotient P input unit : Nat) : ℝ)) +
          ((phaseError P input unit tail b : Nat) : ℝ) := by
    exact_mod_cast hphase
  have hratio :
      -((((fiberLeft P input tail b).val : ℝ) *
              ((selectedIndex P (unit : ZMod P.order)).val : ℝ) +
            (b.val : ℝ) *
              ((selectedIndex P
                (-input.secret * (unit : ZMod P.order))).val : ℝ)) /
          (fourierModulus P : ℝ)) =
        -(((tail.val *
              (residueIndex P (unit : ZMod P.order)).val : Nat) : ℝ) /
            (P.order : ℝ)) -
          (((phaseError P input unit tail b : Nat) : ℝ) /
            ((P.order : ℝ) * (fourierModulus P : ℝ))) +
          (((fiberQuotient P input tail b *
              (residueIndex P (unit : ZMod P.order)).val : Nat) : ℤ) -
            ((b.val * balanceQuotient P input unit : Nat) : ℤ) : ℤ) := by
    push_cast
    unfold selectedLeftResidue at hphaseR
    field_simp
    nlinarith [hphaseR]
  unfold selectedFiberPhase selectedTailPhase selectedErrorPhase
  change (starRingEnd ℂ)
      (ω (orderWidth P) ^
        ((fiberLeft P input tail b).val *
            (selectedIndex P (unit : ZMod P.order)).val +
          b.val *
            (selectedIndex P
              (-input.secret * (unit : ZMod P.order))).val)) = _
  unfold ω
  rw [map_pow, conj_exp_I, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨
    ((fiberQuotient P input tail b *
        (residueIndex P (unit : ZMod P.order)).val : Nat) : ℤ) -
      ((b.val * balanceQuotient P input unit : Nat) : ℤ), ?_⟩
  have hcomplex := congrArg
    (fun x : ℝ => ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) hratio
  push_cast at hcomplex
  unfold fourierModulus at hcomplex ⊢
  push_cast at hcomplex ⊢
  ring_nf at hcomplex ⊢
  exact hcomplex

private theorem selectedError_lt_order (P : KnownOrderProblem G)
    (residue : Fin P.order) : selectedError P residue < P.order := by
  simpa [selectedError] using selectedRawFrequency_error_lt_order P residue

private theorem six_mul_phaseError_le (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (tail b : Fin P.order) :
    6 * phaseError P input unit tail b ≤ P.order * fourierModulus P := by
  have hleftError :
      selectedError P (selectedLeftResidue P unit) ≤ P.order :=
    (selectedError_lt_order P _).le
  have hrightError :
      selectedError P (selectedRightResidue P input unit) ≤ P.order :=
    (selectedError_lt_order P _).le
  have hfiber :
      (fiberLeft P input tail b).val ≤ P.order :=
    (fiberLeft P input tail b).isLt.le
  have hb : b.val ≤ P.order := b.isLt.le
  have hphase :
      phaseError P input unit tail b ≤
        P.order * P.order + P.order * P.order := by
    rw [phaseError_eq_selectedErrors]
    exact Nat.add_le_add
      (Nat.mul_le_mul hfiber hleftError)
      (Nat.mul_le_mul hb hrightError)
  have hmodulus : 12 * P.order ≤ fourierModulus P := by
    simpa [oversampledOrder, fourierOversamplingFactor] using
      oversampledOrder_le_fourierModulus P
  calc
    6 * phaseError P input unit tail b ≤
        6 * (P.order * P.order + P.order * P.order) :=
      Nat.mul_le_mul_left 6 hphase
    _ = P.order * (12 * P.order) := by ring
    _ ≤ P.order * fourierModulus P :=
      Nat.mul_le_mul_left P.order hmodulus

private def phaseAngle (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail b : Fin P.order) : ℝ :=
  -(2 * Real.pi * (phaseError P input unit tail b : ℝ) /
    ((P.order : ℝ) * (fourierModulus P : ℝ)))

private theorem abs_phaseAngle_le_pi_div_three (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (tail b : Fin P.order) :
    |phaseAngle P input unit tail b| ≤ Real.pi / 3 := by
  have horder : (0 : ℝ) < P.order := by exact_mod_cast P.order_pos
  have hmodulus : (0 : ℝ) < fourierModulus P := by
    unfold fourierModulus
    positivity
  have hphaseR :
      (6 : ℝ) * (phaseError P input unit tail b : ℝ) ≤
        (P.order : ℝ) * (fourierModulus P : ℝ) := by
    exact_mod_cast six_mul_phaseError_le P input unit tail b
  have hratio :
      (phaseError P input unit tail b : ℝ) /
          ((P.order : ℝ) * (fourierModulus P : ℝ)) ≤ (1 : ℝ) / 6 := by
    apply (div_le_iff₀ (mul_pos horder hmodulus)).2
    nlinarith
  unfold phaseAngle
  rw [abs_neg, abs_of_nonneg (by positivity :
    0 ≤ 2 * Real.pi * (phaseError P input unit tail b : ℝ) /
      ((P.order : ℝ) * (fourierModulus P : ℝ)))]
  calc
    2 * Real.pi * (phaseError P input unit tail b : ℝ) /
          ((P.order : ℝ) * (fourierModulus P : ℝ)) =
        2 * Real.pi *
          ((phaseError P input unit tail b : ℝ) /
            ((P.order : ℝ) * (fourierModulus P : ℝ))) := by ring
    _ ≤ 2 * Real.pi * ((1 : ℝ) / 6) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = Real.pi / 3 := by ring

private theorem one_half_le_re_selectedErrorPhase (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (tail b : Fin P.order) :
    (1 : ℝ) / 2 ≤ (selectedErrorPhase P input unit tail b).re := by
  have hphase :
      selectedErrorPhase P input unit tail b =
        Complex.exp ((phaseAngle P input unit tail b : ℝ) * Complex.I) := by
    unfold selectedErrorPhase
    congr 2
    unfold phaseAngle
    push_cast
    ring
  rw [hphase]
  rw [Complex.exp_ofReal_mul_I_re, ← Real.cos_abs,
    ← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg _)
    (by nlinarith [Real.pi_pos])
    (abs_phaseAngle_le_pi_div_three P input unit tail b)

@[simp] theorem norm_selectedTailPhase (P : KnownOrderProblem G)
    (unit : (ZMod P.order)ˣ) (tail : Fin P.order) :
    ‖selectedTailPhase P unit tail‖ = 1 := by
  rw [selectedTailPhase, Complex.norm_exp]
  simp

public theorem half_order_le_norm_sum_selectedFiberPhase
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail : Fin P.order) :
    (P.order : ℝ) / 2 ≤
      ‖∑ b : Fin P.order, selectedFiberPhase P input unit tail b‖ := by
  have hsum :
      (∑ b : Fin P.order, selectedFiberPhase P input unit tail b) =
        selectedTailPhase P unit tail *
          ∑ b : Fin P.order, selectedErrorPhase P input unit tail b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact selectedFiberPhase_eq_tail_mul_error P input unit tail b
  rw [hsum, norm_mul, norm_selectedTailPhase, one_mul]
  calc
    (P.order : ℝ) / 2 = ∑ _b : Fin P.order, ((1 : ℝ) / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin, div_eq_mul_inv]
      norm_num
    _ ≤ ∑ b : Fin P.order,
        (selectedErrorPhase P input unit tail b).re :=
      Finset.sum_le_sum fun b _ =>
        one_half_le_re_selectedErrorPhase P input unit tail b
    _ = (∑ b : Fin P.order,
        selectedErrorPhase P input unit tail b).re := by
      rw [Complex.re_sum]
    _ ≤ ‖∑ b : Fin P.order,
        selectedErrorPhase P input unit tail b‖ :=
      Complex.re_le_norm _

private theorem invSqrtOrder_mul_self (P : KnownOrderProblem G) :
    invSqrtOrder P.order * invSqrtOrder P.order =
      (((P.order : ℝ) : ℂ))⁻¹ := by
  rw [invSqrtOrder, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ P.order)]

/-- Common amplitude scale shared by every selected fibre term. -/
@[expose] public def amplitudeScale (P : KnownOrderProblem G) : ℂ :=
  ((((2 : ℝ) ^ orderWidth P : ℂ))⁻¹) *
    (((P.order : ℝ) : ℂ))⁻¹

public theorem selectedFiberTerm_eq_scale_mul_phase
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail b : Fin P.order) :
    selectedFiberTerm input
        (selectedIndex P (unit : ZMod P.order))
        (selectedIndex P (-input.secret * (unit : ZMod P.order)))
        tail b =
      amplitudeScale P * selectedFiberPhase P input unit tail b := by
  have hphase :
      star (ω (orderWidth P) ^
          ((fiberLeft P input tail b).val *
            (selectedIndex P (unit : ZMod P.order)).val)) *
          star (ω (orderWidth P) ^
            (b.val *
              (selectedIndex P
                (-input.secret * (unit : ZMod P.order))).val)) =
        selectedFiberPhase P input unit tail b := by
    unfold selectedFiberPhase
    rw [← star_mul', ← pow_add]
  unfold selectedFiberTerm amplitudeScale
  simp only [star_mul', star_invSqrtN]
  calc
    (invSqrtN (orderWidth P) *
          star (ω (orderWidth P) ^
            ((fiberLeft P input tail b).val *
              (selectedIndex P (unit : ZMod P.order)).val))) *
        (invSqrtN (orderWidth P) *
          star (ω (orderWidth P) ^
            (b.val *
              (selectedIndex P
                (-input.secret * (unit : ZMod P.order))).val))) *
        (invSqrtOrder P.order * invSqrtOrder P.order) =
      (invSqrtN (orderWidth P) * invSqrtN (orderWidth P)) *
        (invSqrtOrder P.order * invSqrtOrder P.order) *
        (star (ω (orderWidth P) ^
            ((fiberLeft P input tail b).val *
              (selectedIndex P (unit : ZMod P.order)).val)) *
          star (ω (orderWidth P) ^
            (b.val *
              (selectedIndex P
                (-input.secret * (unit : ZMod P.order))).val))) := by ring
    _ = ((((2 : ℝ) ^ orderWidth P : ℂ))⁻¹) *
        (((P.order : ℝ) : ℂ))⁻¹ *
        selectedFiberPhase P input unit tail b := by
      rw [invSqrtN_mul_self, invSqrtOrder_mul_self, hphase]
      norm_num [Nat.cast_pow]

/-- The original selected Fourier fiber has its calibrated backend-independent amplitude floor. -/
theorem one_div_two_fourierModulus_le_norm_sum_selectedFiberTerm
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) (tail : Fin P.order) :
    1 / (2 * (fourierModulus P : ℝ)) ≤
      ‖∑ b : Fin P.order, selectedFiberTerm input
        (selectedIndex P (unit : ZMod P.order))
        (selectedIndex P (-input.secret * (unit : ZMod P.order))) tail b‖ := by
  rw [show
    (∑ b : Fin P.order,
      selectedFiberTerm input
        (selectedIndex P (unit : ZMod P.order))
        (selectedIndex P (-input.secret * (unit : ZMod P.order)))
        tail b) =
      ∑ b : Fin P.order,
        amplitudeScale P * selectedFiberPhase P input unit tail b by
    apply Finset.sum_congr rfl
    intro b _
    exact selectedFiberTerm_eq_scale_mul_phase P input unit tail b]
  rw [← Finset.mul_sum, norm_mul]
  have horder : (0 : ℝ) < P.order := by exact_mod_cast P.order_pos
  have hmodulus : (0 : ℝ) < fourierModulus P := by
    unfold fourierModulus
    positivity
  have hscale :
      ‖amplitudeScale P‖ =
        (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) := by
    have hpow :
        ‖(((2 : ℝ) ^ orderWidth P : ℂ))‖ =
          (2 : ℝ) ^ orderWidth P := by
      rw [norm_pow]
      norm_num
    have horderNorm :
        ‖((P.order : ℝ) : ℂ)‖ = (P.order : ℝ) := by norm_num
    unfold amplitudeScale
    rw [norm_mul, norm_inv, norm_inv, hpow, horderNorm, ← mul_inv]
    congr 2
    norm_num [fourierModulus, Nat.cast_pow]
  rw [hscale]
  calc
    1 / (2 * (fourierModulus P : ℝ)) =
        (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) *
          ((P.order : ℝ) / 2) := by field_simp
    _ ≤ (((fourierModulus P : ℝ) * (P.order : ℝ))⁻¹) *
        ‖∑ b : Fin P.order, selectedFiberPhase P input unit tail b‖ :=
      mul_le_mul_of_nonneg_left
        (half_order_le_norm_sum_selectedFiberPhase P input unit tail)
        (by positivity)

end Probability
end Canonical
end FiniteCyclicDLP

end

end QuantumAlg

end
