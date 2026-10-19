/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.StatePreparation
import all QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Util.Nat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Complex.Basic

/-!
# Source-faithful finite-cyclic DLP exponent preparation

Shor's finite-cyclic discrete-logarithm experiment prepares the exponent
register uniformly on `0, ..., N - 1`, even though the physical register has
the next power-of-two capacity.  This module retains the source mathematics
and its model-independent basis-change operator.  The actual default-model
word and resource derivation live in `Order.Preparation.Native`.
-/

section

namespace QuantumAlg

noncomputable section

namespace FiniteCyclicDLP

universe u

variable {G : Type u} [Group G]

/-- Constant oversampling used by the two-register Fourier experiment.  The
factor twelve makes every residue class admit a one-sided rounded raw Fourier
index whose error lies in the source phase cone. -/
@[expose] public def fourierOversamplingFactor : Nat := 12

/-- Oversampled source size whose next power of two is the Fourier modulus. -/
@[expose] public def oversampledOrder (P : KnownOrderProblem G) : Nat :=
  fourierOversamplingFactor * P.order

/-- Exponent-register width for the oversampled Fourier modulus. -/
@[expose] public def orderWidth (P : KnownOrderProblem G) : Nat :=
  Nat.clog 2 (oversampledOrder P)

/-- Power-of-two Fourier modulus used by both exponent registers. -/
@[expose] public def fourierModulus (P : KnownOrderProblem G) : Nat :=
  2 ^ orderWidth P

/-- The source-safe oversampled range fits in the Fourier register. -/
public lemma oversampledOrder_le_fourierModulus (P : KnownOrderProblem G) :
    oversampledOrder P ≤ fourierModulus P := by
  exact Nat.le_pow_clog (by norm_num : 1 < 2) (oversampledOrder P)

/-- The selected power of two is strictly less than twice the oversampled
range, so `12N ≤ q < 24N`. -/
public lemma fourierModulus_lt_twice_oversampledOrder
    (P : KnownOrderProblem G) :
    fourierModulus P < 2 * oversampledOrder P := by
  have hlarge : 1 < oversampledOrder P := by
    unfold oversampledOrder fourierOversamplingFactor
    have := P.order_pos
    omega
  have hpred := Nat.pow_pred_clog_lt_self
    (b := 2) (by norm_num : 1 < 2) hlarge
  have hclog : 0 < Nat.clog 2 (oversampledOrder P) :=
    Nat.clog_pos (by norm_num : 1 < 2) hlarge
  unfold fourierModulus orderWidth
  rw [← Nat.succ_pred_eq_of_pos hclog, pow_succ]
  omega

/-- The actual source range `0, ..., N-1` fits in the oversampled register. -/
public lemma order_le_fourierModulus (P : KnownOrderProblem G) :
    P.order ≤ fourierModulus P := by
  calc
    P.order ≤ oversampledOrder P := by
      unfold oversampledOrder fourierOversamplingFactor
      omega
    _ ≤ fourierModulus P := oversampledOrder_le_fourierModulus P

/-- The actual group order fits strictly below the Fourier-register capacity.
The stronger inequality follows from the twelve-fold oversampling and is the
boundary needed by fixed-width routines that materialize the modulus itself. -/
public lemma order_lt_fourierModulus (P : KnownOrderProblem G) :
    P.order < fourierModulus P := by
  calc
    P.order < oversampledOrder P := by
      unfold oversampledOrder fourierOversamplingFactor
      have := P.order_pos
      omega
    _ ≤ fourierModulus P := oversampledOrder_le_fourierModulus P

/-- Canonical raw Fourier index immediately above the exact residue frequency.
The oversampled register guarantees that this ceiling index remains in range. -/
public def selectedRawFrequency (P : KnownOrderProblem G) (residue : Fin P.order) :
    Fin (fourierModulus P) :=
  ⟨QuantumAlg.Nat.ceilDiv (residue.val * fourierModulus P) P.order, by
    have hceil := QuantumAlg.Nat.ceilDiv_mul_lt_add
      (num := residue.val * fourierModulus P) P.order_pos
    have horder_le := order_le_fourierModulus P
    have hresidue : residue.val + 1 ≤ P.order := residue.isLt
    have hadd :
        residue.val * fourierModulus P + P.order ≤
          (residue.val + 1) * fourierModulus P := by
      calc
        residue.val * fourierModulus P + P.order ≤
            residue.val * fourierModulus P + fourierModulus P :=
          Nat.add_le_add_left horder_le _
        _ = (residue.val + 1) * fourierModulus P := by ring
    have hmul :
        (residue.val + 1) * fourierModulus P ≤
          P.order * fourierModulus P :=
      Nat.mul_le_mul_right (fourierModulus P) hresidue
    have hproduct :
        QuantumAlg.Nat.ceilDiv
              (residue.val * fourierModulus P) P.order * P.order <
            fourierModulus P * P.order := by
      calc
        QuantumAlg.Nat.ceilDiv
              (residue.val * fourierModulus P) P.order * P.order <
            residue.val * fourierModulus P + P.order := hceil
        _ ≤ (residue.val + 1) * fourierModulus P := hadd
        _ ≤ P.order * fourierModulus P := hmul
        _ = fourierModulus P * P.order := Nat.mul_comm _ _
    exact (Nat.mul_lt_mul_right P.order_pos).mp hproduct⟩

/-- The canonical raw frequency scales back to its exact residue. -/
public lemma selectedRawFrequency_scale
    (P : KnownOrderProblem G) (residue : Fin P.order) :
    (selectedRawFrequency P residue).val * P.order / fourierModulus P =
      residue.val := by
  have hq : 0 < fourierModulus P := by
    unfold fourierModulus
    positivity
  have hlower := QuantumAlg.Nat.le_ceilDiv_mul
    (num := residue.val * fourierModulus P) P.order_pos
  have hupper := QuantumAlg.Nat.ceilDiv_mul_lt_add
    (num := residue.val * fourierModulus P) P.order_pos
  have horder_le := order_le_fourierModulus P
  have hupper' :
      (selectedRawFrequency P residue).val * P.order <
        (residue.val + 1) * fourierModulus P := by
    calc
      (selectedRawFrequency P residue).val * P.order <
          residue.val * fourierModulus P + P.order := hupper
      _ ≤ residue.val * fourierModulus P + fourierModulus P :=
        Nat.add_le_add_left horder_le _
      _ = (residue.val + 1) * fourierModulus P := by ring
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ
      ((Nat.div_lt_iff_lt_mul hq).2 hupper')
  · exact (Nat.le_div_iff_mul_le hq).2 hlower

/-- The one-sided raw-frequency rounding error is less than one group order. -/
public lemma selectedRawFrequency_error_lt_order
    (P : KnownOrderProblem G) (residue : Fin P.order) :
    (selectedRawFrequency P residue).val * P.order -
        residue.val * fourierModulus P < P.order := by
  have hlower := QuantumAlg.Nat.le_ceilDiv_mul
    (num := residue.val * fourierModulus P) P.order_pos
  have hupper := QuantumAlg.Nat.ceilDiv_mul_lt_add
    (num := residue.val * fourierModulus P) P.order_pos
  change
    QuantumAlg.Nat.ceilDiv
          (residue.val * fourierModulus P) P.order * P.order -
        residue.val * fourierModulus P < P.order
  omega

/-- Twelve times the rounding error remains strictly below the Fourier
modulus, the arithmetic form of the phase-cone margin. -/
public lemma twelve_mul_selectedRawFrequency_error_lt
    (P : KnownOrderProblem G) (residue : Fin P.order) :
    12 * ((selectedRawFrequency P residue).val * P.order -
        residue.val * fourierModulus P) < fourierModulus P := by
  have herr := selectedRawFrequency_error_lt_order P residue
  have hscaled : 12 * P.order ≤ fourierModulus P := by
    simpa [oversampledOrder, fourierOversamplingFactor] using
      oversampledOrder_le_fourierModulus P
  have hstrict :
      12 * ((selectedRawFrequency P residue).val * P.order -
          residue.val * fourierModulus P) < 12 * P.order :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 12)).2 herr
  exact hstrict.trans_le hscaled

/-- One over the square root of a positive finite range size. -/
public def invSqrtOrder (order : Nat) : ℂ :=
  (Real.sqrt (order : ℝ) : ℂ)⁻¹

lemma norm_sq_invSqrtOrder {order : Nat} (horder : 0 < order) :
    ‖invSqrtOrder order‖ ^ 2 = ((order : ℝ)⁻¹) := by
  rw [invSqrtOrder, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (order : ℝ))]

/-- The source state: equal amplitude on the first `order` computational
basis labels and zero amplitude on unused power-of-two labels. -/
def rangeUniformState (order width : Nat) (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) : NormalizedVector (Qubits width) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun i =>
      if i.val < order then invSqrtOrder order else 0)
    (by
      rw [EuclideanSpace.norm_eq]
      have hsum :
          ∑ i : Fin (2 ^ width),
              ‖if i.val < order then invSqrtOrder order else 0‖ ^ 2 = 1 := by
        simp_rw [apply_ite, ite_pow, norm_zero,
          zero_pow (by omega : 2 ≠ 0)]
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, Fin.card_filter_val_lt,
          min_eq_right hfits, nsmul_eq_mul,
          norm_sq_invSqrtOrder horder]
        field_simp
      rw [hsum, Real.sqrt_one])

@[simp]
lemma rangeUniformState_apply {order width : Nat} (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) (i : Fin (2 ^ width)) :
    rangeUniformState order width horder hfits i =
      if i.val < order then invSqrtOrder order else 0 :=
  rfl

lemma rangeUniformState_singleton_orthonormal
    {order width : Nat} (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) :
    Orthonormal ℂ
      (({0} : Set (Fin (2 ^ width))).domRestrict
        (fun _ : Fin (2 ^ width) =>
          (rangeUniformState order width horder hfits :
            HilbertVector (Qubits width)))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := by
    apply Subtype.ext
    simpa using i.property.trans j.property.symm
  subst j
  rw [if_pos rfl]
  exact inner_self_eq_one_of_norm_eq_one
    (rangeUniformState order width horder hfits).norm_eq_one

/-- The singleton range-uniform state extends to a full orthonormal basis. -/
lemma exists_rangeUniformBasis
    (order width : Nat) (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) :
    ∃ b : OrthonormalBasis (Fin (2 ^ width)) ℂ
        (HilbertVector (Qubits width)),
      ∀ i ∈ ({0} : Set (Fin (2 ^ width))),
        b i = (rangeUniformState order width horder hfits :
          HilbertVector (Qubits width)) :=
  Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (s := ({0} : Set (Fin (2 ^ width))))
    (v := fun _ : Fin (2 ^ width) =>
      (rangeUniformState order width horder hfits :
        HilbertVector (Qubits width)))
    (by simp) (rangeUniformState_singleton_orthonormal horder hfits)

/-- An orthonormal basis whose zero column is the source range-uniform state. -/
noncomputable def rangeUniformBasis
    (order width : Nat) (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) :
    OrthonormalBasis (Fin (2 ^ width)) ℂ
      (HilbertVector (Qubits width)) :=
  Classical.choose (exists_rangeUniformBasis order width horder hfits)

private lemma rangeUniformBasis_zero
    (order width : Nat) (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) :
    rangeUniformBasis order width horder hfits 0 =
      (rangeUniformState order width horder hfits :
        HilbertVector (Qubits width)) := by
  exact (Classical.choose_spec
    (exists_rangeUniformBasis order width horder hfits)) 0 (by simp)

/-- A certified unitary whose zero column is the source range-uniform state. -/
def rangePreparationOperator (order width : Nat) (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) : UnitaryOperator (Qubits width) :=
  Gate.finiteCyclicRangePreparationOp
    (rangeUniformState order width horder hfits)

/-- The selected unitary really prepares the source range-uniform state. -/
lemma rangePreparationOperator_apply_zero
    (order width : Nat) (horder : 0 < order)
    (hfits : order ≤ 2 ^ width) :
    (rangePreparationOperator order width horder hfits).apply
        (NormalizedVector.ket (R := Qubits width) 0) =
      rangeUniformState order width horder hfits := by
  exact Gate.finiteCyclicRangePreparationOp_apply_zero
    (rangeUniformState order width horder hfits)

end FiniteCyclicDLP

end

end QuantumAlg

end
