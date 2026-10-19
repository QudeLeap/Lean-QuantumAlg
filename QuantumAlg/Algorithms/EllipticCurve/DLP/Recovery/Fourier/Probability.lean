/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Fiber
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support.Reference
import all QuantumAlg.Core.Base.State.Density.Vector
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract

/-!
# Original selected-frequency event bound

The source frequencies indexed by units and the full-group labels indexed
by original residues give distinct coordinates of the same certified Fourier
state. Summing their squared amplitudes preserves the original oversampling
and yields the original known-order lower bound. The secret only specifies
the mathematical success event; it is not a parameter of an executable run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution
open FiniteCyclicDLP ConcreteCircuitAccess Canonical.Probability
open scoped BigOperators ComplexOrder

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The two original normalized range states retain an arbitrary normalized reference. -/
def idealPreparedBranchState (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector ((idealBranchRegister problem).prod Reference) :=
  normalizedReferenceFrame
    (normalizedReferenceFrame (Concrete.BornBridge.exponentState problem)
      (Concrete.BornBridge.exponentState problem)) reference

/-- Every prepared branch and reference has its unchanged original complex amplitude. -/
lemma idealPreparedBranchState_apply (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} (reference : NormalizedVector Reference)
    (branch : (idealBranchRegister problem).Index) (label : Reference.Index) :
    idealPreparedBranchState problem reference (branch, label) =
      preparedBranchAmplitude problem branch * reference label := rfl

/-- The original Fourier operator acts on the exact finite-image group state and reference. -/
def idealFourierState (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference) :=
  (idealReadoutOperator problem seed Reference).apply
    (NormalizedVector.ofVector
      (Effect.extensionVector (idealOracleEmbedding problem seed Reference)
        (idealPreparedBranchState problem reference).vec)
      (by rw [Effect.norm_extensionVector _
            (idealOracleEmbedding_injective problem seed Reference),
          (idealPreparedBranchState problem reference).norm_eq_one]))

/-- The full normalized Fourier state has the original fiber amplitude times its reference. -/
lemma idealFourierState_entry (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    (frequency : (idealBranchRegister problem).Index)
    (output : (idealGroupRegister problem seed).Index) (label : Reference.Index) :
    idealFourierState problem seed reference ((prodEquiv frequency, output), label) =
      idealFiberAmplitude problem seed frequency output * reference label :=
  idealReadout_prepared_entry problem seed Reference reference.vec frequency output label

/-- Each original selected group fiber contributes the unchanged squared amplitude floor. -/
lemma idealFiberAmplitude_selected_sq_lower (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem) (unit : (ZMod problem.order)ˣ)
    (tail : Fin problem.order) :
    1 / (4 * (fourierModulus problem : ℝ) ^ 2) ≤
      ‖idealFiberAmplitude problem seed (selectedExponentFrequency problem input unit)
        (selectedIdealGroupLabel problem seed tail)‖ ^ 2 := by
  have amplitude := idealFiberAmplitude_selected_lower problem seed input unit tail
  calc
    _ = (1 / (2 * (fourierModulus problem : ℝ))) ^ 2 := by
      field_simp
      ring
    _ ≤ _ := (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 amplitude

/-- Summing all original unit and group-residue fibers gives the original numerical floor. -/
lemma selectedFiberSum_lower (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (input : SecretInput problem) :
    letI : NeZero problem.order := ⟨problem.order_ne_zero⟩
    (problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) ≤
      ∑ unit : (ZMod problem.order)ˣ, ∑ tail : Fin problem.order,
        ‖idealFiberAmplitude problem seed (selectedExponentFrequency problem input unit)
          (selectedIdealGroupLabel problem seed tail)‖ ^ 2 := by
  let _ : NeZero problem.order := ⟨problem.order_ne_zero⟩
  calc
    _ = ∑ _unit : (ZMod problem.order)ˣ, ∑ _tail : Fin problem.order,
        1 / (4 * (fourierModulus problem : ℝ) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ZMod.card_units_eq_totient, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum fun unit _ =>
      Finset.sum_le_sum fun tail _ => idealFiberAmplitude_selected_sq_lower
        problem seed input unit tail

/-- Selected unit, group residue, and reference coordinates occupy their actual output labels. -/
def selectedIdealOutput (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (input : SecretInput problem) (Reference : Register)
    (index : ((ZMod problem.order)ˣ × Fin problem.order) × Reference.Index) :
    (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference).Index :=
  ((prodEquiv (selectedExponentFrequency problem input index.1.1),
    selectedIdealGroupLabel problem seed index.1.2), index.2)

/-- No selected frequency, group tail, or coherent reference coordinate is counted twice. -/
lemma selectedIdealOutput_injective (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem) (Reference : Register) :
    Function.Injective (selectedIdealOutput problem seed input Reference) := by
  intro left right same
  apply Prod.ext
  · apply Prod.ext
    · exact selectedExponentFrequency_injective problem input
        (prodEquiv.injective (congrArg (fun output => output.1.1) same))
    · exact selectedIdealGroupLabel_injective problem seed
        (congrArg (fun output => output.1.2) same)
  · have referenceSame := congrArg (fun output => output.2) same
    exact referenceSame

/-- The mathematical event accepts every selected actual output coordinate. -/
lemma selectedIdealOutput_event (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem) (Reference : Register)
    (index : ((ZMod problem.order)ˣ × Fin problem.order) × Reference.Index) :
    idealReadoutEvent problem seed (selectedExponentEvent problem input) Reference
      (selectedIdealOutput problem seed input Reference index) = true := by
  have unpacked := (prodEquiv (m := orderWidth problem) (n := orderWidth problem)).symm_apply_apply
    (selectedExponentFrequency problem input index.1.1)
  exact (congrArg (fun frequency => selectedExponentEvent problem input
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) frequency))
      unpacked).trans (selectedExponentEvent_selected problem input index.1.1)

/-- A retained normalized reference contributes total squared amplitude one. -/
private lemma normalizedReference_square_sum {Reference : Register}
    (reference : NormalizedVector Reference) :
    (∑ label : Reference.Index, ‖reference label‖ ^ 2) = 1 := by
  exact (EuclideanSpace.norm_sq_eq reference.vec).symm.trans
    (by rw [reference.norm_eq_one, one_pow])

/-- The same selected coordinates retain their full weight beside any normalized reference. -/
lemma selectedIdealOutput_sum_lower (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem)
    {Reference : Register} (reference : NormalizedVector Reference) :
    letI : NeZero problem.order := ⟨problem.order_ne_zero⟩
    (problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) ≤
      ∑ index : ((ZMod problem.order)ˣ × Fin problem.order) × Reference.Index,
        ‖idealFourierState problem seed reference
          (selectedIdealOutput problem seed input Reference index)‖ ^ 2 := by
  let _ : NeZero problem.order := ⟨problem.order_ne_zero⟩
  have same : (∑ index : ((ZMod problem.order)ˣ × Fin problem.order) × Reference.Index,
      ‖idealFourierState problem seed reference
        (selectedIdealOutput problem seed input Reference index)‖ ^ 2) =
      ∑ unit : (ZMod problem.order)ˣ, ∑ tail : Fin problem.order,
        ‖idealFiberAmplitude problem seed (selectedExponentFrequency problem input unit)
          (selectedIdealGroupLabel problem seed tail)‖ ^ 2 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro unit _
    apply Finset.sum_congr rfl
    intro tail _
    calc
      _ = ∑ label : Reference.Index,
          ‖idealFiberAmplitude problem seed (selectedExponentFrequency problem input unit)
            (selectedIdealGroupLabel problem seed tail) * reference label‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro label _
        exact congrArg (fun value : ℂ => ‖value‖ ^ 2)
          (idealFourierState_entry problem seed reference
            (selectedExponentFrequency problem input unit)
            (selectedIdealGroupLabel problem seed tail) label)
      _ = _ := by
        simp only [norm_mul, mul_pow, ← Finset.mul_sum, normalizedReference_square_sum, mul_one]
  exact (selectedFiberSum_lower problem seed input).trans_eq same.symm

/-- The certified diagonal event has the true sum of retained squared amplitudes. -/
lemma idealReadoutEffect_weight_pure (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register)
    (state : NormalizedVector (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference)) :
    (idealReadoutEffect problem seed event Reference).weight (DensityOperator.ofPure state) =
      ∑ output, if idealReadoutEvent problem seed event Reference output = true then
        ‖state output‖ ^ 2 else 0 := by
  have sameDecision : instDecidableEqBool = Classical.decEq Bool := Subsingleton.elim _ _
  rw [sameDecision]
  simp only [Effect.weight, idealReadoutEffect, ZMeasurement.projector, Matrix.diagonal_mul,
    Matrix.trace, Matrix.diag, DensityOperator.ofPure_matrix, ite_mul, one_mul, zero_mul]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro output _
  split_ifs
  · simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re] using
      Complex.normSq_eq_norm_sq (state output)
  · rfl

/-- All selected coordinates belong to the true event, with no assumptions about other outputs. -/
lemma idealReadoutEffect_selected_lower (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (input : SecretInput problem)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) ≤
      (idealReadoutEffect problem seed (selectedExponentEvent problem input) Reference).weight
        (DensityOperator.ofPure (idealFourierState problem seed reference)) := by
  let _ : NeZero problem.order := ⟨problem.order_ne_zero⟩
  let value := fun output =>
    if idealReadoutEvent problem seed (selectedExponentEvent problem input) Reference output = true
    then ‖idealFourierState problem seed reference output‖ ^ 2 else 0
  have nonnegative (output) : 0 ≤ value output := by
    dsimp only [value]
    split_ifs <;> positivity
  calc
    _ ≤ ∑ index : ((ZMod problem.order)ˣ × Fin problem.order) × Reference.Index,
        ‖idealFourierState problem seed reference
          (selectedIdealOutput problem seed input Reference index)‖ ^ 2 :=
      selectedIdealOutput_sum_lower problem seed input reference
    _ = ∑ index : ((ZMod problem.order)ˣ × Fin problem.order) × Reference.Index,
        value (selectedIdealOutput problem seed input Reference index) := by
      apply Finset.sum_congr rfl
      intro index _
      exact (if_pos (selectedIdealOutput_event problem seed input Reference index)).symm
    _ = ∑ output ∈ Finset.univ.image (selectedIdealOutput problem seed input Reference),
        value output := by
      rw [Finset.sum_image (selectedIdealOutput_injective problem seed input Reference).injOn]
    _ ≤ ∑ output, value output :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun output _ _ => nonnegative output)
    _ = _ := (idealReadoutEffect_weight_pure problem seed
      (selectedExponentEvent problem input) Reference
      (idealFourierState problem seed reference)).symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
