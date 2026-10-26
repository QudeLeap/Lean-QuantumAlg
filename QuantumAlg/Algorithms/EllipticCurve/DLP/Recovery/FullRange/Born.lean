/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Group
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Geometry
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Probability
import all QuantumAlg.Core.Base.State.Density.Vector
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Full-range kernel probabilities in the certified group-output Born effect

The full physical source enters the certified ideal group oracle and both
actual inverse Fourier matrices.  Selected cyclic group-output coordinates
are injective coordinates of that normalized state.  Their exact kernel
amplitudes therefore lower-bound the full observable Born weight, retaining
every external Reference amplitude.
-/

namespace QuantumAlg.EllipticCurve.FullRange

noncomputable section

open PrimeFieldShortWeierstrass FiniteCyclicDLP ECDLP.Measured
open FiniteCyclicDLP.ConcreteCircuitAccess
open FiniteCyclicDLP.Canonical.Probability (SecretInput)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private lemma pairedBranch_bit (exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (index : Fin (2 * exponentWidth)) :
    (prodEquiv branch).val.testBit index.rev.val =
      ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index := by
  unfold ExceptionalOffsetAveraging.pairedBigEndianSelected
  split_ifs with first
  · have localLt : exponentWidth - 1 - index.val < exponentWidth := by omega
    have reversed : index.rev.val = exponentWidth + (exponentWidth - 1 - index.val) := by
      rw [Fin.val_rev]
      omega
    rw [reversed]
    exact prodEquiv_testBit_left branch.1 branch.2
      (⟨exponentWidth - 1 - index.val, localLt⟩ : Fin exponentWidth)
  · have localLt : exponentWidth - 1 - (index.val - exponentWidth) < exponentWidth := by omega
    have reversed : index.rev.val = exponentWidth - 1 - (index.val - exponentWidth) := by
      rw [Fin.val_rev]
      omega
    rw [reversed]
    exact prodEquiv_testBit_right branch.1 branch.2
      (⟨exponentWidth - 1 - (index.val - exponentWidth), localLt⟩ : Fin exponentWidth)

private lemma originalPairedBits_injective (width : Nat) :
    Function.Injective (ExceptionalOffsetAveraging.pairedBigEndianSelected width) := by
  intro left right same
  apply (prodEquiv (m := width) (n := width)).injective
  let packedWidth : width + width = 2 * width := by omega
  let castPacked := finCongr (congrArg (fun count : Nat => 2 ^ count) packedWidth)
  apply castPacked.injective
  apply (BinaryBasis.bigEndianEquiv (2 * width)).symm.injective
  funext index
  rw [BinaryBasis.bigEndianEquiv_symm_value, BinaryBasis.bigEndianEquiv_symm_value]
  change finTwoEquiv.symm ((prodEquiv left).val.testBit index.rev.val) =
    finTwoEquiv.symm ((prodEquiv right).val.testBit index.rev.val)
  exact congrArg finTwoEquiv.symm ((pairedBranch_bit width left index).trans
    ((congrFun same index).trans (pairedBranch_bit width right index).symm))

private lemma normalizedReference_square_sum {Reference : Register}
    (reference : NormalizedVector Reference) :
    (∑ label : Reference.Index, ‖reference label‖ ^ 2) = 1 := by
  exact (EuclideanSpace.norm_sq_eq reference.vec).symm.trans
    (by rw [reference.norm_eq_one, one_pow])

/-- The full source after the certified group oracle and the two inverse Fourier transforms. -/
def fourierState (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference) :=
  let prepared : NormalizedVector ((idealBranchRegister problem).prod Reference) :=
    Geometry.sourceState (orderWidth problem) reference
  (idealReadoutOperator problem seed Reference).apply
    (NormalizedVector.ofVector
      (Effect.extensionVector (idealOracleEmbedding problem seed Reference)
        prepared.vec)
      (by rw [Effect.norm_extensionVector _
            (idealOracleEmbedding_injective problem seed Reference),
          prepared.norm_eq_one]))

/-- The ideal source effect is precisely the Fourier-state event Born weight. -/
lemma idealBranchEffect_fullSource_weight (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (idealBranchEffect problem seed event Reference).weight
        (DensityOperator.ofPure (Geometry.sourceState (orderWidth problem) reference)) =
      (idealReadoutEffect problem seed event Reference).weight
        (DensityOperator.ofPure (fourierState problem seed reference)) := by
  let prepared : NormalizedVector ((idealBranchRegister problem).prod Reference) :=
    Geometry.sourceState (orderWidth problem) reference
  let extended : NormalizedVector (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference) :=
    NormalizedVector.ofVector
      (Effect.extensionVector (idealOracleEmbedding problem seed Reference) prepared.vec)
      (by rw [Effect.norm_extensionVector _
            (idealOracleEmbedding_injective problem seed Reference), prepared.norm_eq_one])
  have preparedBound : ‖prepared.vec‖ ≤ 1 := by rw [prepared.norm_eq_one]
  have extendedBound : ‖extended.vec‖ ≤ 1 := by rw [extended.norm_eq_one]
  have bridge := idealBranchEffect_weight problem seed event Reference prepared.vec preparedBound
  change (idealBranchEffect problem seed event Reference).weight
      (DensityOperator.ofSubnormalizedVector prepared.vec preparedBound) =
    (idealReadoutEffect problem seed event Reference).weight
      (DensityOperator.applyUnitary (idealReadoutOperator problem seed Reference)
        (DensityOperator.ofSubnormalizedVector extended.vec extendedBound)) at bridge
  simp only [DensityOperator.ofSubnormalizedVector_of_normalized] at bridge
  rw [← DensityOperator.ofPure_apply] at bridge
  exact bridge

/-- Both actual Fourier rows multiply the same full-range source coefficient. -/
lemma fullReadout_coefficient (problem : KnownOrderProblem E.GroupPoint)
    (raw source : Branch (orderWidth problem)) :
    ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
        (prodEquiv raw) (prodEquiv source) * branchAmplitude (orderWidth problem) source =
      rawFourierCoefficient (orderWidth problem) raw.1 source.1 *
        rawFourierCoefficient (orderWidth problem) raw.2 source.2 := by
  rw [exponentReadout_pair_entry]
  unfold rawFourierCoefficient
  rw [qpeReadout_binary_matrix]
  change _ = (star (QFTOperator (orderWidth problem) source.1 raw.1) *
    exponentState (orderWidth problem) source.1) *
    (star (QFTOperator (orderWidth problem) source.2 raw.2) *
      exponentState (orderWidth problem) source.2)
  simp only [QFTOperator_entry, branchAmplitude]
  ring

variable (problem : KnownOrderProblem E.GroupPoint) [NeZero problem.order]

/-- The full Fourier-state amplitude at every cyclic group-output coordinate. -/
lemma fourierState_selected_entry (seed : AffinePoint E) (input : SecretInput problem)
    {Reference : Register} (reference : NormalizedVector Reference)
    (raw : Branch (orderWidth problem)) (residue : ZMod problem.order)
    (label : Reference.Index) :
    fourierState problem seed reference
        ((prodEquiv raw, selectedIdealGroupLabel problem seed
          ⟨residue.val, ZMod.val_lt residue⟩), label) =
      idealKernel (orderWidth problem) 0 input.secret raw.1 raw.2 residue * reference label := by
  let prepared : NormalizedVector ((idealBranchRegister problem).prod Reference) :=
    Geometry.sourceState (orderWidth problem) reference
  change (idealReadoutOperator problem seed Reference).applyVec
    (Effect.extensionVector (idealOracleEmbedding problem seed Reference)
      prepared.vec) _ = _
  rw [idealReadout_extension_entry problem seed Reference prepared.vec raw
    (selectedIdealGroupLabel problem seed ⟨residue.val, ZMod.val_lt residue⟩) label]
  unfold idealKernel CyclicFourier.fiberAmplitude
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro right _
  have fiber := idealGroupLabel_selected_iff_residue problem seed input (left, right)
    ⟨residue.val, ZMod.val_lt residue⟩
  simp only [ZMod.natCast_zmod_val] at fiber
  have sameResidue : (left.val : ZMod problem.order) - input.secret * right.val = residue ↔
      (0 : ZMod problem.order) + left.val + (-input.secret * right.val) = residue := by
    rw [zero_add, sub_eq_add_neg, neg_mul]
  rw [sameResidue] at fiber
  change _ * (if idealGroupLabel problem seed (left, right) = _ then
    branchAmplitude (orderWidth problem) (left, right) * reference label else 0) = _
  by_cases same : idealGroupLabel problem seed (left, right) =
      selectedIdealGroupLabel problem seed ⟨residue.val, ZMod.val_lt residue⟩
  · rw [if_pos same, if_pos (fiber.mp same)]
    exact (mul_assoc _ _ _).symm.trans
      (congrArg (fun value : ℂ => value * reference label)
        (fullReadout_coefficient problem raw (left, right)))
  · rw [if_neg same, if_neg (fun accepted => same (fiber.mpr accepted))]
    simp only [mul_zero, zero_mul]

/-- The strict recoverable event is a predicate on the actually emitted ordered bits. -/
def recoverableExponentEvent (input : SecretInput problem)
    (bits : Fin (2 * orderWidth problem) → Bool) : Bool :=
  decide (∃ raw : Branch (orderWidth problem),
    recoverableWindow (orderWidth problem) input.secret raw ∧
      bits = ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw)

omit [NeZero problem.order] in
lemma recoverableExponentEvent_pair_iff (input : SecretInput problem)
    (raw : Branch (orderWidth problem)) :
    recoverableExponentEvent problem input
        (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw) = true ↔
      recoverableWindow (orderWidth problem) input.secret raw := by
  simp only [recoverableExponentEvent, decide_eq_true_eq]
  constructor
  · rintro ⟨other, accepted, same⟩
    exact (originalPairedBits_injective (orderWidth problem) same) ▸ accepted
  · intro accepted
    exact ⟨raw, accepted, rfl⟩

/-- All physical frequencies, every cyclic output and the full Reference keep distinct labels. -/
def selectedFullOutput (seed : AffinePoint E) (Reference : Register)
    (index : (Branch (orderWidth problem) × ZMod problem.order) × Reference.Index) :
    (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference).Index :=
  ((prodEquiv index.1.1,
    selectedIdealGroupLabel problem seed ⟨index.1.2.val, ZMod.val_lt index.1.2⟩), index.2)

lemma selectedFullOutput_injective (seed : AffinePoint E) (Reference : Register) :
    Function.Injective (selectedFullOutput problem seed Reference) := by
  intro left right same
  apply Prod.ext
  · apply Prod.ext
    · exact prodEquiv.injective (congrArg (fun label => label.1.1) same)
    · apply ZMod.val_injective problem.order
      exact congrArg Fin.val (selectedIdealGroupLabel_injective problem seed
        (congrArg (fun label => label.1.2) same))
  · exact congrArg (fun output => output.2) same

/-- The exact full-range kernel mass lower-bounds the certified ideal Born effect
for an arbitrary normalized external Reference. -/
lemma idealBranchEffect_recoverable_lower (seed : AffinePoint E) (input : SecretInput problem)
    {Reference : Register} (reference : NormalizedVector Reference) :
    idealRecoverableMass (orderWidth problem) 0 input.secret ≤
      (idealBranchEffect problem seed (recoverableExponentEvent problem input) Reference).weight
        (DensityOperator.ofPure (Geometry.sourceState (orderWidth problem) reference)) := by
  let value := fun output =>
    if idealReadoutEvent problem seed (recoverableExponentEvent problem input) Reference output =
      true then ‖fourierState problem seed reference output‖ ^ 2 else 0
  have nonnegative (output) : 0 ≤ value output := by
    dsimp only [value]
    split_ifs <;> positivity
  have selectedSum :
      (∑ index : (Branch (orderWidth problem) × ZMod problem.order) × Reference.Index,
        value (selectedFullOutput problem seed Reference index)) =
      idealRecoverableMass (orderWidth problem) 0 input.secret := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    unfold idealRecoverableMass
    apply Finset.sum_congr rfl
    intro raw _
    by_cases accepted : recoverableWindow (orderWidth problem) input.secret raw
    · simp only [if_pos accepted]
      apply Finset.sum_congr rfl
      intro residue _
      have event := (recoverableExponentEvent_pair_iff problem input raw).mpr accepted
      change (∑ label : Reference.Index,
        if recoverableExponentEvent problem input
            (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
              (prodEquiv.symm (prodEquiv raw))) = true then
          ‖fourierState problem seed reference
            ((prodEquiv raw, selectedIdealGroupLabel problem seed
              ⟨residue.val, ZMod.val_lt residue⟩), label)‖ ^ 2 else 0) = _
      simp only [Equiv.symm_apply_apply, event, if_true]
      calc
        _ = ∑ label : Reference.Index,
            ‖idealKernel (orderWidth problem) 0 input.secret raw.1 raw.2 residue *
              reference label‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro label _
          exact congrArg (fun value : ℂ => ‖value‖ ^ 2)
            (fourierState_selected_entry problem seed input reference raw residue label)
        _ = _ := by
          simp only [norm_mul, mul_pow, ← Finset.mul_sum, normalizedReference_square_sum,
            mul_one]
    · have event := (recoverableExponentEvent_pair_iff problem input raw).not.mpr accepted
      simp only [value, selectedFullOutput, idealReadoutEvent, Equiv.symm_apply_apply,
        event, Bool.false_eq_true, if_false, Finset.sum_const_zero, if_neg accepted]
  have readoutLower : idealRecoverableMass (orderWidth problem) 0 input.secret ≤
      (idealReadoutEffect problem seed (recoverableExponentEvent problem input) Reference).weight
        (DensityOperator.ofPure (fourierState problem seed reference)) := by
    rw [idealReadoutEffect_weight_pure]
    calc
      _ = ∑ index : (Branch (orderWidth problem) × ZMod problem.order) × Reference.Index,
        value (selectedFullOutput problem seed Reference index) := selectedSum.symm
      _ = ∑ output ∈ Finset.univ.image (selectedFullOutput problem seed Reference),
          value output := by
        rw [Finset.sum_image (selectedFullOutput_injective problem seed Reference).injOn]
      _ ≤ ∑ output, value output := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun output _ _ => nonnegative output)
  exact readoutLower.trans_eq (idealBranchEffect_fullSource_weight problem seed
    (recoverableExponentEvent problem input) reference).symm

end

end QuantumAlg.EllipticCurve.FullRange
