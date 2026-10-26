/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Instrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Matrix
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Mixed

/-!
# Complete actual two-stream posterior with its common arithmetic scalar

The complete first unnormalized accumulator/reference posterior enters the
second stream without reinitialization. All original actual records remain
explicit, and every branch restores the original zero-control physical frame
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberMatrixCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]
  (wide : 2 ≤ width) (generator target : (ZMod modulus.toNat)ˣ)

/-- The public two-stream arithmetic scalar is independent of every actual measurement record. -/
def memberAlpha : ℂ :=
  exponentAlpha width modulus (bits := ell) target⁻¹ ell 0 (by omega) *
    exponentAlpha width modulus (bits := ell + m) generator (ell + m) 0 (by omega)

/-- Chronological logical products preserve the complete first posterior for the second stream. -/
def memberSourceKraus (Reference : Register)
    (store : Store (MemberMatrixCtx base noQuantum m ell width))
    (outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target) :
    HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) :=
  exponentSourceKraus base noQuantum m ell width modulus wide target⁻¹ true
      (secondCell base noQuantum m ell width) Reference ell 0 (by omega)
      (exponentActualRecord base noQuantum m ell width modulus wide generator true
        (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) store outcomes.1).1
      outcomes.2 *
    exponentSourceKraus base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) Reference (ell + m) 0 (by omega) store outcomes.1

/-- Every actual member record has the same scalar beside the entire coherent reference. -/
lemma memberActualKraus_zero_matrix (positive : 0 < modulus.toNat)
    (environment : model.Environment) (Reference : Register)
    (store : Store (MemberMatrixCtx base noQuantum m ell width))
    (outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target) :
    memberActualKraus base noQuantum m ell width modulus wide generator target environment Reference
        store outcomes *
      BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) =
    memberAlpha m ell width modulus generator target •
      (BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) *
        memberSourceKraus base noQuantum m ell width modulus wide generator target Reference store
          outcomes) := by
  have first := exponentActualKraus_zero_matrix base noQuantum m ell width modulus wide generator
    true (firstCell base noQuantum m ell width) positive
    (firstCell_vent_distinct base noQuantum m ell width) environment Reference (ell + m) 0
    (by omega) store outcomes.1
  have second := exponentActualKraus_zero_matrix base noQuantum m ell width modulus wide target⁻¹
    true (secondCell base noQuantum m ell width) positive
    (secondCell_vent_distinct base noQuantum m ell width) environment Reference ell 0 (by omega)
    (exponentActualRecord base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) store outcomes.1).1 outcomes.2
  change (_ * _) * _ = _
  rw [Matrix.mul_assoc, first, Matrix.mul_smul, ← Matrix.mul_assoc, second, Matrix.smul_mul,
    smul_smul]
  simp only [memberAlpha, memberSourceKraus, Matrix.mul_assoc]
  congr 1
  exact mul_comm _ _

/-- Every original member record transports the full unnormalized mixed/reference matrix. -/
lemma memberActualKraus_mixed (positive : 0 < modulus.toNat) (environment : model.Environment)
    (Reference : Register) (store : Store (MemberMatrixCtx base noQuantum m ell width))
    (outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target)
    (density : HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference)) :
    let actual := memberActualKraus base noQuantum m ell width modulus wide generator target
      environment Reference store outcomes
    let embedding := BasisEmbedding.matrix
      (zeroJointEmbedding base noQuantum m ell width modulus Reference)
    let source := memberSourceKraus base noQuantum m ell width modulus wide generator target
      Reference store outcomes
    actual * (embedding * density * embedding.conjTranspose) * actual.conjTranspose =
      (memberAlpha m ell width modulus generator target *
        star (memberAlpha m ell width modulus generator target)) •
        (embedding * (source * density * source.conjTranspose) * embedding.conjTranspose) := by
  exact scaled_conjugation _ _ _ _ _ (memberActualKraus_zero_matrix base noQuantum m ell width
    modulus wide generator target positive environment Reference store outcomes)

/-- The actual whole member retains every original correlation and chronological path. -/
lemma member_clean_blocks (positive : 0 < modulus.toNat) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : ExecutionState (Store (MemberMatrixCtx base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Recycling.Carrier.units modulus.toNat).prod Reference))
    (result : Store (MemberMatrixCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (member base noQuantum m ell width wide modulus generator target).Path))) :
    (((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference (encodeUnitState base noQuantum m ell width modulus state)).block result).matrix =
      ∑ original : Store (MemberMatrixCtx base noQuantum m ell width) ×
          (model.HiddenState × History),
        ∑ outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target,
          if Execution.Instrument.retainedRecord
              (memberActualRecord base noQuantum m ell width modulus wide generator target)
              original outcomes = result then
            let embedding := BasisEmbedding.matrix
              (zeroJointEmbedding base noQuantum m ell width modulus Reference)
            let source := memberSourceKraus base noQuantum m ell width modulus wide generator target
              Reference original.1 outcomes
            (memberAlpha m ell width modulus generator target *
              star (memberAlpha m ell width modulus generator target)) •
              (embedding * (source * (state.block original).matrix * source.conjTranspose) *
                embedding.conjTranspose)
          else 0 := by
  rw [member_block_matrix]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcomes _
  split_ifs
  · exact memberActualKraus_mixed base noQuantum m ell width modulus wide generator target positive
      environment Reference original.1 outcomes (state.block original).matrix
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
