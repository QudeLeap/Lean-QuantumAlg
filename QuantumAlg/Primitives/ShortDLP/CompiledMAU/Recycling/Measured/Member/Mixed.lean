/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Normalization
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Mixed

/-!
# Actual two-stream mixed records with arithmetic-independent source matrices

The actual full member interpreter keeps every original Store, hidden state
and chronological Path. Each original arithmetic record transports the same
retained-bit unit/reference posterior beside its independently proved common
coefficient [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberMixedCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- All actual member records realize the same complete retained-bit source operator. -/
lemma memberActualKraus_readout_matrix (positive : 0 < modulus.toNat) (Reference : Register)
    (environment : model.Environment) (store : Store (MemberMixedCtx base noQuantum m ell width))
    (arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target)
    (readout : MemberReadouts m ell) :
    memberActualKraus base noQuantum m ell width modulus wide generator target environment Reference
        store ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout)) *
      BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) =
    memberAlpha m ell width modulus generator target •
      (BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) *
        memberReadoutSource base noQuantum m ell width modulus generator target Reference store
          readout) := by
  have action := memberActualKraus_zero_matrix base noQuantum m ell width modulus wide generator
    target positive environment Reference store
    ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
      (arithmetic, readout))
  rw [memberSourceKraus_readout base noQuantum m ell width modulus wide generator target Reference
    store arithmetic readout] at action
  exact action

/-- The actual member record carries the full unnormalized mixed/reference posterior. -/
lemma memberActualKraus_readout_mixed (positive : 0 < modulus.toNat) (Reference : Register)
    (environment : model.Environment) (store : Store (MemberMixedCtx base noQuantum m ell width))
    (arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target)
    (readout : MemberReadouts m ell)
    (density : HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference)) :
    let actual := memberActualKraus base noQuantum m ell width modulus wide generator target
      environment Reference store
      ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
        (arithmetic, readout))
    let embedding := BasisEmbedding.matrix
      (zeroJointEmbedding base noQuantum m ell width modulus Reference)
    let source := memberReadoutSource base noQuantum m ell width modulus generator target Reference
      store readout
    actual * (embedding * density * embedding.conjTranspose) * actual.conjTranspose =
      (memberAlpha m ell width modulus generator target *
        star (memberAlpha m ell width modulus generator target)) •
        (embedding * (source * density * source.conjTranspose) * embedding.conjTranspose) := by
  exact scaled_conjugation _ _ _ _ _ (memberActualKraus_readout_matrix base noQuantum m ell width
    modulus wide generator target positive Reference environment store arithmetic readout)

/-- The same actual complete interpreter retains every chronological physical record block. -/
lemma member_readout_clean_blocks (positive : 0 < modulus.toNat) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : ExecutionState (Store (MemberMixedCtx base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Recycling.Carrier.units modulus.toNat).prod Reference))
    (result : Store (MemberMixedCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (member base noQuantum m ell width wide modulus generator target).Path))) :
    (((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference (encodeUnitState base noQuantum m ell width modulus state)).block result).matrix =
      ∑ original : Store (MemberMixedCtx base noQuantum m ell width) ×
          (model.HiddenState × History),
        ∑ arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator
            target,
          ∑ readout : MemberReadouts m ell,
            if Execution.Instrument.retainedRecord
                (memberActualRecord base noQuantum m ell width modulus wide generator target)
                original ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator
                  target).symm (arithmetic, readout)) = result then
              let embedding := BasisEmbedding.matrix
                (zeroJointEmbedding base noQuantum m ell width modulus Reference)
              let source := memberReadoutSource base noQuantum m ell width modulus generator target
                Reference original.1 readout
              (memberAlpha m ell width modulus generator target *
                star (memberAlpha m ell width modulus generator target)) •
                (embedding * (source * (state.block original).matrix * source.conjTranspose) *
                  embedding.conjTranspose)
            else 0 := by
  rw [member_block_matrix]
  apply Finset.sum_congr rfl
  intro original _
  rw [member_outcome_sum_reindex base noQuantum m ell width modulus wide generator target]
  apply Finset.sum_congr rfl
  intro arithmetic _
  apply Finset.sum_congr rfl
  intro readout _
  split_ifs
  · exact memberActualKraus_readout_mixed base noQuantum m ell width modulus wide generator target
      positive Reference environment original.1 arithmetic readout (state.block original).matrix
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
