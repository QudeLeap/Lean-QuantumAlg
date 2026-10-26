/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Remap
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Mixed

/-!
# Actual complete two-stream output observation and coherent posterior

The real member interpreter writes both exponent tuples into its retained
cells. Only unobserved arithmetic/path fibers are merged. The exact total
arithmetic weight is one, and the complete first accumulator/reference
posterior passes into the second exponent [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberObsCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- The actual entire member output carries its full original two-stream coherent posterior. -/
lemma member_observed_blocks (positive : 0 < modulus.toNat) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : ExecutionState (Store (MemberObsCtx base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Recycling.Carrier.units modulus.toNat).prod Reference))
    (observed : CShape.Value (.fixedVector (resultBits m ell) (.finite 2))) :
    ((((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference (encodeUnitState base noQuantum m ell width modulus state)).mapClassical
      (fun entry => (resultRead base noQuantum m ell width).eval entry.1)).block observed).matrix =
      let embedding := BasisEmbedding.matrix
        (zeroJointEmbedding base noQuantum m ell width modulus Reference)
      ∑ original : Store (MemberObsCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ readout : MemberReadouts m ell,
          let source := memberReadoutSource base noQuantum m ell width modulus generator target
            Reference original.1 readout
          if (resultRead base noQuantum m ell width).eval
              (memberReadoutStore base noQuantum m ell width original.1 readout) = observed then
            embedding * (source * (state.block original).matrix * source.conjTranspose) *
              embedding.conjTranspose
          else 0 := by
  let Outcomes :=
    MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target ×
      MemberReadouts m ell
  let embedding := BasisEmbedding.matrix
    (zeroJointEmbedding base noQuantum m ell width modulus Reference)
  let contribution
      (original : Store (MemberObsCtx base noQuantum m ell width) × (model.HiddenState × History))
      (readout : MemberReadouts m ell) :=
    let source := memberReadoutSource base noQuantum m ell width modulus generator target Reference
      original.1 readout
    embedding * (source * (state.block original).matrix * source.conjTranspose) *
      embedding.conjTranspose
  have actual := Execution.Instrument.mapClassical_retained_matrix
    ((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference (encodeUnitState base noQuantum m ell width modulus state))
    (Execution.Instrument.retainedRecord (fun store (outcomes : Outcomes) => memberActualRecord
      base noQuantum m ell
      width modulus wide generator target store
      ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
        outcomes)))
    (fun original (outcomes : Outcomes) =>
      (memberAlpha m ell width modulus generator target *
        star (memberAlpha m ell width modulus generator target)) •
          contribution original outcomes.2)
    (by
      intro result
      have proved := member_readout_clean_blocks base noQuantum m ell width modulus wide generator
        target positive environment Reference state result
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro arithmetic _
      apply Finset.sum_congr rfl
      intro readout _
      split_ifs with first second third
      · rfl
      · exact False.elim (second first)
      · exact False.elim (first third)
      · rfl)
    (fun entry => (resultRead base noQuantum m ell width).eval entry.1) observed
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  conv_lhs => rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro readout _
  have preserved (arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide
      generator target) :
      (resultRead base noQuantum m ell width).eval
          (memberActualRecord base noQuantum m ell width modulus wide generator target original.1
            ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
              (arithmetic, readout))).1 =
        (resultRead base noQuantum m ell width).eval
          (memberReadoutStore base noQuantum m ell width original.1 readout) := by
    apply congrArg CShape.Value.fixedVector
    funext index
    exact memberRecord_resultStoreAgree base noQuantum m ell width modulus wide generator target
      original.1 arithmetic readout index
  by_cases selected : (resultRead base noQuantum m ell width).eval
      (memberReadoutStore base noQuantum m ell width original.1 readout) = observed
  · rw [if_pos selected]
    calc
      _ = ∑ _arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator
          target,
          (memberAlpha m ell width modulus generator target *
            star (memberAlpha m ell width modulus generator target)) •
              contribution original readout := by
        apply Finset.sum_congr rfl
        intro arithmetic _
        apply if_pos
        exact (preserved arithmetic).trans selected
      _ = _ := by rw [← Finset.sum_smul, member_arithmetic_weights_sum, one_smul]
  · rw [if_neg selected]
    apply Finset.sum_eq_zero
    intro arithmetic _
    apply if_neg
    intro hit
    exact selected ((preserved arithmetic).symm.trans hit)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
