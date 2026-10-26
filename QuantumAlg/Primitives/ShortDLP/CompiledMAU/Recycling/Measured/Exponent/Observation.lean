/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Remap
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Mixed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Normalization

/-!
# Actual full exponent output observation after summing arithmetic histories

Only unobserved arithmetic records and path fibers are merged. Every real
retained exponent output and the complete unit/reference matrix remain.
The exact common arithmetic coefficient weights sum to one, while the
retained-bit source probabilities remain unchanged [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute
open QuantumFourierTransform.Semiclassical (Bits)

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ExpObsCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (unit : (ZMod modulus.toNat)ˣ) (inverse : Bool) {bits : Nat}
  (selection : Fin bits → Fin (resultBits m ell))

/-- Actual observed exponent blocks have their complete original retained-bit source posterior. -/
lemma exponentSuffix_observed_blocks (positive : 0 < modulus.toNat)
    (environment : model.Environment) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) (Reference : Register)
    {History : Type} [Fintype History]
    (state : ExecutionState (Store (ExpObsCtx base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Recycling.Carrier.units modulus.toNat).prod Reference))
    (observed : CShape.Value (.fixedVector (resultBits m ell) (.finite 2))) :
    ((((exponentSuffix base noQuantum m ell width wide inverse
      (fun index => resultCell base noQuantum m ell width (selection index)) modulus unit remaining
      position bounded).execute environment Reference
        (encodeUnitState base noQuantum m ell width modulus state)).mapClassical
      (fun entry => (resultRead base noQuantum m ell width).eval entry.1)).block observed).matrix =
      let embedding := BasisEmbedding.matrix
        (zeroJointEmbedding base noQuantum m ell width modulus Reference)
      ∑ original : Store (ExpObsCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ readout : Bits remaining,
          let source := exponentReadoutSource base noQuantum m ell width modulus unit inverse
            selection Reference remaining position bounded original.1 readout
          if (resultRead base noQuantum m ell width).eval
              (exponentOutputStore base noQuantum m ell width selection remaining position bounded
                original.1 readout) = observed then
            embedding * (source * (state.block original).matrix * source.conjTranspose) *
              embedding.conjTranspose
          else 0 := by
  let Outcomes := ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
    position bounded × Bits remaining
  let outputs := fun index => resultCell base noQuantum m ell width (selection index)
  let embedding := BasisEmbedding.matrix
    (zeroJointEmbedding base noQuantum m ell width modulus Reference)
  let contribution
      (original : Store (ExpObsCtx base noQuantum m ell width) × (model.HiddenState × History))
      (readout : Bits remaining) :=
    let source := exponentReadoutSource base noQuantum m ell width modulus unit inverse selection
      Reference remaining position bounded original.1 readout
    embedding * (source * (state.block original).matrix * source.conjTranspose) *
      embedding.conjTranspose
  have actual := Execution.Instrument.mapClassical_retained_matrix
    ((exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit remaining position
      bounded).execute environment Reference (encodeUnitState base noQuantum m ell width modulus
        state))
    (Execution.Instrument.retainedRecord (fun store (outcomes : Outcomes) =>
      exponentActualRecord base noQuantum m ell width modulus wide unit inverse outputs remaining
        position bounded store
        ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining position
          bounded).symm outcomes)))
    (fun original (outcomes : Outcomes) =>
      (exponentAlpha width modulus unit remaining position bounded *
        star (exponentAlpha width modulus unit remaining position bounded)) •
          contribution original outcomes.2)
    (by
      intro result
      have proved := exponentSuffix_clean_blocks base noQuantum m ell width modulus wide unit
        inverse selection positive environment remaining position bounded Reference state result
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
  have preserved (arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide
      unit remaining position bounded) :
      (resultRead base noQuantum m ell width).eval
          (exponentActualRecord base noQuantum m ell width modulus wide unit inverse outputs
            remaining position bounded original.1
            ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining position
              bounded).symm (arithmetic, readout))).1 =
        (resultRead base noQuantum m ell width).eval
          (exponentOutputStore base noQuantum m ell width selection remaining position bounded
            original.1 readout) := by
    apply congrArg CShape.Value.fixedVector
    funext index
    exact exponentRecord_resultStoreAgree base noQuantum m ell width selection modulus wide unit
      inverse remaining position bounded original.1 original.1 (fun _ => rfl) arithmetic readout
      index
  by_cases selected : (resultRead base noQuantum m ell width).eval
      (exponentOutputStore base noQuantum m ell width selection remaining position bounded
        original.1 readout) = observed
  · rw [if_pos selected]
    calc
      _ = ∑ _arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit
          remaining position bounded,
          (exponentAlpha width modulus unit remaining position bounded *
            star (exponentAlpha width modulus unit remaining position bounded)) •
              contribution original readout := by
        apply Finset.sum_congr rfl
        intro arithmetic _
        apply if_pos
        exact (preserved arithmetic).trans selected
      _ = _ := by rw [← Finset.sum_smul, exponent_arithmetic_weights_sum, one_smul]
  · rw [if_neg selected]
    apply Finset.sum_eq_zero
    intro arithmetic _
    apply if_neg
    intro hit
    exact selected ((preserved arithmetic).symm.trans hit)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
