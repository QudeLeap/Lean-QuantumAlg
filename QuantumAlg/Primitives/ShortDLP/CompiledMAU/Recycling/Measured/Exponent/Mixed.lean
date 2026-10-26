/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Execution
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Mixed

/-!
# Actual complete exponent mixed blocks at every arithmetic and retained-bit record

The actual chronological interpreter acts on the complete unnormalized
unit/reference matrix. Each arithmetic record has the same public scalar
and the same retained-bit source operator, while its full actual Store and
Path remain explicit [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute
open QuantumFourierTransform.Semiclassical (Bits)

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ExpMixedCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (unit : (ZMod modulus.toNat)ˣ) (inverse : Bool) {bits : Nat}
  (selection : Fin bits → Fin (resultBits m ell))

/-- Every reindexed actual record realizes the same full logical retained-bit source matrix. -/
lemma exponentActualKraus_readout_matrix (positive : 0 < modulus.toNat) (Reference : Register)
    (environment : model.Environment) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) (store : Store (ExpMixedCtx base noQuantum m ell width))
    (arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
      position bounded) (readout : Bits remaining) :
    exponentActualKraus base noQuantum m ell width modulus wide unit inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) environment Reference
        remaining position bounded store
        ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining position
          bounded).symm (arithmetic, readout)) *
      BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) =
    exponentAlpha width modulus unit remaining position bounded •
      (BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) *
        exponentReadoutSource base noQuantum m ell width modulus unit inverse selection Reference
          remaining position bounded store readout) := by
  have action := exponentActualKraus_zero_matrix base noQuantum m ell width modulus wide unit
    inverse (fun index => resultCell base noQuantum m ell width (selection index)) positive
    (fun vent index => vent_result_distinct base noQuantum m ell width vent (selection index))
    environment Reference remaining position bounded store
    ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining position
      bounded).symm (arithmetic, readout))
  rw [exponentSourceKraus_readout base noQuantum m ell width modulus wide unit inverse selection
    Reference remaining position bounded store store (fun _ => rfl) arithmetic readout] at action
  exact action

/-- Every actual exponent record keeps the complete mixed/reference posterior. -/
lemma exponentActualKraus_readout_mixed (positive : 0 < modulus.toNat) (Reference : Register)
    (environment : model.Environment) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) (store : Store (ExpMixedCtx base noQuantum m ell width))
    (arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
      position bounded) (readout : Bits remaining)
    (density : HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference)) :
    let actual := exponentActualKraus base noQuantum m ell width modulus wide unit inverse
      (fun index => resultCell base noQuantum m ell width (selection index)) environment Reference
      remaining position bounded store
      ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining position
        bounded).symm (arithmetic, readout))
    let embedding := BasisEmbedding.matrix
      (zeroJointEmbedding base noQuantum m ell width modulus Reference)
    let source := exponentReadoutSource base noQuantum m ell width modulus unit inverse selection
      Reference remaining position bounded store readout
    actual * (embedding * density * embedding.conjTranspose) * actual.conjTranspose =
      (exponentAlpha width modulus unit remaining position bounded *
        star (exponentAlpha width modulus unit remaining position bounded)) •
        (embedding * (source * density * source.conjTranspose) * embedding.conjTranspose) := by
  exact scaled_conjugation _ _ _ _ _ (exponentActualKraus_readout_matrix base noQuantum m ell width
    modulus wide unit inverse selection positive Reference environment remaining position bounded
    store arithmetic readout)

/-- The actual complete suffix retains every original Store, hidden state and chronological path. -/
lemma exponentSuffix_clean_blocks (positive : 0 < modulus.toNat) (environment : model.Environment)
    (remaining position : Nat) (bounded : position + remaining ≤ bits) (Reference : Register)
    {History : Type} [Fintype History]
    (state : ExecutionState (Store (ExpMixedCtx base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Recycling.Carrier.units modulus.toNat).prod Reference))
    (result : Store (ExpMixedCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (exponentSuffix base noQuantum m ell width wide inverse
          (fun index => resultCell base noQuantum m ell width (selection index)) modulus unit
          remaining position bounded).Path))) :
    (((exponentSuffix base noQuantum m ell width wide inverse
      (fun index => resultCell base noQuantum m ell width (selection index)) modulus unit remaining
      position bounded).execute environment Reference
        (encodeUnitState base noQuantum m ell width modulus state)).block result).matrix =
      ∑ original : Store (ExpMixedCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit
            remaining position bounded,
          ∑ readout : Bits remaining,
            if Execution.Instrument.retainedRecord (exponentActualRecord base noQuantum m ell
              width modulus wide unit
                inverse (fun index => resultCell base noQuantum m ell width (selection index))
                remaining position bounded) original
                ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining
                  position bounded).symm (arithmetic, readout)) = result then
              let embedding := BasisEmbedding.matrix
                (zeroJointEmbedding base noQuantum m ell width modulus Reference)
              let source := exponentReadoutSource base noQuantum m ell width modulus unit inverse
                selection Reference remaining position bounded original.1 readout
              (exponentAlpha width modulus unit remaining position bounded *
                star (exponentAlpha width modulus unit remaining position bounded)) •
                (embedding * (source * (state.block original).matrix * source.conjTranspose) *
                  embedding.conjTranspose)
            else 0 := by
  rw [exponentSuffix_block_matrix]
  apply Finset.sum_congr rfl
  intro original _
  rw [exponent_outcome_sum_reindex base noQuantum m ell width modulus wide unit remaining position
    bounded]
  apply Finset.sum_congr rfl
  intro arithmetic _
  apply Finset.sum_congr rfl
  intro readout _
  split_ifs
  · exact exponentActualKraus_readout_mixed base noQuantum m ell width modulus wide unit inverse
      selection positive Reference environment remaining position bounded original.1 arithmetic
      readout (state.block original).matrix
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
