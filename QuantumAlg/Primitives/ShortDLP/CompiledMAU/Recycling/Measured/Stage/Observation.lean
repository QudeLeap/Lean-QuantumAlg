/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Remap
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Mixed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Readout
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Normalization

/-!
# Actual stage observation after summing only unobserved arithmetic records

Every retained exponent output and the complete unit/reference matrix remain
in the observation. Exact chronological arithmetic outcome weights sum to
one; the physical exponent outcome remains as the original paid output
write. No intermediate accumulator is replaced by a new seed
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ObsCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Actual retained output blocks are the independently specified mixed half-sum branches. -/
lemma stage_observed_blocks (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (inverse : Bool) {bits : Nat} (selection : Fin bits → Fin (resultBits m ell))
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : ExecutionState (Store (ObsCtx base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Recycling.Carrier.units modulus.toNat).prod Reference))
    (observed : CShape.Value (.fixedVector (resultBits m ell) (.finite 2))) :
    ((((stage base noQuantum m ell width wide inverse
      (fun index => resultCell base noQuantum m ell width (selection index)) modulus unit
      position).execute environment Reference
        (encodeUnitState base noQuantum m ell width modulus state)).mapClassical
      (fun entry => (resultRead base noQuantum m ell width).eval entry.1)).block observed).matrix =
      let embedding := BasisEmbedding.matrix
        (zeroJointEmbedding base noQuantum m ell width modulus Reference)
      ∑ original : Store (ObsCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome : Fin ((ObsCtx base noQuantum m ell width).quantumLayout.wire
            (control base noQuantum m ell width)).dimension,
          let bit := placedOutcome (Physical.layout width).control (Physical.qubits width)
            (ObsCtx base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome
          let source := stageSourceKraus base noQuantum m ell width modulus inverse
            (fun index => resultCell base noQuantum m ell width (selection index)) unit position
            Reference original.1 bit
          if (resultRead base noQuantum m ell width).eval
              (original.1.write (resultCell base noQuantum m ell width (selection position))
                (.finite bit)) = observed then
            embedding * (source * (state.block original).matrix * source.conjTranspose) *
              embedding.conjTranspose
          else 0 := by
  let outputs := fun index => resultCell base noQuantum m ell width (selection index)
  let embedding := BasisEmbedding.matrix
    (zeroJointEmbedding base noQuantum m ell width modulus Reference)
  let contribution
      (original : Store (ObsCtx base noQuantum m ell width) × (model.HiddenState × History))
      (outcome : Fin ((ObsCtx base noQuantum m ell width).quantumLayout.wire
        (control base noQuantum m ell width)).dimension) :=
    let bit := placedOutcome (Physical.layout width).control (Physical.qubits width)
      (ObsCtx base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome
    let source := stageSourceKraus base noQuantum m ell width modulus inverse outputs unit position
      Reference original.1 bit
    embedding * (source * (state.block original).matrix * source.conjTranspose) *
      embedding.conjTranspose
  have actual := Execution.Instrument.mapClassical_retained_matrix
    ((stage base noQuantum m ell width wide inverse outputs modulus unit position).execute
      environment Reference (encodeUnitState base noQuantum m ell width modulus state))
    (Execution.Instrument.retainedRecord (fun store
        (outcomes : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position ×
          Fin ((ObsCtx base noQuantum m ell width).quantumLayout.wire
            (control base noQuantum m ell width)).dimension) =>
      stageRecord base noQuantum m ell width modulus wide inverse outputs unit position store
        outcomes.1 outcomes.2))
    (fun original
        (outcomes : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position ×
          Fin ((ObsCtx base noQuantum m ell width).quantumLayout.wire
            (control base noQuantum m ell width)).dimension) =>
      (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)) *
        star (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)))) •
          contribution original outcomes.2)
    (by
      intro result
      have proved := stage_clean_blocks base noQuantum m ell width modulus wide positive inverse
        outputs (fun vent index => vent_result_distinct base noQuantum m ell width vent
          (selection index)) unit position environment Reference state result
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      conv_rhs => rw [Fintype.sum_prod_type])
    (fun entry => (resultRead base noQuantum m ell width).eval entry.1) observed
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  conv_lhs => rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  have preserved (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
      position) := stageRecord_resultRead base noQuantum m ell width modulus wide inverse selection
        unit position original.1 measured outcome
  let bit := placedOutcome (Physical.layout width).control (Physical.qubits width)
    (ObsCtx base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome
  by_cases selected : (resultRead base noQuantum m ell width).eval
      (original.1.write (resultCell base noQuantum m ell width (selection position))
        (.finite bit)) = observed
  · rw [if_pos selected]
    calc
      _ = ∑ _measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
          position,
          (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)) *
            star (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)))) •
              contribution original outcome := by
        apply Finset.sum_congr rfl
        intro measured _
        apply if_pos
        exact (preserved measured).trans selected
      _ = _ := by rw [← Finset.sum_smul, arithmetic_record_weights_sum, one_smul]
  · rw [if_neg selected]
    apply Finset.sum_eq_zero
    intro measured _
    apply if_neg
    intro hit
    exact selected ((preserved measured).symm.trans hit)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
