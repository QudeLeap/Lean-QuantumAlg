/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Matrix
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Feedback
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Execution
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Mixed

/-!
# Complete mixed/reference instrument of the actual measured stage

The full unnormalized accumulator posterior passes through the stage without
reinitialization. The arithmetic-record scalar is independent of the old
Store, controls, modular-unit amplitudes and arbitrary external reference.
Actual physical reset restores the zero-control frame [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MixCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Independent logical half-sum on the same accumulator and unchanged reference. -/
def stageSourceKraus (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (MixCtx base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (Reference : Register)
    (store : Store (MixCtx base noQuantum m ell width)) (outcome : Fin 2) :
    HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) :=
  sourceWithReference
    (Recycling.ControlKraus.halfSum
      (unitTranslation modulus (unit ^ (2 ^ position.rev.val)) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat))
      (feedbackScalar base noQuantum m ell width inverse outputs position position.val le_rfl store)
      outcome) Reference

/-- Every actual stage record carries the complete mixed accumulator/reference posterior. -/
lemma stageActualKraus_mixed (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (MixCtx base noQuantum m ell width) (.finite 2))
    (separate : ∀ vent index,
      (ventCell base noQuantum m ell width vent).key ≠ (outputs index).key)
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (environment : model.Environment)
    (store : Store (MixCtx base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((MixCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) (Reference : Register)
    (density : HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference)) :
    let actual := stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit
      position environment store measured outcome Reference
    let embedding := BasisEmbedding.matrix
      (zeroJointEmbedding base noQuantum m ell width modulus Reference)
    let source := stageSourceKraus base noQuantum m ell width modulus inverse outputs unit position
      Reference store
      (placedOutcome (Physical.layout width).control (Physical.qubits width)
        (MixCtx base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome)
    actual * (embedding * density * embedding.conjTranspose) * actual.conjTranspose =
      (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)) *
        star (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)))) •
        (embedding * (source * density * source.conjTranspose) * embedding.conjTranspose) := by
  have action := stageActualKraus_zero_matrix base noQuantum m ell width modulus wide positive
    inverse outputs unit position environment store measured outcome Reference
  rw [stageArithmetic_feedbackScalar base noQuantum m ell width modulus wide inverse outputs
    separate unit position store measured] at action
  exact scaled_conjugation _ _ _ _ _ action

/-- The actual retained stage blocks preserve all original correlations and chronological paths. -/
lemma stage_clean_blocks (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (MixCtx base noQuantum m ell width) (.finite 2))
    (separate : ∀ vent index,
      (ventCell base noQuantum m ell width vent).key ≠ (outputs index).key)
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : ExecutionState (Store (MixCtx base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Recycling.Carrier.units modulus.toNat).prod Reference))
    (result : Store (MixCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path))) :
    (((stage base noQuantum m ell width wide inverse outputs modulus unit position).execute
      environment Reference (encodeUnitState base noQuantum m ell width modulus state)).block
        result).matrix =
      ∑ original : Store (MixCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position,
          ∑ outcome,
            if Execution.Instrument.retainedRecord (fun store outcomes => stageRecord base
              noQuantum m ell width modulus
                wide inverse outputs unit position store outcomes.1 outcomes.2)
                original (measured, outcome) = result then
              let embedding := BasisEmbedding.matrix
                (zeroJointEmbedding base noQuantum m ell width modulus Reference)
              let source := stageSourceKraus base noQuantum m ell width modulus inverse outputs unit
                position Reference original.1
                (placedOutcome (Physical.layout width).control (Physical.qubits width)
                  (MixCtx base noQuantum m ell width) (context_wires base noQuantum m ell width)
                  outcome)
              (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)) *
                star (arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)))) •
                (embedding * (source * (state.block original).matrix * source.conjTranspose) *
                  embedding.conjTranspose)
            else 0 := by
  rw [stage_block_matrix]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro measured _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs
  · exact stageActualKraus_mixed base noQuantum m ell width modulus wide positive inverse outputs
      separate unit position environment original.1 measured outcome Reference
      (state.block original).matrix
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
