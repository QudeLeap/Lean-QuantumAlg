/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Record
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Execution

/-!
# Actual chronological instrument of the complete measured exponent stream

The induction composes the original stage interpreter with the original
remaining suffix. Each next native matrix reads the real preceding Store.
All arithmetic outcomes, measured exponent bits and original reference
coherences remain in the retained blocks [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ExpExecCtx := context base noQuantum m ell width

variable (modulus : BitVec width) (wide : 2 ≤ width) {bits : Nat}
  (unit : (ZMod modulus.toNat)ˣ) (inverse : Bool)
  (outputs : Fin bits → CWriteRef (ExpExecCtx base noQuantum m ell width) (.finite 2))

/-- The original complete exponent interpreter derives its chronological native record products. -/
lemma exponentSuffix_block_matrix (environment : model.Environment) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (ExpExecCtx base noQuantum m ell width) Reference (model.HiddenState × History))
    (result : Store (ExpExecCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit remaining
          position bounded).Path))) :
    (((exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit remaining
      position bounded).execute environment Reference state).block result).matrix =
      ∑ original : Store (ExpExecCtx base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcomes : ExponentOutcomes base noQuantum m ell width modulus wide unit remaining
            position bounded,
          if Execution.Instrument.retainedRecord (exponentActualRecord base noQuantum m ell width
            modulus wide unit
              inverse outputs remaining position bounded) original outcomes = result then
            exponentActualKraus base noQuantum m ell width modulus wide unit inverse outputs
                environment Reference remaining position bounded original.1 outcomes *
              (state.block original).matrix *
              (exponentActualKraus base noQuantum m ell width modulus wide unit inverse outputs
                environment Reference remaining position bounded original.1 outcomes).conjTranspose
          else 0 := by
  induction remaining generalizing position Reference History with
  | zero =>
      change Store (ExpExecCtx base noQuantum m ell width) ×
        (model.HiddenState × (History × Unit)) at result
      have actual := Circuit.execute_id (allowAllocation := false) environment state
      have observed := congrArg (fun final : State (ExpExecCtx base noQuantum m ell width) Reference
          (model.HiddenState × (History × Unit)) => (final.block result).matrix) actual
      have grouped := ExecutionState.mapClassical_block_matrix state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) result
      refine observed.trans (grouped.trans ?_)
      let _ : Unique (ExponentOutcomes base noQuantum m ell width modulus wide unit 0 position
          bounded) := by
        change Unique Unit
        infer_instance
      simp only [Fintype.sum_unique, exponentActualKraus,
        Matrix.conjTranspose_one, one_mul, mul_one]
      apply Finset.sum_congr rfl
      intro original _
      have sameRecord : Execution.Instrument.retainedRecord
          (exponentActualRecord base noQuantum m ell width modulus wide unit inverse outputs 0
            position bounded) original default =
          (original.1, (original.2.1, (original.2.2, ()))) := rfl
      split_ifs with first second third
      · rfl
      · exact False.elim (second (sameRecord.trans first))
      · exact False.elim (first (sameRecord.symm.trans third))
      · rfl
  | succ remaining induction =>
      let current : Fin bits := ⟨position, by omega⟩
      have actual := Execution.Instrument.execute_sequenceRetainedBlocks
        (stage base noQuantum m ell width wide inverse outputs modulus unit current)
        (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit remaining
          (position + 1) (by omega))
        (fun store (outcomes : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
            current × Fin ((ExpExecCtx base noQuantum m ell width).quantumLayout.wire
              (control base noQuantum m ell width)).dimension) =>
          stageRecord base noQuantum m ell width modulus wide inverse outputs unit current store
            outcomes.1 outcomes.2)
        (exponentActualRecord base noQuantum m ell width modulus wide unit inverse outputs remaining
          (position + 1) (by omega))
        (fun reference store outcomes => stageActualKraus base noQuantum m ell width modulus wide
          inverse outputs unit current environment store outcomes.1 outcomes.2 reference)
        (fun reference store outcomes => exponentActualKraus base noQuantum m ell width modulus wide
          unit inverse outputs environment reference remaining (position + 1) (by omega) store
            outcomes)
        environment
        (by
          intro reference history historyFinite original selected
          have proved := stage_block_matrix base noQuantum m ell width modulus wide inverse outputs
            unit current environment reference original selected
          refine proved.trans ?_
          apply Finset.sum_congr rfl
          intro entry _
          conv_rhs => rw [Fintype.sum_prod_type])
        (by
          intro reference history historyFinite original selected
          have proved := induction (position + 1) (by omega) reference original selected
          refine proved.trans ?_
          apply Finset.sum_congr rfl
          intro entry _
          apply Finset.sum_congr rfl
          intro outcome _
          split_ifs <;> rfl)
        Reference state result
      refine actual.trans ?_
      simp only [ExponentOutcomes]
      apply Finset.sum_congr rfl
      intro original _
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro head _
      apply Finset.sum_congr rfl
      intro tail _
      rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
