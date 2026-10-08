/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State
import all QuantumAlg.Core.Base.Gate.Effect.BasisSlice
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Exact observations after actual complete basis reset

Every real final Store and measurement path keeps its own conditional
reference matrix. The original observable compresses to that matrix exactly.
A bound uniform over pure references and the actual classical records extends
to arbitrary initial mixtures and correlations, with no branch normalization
or independent-sample interpreter.
-/

namespace QuantumAlg.QuditShift

noncomputable section

open Execution

variable {gates : GateModel} {oracles : OracleModel}
variable {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History]

variable {implementations : ∀ wire,
  Realizations gates oracles ctx.quantumLayout wire}

/-- Every real reset outcome has its own exact compressed reference observation. -/
theorem resetToBasis_effectWeight
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis)
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      ((ExecutionModel.quantum gates oracles).HiddenState ×
      (History × (resetToBasis implementations outputs label).Path))) :
    ((resetToBasis implementations outputs label).execute Reference state).effectWeight effects =
      ∑ record : Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
          (History × (resetToBasis implementations outputs label).Path)),
        ((effects record).basisSliceEffect label).weight
          ((((resetToBasis implementations outputs label).execute Reference state).block
            record).basisSlice
            label) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro record _
  exact Effect.weight_basisSlice_of_factor (R := ctx.register) (Reference := Reference)
    (effects record) (((resetToBasis implementations outputs label).execute Reference state).block
      record)
    label (resetToBasis_block_factor (implementations := implementations) outputs label state
      record)

/-- Pure-reference bounds extend to the same actual reset, retaining every branch's mass. -/
theorem resetToBasis_effectWeight_lower
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis)
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      ((ExecutionModel.quantum gates oracles).HiddenState ×
      (History × (resetToBasis implementations outputs label).Path)))
    (lower : ℝ)
    (bound : ∀ record (reference : NormalizedVector Reference),
      lower ≤ ((effects record).basisSliceEffect label).weight
        (DensityOperator.ofPure reference)) :
    state.mass * lower ≤
      ((resetToBasis implementations outputs label).execute Reference state).effectWeight effects
        := by
  have mass := Circuit.execute_mass (resetToBasis implementations outputs label) Reference state
  rw [← mass]
  unfold ExecutionState.mass ExecutionState.effectWeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro record _
  exact Effect.mass_mul_le_weight_of_basis_factor (R := ctx.register) (Reference := Reference)
    (effects record) (((resetToBasis implementations outputs label).execute Reference state).block
      record)
    label lower (resetToBasis_block_factor (implementations := implementations) outputs label
      state record) (bound record)

end

end QuantumAlg.QuditShift
