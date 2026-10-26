/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Inverse
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Bank
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Reset

/-!
# Entire active-bank reset in every full actual output record

The reset support holds separately in each actual Store/HiddenState/History/
Path fiber, before summing a classical marginal. No assumption is imposed on
the input density, original cell values or correlations with the reference.
The quantum systems remain present and are reset by their actual measured
negative-shift corrections.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Causal earlier-cell phases cannot change the output-bank zero support of the real readout. -/
lemma window_feedbackKraus_zero_row (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (store : Store ctx) (outcome : Bits active) (index : Fin active)
    (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires index) ≠ 0) :
    (outcomeKraus environment Reference active ports outcome *
      Feedback.wordOperator ports environment Reference store (List.finRange active))
        row column = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro middle _
  rw [window_outcomeKraus_zero_row environment Reference active ports outcome index
    row middle nonzero, zero_mul]

/-- Every full measured output record has the entire physical active bank reset to zero. -/
lemma window_readout_record_zero_row
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (count : Nat) (ports : Ports ctx totalBits count)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (readout (operations := operations) (services := services) count ports).Path)))
    (index : Fin count) (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires index) ≠ 0) :
    (((readout count ports).execute environment Reference state).block result).matrix
      row column = 0 := by
  refine (congrArg (fun density : HilbertOperator (ctx.register.prod Reference) =>
    density row column)
      (window_readout_record_matrix environment count ports Reference state result)).trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro original _
  apply Finset.sum_eq_zero
  intro outcome _
  split_ifs
  · exact conjugation_zero_row _ _ row column (fun middle =>
      window_outcomeKraus_zero_row environment.quantum Reference count ports outcome index
        row middle nonzero)
  · rfl

/-- Exact full-record reset after the literal previous-cell feedback and same-bank readout. -/
lemma window_inverseCode_record_zero_row (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (inverseCode (operations := operations) (services := services) ports).Path)))
    (index : Fin active) (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires index) ≠ 0) :
    (((inverseCode ports).execute environment Reference state).block result).matrix
      row column = 0 := by
  refine (congrArg (fun density : HilbertOperator (ctx.register.prod Reference) =>
    density row column)
      (window_inverseCode_record_matrix ports environment Reference state result)).trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro original _
  apply Finset.sum_eq_zero
  intro outcome _
  split_ifs
  · exact conjugation_zero_row _ _ row column (fun middle =>
      window_feedbackKraus_zero_row ports environment.quantum Reference original.1 outcome index
        row middle nonzero)
  · rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
