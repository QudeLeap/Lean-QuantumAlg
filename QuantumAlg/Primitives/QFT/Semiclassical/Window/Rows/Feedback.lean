/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Rows
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Word

/-!
# Full actual window source rows, including real earlier-cell feedback

The measured/reset source row multiplies the exact native phase word read
from the original complete Store. The derived full-layout row and stored
instrument keep every complementary coordinate, all History and Reference.
The equality is a result about the same executed inverseCode, not a source
operator or a branch-correctness assumption supplied by its caller.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Independently written source row and the real prior-cell phase scalar on each input column. -/
def sourceWindowKraus (ports : Ports ctx totalBits active) (Reference : Register)
    (original : Store ctx) (outcome : Bits active) :
    HilbertOperator (ctx.register.prod Reference) :=
  fun row column =>
    if (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
          Partner.zeroBits active ∧
        (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
          (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
      signedSourceMatrix true active outcome
          (referenceBankCoordinates ports.wires ports.qubits Reference column).1 *
        Feedback.wordScalar ports original column.1 (List.finRange active)
    else 0

lemma window_feedbackKraus_source_entry (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (original : Store ctx) (outcome : Bits active)
    (row column : (ctx.register.prod Reference).Index) :
    (outcomeKraus environment Reference active ports outcome *
        Feedback.wordOperator ports environment Reference original (List.finRange active))
          row column = sourceWindowKraus ports Reference original outcome row column := by
  rw [Feedback.wordOperator_diagonal, Matrix.mul_diagonal, window_outcomeKraus_source_entry]
  unfold sourceWindowKraus
  by_cases selected :
      (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
          Partner.zeroBits active ∧
        (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
          (referenceBankCoordinates ports.wires ports.qubits Reference column).2
  · simp only [if_pos selected]
  · simp only [if_neg selected, zero_mul]

/-- Actual native feedback and measured/reset recursion have precisely the source row matrix. -/
lemma window_feedbackKraus_eq_source (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (original : Store ctx) (outcome : Bits active) :
    outcomeKraus environment Reference active ports outcome *
        Feedback.wordOperator ports environment Reference original (List.finRange active) =
      sourceWindowKraus ports Reference original outcome := by
  ext row column
  exact window_feedbackKraus_source_entry ports environment Reference original outcome row column

/-- Exact full original-Store source instrument of the actual complete inverse-Fourier window. -/
lemma window_inverseCode_source_store_matrix (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((inverseCode ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Bits active,
        if outcomeStore active ports original outcome = stored then
          sourceWindowKraus ports Reference original outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (sourceWindowKraus ports Reference original outcome).conjTranspose
        else 0 := by
  rw [Feedback.inverseCode_instrument_store_matrix]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : outcomeStore active ports original outcome = stored
  · simp only [if_pos written]
    rw [window_feedbackKraus_eq_source]
  · simp only [if_neg written]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
