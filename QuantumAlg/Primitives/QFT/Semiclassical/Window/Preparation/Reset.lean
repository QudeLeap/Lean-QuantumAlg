/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Recorded

/-!
# A genuinely reset zero wire has one deterministic actual record

The real MZ and same-cell native correction preserve every quantum and
external-reference density entry on the zero-wire subspace. The output
Store write and chronological measurement Path remain explicit. This is
the zero-input law of the executed reset, not deletion of its paid events.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators ComplexOrder

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private instance preparationResetDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- Full-record identity of the actual paid MZ/correction on its original zero subspace. -/
lemma window_preparation_reset_zero_record
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry left right (refLeft refRight : Reference.Index), left wire ≠ 0 →
      (state.block entry).matrix (left, refLeft) (right, refRight) = 0) :
    (QuditShift.resetCircuit wire output realizations operations services false).execute
        environment Reference state =
      state.mapClassical (fun entry => QuditShift.Recorded.record
        (operations := operations) wire output realizations entry 0) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  ext ⟨left, refLeft⟩ ⟨right, refRight⟩
  rw [QuditShift.Recorded.block_entry, ExecutionState.mapClassical_block_matrix,
    Matrix.sum_apply]
  simp only [Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_congr rfl
  intro entry _
  calc
    _ = if QuditShift.Recorded.record (operations := operations)
            wire output realizations entry 0 = result then
          if left wire = 0 ∧ right wire = 0 then
            (state.block entry).matrix (Function.update left wire 0, refLeft)
              (Function.update right wire 0, refRight) else 0
        else 0 := by
      apply Finset.sum_eq_single 0
      · intro outcome _ nonzero
        by_cases written : QuditShift.Recorded.record (operations := operations)
            wire output realizations entry outcome = result
        · rw [if_pos written]
          split_ifs
          · exact supported entry _ _ _ _ (by
              simpa only [Function.update_self] using nonzero)
          · rfl
        · rw [if_neg written]
      · simp
    _ = _ := by
      by_cases written : QuditShift.Recorded.record (operations := operations)
          wire output realizations entry 0 = result
      · rw [if_pos written, if_pos written]
        by_cases leftZero : left wire = 0
        · by_cases rightZero : right wire = 0
          · rw [if_pos ⟨leftZero, rightZero⟩]
            have sameLeft : Function.update left wire 0 = left := by
              rw [← leftZero, Function.update_eq_self]
            have sameRight : Function.update right wire 0 = right := by
              rw [← rightZero, Function.update_eq_self]
            rw [sameLeft, sameRight]
          · rw [if_neg (fun pair => rightZero pair.2)]
            have zero := supported entry right left refRight refLeft rightZero
            rw [← (state.block entry).positive.isHermitian.apply
              (left, refLeft) (right, refRight), zero, star_zero]
        · rw [if_neg (fun pair => leftZero pair.1),
            supported entry left right refLeft refRight leftZero]
      · rw [if_neg written, if_neg written]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
