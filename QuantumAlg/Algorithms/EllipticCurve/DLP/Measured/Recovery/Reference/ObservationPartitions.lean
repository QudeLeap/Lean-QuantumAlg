/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Effect
import all QuantumAlg.Core.Execution.State.Effect
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Classical.Branch

/-!
# Complete finite record partitions for event weights

These identities concern finite execution states and their exact classical
fibers. They do not introduce an algorithm or depend on a readout compiler.
The density matrices may retain arbitrary external Reference entries and
arbitrary subnormalized mass, including zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ObservationPartitions

noncomputable section
open QuantumAlg QuantumAlg.Execution
open scoped BigOperators
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

lemma fiber_partition_effectWeight {Records Stores Frames : Type}
    [Fintype Records] [Fintype Stores] [Fintype Frames] {Reference : Register}
    (state : ExecutionState Records Reference) (stored : Records → Stores)
    (frame : Records → Frames) (predicate : Records → Prop) (event : Stores × Frames → Prop) :
    state.effectWeight (fun record =>
      if predicate record ∧ event (stored record, frame record) then
        Effect.one Reference else Effect.zero Reference) =
      ∑ final, ∑ frameFinal, if event (final, frameFinal) then
        (state.filterClassical (fun record => stored record = final ∧
          (predicate record ∧ frame record = frameFinal))).quantumMarginal.mass else 0 := by
  let selected := state.filterClassical predicate
  let grouped := selected.mapClassical (fun record => (stored record, frame record))
  have fiber (final : Stores) (frameFinal : Frames) :
      (grouped.block (final, frameFinal)).mass =
        (state.filterClassical (fun record => stored record = final ∧
          (predicate record ∧ frame record = frameFinal))).quantumMarginal.mass := by
    apply congrArg DensityOperator.mass
    apply DensityOperator.ext
    simp only [grouped, selected, ExecutionState.mapClassical_block_matrix,
      ExecutionState.filterClassical_block, ExecutionState.quantumMarginal,
      apply_ite DensityOperator.matrix, DensityOperator.zero_matrix]
    apply Finset.sum_congr rfl
    intro record _
    by_cases sameStore : stored record = final
    <;> by_cases sameFrame : frame record = frameFinal
    <;> by_cases accepted : predicate record
    <;> simp [sameStore, sameFrame, accepted]
  have grouped_weight :
      grouped.effectWeight (fun value =>
        if event value then Effect.one Reference else Effect.zero Reference) =
      state.effectWeight (fun record =>
        if predicate record ∧ event (stored record, frame record) then
          Effect.one Reference else Effect.zero Reference) := by
    calc
      _ = selected.effectWeight (fun record =>
          if event (stored record, frame record) then
            Effect.one Reference else Effect.zero Reference) :=
        ExecutionState.effectWeight_mapClassical_decision
          (inferInstance : DecidableEq (Stores × Frames)) selected
          (fun record => (stored record, frame record))
          (fun value => if event value then Effect.one Reference else Effect.zero Reference)
      _ = _ := by
        unfold ExecutionState.effectWeight
        apply Finset.sum_congr rfl
        intro record _
        by_cases accepted : predicate record
        <;> by_cases observed : event (stored record, frame record)
        <;> simp [selected, accepted, observed]
  rw [← grouped_weight, ExecutionState.effectWeight, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro final _
  apply Finset.sum_congr rfl
  intro frameFinal _
  by_cases observed : event (final, frameFinal)
  · simp only [if_pos observed, Effect.weight_one, fiber]
  · simp only [if_neg observed, Effect.weight_zero]


end
end ObservationPartitions
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
