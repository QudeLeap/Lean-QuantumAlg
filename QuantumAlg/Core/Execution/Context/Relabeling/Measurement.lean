/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.Local
import all QuantumAlg.Core.Execution.Context.Relabeling.State
import all QuantumAlg.Core.Execution.Context.Union.Measurement
import all QuantumAlg.Core.Execution.State.Coordinate.Measurement

/-!
# Actual Z outcomes and writes under injective placement

The actual measured wire keeps its dimension and numerical result. Its write
targets the corresponding finite cell. The complete conditional state equality retains
every measurement outcome, classical fiber and external-reference coordinate.
-/

namespace QuantumAlg.Execution.ContextRelabeling

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (source : RuntimeCtx .quantum)
  (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) (wire : Fin source.systemCount)

/-- Identify the finite outcomes by equality of the original physical wire's dimension. -/
def measurementOutcome : Fin (source.quantumLayout.wire wire).dimension ≃
    Fin ((source.relabel keys physical).quantumLayout.wire
      (positions source keys physical wire)).dimension :=
  finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
    (positions_dimension source keys physical wire).symm)

/-- Reading the corresponding wire gives the identical numerical observation. -/
theorem measurement_read (value : source.register.Index) :
    measurementOutcome source keys physical wire (value wire) =
      basis source keys physical value (positions source keys physical wire) := by
  apply Fin.ext
  exact (basis_value source keys physical value wire).symm

/-- Writing the observed value commutes with the complete actual store correspondence. -/
theorem measurement_write (original : Store source)
    (output : CWriteRef source (.finite (source.quantumLayout.wire wire).dimension))
    (outcome : Fin (source.quantumLayout.wire wire).dimension) :
    storeEquiv keys physical source (original.write output (.finite outcome)) =
      (storeEquiv keys physical source original).write
        (measurement source keys physical wire output)
        (.finite (measurementOutcome source keys physical wire outcome)) :=
  (store_write keys physical original output (.finite outcome)).trans
    (write_finite_transport (storeEquiv keys physical source original)
      (positions_dimension source keys physical wire).symm
      (writable keys physical output) outcome).symm

/-- The existing interpreter preserves the full conditional state and actual written outcome. -/
theorem state_measureZ {Reference : Register} {H : Type} [Fintype H]
    (original : State source Reference H)
    (output : CWriteRef source (.finite (source.quantumLayout.wire wire).dimension)) :
    (state keys physical (original.measureZ wire output)).mapHistory
        (fun record => (record.1, measurementOutcome source keys physical wire record.2)) =
      (state keys physical original).measureZ (positions source keys physical wire)
        (measurement source keys physical wire output) := by
  let outcomes := measurementOutcome source keys physical wire
  let labels := recordEquiv (source := source) keys physical H
  let coordinates := referenceBasis (source := source) keys physical Reference
  let sourceRead := fun value : (Register.prod source.register Reference).Index => value.1 wire
  let targetRead := fun value :
      (Register.prod (source.relabel keys physical).register Reference).Index =>
    value.1 (positions source keys physical wire)
  have reads : ∀ value, outcomes (sourceRead value) = targetRead (coordinates value) := by
    intro value
    exact measurement_read source keys physical wire value.1
  have measured := ExecutionState.coordinate_measureZ original coordinates labels outcomes
    sourceRead targetRead reads
  let targetWrite := fun value : (Store (source.relabel keys physical) × H) ×
      Fin ((source.relabel keys physical).quantumLayout.wire
      (positions source keys physical wire)).dimension =>
    (value.1.1.write (measurement source keys physical wire output) (.finite value.2),
      (value.1.2, value.2))
  let finalLabels := (storeEquiv keys physical source).prodCongr ((Equiv.refl H).prodCongr outcomes)
  have diagram : ∀ value : (Store source × H) ×
      Fin (source.quantumLayout.wire wire).dimension,
      finalLabels (value.1.1.write output (.finite value.2), (value.1.2, value.2)) =
        targetWrite ((labels.prodCongr outcomes) value) := by
    intro value
    exact Prod.ext (measurement_write source keys physical wire value.1.1 output value.2) rfl
  have writes := ExecutionState.coordinate_transport_diagram
    (ExecutionState.measureZ original sourceRead) coordinates (labels.prodCongr outcomes)
    finalLabels (fun value => (value.1.1.write output (.finite value.2), (value.1.2, value.2)))
    targetWrite diagram
  have steps := congrArg (fun value => value.mapClassical targetWrite) measured
  have result := writes.trans steps
  have histories := ExecutionState.executionState_mapClassical_comp
    (original.measureZ wire output)
    (fun value => (value.1, (value.2.1, outcomes value.2.2)))
    (recordEquiv (source := source) keys physical
      (H × Fin ((source.relabel keys physical).quantumLayout.wire
      (positions source keys physical wire)).dimension))
  have fused := congrArg (fun value => value.reindex coordinates) histories
  rw [← state_mapHistory]
  convert fused.trans result using 1 <;>
    dsimp only [state, State.mapHistory, State.measureZ, coordinates,
      finalLabels, recordEquiv, labels, sourceRead,
      targetRead, targetWrite, outcomes, Function.comp_def];
    congr! 2
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  simp only [ExecutionState.mapClassical_block_matrix]
  apply Finset.sum_congr rfl
  intro entry _
  split_ifs <;> rfl

end

end QuantumAlg.Execution.ContextRelabeling
