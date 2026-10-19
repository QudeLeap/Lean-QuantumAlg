/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Model
import all QuantumAlg.Core.Execution.Context.Permutation.References
import all QuantumAlg.Core.Execution.Context.Permutation.State
import all QuantumAlg.Core.Execution.Context.Union.Measurement
import all QuantumAlg.Core.Execution.State.Coordinate.Measurement
import all QuantumAlg.Core.Execution.Interpret

/-!
# Actual Z outcomes and writes under entry permutation

The actual measured wire keeps its dimension and numerical result. Its write
targets the same finite cell. The complete conditional state equality retains
every measurement outcome, classical fiber and external-reference coordinate.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

variable {allowAllocation : Bool}

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {source target : RuntimeCtx .quantum}
  (same : source.entries.Perm target.entries) (wire : Fin source.systemCount)

/-- Identify the finite outcomes by equality of the original physical wire's dimension. -/
def measurementOutcome : Fin (source.quantumLayout.wire wire).dimension ≃
    Fin (target.quantumLayout.wire (positions same wire)).dimension :=
  finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
    (congrArg QuantumWire.dimension (positions_wire same wire)).symm)

/-- Reading the corresponding wire gives the identical numerical observation. -/
lemma measurement_read (value : source.register.Index) :
    measurementOutcome same wire (value wire) = basis same value (positions same wire) := by
  apply Fin.ext
  exact (basis_value same value wire).symm

/-- Writing the observed value commutes with the complete actual store correspondence. -/
lemma measurement_write (original : Store source)
    (output : CWriteRef source (.finite (source.quantumLayout.wire wire).dimension))
    (outcome : Fin (source.quantumLayout.wire wire).dimension) :
    store same (original.write output (.finite outcome)) =
      (store same original).write (measurement same wire output)
        (.finite (measurementOutcome same wire outcome)) :=
  (store_write same original output (.finite outcome)).trans
    (write_finite_transport (store same original)
      (congrArg QuantumWire.dimension (positions_wire same wire)).symm
      (writable same output) outcome).symm

/-- The existing interpreter preserves the full conditional state and actual written outcome. -/
private lemma state_measureZ_raw {Reference : Register} {H : Type} [Fintype H]
    (original : State source Reference H)
    (output : CWriteRef source (.finite (source.quantumLayout.wire wire).dimension)) :
    (state same (original.measureZ wire output)).mapHistory
        (fun record => (record.1, measurementOutcome same wire record.2)) =
      (state same original).measureZ (positions same wire) (measurement same wire output) := by
  let outcomes := measurementOutcome same wire
  let labels := recordEquiv same H
  let coordinates := referenceBasis same Reference
  let sourceRead := fun value : (Register.prod source.register Reference).Index => value.1 wire
  let targetRead := fun value : (Register.prod target.register Reference).Index =>
    value.1 (positions same wire)
  have reads : ∀ value, outcomes (sourceRead value) = targetRead (coordinates value) := by
    intro value
    exact measurement_read same wire value.1
  have measured := ExecutionState.coordinate_measureZ original coordinates labels outcomes
    sourceRead targetRead reads
  let targetWrite := fun value : (Store target × H) ×
      Fin (target.quantumLayout.wire (positions same wire)).dimension =>
    (value.1.1.write (measurement same wire output) (.finite value.2), (value.1.2, value.2))
  let finalLabels := (storeEquiv same).prodCongr ((Equiv.refl H).prodCongr outcomes)
  have diagram : ∀ value : (Store source × H) ×
      Fin (source.quantumLayout.wire wire).dimension,
      finalLabels (value.1.1.write output (.finite value.2), (value.1.2, value.2)) =
        targetWrite ((labels.prodCongr outcomes) value) := by
    intro value
    exact Prod.ext (measurement_write same wire value.1.1 output value.2) rfl
  have writes := ExecutionState.coordinate_transport_diagram
    (ExecutionState.measureZ original sourceRead) coordinates (labels.prodCongr outcomes)
    finalLabels (fun value => (value.1.1.write output (.finite value.2), (value.1.2, value.2)))
    targetWrite diagram
  have steps := congrArg (fun value => value.mapClassical targetWrite) measured
  have result := writes.trans steps
  have histories := ExecutionState.executionState_mapClassical_comp
    (original.measureZ wire output)
    (fun value => (value.1, (value.2.1, outcomes value.2.2)))
    (recordEquiv same
      (H × Fin (target.quantumLayout.wire (positions same wire)).dimension))
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

/-- The actual modeled measurement retains its service label and corresponding Z outcome. -/
lemma state_measureZ {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State source Reference (services.HiddenState × H))
    (output : CWriteRef source (.finite (source.quantumLayout.wire wire).dimension)) :
    (state same ((Circuit.measureZ
        (allowAllocation := allowAllocation)
        (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) wire output).execute
        environment Reference original)).mapHistory (fun record =>
          (record.1, (record.2.1, measurementOutcome same wire record.2.2))) =
      (Circuit.measureZ
          (allowAllocation := allowAllocation)
          (gates := gates) (oracles := oracles) (operations := operations)
        (classicalOracles := services) (positions same wire) (measurement same wire output)).execute
          environment Reference (state same original) := by
  have measured := congrArg
    (fun value : State target Reference ((services.HiddenState × H) ×
        Fin (target.quantumLayout.wire (positions same wire)).dimension) =>
      value.mapHistory (fun record => (record.1.1, (record.1.2, record.2))))
    (state_measureZ_raw same wire original output)
  dsimp only [Circuit.execute, interpret, preserveService]
  erw [state_mapHistory]
  simp only [State.mapHistory_comp, Function.comp_def] at measured ⊢
  erw [measured]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Execution.ContextPermutation
