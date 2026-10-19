/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Composition.Parallel.State
import all QuantumAlg.Core.Execution.Context.Embedding.References
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Probability

/-!
# Original relational distributions inside actual parallel execution

The observed distribution retains each child's original local input Store
together with its actual structural output. Both marginals come from one
correlated parallel distribution. No product law or independence is asserted.
-/

namespace QuantumAlg.Algorithm

noncomputable section

open Execution

attribute [local instance] Classical.decEq

section Classical

variable {operations : ClassicalOpModel}
  {leftService rightService parentService : ClassicalOracleModel}
  {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
  {allowAllocation : Bool}
  (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
  (separate : RuntimeCtx.StorageDisjoint left right)
  (first : Algorithm (.classical operations leftService) left left leftShape false)
  (second : Algorithm (.classical operations rightService) right right rightShape false)
  (environment : (ExecutionModel.classical operations parentService).Environment)
  {Reference : Register}
  (input : OracleInput parentService (left.disjointUnion right separate) Reference)

/-- Every original left child distribution is the corresponding actual parallel marginal. -/
lemma parallelClassical_observationDistribution_left {Result : Type} [Finite Result]
    (read : first.run.Record → Result) :
    ((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.executionDistribution environment input).map
        (fun record => read
          (((ContextEmbedding.alongUnion left right separate).store record.1).1,
            ((join.hidden record.2.1).1,
              (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
                record.2.2.2.1)))) =
      (first.run.executionDistribution
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input))).map read := by
  let : Fintype Result := Fintype.ofFinite Result
  let run := (parallelClassical (allowAllocation := allowAllocation)
    join separate first second).run
  let childInput := (ContextEmbedding.alongUnion left right separate).localInput
    (join.leftInput input)
  let readCaller : run.Record → Result := fun record => read
    (((ContextEmbedding.alongUnion left right separate).store record.1).1,
      ((join.hidden record.2.1).1,
        (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
          record.2.2.2.1)))
  apply PMF.ext
  intro result
  have blocks := congrArg (fun current : ExecutionState Result (left.register.prod Reference) =>
    (current.block result).mass)
    (parallelClassical_observe_left (allowAllocation := allowAllocation)
      join separate first second environment input read)
  rw [ExecutionState.forgetReferenceFrame_block_mass,
    ExecutionState.reindex_block_mass] at blocks
  calc
    _ = ENNReal.ofReal
        (((run.execute environment Reference input.state).mapClassical
          readCaller).block result).mass :=
      (congrArg (fun distribution : PMF Result => distribution result)
        (ExecutionState.toPMF_mapClassical (run.execute environment Reference input.state)
          (run.execute_normalized environment input) readCaller)).symm
    _ = ENNReal.ofReal
        (((first.run.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          Reference childInput.state).mapClassical read).block result).mass :=
      congrArg ENNReal.ofReal blocks
    _ = _ := congrArg (fun distribution : PMF Result => distribution result)
      (ExecutionState.toPMF_mapClassical (first.run.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          Reference childInput.state)
        (first.run.execute_normalized
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ childInput) read)

/-- Original left input and actual left result have precisely the original child joint law. -/
lemma parallelClassical_relationalDistribution_left :
    ((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.relationalDistribution environment input).map
        (fun outcome => match outcome.2 with
          | .product result _ =>
              (((ContextEmbedding.alongUnion left right separate).store outcome.1).1, result)) =
      first.run.relationalDistribution
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)) := by
  unfold AlgorithmRun.relationalDistribution
  rw [PMF.map_comp]
  calc
    _ = ((parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.executionDistribution environment input).map
          (fun record =>
            (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
              first.run.output.eval
                ((ContextEmbedding.alongUnion left right separate).store record.1).1)) := by
      apply congrArg (fun read =>
        ((parallelClassical (allowAllocation := allowAllocation)
          join separate first second).run.executionDistribution environment input).map read)
      funext record
      change (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
        ((ContextEmbedding.alongUnion left right separate).outputRead
          first.run.output.result).eval record.1) = _
      apply congrArg (fun result =>
        (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1, result))
      simpa only [Output.eval, Prod.mk.eta, Equiv.symm_apply_apply] using
        (ContextEmbedding.alongUnion left right separate).contextEmbedding_outputRead_eval
          ((ContextEmbedding.alongUnion left right separate).store record.1).1
          ((ContextEmbedding.alongUnion left right separate).store record.1).2
          first.run.output.result
    _ = _ := parallelClassical_observationDistribution_left
      join separate first second environment input
        (fun record => (record.2.2.1, first.run.result record))

/-- Every original right child distribution is the corresponding actual parallel marginal. -/
lemma parallelClassical_observationDistribution_right {Result : Type} [Finite Result]
    (read : second.run.Record → Result) :
    ((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.executionDistribution environment input).map
        (fun record => read
          (((ContextEmbedding.alongUnionRight left right separate).store record.1).1,
            ((join.hidden record.2.1).2,
              (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
                record.2.2.2.2)))) =
      (second.run.executionDistribution
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input))).map read := by
  let : Fintype Result := Fintype.ofFinite Result
  let run := (parallelClassical (allowAllocation := allowAllocation)
    join separate first second).run
  let childInput := (ContextEmbedding.alongUnionRight left right separate).localInput
    (join.rightInput input)
  let readCaller : run.Record → Result := fun record => read
    (((ContextEmbedding.alongUnionRight left right separate).store record.1).1,
      ((join.hidden record.2.1).2,
        (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
          record.2.2.2.2)))
  apply PMF.ext
  intro result
  have blocks := congrArg (fun current : ExecutionState Result (right.register.prod Reference) =>
    (current.block result).mass)
    (parallelClassical_observe_right (allowAllocation := allowAllocation)
      join separate first second environment input read)
  rw [ExecutionState.forgetReferenceFrame_block_mass,
    ExecutionState.reindex_block_mass] at blocks
  calc
    _ = ENNReal.ofReal
        (((run.execute environment Reference input.state).mapClassical
          readCaller).block result).mass :=
      (congrArg (fun distribution : PMF Result => distribution result)
        (ExecutionState.toPMF_mapClassical (run.execute environment Reference input.state)
          (run.execute_normalized environment input) readCaller)).symm
    _ = ENNReal.ofReal
        (((second.run.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
          Reference childInput.state).mapClassical read).block result).mass :=
      congrArg ENNReal.ofReal blocks
    _ = _ := congrArg (fun distribution : PMF Result => distribution result)
      (ExecutionState.toPMF_mapClassical (second.run.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
          Reference childInput.state)
        (second.run.execute_normalized
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ childInput) read)

/-- Original right input and actual right result have precisely the original child joint law. -/
lemma parallelClassical_relationalDistribution_right :
    ((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.relationalDistribution environment input).map
        (fun outcome => match outcome.2 with
          | .product _ result =>
              (((ContextEmbedding.alongUnionRight left right separate).store outcome.1).1,
                result)) =
      second.run.relationalDistribution
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)) := by
  unfold AlgorithmRun.relationalDistribution
  rw [PMF.map_comp]
  calc
    _ = ((parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.executionDistribution environment input).map
          (fun record =>
            (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
              second.run.output.eval
                ((ContextEmbedding.alongUnionRight left right separate).store record.1).1)) := by
      apply congrArg (fun read =>
        ((parallelClassical (allowAllocation := allowAllocation)
          join separate first second).run.executionDistribution environment input).map read)
      funext record
      change (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
        ((ContextEmbedding.alongUnionRight left right separate).outputRead
          second.run.output.result).eval record.1) = _
      apply congrArg (fun result =>
        (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1, result))
      simpa only [Output.eval, Prod.mk.eta, Equiv.symm_apply_apply] using
        (ContextEmbedding.alongUnionRight left right separate).contextEmbedding_outputRead_eval
          ((ContextEmbedding.alongUnionRight left right separate).store record.1).1
          ((ContextEmbedding.alongUnionRight left right separate).store record.1).2
          second.run.output.result
    _ = _ := parallelClassical_observationDistribution_right
      join separate first second environment input
        (fun record => (record.2.2.1, second.run.result record))

end Classical

section Quantum

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {leftService rightService parentService : ClassicalOracleModel}
  {left right : RuntimeCtx .quantum} {leftShape rightShape : CShape}
  {allowAllocation : Bool}
  (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
  (separate : RuntimeCtx.StorageDisjoint left right)
  (first : Algorithm (.quantum gates oracles operations leftService) left left leftShape false)
  (second : Algorithm (.quantum gates oracles operations rightService) right right rightShape false)
  (environment : (ExecutionModel.quantum gates oracles operations parentService).Environment)
  {Reference : Register}
  (input : OracleInput parentService (left.disjointUnion right separate) Reference)

/-- Every original left child distribution is the corresponding actual parallel marginal. -/
lemma parallelQuantum_observationDistribution_left {Result : Type} [Finite Result]
    (read : first.run.Record → Result) :
    ((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.executionDistribution environment input).map
        (fun record => read
          (((ContextEmbedding.alongUnion left right separate).store record.1).1,
            ((join.hidden record.2.1).1,
              (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
                record.2.2.2.1)))) =
      (first.run.executionDistribution
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input))).map read := by
  let : Fintype Result := Fintype.ofFinite Result
  let run := (parallelQuantum (allowAllocation := allowAllocation)
    join separate first second).run
  let childInput := (ContextEmbedding.alongUnion left right separate).localInput
    (join.leftInput input)
  let readCaller : run.Record → Result := fun record => read
    (((ContextEmbedding.alongUnion left right separate).store record.1).1,
      ((join.hidden record.2.1).1,
        (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
          record.2.2.2.1)))
  apply PMF.ext
  intro result
  have blocks := congrArg (fun current : ExecutionState Result (left.register.prod Reference) =>
    (current.block result).mass)
    (parallelQuantum_observe_left (allowAllocation := allowAllocation)
      join separate first second environment input read)
  rw [ExecutionState.forgetReferenceFrame_block_mass,
    ExecutionState.reindex_block_mass] at blocks
  calc
    _ = ENNReal.ofReal
        (((run.execute environment Reference input.state).mapClassical
          readCaller).block result).mass :=
      (congrArg (fun distribution : PMF Result => distribution result)
        (ExecutionState.toPMF_mapClassical (run.execute environment Reference input.state)
          (run.execute_normalized environment input) readCaller)).symm
    _ = ENNReal.ofReal
        (((first.run.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          Reference childInput.state).mapClassical read).block result).mass :=
      congrArg ENNReal.ofReal blocks
    _ = _ := congrArg (fun distribution : PMF Result => distribution result)
      (ExecutionState.toPMF_mapClassical (first.run.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          Reference childInput.state)
        (first.run.execute_normalized
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ childInput) read)

/-- Original left input and actual left result have precisely the original child joint law. -/
lemma parallelQuantum_relationalDistribution_left :
    ((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.relationalDistribution environment input).map
        (fun outcome => match outcome.2 with
          | .product result _ =>
              (((ContextEmbedding.alongUnion left right separate).store outcome.1).1, result)) =
      first.run.relationalDistribution
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)) := by
  unfold AlgorithmRun.relationalDistribution
  rw [PMF.map_comp]
  calc
    _ = ((parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.executionDistribution environment input).map
          (fun record =>
            (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
              first.run.output.eval
                ((ContextEmbedding.alongUnion left right separate).store record.1).1)) := by
      apply congrArg (fun read =>
        ((parallelQuantum (allowAllocation := allowAllocation)
          join separate first second).run.executionDistribution environment input).map read)
      funext record
      change (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
        ((ContextEmbedding.alongUnion left right separate).outputRead
          first.run.output.result).eval record.1) = _
      apply congrArg (fun result =>
        (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1, result))
      simpa only [Output.eval, Prod.mk.eta, Equiv.symm_apply_apply] using
        (ContextEmbedding.alongUnion left right separate).contextEmbedding_outputRead_eval
          ((ContextEmbedding.alongUnion left right separate).store record.1).1
          ((ContextEmbedding.alongUnion left right separate).store record.1).2
          first.run.output.result
    _ = _ := parallelQuantum_observationDistribution_left
      join separate first second environment input
        (fun record => (record.2.2.1, first.run.result record))

/-- Every original right child distribution is the corresponding actual parallel marginal. -/
lemma parallelQuantum_observationDistribution_right {Result : Type} [Finite Result]
    (read : second.run.Record → Result) :
    ((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.executionDistribution environment input).map
        (fun record => read
          (((ContextEmbedding.alongUnionRight left right separate).store record.1).1,
            ((join.hidden record.2.1).2,
              (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
                record.2.2.2.2)))) =
      (second.run.executionDistribution
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input))).map read := by
  let : Fintype Result := Fintype.ofFinite Result
  let run := (parallelQuantum (allowAllocation := allowAllocation)
    join separate first second).run
  let childInput := (ContextEmbedding.alongUnionRight left right separate).localInput
    (join.rightInput input)
  let readCaller : run.Record → Result := fun record => read
    (((ContextEmbedding.alongUnionRight left right separate).store record.1).1,
      ((join.hidden record.2.1).2,
        (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
          record.2.2.2.2)))
  apply PMF.ext
  intro result
  have blocks := congrArg (fun current : ExecutionState Result (right.register.prod Reference) =>
    (current.block result).mass)
    (parallelQuantum_observe_right (allowAllocation := allowAllocation)
      join separate first second environment input read)
  rw [ExecutionState.forgetReferenceFrame_block_mass,
    ExecutionState.reindex_block_mass] at blocks
  calc
    _ = ENNReal.ofReal
        (((run.execute environment Reference input.state).mapClassical
          readCaller).block result).mass :=
      (congrArg (fun distribution : PMF Result => distribution result)
        (ExecutionState.toPMF_mapClassical (run.execute environment Reference input.state)
          (run.execute_normalized environment input) readCaller)).symm
    _ = ENNReal.ofReal
        (((second.run.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
          Reference childInput.state).mapClassical read).block result).mass :=
      congrArg ENNReal.ofReal blocks
    _ = _ := congrArg (fun distribution : PMF Result => distribution result)
      (ExecutionState.toPMF_mapClassical (second.run.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
          Reference childInput.state)
        (second.run.execute_normalized
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ childInput) read)

/-- Original right input and actual right result have precisely the original child joint law. -/
lemma parallelQuantum_relationalDistribution_right :
    ((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.relationalDistribution environment input).map
        (fun outcome => match outcome.2 with
          | .product _ result =>
              (((ContextEmbedding.alongUnionRight left right separate).store outcome.1).1,
                result)) =
      second.run.relationalDistribution
        ⟨environment.quantum, join.interpretationRight environment.classical⟩
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)) := by
  unfold AlgorithmRun.relationalDistribution
  rw [PMF.map_comp]
  calc
    _ = ((parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.executionDistribution environment input).map
          (fun record =>
            (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
              second.run.output.eval
                ((ContextEmbedding.alongUnionRight left right separate).store record.1).1)) := by
      apply congrArg (fun read =>
        ((parallelQuantum (allowAllocation := allowAllocation)
          join separate first second).run.executionDistribution environment input).map read)
      funext record
      change (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
        ((ContextEmbedding.alongUnionRight left right separate).outputRead
          second.run.output.result).eval record.1) = _
      apply congrArg (fun result =>
        (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1, result))
      simpa only [Output.eval, Prod.mk.eta, Equiv.symm_apply_apply] using
        (ContextEmbedding.alongUnionRight left right separate).contextEmbedding_outputRead_eval
          ((ContextEmbedding.alongUnionRight left right separate).store record.1).1
          ((ContextEmbedding.alongUnionRight left right separate).store record.1).2
          second.run.output.result
    _ = _ := parallelQuantum_observationDistribution_right
      join separate first second environment input
        (fun record => (record.2.2.1, second.run.result record))

end Quantum

end

end QuantumAlg.Algorithm

