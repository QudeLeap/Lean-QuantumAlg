/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Measurement.Effect
import all QuantumAlg.Core.Execution.Classical.MapLaws

/-!
# Full retained blocks of actual sequential Z measurements

The complete measured path is the readout of the same actual named wires.
The existing sequential interpreter equals its joint retained projector
instrument followed by the actual chronological Store writes. Every original
Store/history fiber is retained, including overwrite collisions and all
off-diagonal entries of arbitrary unmeasured and external reference systems.
-/

namespace QuantumAlg

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

namespace ExecutionState

/-- Selecting one complete classical record recovers its entire retained density block. -/
lemma weightedMatrixEntry_record {C : Type} [Fintype C] [DecidableEq C] {R : Register}
    (state : ExecutionState C R) (result : C) (row column : R.Index) :
    weightedMatrixEntry state (fun entry => if entry = result then 1 else 0) row column =
      (state.block result).matrix row column := by
  simp only [weightedMatrixEntry, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

end ExecutionState

namespace Circuit

open Execution
open scoped BigOperators

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {ctx : RuntimeCtx .quantum} {allowAllocation : Bool}

/-- The actual chronological measurement writes retain the incoming hidden state and history. -/
def measurementRecord (readouts : List (ZReadout ctx)) {History : Type}
    (entry : Store ctx × (services.HiddenState × History))
    (path : (measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (allowAllocation := allowAllocation) readouts).Path) :
    Store ctx × (services.HiddenState × (History ×
      (measurementSequence (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (allowAllocation := allowAllocation) readouts).Path)) :=
  (writeMeasurementPath readouts entry.1 path, (entry.2.1, (entry.2.2, path)))

/-- The actual outcome tuple agrees exactly when every named measured coordinate agrees. -/
lemma measurementBasisPath_eq_iff (readouts : List (ZReadout ctx))
    (left right : ctx.register.Index) :
    measurementBasisPath (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := services) (allowAllocation := allowAllocation) readouts left =
      measurementBasisPath (gates := gates) (oracles := oracles) (operations := operations)
        (classicalOracles := services) (allowAllocation := allowAllocation) readouts right ↔
      measurementLabelsAgree readouts left right := by
  induction readouts with
  | nil => exact iff_true_intro rfl
  | cons head tail ih =>
      change (((left head.wire, measurementBasisPath (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (allowAllocation := allowAllocation) tail left) :
        Fin (ctx.quantumLayout.wire head.wire).dimension ×
          (measurementSequence (gates := gates) (oracles := oracles) (operations := operations)
            (classicalOracles := services) (allowAllocation := allowAllocation) tail).Path) =
        (right head.wire, measurementBasisPath (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := services)
          (allowAllocation := allowAllocation) tail right)) ↔
        left head.wire = right head.wire ∧ measurementLabelsAgree tail left right
      rw [Prod.mk.injEq, ih]

/-- Exact joint retained instrument of the same actual sequential measurement circuit. -/
lemma measurementSequence_execute_joint (readouts : List (ZReadout ctx))
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (measurementSequence (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := services) (allowAllocation := allowAllocation) readouts).execute
        environment Reference state =
      ExecutionState.mapClassical
        (ExecutionState.measureZ state
          (fun basis : (Register.prod ctx.register Reference).Index =>
          measurementBasisPath (gates := gates) (oracles := oracles) (operations := operations)
            (classicalOracles := services) (allowAllocation := allowAllocation) readouts basis.1))
        (fun entry => measurementRecord readouts entry.1 entry.2) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  ext row column
  have actual := measurementSequence_weightedMatrixEntry readouts environment state
    (fun entry => if entry = result then (1 : ℂ) else 0) row.1 column.1 row.2 column.2
  have expected := ExecutionState.weightedMatrixEntry_mapClassical
    (ExecutionState.measureZ state
      (fun basis : (Register.prod ctx.register Reference).Index =>
        measurementBasisPath (gates := gates) (oracles := oracles) (operations := operations)
          (classicalOracles := services) (allowAllocation := allowAllocation) readouts basis.1))
    (fun entry => measurementRecord readouts entry.1 entry.2)
    (fun entry => if entry = result then (1 : ℂ) else 0) row column
  rw [ExecutionState.weightedMatrixEntry_measureZ] at expected
  simp only [ExecutionState.weightedMatrixEntry, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, measurementRecord] at actual expected
  refine actual.trans (Eq.trans ?_ expected.symm)
  by_cases agree : measurementLabelsAgree readouts row.1 column.1
  · have paths := (measurementBasisPath_eq_iff (gates := gates) (oracles := oracles)
      (operations := operations) (services := services) (allowAllocation := allowAllocation)
      readouts row.1 column.1).mpr agree
    simp only [if_pos agree, if_pos paths]
    apply Finset.sum_congr rfl
    intro entry _
    split_ifs <;> simp_all
  · have paths : ¬ measurementBasisPath (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (allowAllocation := allowAllocation) readouts row.1 =
      measurementBasisPath (gates := gates) (oracles := oracles) (operations := operations)
        (classicalOracles := services) (allowAllocation := allowAllocation) readouts column.1 :=
      fun same => agree ((measurementBasisPath_eq_iff readouts row.1 column.1).mp same)
    simp only [if_neg agree, if_neg paths]

/-- Joint projector for precisely the path of the same actual measured physical wires. -/
def measurementPathProjector (readouts : List (ZReadout ctx)) (Reference : Register)
    (path : (measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (allowAllocation := allowAllocation) readouts).Path) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  ZMeasurement.projector
    (fun basis : (Register.prod ctx.register Reference).Index =>
      measurementBasisPath (gates := gates) (oracles := oracles) (operations := operations)
        (classicalOracles := services) (allowAllocation := allowAllocation) readouts basis.1) path

/-- Every full output block retains all original Store/history fibers and reference coherences. -/
lemma measurementSequence_block_matrix (readouts : List (ZReadout ctx))
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (measurementSequence (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (allowAllocation := allowAllocation) readouts).Path)))
    (row column : (Register.prod ctx.register Reference).Index) :
    (((measurementSequence (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := services) (allowAllocation := allowAllocation) readouts).execute
        environment Reference state).block result).matrix row column =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if measurementRecord readouts original path = result then
          (measurementPathProjector readouts Reference path * (state.block original).matrix *
            (measurementPathProjector readouts Reference path).conjTranspose) row column
        else 0 := by
  rw [measurementSequence_execute_joint, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Fintype.sum_prod_type,
    ExecutionState.measureZ_block]
  rfl

end Circuit

end

end QuantumAlg
