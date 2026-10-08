/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Selected
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Classical.Native

/-!
# Physical phase measurement and paid bit packing

The declared observation measures the original phase wires, retains every
unmeasured matrix coordinate, and records the actual finite measurement path.
Its packing operation performs the declared deterministic store update while
preserving the classical service state and complete prior history.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev measurementCode (base : RuntimeCtx .quantum)
    (N : Nat) (input : Input N) (sameWires : base.quantumWires = (layout N).wires) :
    Circuit (executionModel input) (Storage.context base N)
      (Storage.context base N) :=
  Circuit.measurementSequence (readouts base N sameWires)

/-- The physical path produced by the declared phase readouts on one basis label. -/
abbrev basisPath (base : RuntimeCtx .quantum)
    (N : Nat) (input : Input N) (sameWires : base.quantumWires = (layout N).wires)
    (basis : (Storage.context base N).register.Index) :
    (measurementCode base N input sameWires).Path :=
  Circuit.measurementBasisPath
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    (readouts base N sameWires) basis

/-- The complete store after actual phase-cell writes on one basis label. -/
abbrev measuredStore (base : RuntimeCtx .quantum)
    (N : Nat) (input : Input N) (sameWires : base.quantumWires = (layout N).wires)
    (store : Store (Storage.context base N))
    (basis : (Storage.context base N).register.Index) :
    Store (Storage.context base N) :=
  Circuit.writeMeasurementPath
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    (readouts base N sameWires) store (basisPath base N input sameWires basis)

/-- Actual phase measurements suppress only matrix entries with unequal
measured labels; the store, reference, and history remain in the weight. -/
theorem readouts_weighted_entry (base : RuntimeCtx .quantum)
    (N : Nat) (input : Input N) (sameWires : base.quantumWires = (layout N).wires)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel input).HiddenState × History))
    (weight : Store (Storage.context base N) ×
      ((executionModel input).HiddenState ×
        (History × (measurementCode base N input sameWires).Path)) → ℂ)
    (left right : (Storage.context base N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      ((measurementCode base N input sameWires).execute Reference state)
      weight (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree (readouts base N sameWires) left right then
        ExecutionState.weightedMatrixEntry state
          (fun entry => weight
            (measuredStore base N input sameWires entry.1 left,
              (entry.2.1, (entry.2.2,
                basisPath base N input sameWires left))))
          (left, leftRef) (right, rightRef)
      else 0 := by
  exact Circuit.measurementSequence_weightedMatrixEntry
    (readouts base N sameWires) state weight left right leftRef rightRef

/-- The declared paid packing instruction executes its original deterministic
store update and records the packed word after the prior history. -/
theorem packing_execute (base : RuntimeCtx .quantum)
    (N : Nat) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel input).HiddenState × History)) :
    (Circuit.classical (model := executionModel input)
      (BitWord.application (packing base N))).execute Reference state =
        state.mapClassical (fun entry =>
          let result := (packing base N).eval
            (entry.1.read (BitWord.application (packing base N)).input)
          (entry.1.write (BitWord.application (packing base N)).output result,
            (entry.2.1, (entry.2.2, result)))) := by
  exact Circuit.execute_classical_mapClassical (model := executionModel input)
    (BitWord.application (packing base N))
    (packing base N).eval
    (BitWord.bitWord_application_evaluate (packing base N))
    Reference state

/-- The complete selected, measured, and packed body retains each original
reference matrix entry and its hidden state and history. -/
theorem body_weighted_entry (base : RuntimeCtx .quantum)
    (N : Nat) (input : Input N) (sameWires : base.quantumWires = (layout N).wires)
    (parameter : CInputRef base (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel input).HiddenState × History))
    (weight : Store (Storage.context base N) ×
      ((executionModel input).HiddenState ×
        (History × (body base N input sameWires parameter).Path)) → ℂ)
    (left right : (Storage.context base N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      ((body base N input sameWires parameter).execute Reference state)
      weight (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree (readouts base N sameWires) left right then
        ExecutionState.weightedMatrixEntry
          ((selected base N input sameWires parameter).execute Reference state)
          (fun entry =>
            let measured := measuredStore base N input sameWires entry.1 left
            let packed := (packing base N).eval
              (measured.read (packing base N).inputRef)
            weight
              (measured.applyOp (packing base N),
                (entry.2.1, (entry.2.2.1,
                  (entry.2.2.2, (basisPath base N input sameWires left, packed))))))
          (left, leftRef) (right, rightRef)
      else 0 := by
  dsimp +instances only [body] at weight ⊢
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical]
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical]
  rw [packing_execute base N input]
  simp only [ExecutionState.weightedMatrixEntry_mapClassical]
  exact readouts_weighted_entry base N input sameWires
    ((selected base N input sameWires parameter).execute Reference state)
    _ left right leftRef rightRef

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
