/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Selected
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Classical.Native

/-!
# Physical exponent measurement and paid bit packing

The declared observation measures the original exponent wires, retains every
unmeasured matrix coordinate, and records the actual finite measurement path.
Its packing operation performs the declared deterministic store update while
preserving the classical service state and complete prior history.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev measurementCode (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) :
    Circuit (model N) (Native.context base noQuantum N)
      (Native.context base noQuantum N) :=
  Circuit.measurementSequence (readouts base noQuantum N)

/-- The physical path produced by the declared exponent readouts on one basis label. -/
abbrev basisPath (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat)
    (basis : (Native.context base noQuantum N).register.Index) :
    (measurementCode base noQuantum N).Path :=
  Circuit.measurementBasisPath
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    (readouts base noQuantum N) basis

/-- The complete store after actual exponent-cell writes on one basis label. -/
abbrev measuredStore (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat)
    (store : Store (Native.context base noQuantum N))
    (basis : (Native.context base noQuantum N).register.Index) :
    Store (Native.context base noQuantum N) :=
  Circuit.writeMeasurementPath
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (operations := BitWord.model)
    (classicalOracles := ClassicalOracleModel.empty)
    (readouts base noQuantum N) store (basisPath base noQuantum N basis)

/-- Actual exponent measurements suppress only matrix entries with unequal
measured labels; the store, reference, and history remain in the weight. -/
lemma readouts_weighted_entry (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat)
    {environment : (model N).Environment}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : Store (Native.context base noQuantum N) ×
      ((model N).HiddenState ×
        (History × (measurementCode base noQuantum N).Path)) → ℂ)
    (left right : (Native.context base noQuantum N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      ((measurementCode base noQuantum N).execute environment Reference state)
      weight (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree (readouts base noQuantum N) left right then
        ExecutionState.weightedMatrixEntry state
          (fun entry => weight
            (measuredStore base noQuantum N entry.1 left,
              (entry.2.1, (entry.2.2,
                basisPath base noQuantum N left))))
          (left, leftRef) (right, rightRef)
      else 0 := by
  exact Circuit.measurementSequence_weightedMatrixEntry
    (readouts base noQuantum N) environment state weight left right leftRef rightRef

/-- The declared paid packing instruction executes its original deterministic
store update and records the packed word after the prior history. -/
lemma packing_execute (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat)
    {environment : (model N).Environment}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History)) :
    (Circuit.classical (allowAllocation := true) (model := model N)
      (BitWord.application (packing base noQuantum N))).execute environment Reference state =
        state.mapClassical (fun entry =>
          let result := (packing base noQuantum N).eval
            (entry.1.read (BitWord.application (packing base noQuantum N)).input)
          (entry.1.write (BitWord.application (packing base noQuantum N)).output result,
            (entry.2.1, (entry.2.2, result)))) := by
  exact Circuit.execute_classical_mapClassical (model := model N)
    environment
    (BitWord.application (packing base noQuantum N))
    (packing base noQuantum N).eval
    (BitWord.bitWord_application_evaluate (packing base noQuantum N))
    Reference state

/-- The complete selected, measured, and packed body retains each original
reference matrix entry and its hidden state and history. -/
lemma body_weighted_entry (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat)
    (parameter : CInputRef base (ParameterShape N))
    {environment : (model N).Environment}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : Store (Native.context base noQuantum N) ×
      ((model N).HiddenState ×
        (History × (body base noQuantum N parameter).Path)) → ℂ)
    (left right : (Native.context base noQuantum N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      ((body base noQuantum N parameter).execute environment Reference state)
      weight (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree (readouts base noQuantum N) left right then
        ExecutionState.weightedMatrixEntry
          ((selected base noQuantum N parameter).execute environment Reference state)
          (fun entry =>
            let measured := measuredStore base noQuantum N entry.1 left
            let packed := (packing base noQuantum N).eval
              (measured.read (packing base noQuantum N).inputRef)
            weight
              (measured.applyOp (packing base noQuantum N),
                (entry.2.1, (entry.2.2.1,
                  (entry.2.2.2, (basisPath base noQuantum N left, packed))))))
          (left, leftRef) (right, rightRef)
      else 0 := by
  dsimp +instances only [body] at weight ⊢
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical]
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical]
  rw [packing_execute]
  simp only [ExecutionState.weightedMatrixEntry_mapClassical]
  exact readouts_weighted_entry base noQuantum N
    ((selected base noQuantum N parameter).execute environment Reference state)
    _ left right leftRef rightRef

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
