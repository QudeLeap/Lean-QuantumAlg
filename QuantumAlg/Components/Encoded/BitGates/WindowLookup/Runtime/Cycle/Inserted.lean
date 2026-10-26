/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Coherent
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Instrument

/-!
# Complete actual runtime query with inserted native arithmetic

The original structural table read, native body, measured result reset and
paid same-table feedback retain the complete Store, service state, History
and chronological Path. The equations hold on arbitrary mixed inputs and
external references, without a clean-state or arithmetic-domain premise.
The separate coherent-column theorem discharges clean graph behavior.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

namespace CycleParameters

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {wordWidth lowWidth highRemaining : Nat}
    (parameters : CycleParameters encoding ctx wordWidth lowWidth highRemaining)

private abbrev nativeCircuit
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  .unitary body

private lemma unitRecord_eq {A B C : Type} (initial final : A × (B × C)) :
    (initial.1, (initial.2.1, (initial.2.2, ()))) =
      (final.1, (final.2.1, (final.2.2, ()))) ↔ initial = final := by
  constructor
  · intro same
    exact congrArg (fun entry : A × (B × (C × Unit)) =>
      (entry.1, (entry.2.1, entry.2.2.1))) same
  · rintro rfl
    rfl

/-- Original runtime load, actual native arithmetic, then actual same-table paid unlookup. -/
def insertedCircuit (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (lookupCircuit (oracles := .empty) parameters.source parameters.lookup
    (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
      parameters.outsideStack)
    parameters.physical parameters.sameWires parameters.height).seq
    ((nativeCircuit (services := services) body).seq
      (RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
        parameters.output parameters.mask parameters.parity parameters.temporary
        (splitInputs parameters.source)))

private def lookupRecord (store : Store ctx) (_ : Unit) :
    Store ctx × (lookupCircuit (oracles := .empty) (services := services)
      parameters.source parameters.lookup
      (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
        parameters.outsideStack)
      parameters.physical parameters.sameWires parameters.height).Path :=
  (store, ⟨store.read parameters.source, ()⟩)

/-- The original table snapshot and every measurement and paid feedback record are retained. -/
def insertedRecord (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts parameters.physical parameters.sameWires
        parameters.frame.result parameters.output)).Path) :
    Store ctx × (parameters.insertedCircuit (services := services) body).Path :=
  let tail := RuntimeUnlookup.record parameters.frame parameters.physical parameters.sameWires
    parameters.output parameters.mask parameters.parity parameters.temporary
    (splitInputs parameters.source) store path
  (tail.1, ((parameters.lookupRecord (services := services) store ()).2, ((), tail.2)))

private lemma lookup_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result :
    (((lookupCircuit (oracles := .empty) parameters.source parameters.lookup
      (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
        parameters.outsideStack)
      parameters.physical parameters.sameWires parameters.height).execute
      environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ _outcome : Unit,
        if Execution.Instrument.retainedRecord (parameters.lookupRecord (services := services))
          original () = result then
          (UnitaryOperator.prodTensor
            ((parameters.observedLoader original.1).matrix environment.quantum)
            (1 : UnitaryOperator Reference) : HilbertOperator
              (Register.prod ctx.register Reference)) * (state.block original).matrix *
            (UnitaryOperator.prodTensor
              ((parameters.observedLoader original.1).matrix environment.quantum)
              (1 : UnitaryOperator Reference) : HilbertOperator
                (Register.prod ctx.register Reference)).conjTranspose
        else 0 := by
  rw [lookupCircuit_execute, ExecutionState.mapClassical_block_matrix]
  simp only [Fintype.sum_unique, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix]
  apply Finset.sum_congr rfl
  intro original _
  rfl

private lemma native_block_matrix
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × Unit))) :
    (((nativeCircuit (services := services) body).execute environment Reference state).block
        result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ _outcome : Unit,
        if Execution.Instrument.retainedRecord (Path := Unit) (fun store (_ : Unit) => (store, ()))
            original () = result then
          (UnitaryOperator.prodTensor (body.matrix environment.quantum)
            (1 : UnitaryOperator Reference) : HilbertOperator
              (Register.prod ctx.register Reference)) * (state.block original).matrix *
            (UnitaryOperator.prodTensor (body.matrix environment.quantum)
              (1 : UnitaryOperator Reference) : HilbertOperator
                (Register.prod ctx.register Reference)).conjTranspose
        else 0 := by
  rcases result with ⟨store, hidden, history, outcome⟩
  cases outcome
  refine (Circuit.circuit_execute_unitary_block_matrix (allowAllocation := false)
    environment state body store hidden history).trans ?_
  simp only [Fintype.sum_unique, Execution.Instrument.retainedRecord]
  have condition (original : Store ctx × (services.HiddenState × History)) :
      (original.1, (original.2.1, (original.2.2, ()))) =
        (store, (hidden, (history, ()))) ↔ original = (store, (hidden, history)) :=
    unitRecord_eq original (store, (hidden, history))
  simp_rw [condition]
  exact (Fintype.sum_ite_eq' (store, (hidden, history)) (fun original =>
    (UnitaryOperator.prodTensor (body.matrix environment.quantum)
      (1 : UnitaryOperator Reference) : HilbertOperator
        (Register.prod ctx.register Reference)) * (state.block original).matrix *
      (UnitaryOperator.prodTensor (body.matrix environment.quantum)
        (1 : UnitaryOperator Reference) : HilbertOperator
          (Register.prod ctx.register Reference)).conjTranspose)).symm

private lemma tail_block_matrix
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      ((nativeCircuit (services := services) body).seq
        (RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
          parameters.output parameters.mask parameters.parity parameters.temporary
          (splitInputs parameters.source))).Path))) :
    ((((nativeCircuit (services := services) body).seq
      (RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
        parameters.output parameters.mask parameters.parity parameters.temporary
        (splitInputs parameters.source))).execute environment Reference state).block
          result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if Execution.Instrument.retainedRecord
          (fun store path => Execution.Instrument.sequenceRetainedRecord (nativeCircuit (services
            := services) body)
            (RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
              parameters.output parameters.mask parameters.parity parameters.temporary
              (splitInputs parameters.source))
            (fun store (_ : Unit) => (store, ()))
            (RuntimeUnlookup.record parameters.frame parameters.physical parameters.sameWires
              parameters.output parameters.mask parameters.parity parameters.temporary
              (splitInputs parameters.source)) store () path) original path = result then
          (RuntimeUnlookup.branchOperator parameters.frame parameters.physical parameters.sameWires
            parameters.output parameters.mask parameters.parity parameters.temporary
            (splitInputs parameters.source) original.1 path environment.quantum Reference *
            (UnitaryOperator.prodTensor (body.matrix environment.quantum)
              (1 : UnitaryOperator Reference) : HilbertOperator
                (Register.prod ctx.register Reference))) * (state.block original).matrix *
            (RuntimeUnlookup.branchOperator parameters.frame parameters.physical
              parameters.sameWires
              parameters.output parameters.mask parameters.parity parameters.temporary
              (splitInputs parameters.source) original.1 path environment.quantum Reference *
              (UnitaryOperator.prodTensor (body.matrix environment.quantum)
                (1 : UnitaryOperator Reference) : HilbertOperator
                  (Register.prod ctx.register Reference))).conjTranspose
        else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (nativeCircuit (services := services) body)
    (RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
      parameters.output parameters.mask parameters.parity parameters.temporary
      (splitInputs parameters.source))
    (fun store (_ : Unit) => (store, ()))
    (RuntimeUnlookup.record parameters.frame parameters.physical parameters.sameWires
      parameters.output parameters.mask parameters.parity parameters.temporary
      (splitInputs parameters.source))
    (fun reference _ (_ : Unit) =>
      (UnitaryOperator.prodTensor (body.matrix environment.quantum)
        (1 : UnitaryOperator reference) : HilbertOperator
          (Register.prod ctx.register reference)))
    (fun reference store path => RuntimeUnlookup.branchOperator parameters.frame
      parameters.physical parameters.sameWires parameters.output parameters.mask
      parameters.parity parameters.temporary (splitInputs parameters.source) store path
      environment.quantum reference)
    environment (by
      intro reference history historyFinite input output
      rcases output with ⟨store, hidden, oldHistory, outcome⟩
      cases outcome
      have actual := native_block_matrix body environment reference input
        (store, (hidden, (oldHistory, ())))
      simpa only [Fintype.sum_unique, Execution.Instrument.retainedRecord, Prod.mk.injEq,
        and_true] using actual)
    (by
      intro reference history historyFinite input output
      exact RuntimeUnlookup.circuit_block_matrix parameters.frame parameters.physical
        parameters.sameWires parameters.output parameters.mask parameters.parity
        parameters.temporary
        (splitInputs parameters.source) environment reference input output)
    Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_unique, Execution.Instrument.sequenceRetainedRecord,
    Execution.Instrument.retainedRecord]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  split_ifs <;> rfl

/-- Every output block of the actual query has its exact original-record Kraus matrix. -/
lemma insertedCircuit_block_matrix
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (parameters.insertedCircuit (services := services) body).Path))) :
    (((parameters.insertedCircuit body).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if Execution.Instrument.retainedRecord (parameters.insertedRecord (services := services)
          body) original path =
            result then
          parameters.insertedBranchOperator body original.1 path environment.quantum Reference *
            (state.block original).matrix *
            (parameters.insertedBranchOperator body original.1 path
              environment.quantum Reference).conjTranspose
        else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (lookupCircuit (oracles := .empty) parameters.source parameters.lookup
      (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
        parameters.outsideStack)
      parameters.physical parameters.sameWires parameters.height)
    ((nativeCircuit (services := services) body).seq
      (RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
        parameters.output parameters.mask parameters.parity parameters.temporary
        (splitInputs parameters.source)))
    (parameters.lookupRecord (services := services))
    (fun store path => Execution.Instrument.sequenceRetainedRecord (nativeCircuit (services :=
      services) body)
      (RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
        parameters.output parameters.mask parameters.parity parameters.temporary
        (splitInputs parameters.source))
      (fun store (_ : Unit) => (store, ()))
      (RuntimeUnlookup.record parameters.frame parameters.physical parameters.sameWires
        parameters.output parameters.mask parameters.parity parameters.temporary
        (splitInputs parameters.source)) store () path)
    (fun reference store (_ : Unit) =>
      (UnitaryOperator.prodTensor ((parameters.observedLoader store).matrix environment.quantum)
        (1 : UnitaryOperator reference) : HilbertOperator
          (Register.prod ctx.register reference)))
    (fun reference store path => RuntimeUnlookup.branchOperator parameters.frame
      parameters.physical parameters.sameWires parameters.output parameters.mask
      parameters.parity parameters.temporary (splitInputs parameters.source) store path
      environment.quantum reference *
        (UnitaryOperator.prodTensor (body.matrix environment.quantum)
          (1 : UnitaryOperator reference) : HilbertOperator
            (Register.prod ctx.register reference)))
    environment (parameters.lookup_block_matrix environment)
    (by
      intro reference history historyFinite input output
      have tail := parameters.tail_block_matrix body environment reference input output
      simpa only [Fintype.sum_unique] using tail)
    Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  rfl

end CycleParameters

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
