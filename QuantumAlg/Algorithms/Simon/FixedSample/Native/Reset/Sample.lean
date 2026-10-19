/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Readout
import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Store
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Complete-state insensitivity to overwritten Simon raw cells

The actual sample overwrites every raw measurement cell before its paid
packing instruction. Equality on the entire old store and joint quantum
bank/reference therefore implies equality on the entire final store and
joint quantum bank/reference. Inputs may have different history types and
arbitrary mixed, entangled states; no zero seed or probability-only premise
is needed for this congruence.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {oracles : OracleModel}
  {environment : (nativeModel oracles).Environment}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- The exact store written by the sample's actual first-register Z sequence. -/
def sampleWritten (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) :
    Store (context base noQuantum n count) :=
  Circuit.writeMeasurementPath (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := BitWord.model) (classicalOracles := .empty)
    (Native.readouts base noQuantum n count) store
    (Circuit.measurementBasisPath (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
      (Native.readouts base noQuantum n count) basis)

/-- The sample's measurement writes leave every original caller and packed-sample cell untouched.
-/
lemma sampleWritten_original (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) :
    originalStore base noQuantum n count
      (sampleWritten (oracles := oracles) base noQuantum n count store basis) =
        originalStore base noQuantum n count store := by
  apply originalStore_writePath
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact ⟨index, Native.readout_key base noQuantum n count index⟩

/-- Complete replacement of the real raw cells removes dependence on all their previous values.
-/
lemma sampleWritten_congr (first second : Store (context base noQuantum n count))
    (same : originalStore base noQuantum n count first =
      originalStore base noQuantum n count second)
    (basis : (context base noQuantum n count).register.Index) :
    sampleWritten (oracles := oracles) base noQuantum n count first basis =
      sampleWritten (oracles := oracles) base noQuantum n count second basis := by
  apply store_ext
  · rw [sampleWritten_original, sampleWritten_original, same]
  · intro index
    apply (ClassicalRegister.finEquiv 2).injective
    apply Fin.ext
    exact (Native.measured_cell (oracles := oracles)
      base noQuantum n count first basis index).trans
      (Native.measured_cell (oracles := oracles)
        base noQuantum n count second basis index).symm

/-- A canonical raw-cell head is only a mathematical representative of the same complete writes.
-/
lemma sampleWritten_canonical (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) :
    sampleWritten (oracles := oracles) base noQuantum n count store basis =
      sampleWritten (oracles := oracles) base noQuantum n count
        (MeasurementCells.pushStore 2 n (originalStore base noQuantum n count store)) basis := by
  apply sampleWritten_congr
  exact (originalStore_push n (originalStore base noQuantum n count store)).symm

/-- History reassociation preserves the complete final-store state. -/
lemma sequence_store {model : ExecutionModel}
    {environment : model.Environment} {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History)) :
    ((first.seq second).execute environment Reference state).mapClassical (fun entry => entry.1) =
      (second.execute environment Reference (first.execute environment
        Reference state)).mapClassical
        (fun entry => entry.1) := by
  rw [Circuit.execute_seq (environment := environment)]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp]
  rfl

/-- The fixed sample unitary commutes with the complete old-store observation. -/
lemma unitary_originalStore (program : UnitaryCircuit AlgorithmGate.model oracles
      (context base noQuantum n count).quantumLayout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History)) :
    ((Circuit.unitary (allowAllocation := true)
      (operations := BitWord.model) (classicalOracles := .empty)
      program).execute environment Reference state).mapClassical
      (fun entry => originalStore base noQuantum n count entry.1) =
      (state.mapClassical (fun entry => originalStore base noQuantum n count entry.1)).applyUnitary
        (fun _ => UnitaryOperator.prodTensor (program.matrix environment.quantum) (1 :
          UnitaryOperator Reference)) := by
  rw [Circuit.execute_unitary (quantumEnvironment := environment)]
  rw [Circuit.mapClassical_comp_any (result := inferInstance),
    ExecutionState.applyUnitary_mapClassical]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every final measured store depends on exactly the complete old-store input block. -/
lemma measurement_entry_originalStore
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (stored : Store (context base noQuantum n count))
    (left right : (context base noQuantum n count).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
      (Native.readouts base noQuantum n count)).execute environment Reference state).mapClassical
      (fun entry => entry.1)).block stored).matrix (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree (Native.readouts base noQuantum n count) left right then
        ExecutionState.weightedMatrixEntry
          (state.mapClassical (fun entry => originalStore base noQuantum n count entry.1))
          (fun original => if sampleWritten (oracles := oracles) base noQuantum n count
            (MeasurementCells.pushStore 2 n original) left = stored then 1 else 0)
          (left, leftRef) (right, rightRef)
      else 0 := by
  rw [BasisSeeded.store_matrix, Circuit.measurementSequence_store_matrix_entry,
    ExecutionState.weightedMatrixEntry_mapClassical]
  change (if Circuit.measurementLabelsAgree (Native.readouts base noQuantum n count) left right
    then ExecutionState.weightedMatrixEntry state
      (fun entry => if sampleWritten (oracles := oracles) base noQuantum n count entry.1 left =
        stored then 1 else 0) (left, leftRef) (right, rightRef) else 0) = _
  simp only [sampleWritten_canonical]

/-- Equality on the old store becomes equality on the whole store after the actual Z writes. -/
lemma measurement_congr_originalStore
    {Reference : Register} {FirstHistory SecondHistory : Type}
    [Fintype FirstHistory] [Fintype SecondHistory]
    (first : State (context base noQuantum n count) Reference (Unit × FirstHistory))
    (second : State (context base noQuantum n count) Reference (Unit × SecondHistory))
    (same : first.mapClassical (fun entry => originalStore base noQuantum n count entry.1) =
      second.mapClassical (fun entry => originalStore base noQuantum n count entry.1)) :
    ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
      (Native.readouts base noQuantum n count)).execute environment Reference first).mapClassical
      (fun entry => entry.1) =
    ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
      (Native.readouts base noQuantum n count)).execute environment Reference second).mapClassical
      (fun entry => entry.1) := by
  apply ExecutionState.ext
  intro stored
  apply DensityOperator.ext
  funext left right
  obtain ⟨left, leftRef⟩ := left
  obtain ⟨right, rightRef⟩ := right
  rw [measurement_entry_originalStore, measurement_entry_originalStore, same]

/-- Paid packing processes the complete measured store without changing any quantum block. -/
lemma packing_store
    {environment : (executionModel n).Environment} (index : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History)) :
    ((BitWord.instruction (execution := executionModel n)
      (packing base noQuantum n count index)).execute environment Reference state).mapClassical
      (fun entry => entry.1) =
      (state.mapClassical (fun entry => entry.1)).mapClassical
        (fun store => store.applyOp (packing base noQuantum n count index)) := by
  rw [BitWord.bitWord_instruction_execute (environment := environment),
    ExecutionState.executionState_mapClassical_comp,
    ExecutionState.executionState_mapClassical_comp]
  rfl

/-- The complete sample restores full-store equivalence despite arbitrary old raw-cell values. -/
lemma sample_congr_originalStore (sampling : SamplingCircuit n)
    {environment : (executionModel n).Environment} (index : Fin count)
    {Reference : Register} {FirstHistory SecondHistory : Type}
    [Fintype FirstHistory] [Fintype SecondHistory]
    (first : State (context base noQuantum n count) Reference (Unit × FirstHistory))
    (second : State (context base noQuantum n count) Reference (Unit × SecondHistory))
    (same : first.mapClassical (fun entry => originalStore base noQuantum n count entry.1) =
      second.mapClassical (fun entry => originalStore base noQuantum n count entry.1)) :
    ((sample base noQuantum n count sampling index).execute environment Reference
      first).mapClassical
      (fun entry => entry.1) =
      ((sample base noQuantum n count sampling index).execute environment Reference
        second).mapClassical
        (fun entry => entry.1) := by
  let unitary := Circuit.unitary (allowAllocation := true)
    (operations := BitWord.model) (classicalOracles := .empty)
    (member n (nativeSimon_context_wires base noQuantum n count) sampling)
  have acted : (unitary.execute environment Reference first).mapClassical
      (fun entry => originalStore base noQuantum n count entry.1) =
      (unitary.execute environment Reference second).mapClassical
        (fun entry => originalStore base noQuantum n count entry.1) := by
    rw [unitary_originalStore, unitary_originalStore, same]
  have measured := measurement_congr_originalStore (environment := environment)
    (oracles := sourceModel n) base noQuantum n count
      (unitary.execute environment Reference first) (unitary.execute environment Reference second)
        acted
  let measurement : Circuit (executionModel n)
      (context base noQuantum n count) (context base noQuantum n count) :=
    Circuit.measurementSequence (Native.readouts base noQuantum n count)
  let pack := BitWord.instruction (execution := executionModel n)
    (packing base noQuantum n count index)
  have complete {H : Type} [Fintype H]
      (state : State (context base noQuantum n count) Reference (Unit × H)) :
      ((sample base noQuantum n count sampling index).execute environment
        Reference state).mapClassical
          (fun entry => entry.1) =
        ((measurement.execute environment Reference (unitary.execute environment
          Reference state)).mapClassical
          (fun entry => entry.1)).mapClassical
            (fun store => store.applyOp (packing base noQuantum n count index)) := by
    exact (sequence_store (environment := environment) unitary (measurement.seq pack) state).trans
      ((sequence_store
        (environment := environment) measurement pack (unitary.execute environment
        Reference state)).trans
        (packing_store (environment := environment) base noQuantum n count index
          (measurement.execute environment Reference (unitary.execute environment
            Reference state))))
  exact (complete first).trans
    ((congrArg (fun state => state.mapClassical
      (fun store => store.applyOp (packing base noQuantum n count index))) measured).trans
      (complete second).symm)

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
