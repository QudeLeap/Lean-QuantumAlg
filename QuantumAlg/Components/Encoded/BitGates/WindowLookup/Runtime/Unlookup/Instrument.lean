/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Branch
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Matrix
import all QuantumAlg.Core.Execution.Instrument.Execution

/-!
# Complete actual runtime-array measurement-unlookup instrument

The original physical word reset and existing unary-restoration tail compose through
their actual interpreter equations. Every original Store, hidden state and
history remains in its true output fiber. The feedback operator reads the
real measured-and-packed Store, with arbitrary external reference matrices.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution
open scoped BigOperators

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (output : Fin resultWidth → CWriteRef ctx (.finite 2))
  (mask : CWriteRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (temporary : CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

/-- The same actual word-reset record, before retaining old hidden state and history. -/
def resetRecord (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path) :
    Store ctx × (measuredResetWordCircuit (oracles := .empty) (services := services)
      physical sameWires frame.result frame.resultDistinct output mask).Path :=
  let measured := Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts physical sameWires frame.result output) store path
  let packed := MaskParity.instructionStep (oracles := .empty) (services := services)
    (resultPackOp output mask) measured
  (packed.1, ((), (path, (packed.2, ⟨packed.1.read (.storage mask.toCStorageRef), ()⟩))))

/-- Every outcome retains its actual reset path and subsequent paid-restoration path. -/
def record (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path) :
    Store ctx × (circuit frame (services := services)
      physical sameWires output mask parity temporary table).Path :=
  let first := resetRecord frame (services := services) physical sameWires output mask store path
  let last := restorationRecord frame (services := services)
    physical sameWires (.storage mask.toCStorageRef) parity temporary table first.1
  (last.1, (first.2, last.2))

private lemma reset_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result :
    (((measuredResetWordCircuit physical sameWires frame.result
      frame.resultDistinct output mask).execute
      environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if Execution.Instrument.retainedRecord (resetRecord frame (services := services)
            physical sameWires output mask) original path = result then
          measuredWordKraus physical sameWires frame.result frame.resultDistinct output mask
              original.1 path environment.quantum Reference * (state.block original).matrix *
            (measuredWordKraus physical sameWires frame.result frame.resultDistinct output mask
              original.1 path environment.quantum Reference).conjTranspose
        else 0 := by
  ext row column
  have actual := measuredResetWordCircuit_block_matrix physical sameWires frame.result
    frame.resultDistinct output mask environment state result row column
  refine actual.trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  rfl

private lemma restoration_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result :
    (((restorationCircuit frame physical sameWires
      (.storage mask.toCStorageRef) parity temporary table).execute
      environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ _outcome : Unit,
        if Execution.Instrument.retainedRecord (fun store (_ : Unit) => restorationRecord frame
            (services := services) physical sameWires (.storage mask.toCStorageRef)
            parity temporary table store) original () = result then
          (UnitaryOperator.prodTensor
            (restorationOperator frame (services := services) physical sameWires
              (.storage mask.toCStorageRef) parity temporary table environment.quantum original.1)
            (1 : UnitaryOperator Reference) : HilbertOperator
              (Register.prod ctx.register Reference)) * (state.block original).matrix *
            (UnitaryOperator.prodTensor
              (restorationOperator frame (services := services) physical sameWires
                (.storage mask.toCStorageRef) parity temporary table environment.quantum original.1)
              (1 : UnitaryOperator Reference) : HilbertOperator
                (Register.prod ctx.register Reference)).conjTranspose
        else 0 := by
  rw [restorationCircuit_execute frame physical sameWires (.storage mask.toCStorageRef)
    parity temporary table, ExecutionState.mapClassical_block_matrix]
  simp only [Fintype.sum_unique, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix]
  apply Finset.sum_congr rfl
  intro original _
  rfl

/-- Exact complete output matrices of the original actual allocation-free unlookup circuit. -/
lemma circuit_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (circuit frame physical sameWires output mask parity temporary table).Path))) :
    (((circuit frame physical sameWires output mask parity temporary table).execute
      environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if Execution.Instrument.retainedRecord (record frame (services := services)
            physical sameWires output mask parity temporary table) original path = result then
          branchOperator frame physical sameWires output mask parity temporary table original.1 path
              environment.quantum Reference * (state.block original).matrix *
            (branchOperator frame physical sameWires output mask parity temporary table
              original.1 path
              environment.quantum Reference).conjTranspose
        else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (measuredResetWordCircuit physical sameWires frame.result frame.resultDistinct output mask)
    (restorationCircuit frame physical sameWires (.storage mask.toCStorageRef)
      parity temporary table)
    (resetRecord frame physical sameWires output mask)
    (fun store (_ : Unit) => restorationRecord frame physical sameWires
      (.storage mask.toCStorageRef) parity temporary table store)
    (fun reference store path => measuredWordKraus physical sameWires frame.result
      frame.resultDistinct output mask store path environment.quantum reference)
    (fun reference store (_ : Unit) => (UnitaryOperator.prodTensor
      (restorationOperator frame (services := services) physical sameWires
        (.storage mask.toCStorageRef) parity temporary table environment.quantum store)
      (1 : UnitaryOperator reference) :
          HilbertOperator (Register.prod ctx.register reference)))
    environment (reset_block_matrix frame physical sameWires output mask environment)
    (restoration_block_matrix frame physical sameWires mask parity temporary table environment)
    Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  rfl

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
