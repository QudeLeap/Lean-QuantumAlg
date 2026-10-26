/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset
import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Selected.Store

/-!
# The actual reset and same-Store selected native feedback instrument

The supplied feedback consists of real native programs on the same complete
854-system bank. Its stored mask is the actual output of the reset, with
all incoming overwritten Store fibers and chronological paths retained.
This generic composition does not establish an arithmetic feedback promise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Reset.Instrument

noncomputable section

open Execution EncodedBit.WindowLookup
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma ite_decisions {Value : Type} {first second : Prop} (same : first ↔ second)
    (firstDecision : Decidable first) (secondDecision : Decidable second) (yes no : Value) :
    @ite Value first firstDecision yes no = @ite Value second secondDecision yes no := by
  cases firstDecision with
  | isTrue selected =>
    cases secondDecision with
    | isTrue _ => rfl
    | isFalse absent => exact False.elim (absent (same.mp selected))
  | isFalse absent =>
    cases secondDecision with
    | isTrue selected => exact False.elim (absent (same.mpr selected))
    | isFalse _ => rfl

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (tail : Fin (2 ^ 256) → UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)

abbrev Outcome :=
  (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts (QubitLayout.canonical _) sameWires (Window.resultWord port) output)).Path

def feedback : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  .branch (.storage mask.toCStorageRef) fun value => .unitary
    (unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
      (tail (resultConstant value)))

def circuit : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (Reset.circuit port sameWires output mask).seq (feedback sameWires mask tail)

/-- The actual reset writes, packed mask and selected physical-X path. -/
def resetRecord (store : Store ctx) (path : Outcome (services := services) port sameWires output) :
    Store ctx × (Reset.circuit (services := services) port sameWires output mask).Path :=
  let measured := Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts (QubitLayout.canonical _) sameWires (Window.resultWord port) output) store path
  let packed := MaskParity.instructionStep (oracles := .empty) (services := services)
    (resultPackOp output mask) measured
  (packed.1, ((), (path, (packed.2, ⟨packed.1.read (.storage mask.toCStorageRef), ()⟩))))

def feedbackRecord (store : Store ctx) :
    Store ctx × (feedback (services := services) sameWires mask tail).Path :=
  (store, ⟨store.read (.storage mask.toCStorageRef), ()⟩)

/-- The feedback adds its true stored-value path to the same chronological record. -/
def record (store : Store ctx) (path : Outcome (services := services) port sameWires output) :
    Store ctx × (circuit (services := services) port sameWires output mask tail).Path :=
  let first := resetRecord (services := services) port sameWires output mask store path
  (first.1, (first.2, ⟨first.1.read (.storage mask.toCStorageRef), ()⟩))

def feedbackOperator (environment : OracleModel.empty.Interpretation) (store : Store ctx) :
    UnitaryOperator ctx.register :=
  (unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
    (tail (resultConstant (store.read (.storage mask.toCStorageRef))))).matrix environment

/-- The second actual operator reads the first actual output Store. -/
def branchOperator (store : Store ctx)
    (path : Outcome (services := services) port sameWires output)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  (UnitaryOperator.prodTensor
    (feedbackOperator sameWires mask tail environment
      (resetRecord (services := services) port sameWires output mask store path).1)
    (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference)) *
      measuredWordKraus (QubitLayout.canonical _) sameWires (Window.resultWord port)
        (Window.resultWord_distinct port) output mask store path environment Reference

private lemma reset_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result :
    (((Reset.circuit port sameWires output mask).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ path : Outcome port sameWires output,
          if Execution.Instrument.retainedRecord (resetRecord (services := services) port
            sameWires output mask)
              original path = result then
            measuredWordKraus (QubitLayout.canonical _) sameWires (Window.resultWord port)
                (Window.resultWord_distinct port) output mask original.1 path
                environment.quantum Reference * (state.block original).matrix *
              (measuredWordKraus (QubitLayout.canonical _) sameWires (Window.resultWord port)
                (Window.resultWord_distinct port) output mask original.1 path
                environment.quantum Reference).conjTranspose
          else 0 := by
  ext row column
  have actual := Reset.circuit_block_matrix port sameWires output mask environment state result
    row column
  refine actual.trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  simp only [Execution.Instrument.retainedRecord, resetRecord, measuredWordRecord]
  exact ite_decisions Iff.rfl _ _ _ _

private lemma feedback_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result :
    (((feedback sameWires mask tail).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ _outcome : Unit,
        if Execution.Instrument.retainedRecord (fun store (_ : Unit) =>
            feedbackRecord (services := services) sameWires mask tail store)
              original () = result then
          (UnitaryOperator.prodTensor (feedbackOperator sameWires mask tail environment.quantum
            original.1) (1 : UnitaryOperator Reference) :
              HilbertOperator (Register.prod ctx.register Reference)) *
            (state.block original).matrix *
            (UnitaryOperator.prodTensor (feedbackOperator sameWires mask tail environment.quantum
              original.1) (1 : UnitaryOperator Reference) :
                HilbertOperator (Register.prod ctx.register Reference)).conjTranspose
        else 0 := by
  dsimp only [feedback, Circuit.Path] at result
  unfold feedback
  rw [Circuit.selectedUnitary_execute, ExecutionState.mapClassical_block_matrix]
  simp only [Fintype.sum_unique, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix]
  apply Finset.sum_congr rfl
  intro original _
  simp only [Execution.Instrument.retainedRecord, feedbackRecord, feedbackOperator]
  exact ite_decisions Iff.rfl _ _ _ _

/-- Complete off-diagonal blocks of the same actual reset and stored-value native feedback. -/
lemma circuit_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (circuit port sameWires output mask tail).Path))) :
    (((circuit port sameWires output mask tail).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ path : Outcome port sameWires output,
          if Execution.Instrument.retainedRecord (record (services := services) port sameWires
            output mask tail)
              original path = result then
            branchOperator port sameWires output mask tail original.1 path
                environment.quantum Reference * (state.block original).matrix *
              (branchOperator port sameWires output mask tail original.1 path
                environment.quantum Reference).conjTranspose
          else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (Reset.circuit port sameWires output mask) (feedback sameWires mask tail)
    (resetRecord (services := services) port sameWires output mask)
    (fun store (_ : Unit) => feedbackRecord (services := services) sameWires mask tail store)
    (fun reference store path => measuredWordKraus (QubitLayout.canonical _) sameWires
      (Window.resultWord port) (Window.resultWord_distinct port) output mask store path
        environment.quantum reference)
    (fun reference store (_ : Unit) => (UnitaryOperator.prodTensor
      (feedbackOperator sameWires mask tail environment.quantum store)
      (1 : UnitaryOperator reference) : HilbertOperator (Register.prod ctx.register reference)))
    environment (reset_block_matrix port sameWires output mask environment)
    (feedback_block_matrix sameWires mask tail environment) Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  simp only [Execution.Instrument.retainedRecord, Execution.Instrument.sequenceRetainedRecord,
    record, feedbackRecord, branchOperator]
  split_ifs <;> rfl

end

end Reset.Instrument

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
