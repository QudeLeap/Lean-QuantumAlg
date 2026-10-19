/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Primitives.QFT.Semiclassical.PhaseMatrix.Source
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Source phases in the actual stored-outcome Fourier stage

The native feedback word is proved to have the source diagonal, retaining
every complementary physical coordinate. The complete mixed-state stage
equation is then expressed with that independently defined diagonal. No
matrix-equality or instrument certificate is supplied as a hypothesis.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum}

/-- The actual wire outcome, transported along its already proved qubit dimension. -/
def outcomeBit (head : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire head).dimension = 2)
    (outcome : Fin (ctx.quantumLayout.wire head).dimension) : Fin 2 :=
  Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) outcome

/-- Dimension transport does not change which native phase word the real stored value selects. -/
lemma selectedPhase_outcomeBit (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (outcome : Fin (ctx.quantumLayout.wire head).dimension) :
    selectedPhase inverse tail tailQubits (.finite outcome) =
      selectedPhase inverse tail tailQubits (dimension := 2)
        (.finite (outcomeBit head headQubit outcome)) := by
  rfl

/-- The Fourier source phase, read in the existing physical tail coordinates. -/
def sourceFeedbackMatrix (inverse : Bool) {n : Nat}
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (bit : Fin 2) : HilbertOperator ctx.register :=
  Matrix.diagonal (fun basis => if bit = 1 then
    (if inverse then star (ω (n + 1) ^ (physicalTailLabel tail tailQubits basis).val)
      else ω (n + 1) ^ (physicalTailLabel tail tailQubits basis).val)
    else 1)

/-- The actual feedback instruction's complete matrix equals the source diagonal. -/
lemma selectedPhase_eq_sourceFeedbackMatrix {environment : OracleModel.empty.Interpretation}
    (inverse : Bool) {n : Nat}
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2) (bit : Fin 2) :
    (((selectedPhase inverse tail tailQubits (dimension := 2) (.finite bit)).matrix environment) :
      HilbertOperator ctx.register) =
      sourceFeedbackMatrix inverse tail tailQubits bit := by
  ext row column
  rw [qftSemiclassical_selectedPhase_matrix_entry]
  by_cases same : row = column
  · subst column
    simp only [sourceFeedbackMatrix, Matrix.diagonal_apply]
  · simp only [sourceFeedbackMatrix, Matrix.diagonal_apply, if_neg same]

/-- Tensoring with the arbitrary external reference is an explicit identity extension. -/
def sourceFeedbackReference (inverse : Bool) {n : Nat}
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (bit : Fin 2) (Reference : Register) : HilbertOperator (ctx.register.prod Reference) :=
  fun row column => sourceFeedbackMatrix inverse tail tailQubits bit row.1 column.1 *
    (if row.2 = column.2 then 1 else 0)

lemma selectedPhase_reference_eq_source {environment : OracleModel.empty.Interpretation}
    (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (Reference : Register) (outcome : Fin (ctx.quantumLayout.wire head).dimension) :
    (UnitaryOperator.prodTensor ((selectedPhase inverse tail tailQubits (.finite outcome)).matrix
      environment)
      (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference)) =
      sourceFeedbackReference inverse tail tailQubits
        (outcomeBit head headQubit outcome) Reference := by
  rw [selectedPhase_outcomeBit inverse head headQubit tail tailQubits outcome]
  ext row column
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  change ((selectedPhase inverse tail tailQubits (dimension := 2)
      (.finite (outcomeBit head headQubit outcome))).matrix environment) row.1 column.1 *
      (if row.2 = column.2 then 1 else 0) = _
  rw [selectedPhase_eq_sourceFeedbackMatrix]
  rfl

/-- The source-form Kraus matrix keeps the actual physical Hadamard and measured wire. -/
def sourceStageKraus {environment : OracleModel.empty.Interpretation} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (Reference : Register) (outcome : Fin (ctx.quantumLayout.wire head).dimension) :
    HilbertOperator (ctx.register.prod Reference) :=
  sourceFeedbackReference inverse tail tailQubits (outcomeBit head headQubit outcome) Reference *
    ZMeasurement.projector (R := ctx.register.prod Reference) (fun basis => basis.1 head) outcome *
      (UnitaryOperator.prodTensor
        ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit).matrix environment)
        (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference))

/-- Source identification is derived from the actual native word,
with no new certificate premise. -/
lemma nativeStageKraus_eq_source {environment : OracleModel.empty.Interpretation} (inverse :
    Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (Reference : Register) (outcome : Fin (ctx.quantumLayout.wire head).dimension) :
    nativeStageKraus (environment := environment) inverse head headQubit tail tailQubits Reference
      outcome =
      sourceStageKraus
        (environment := environment) inverse head headQubit tail tailQubits Reference outcome := by
  unfold nativeStageKraus sourceStageKraus
  rw [selectedPhase_reference_eq_source]

/-- Full actual stored stage, now identified with the source Fourier feedback diagonal. -/
lemma nativeStage_source_store_matrix {environment : (ExecutionModel.quantum AlgorithmGate.model
    .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (ExecutionState.filterClassical
      (((Circuit.seq
        (.unitary (allowAllocation := false) (operations := .empty) (classicalOracles := .empty)
          (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit))
        ((Circuit.measureZ head result).seq (feedbackCode inverse tail tailQubits
          result))).execute environment)
        Reference state) (fun entry
          => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx × (ClassicalOracleModel.empty.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire head).dimension,
          if original.1.write result (.finite outcome) = stored then
            sourceStageKraus
              (environment := environment.quantum) inverse head headQubit tail tailQubits
              Reference outcome *
              (state.block original).matrix *
                (sourceStageKraus
                  (environment := environment.quantum) inverse head headQubit tail tailQubits
                  Reference outcome).conjTranspose
          else 0 := by
  simpa only [nativeStageKraus_eq_source] using
    nativeStage_store_matrix inverse head headQubit tail tailQubits result state stored

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
