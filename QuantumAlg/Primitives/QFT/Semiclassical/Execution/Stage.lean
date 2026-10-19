/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Core.Execution.Measured.Stage
import all QuantumAlg.Core.Measure.Instrument

/-!
# Actual semiclassical Fourier head stage on complete stored blocks

The native Hadamard, literal Z write and phase word selected from that same
written cell compose into their exact retained-bank Kraus matrix. This
interpreter bridge preserves arbitrary input mixtures, all complementary
physical systems and the complete external reference. It precedes the
separate scalar identification with the Fourier recurrence.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum}

/-- Matrix of the real head instruction, observed projector and stored-result feedback word. -/
def nativeStageKraus {environment : OracleModel.empty.Interpretation} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount)
    (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (Reference : Register) (outcome : Fin (ctx.quantumLayout.wire head).dimension) :
    HilbertOperator (ctx.register.prod Reference) :=
  (UnitaryOperator.prodTensor
    ((selectedPhase inverse tail tailQubits (.finite outcome)).matrix environment)
    (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference)) *
      ZMeasurement.projector (R := ctx.register.prod Reference)
        (fun basis => basis.1 head) outcome *
        (UnitaryOperator.prodTensor
          ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit).matrix environment)
          (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference))

/-- Each actual full store retains the exact head-stage instrument, including overwritten inputs. -/
lemma nativeStage_store_matrix {environment : (ExecutionModel.quantum AlgorithmGate.model
    .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount)
    (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (ExecutionState.filterClassical
      (((Circuit.seq
        (.unitary (allowAllocation := false) (operations := .empty)
          (classicalOracles := .empty)
          (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit))
        ((Circuit.measureZ head result).seq (feedbackCode inverse tail tailQubits
          result))).execute environment)
          Reference state) (fun entry
            => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx × (ClassicalOracleModel.empty.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire head).dimension,
          if original.1.write result (.finite outcome) = stored then
            nativeStageKraus
              (environment := environment.quantum) inverse head headQubit tail tailQubits
              Reference outcome *
              (state.block original).matrix *
                (nativeStageKraus
                  (environment := environment.quantum) inverse head headQubit tail tailQubits
                  Reference outcome).conjTranspose
          else 0 := by
  unfold feedbackCode nativeStageKraus
  exact Circuit.unitary_measureZ_selected_store_matrix
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (services := .empty)
    (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit)
    head result (selectedPhase inverse tail tailQubits) environment state stored

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
