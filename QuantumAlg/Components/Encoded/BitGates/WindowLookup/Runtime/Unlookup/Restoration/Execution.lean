/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Execution
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Restoration

/-!
# Complete actual runtime preparation/feedback/inverse execution

The supplied low unary targets are the original physically reset result
systems. Their true unitary preparation and inverse surround the actual paid
feedback. The intended character and clean-input restoration are established
separately from this unconditional complete execution equation.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (temporary : CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

/-- Every actual preparation, feedback and inverse path is retained with its true final Store. -/
def restorationRecord (store : Store ctx) : Store ctx ×
    (restorationCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path :=
  let feedback := phaseRecord frame (services := services)
    physical sameWires measured parity temporary table store
  (feedback.1, ((), (feedback.2, ())))

/-- The same actual preparation and native inverse surround the complete paid feedback matrix. -/
def restorationOperator (environment : OracleModel.Interpretation .empty) (store : Store ctx) :
    UnitaryOperator ctx.register :=
  (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (frame.low.uncomputeProgram physical)).matrix environment *
    phaseOperator frame (services := services)
      physical sameWires measured parity temporary table environment store *
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (frame.low.program physical .empty)).matrix environment

private lemma reference_product {Local Reference : Register}
    (second first : UnitaryOperator Local) :
    UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) *
        UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) =
      UnitaryOperator.prodTensor (second * first) (1 : UnitaryOperator Reference) := by
  apply Subtype.ext
  change (UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) *
    (UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) = _
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    unitaryOperator_prodTensor_identity, HilbertOperator.kronecker_identity_mul]
  rfl

/-- Complete actual feedback-tail execution with all real overwrite fibers
and external references. -/
lemma restorationCircuit_execute
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (restorationCircuit frame physical sameWires measured parity temporary table).execute
      environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (restorationOperator frame (services := services)
          physical sameWires measured parity temporary table environment.quantum entry.1)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let result := restorationRecord frame (services := services)
            physical sameWires measured parity temporary table entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  change ((Circuit.unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (frame.low.program physical .empty))).seq
      ((phaseCircuit frame physical sameWires measured parity temporary table).seq
        (Circuit.unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (frame.low.uncomputeProgram physical))))).execute environment Reference state = _
  rw [Circuit.execute_seq, Circuit.execute_unitary, Circuit.execute_seq,
    phaseCircuit_execute frame physical sameWires measured parity temporary table,
    Circuit.execute_unitary]
  simp only [State.mapHistory, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def,
    ExecutionState.executionState_applyUnitary_comp, reference_product, mul_assoc,
    restorationOperator, restorationRecord]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
