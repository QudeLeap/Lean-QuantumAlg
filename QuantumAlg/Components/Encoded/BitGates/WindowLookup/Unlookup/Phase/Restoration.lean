/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.OneHot
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Restoration

/-!
# Actual unary preparation, paid selected feedback and native restoration

The supplied low unary targets are the original physically reset result
systems. Their explicit initial zero promise supports unary preparation.
The actual inverse of that same preparation restores all quantum labels,
while the paid feedback contributes the original address's measured sign.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

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
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))

/-- The exact actual allocation-free feedback tail after physical result reset. -/
def restorationCircuit :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (SelectorFrame.placedCircuit physical sameWires (frame.low.program physical .empty)).seq
    ((frame.phaseCircuit physical sameWires measured parity table).seq
      (SelectorFrame.placedCircuit physical sameWires (frame.low.uncomputeProgram physical)))

/-- Every actual preparation, feedback and inverse path is retained with its true final Store. -/
def restorationRecord (store : Store ctx) : Store ctx ×
    (frame.restorationCircuit (services := services)
      physical sameWires measured parity table).Path :=
  let feedback := frame.phaseRecord (services := services)
    physical sameWires measured parity table store
  (feedback.1, ((), (feedback.2, ())))

/-- The same actual preparation and native inverse surround the complete paid feedback matrix. -/
def restorationOperator (environment : OracleModel.Interpretation .empty) (store : Store ctx) :
    UnitaryOperator ctx.register :=
  (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (frame.low.uncomputeProgram physical)).matrix environment *
    frame.phaseOperator (services := services)
      physical sameWires measured parity table environment store *
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
    (parityDistinct : Function.Injective fun index => (parity index).key)
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (frame.restorationCircuit physical sameWires measured parity table).execute
      environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (frame.restorationOperator (services := services)
          physical sameWires measured parity table environment.quantum entry.1)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let result := frame.restorationRecord (services := services)
            physical sameWires measured parity table entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  change ((Circuit.unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (frame.low.program physical .empty))).seq
      ((frame.phaseCircuit physical sameWires measured parity table).seq
        (Circuit.unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (frame.low.uncomputeProgram physical))))).execute environment Reference state = _
  rw [Circuit.execute_seq, Circuit.execute_unitary, Circuit.execute_seq,
    frame.phaseCircuit_execute physical sameWires measured parity table parityDistinct separate,
    Circuit.execute_unitary]
  simp only [State.mapHistory, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def,
    ExecutionState.executionState_applyUnitary_comp, reference_product, mul_assoc,
    restorationOperator, restorationRecord]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Ordered-wire placement retains the exact native preparation/inverse cancellation. -/
lemma lowInverse_mul_program (environment : OracleModel.Interpretation .empty) :
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (frame.low.uncomputeProgram physical)).matrix environment *
      (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (frame.low.program physical .empty)).matrix environment = 1 := by
  have native : star ((frame.low.program physical .empty).matrix environment) *
      (frame.low.program physical .empty).matrix environment = 1 := by
    apply Subtype.ext
    exact Matrix.UnitaryGroup.star_mul_self _
  rw [unitaryOfEqualWires_matrix, unitaryOfEqualWires_matrix,
    UnaryFrame.uncomputeProgram, UnitaryCircuit.dagger_matrix,
    show (AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment = environment from
      Subsingleton.elim _ _, ← UnitaryOperator.unitaryOperator_reindex_mul, native,
    UnitaryOperator.unitaryOperator_reindex_one]

/-- The same actual native inverse restores the complete original encoded input
after preparation. -/
lemma lowInverse_apply_prepared (environment : OracleModel.Interpretation .empty) (state : Data) :
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (frame.low.uncomputeProgram physical)).matrix environment).applyVec
        (SelectorFrame.ctxVector physical sameWires (frame.low.step state)) =
      SelectorFrame.ctxVector physical sameWires state := by
  have actual := SelectorFrame.placedProgram_applyVec physical sameWires
    (frame.low.program physical .empty) frame.low.step environment
    (frame.low.program_realizes physical .empty environment) state
  change ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (frame.low.program physical .empty)).matrix environment).applyVec
      (SelectorFrame.ctxVector physical sameWires state) =
        SelectorFrame.ctxVector physical sameWires (frame.low.step state) at actual
  rw [← actual, ← UnitaryOperator.mul_applyVec, frame.lowInverse_mul_program physical sameWires,
    UnitaryOperator.one_applyVec]

/-- The actual restored unary workspace contributes exactly
the original measured table character. -/
lemma restorationOperator_applyVec
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx) (state : Data)
    (zero : ∀ index, (frame.low.target index).get state = false)
    (clean : frame.high.CleanFrom 0 state) :
    (frame.restorationOperator (services := services)
      physical sameWires measured parity table environment store).applyVec
        (SelectorFrame.ctxVector physical sameWires state) =
      (if MaskParity.maskValue (store.read measured)
        (table ((frame.high.stack ⟨0, by omega⟩).get state)
          (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state)
          (frame.low.prefixLabel lowWidth (Nat.le_refl _) state)) then (-1 : ℂ) else 1) •
        SelectorFrame.ctxVector physical sameWires state := by
  have prepared := SelectorFrame.placedProgram_applyVec physical sameWires
    (frame.low.program physical .empty) frame.low.step environment
    (frame.low.program_realizes physical .empty environment) state
  change UnitaryOperator.applyVec _ (SelectorFrame.ctxVector physical sameWires state) =
    SelectorFrame.ctxVector physical sameWires (frame.low.step state) at prepared
  have feedback := frame.phaseOperator_oneHot_applyVec (services := services)
    physical sameWires measured parity table separate environment store (frame.low.step state)
    (frame.low.prefixLabel lowWidth (Nat.le_refl _) state) (frame.low.step_oneHot state zero)
    (frame.lowStep_clean state clean)
  rw [frame.lowStep_highStack, frame.lowStep_highLabel] at feedback
  unfold restorationOperator
  rw [UnitaryOperator.mul_applyVec, prepared, UnitaryOperator.mul_applyVec, feedback,
    UnitaryOperator.applyVec_smul, frame.lowInverse_apply_prepared physical sameWires]

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
