/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Enable

/-! # Actual externally selected original phase-enable XOR, at every source width -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelectionEnable

noncomputable section

open EncodedBit

/-- Both literal original phase CNOTs occupy the original source prefix beside the same pool. -/
def sourceGates (width : Nat) : List (GateSpec (Scanned.encoding width)) :=
  (SelectionEnable.sourceGates width).map (GateSpec.prodLeft (poolEncoding width))

private lemma sourceGates_step (width : Nat) (state : Scanned.Data width) :
    GateSpec.stepList (sourceGates width) state = SelectionEnable.step width state := by
  exact (GateSpec.stepList_prodLeft (poolEncoding width)
    (SelectionEnable.sourceGates width) state).trans
      (congrArg (fun source => (source, state.2)) (SelectionEnable.source_gates_step width state.1))

/-- The same two original phase updates each pay one actual external-control Toffoli. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  ExternalWord.program (Scanned.encoding width) (sourceGates width)

def step (width : Nat) (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  (if state.2.1 then SelectionEnable.step width state.1 else state.1, state.2)

private lemma gates_step (width : Nat) (state : ControlledFrame.Data width) :
    GateSpec.stepList (ExternalWord.gates (Scanned.encoding width) (sourceGates width)) state =
      step width state := by
  rw [ExternalWord.gates_step, ExternalWord.step, sourceGates_step]
  rfl

/-- Every original phase, arbitrary pool and external work amplitude is retained exactly. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding width) (program width) environment
      (step width) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _ (gates_step width) environment

lemma step_pool (width : Nat) (state : ControlledFrame.Data width) :
    (step width state).1.2 = state.1.2 := by
  unfold step
  split <;> rfl

lemma step_step (width : Nat) (state : ControlledFrame.Data width) :
    step width (step width state) = state := by
  cases selected : state.2.1 with
  | false => simp only [step, selected, Bool.false_eq_true, if_false]
  | true => simp only [step, selected, ↓reduceIte, SelectionEnable.step_step]

/-- This actual support-certified lowering has two Toffolis for every source width. -/
lemma program_toffoli_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program width).eventCost = 2 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (ExternalWord.program (Scanned.encoding width) (sourceGates width)).eventCost = 2
  rw [ExternalWord.program_toffoli_count]
  rfl

/-- Neither additional native CNOTs nor X gates are hidden by the phase-enable interface. -/
lemma program_other_counts (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program width).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program width).eventCost = 0 := by
  constructor
  · change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (ExternalWord.program (Scanned.encoding width) (sourceGates width)).eventCost = 0
    rw [ExternalWord.program_cnot_count]
    rfl
  · exact ExternalWord.program_singleQubit_count (Scanned.encoding width) (sourceGates width)

lemma program_quantumTime (width : Nat) :
    (program width).evaluatedEventDepth Resource.Event.quantumDuration = 2 := by
  change (ExternalWord.program (Scanned.encoding width) (sourceGates width)).evaluatedEventDepth
    Resource.Event.quantumDuration = 2
  rw [ExternalWord.program_quantumTime]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelectionEnable
