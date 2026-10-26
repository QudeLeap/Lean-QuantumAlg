/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Callback
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.FrameLaws
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-!
# Literal native words at an ordinary selected unary leaf

The real final prefix controls an original native word. Its extra
Toffoli control is lowered with one arbitrary restored wire. The
source action protects the entire address and stack, so the ordinary
selector traversal retains its complete physical frame. No boundary
toggle is added to this callback.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open GateSpec WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Literal native source gates, one original dirty wire, and every physical frame separation. -/
structure SelectedPayload (frame : SelectorFrame encoding width) where
  source : List (GateSpec encoding)
  work : EncodedBit encoding
  sourceAddress : ∀ index gate, gate ∈ source → bitDisjoint (frame.address index) gate
  sourceStack : ∀ index gate, gate ∈ source → bitDisjoint (frame.stack index) gate
  workDisjoint : ∀ gate, gate ∈ source → bitDisjoint work gate
  controlWork : (frame.stack ⟨width, by omega⟩).wire ≠ work.wire

namespace SelectedPayload

variable {frame : SelectorFrame encoding width} (payload : SelectedPayload frame)

private def controlled : ControlledPayload encoding where
  source := payload.source
  active := frame.stack ⟨width, by omega⟩
  work := payload.work
  activeDisjoint := payload.sourceStack _
  workDisjoint := payload.workDisjoint
  activeWork := payload.controlWork

/-- The unchanged ordered source action, before its physical prefix control. -/
def action : Data → Data := GateSpec.stepList payload.source

/-- Actual native instructions implement the selected leaf on the same full physical carrier. -/
def program (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles payload.controlled.gates

/-- Full coherent selected-leaf semantics include arbitrary dirty work and every reference. -/
lemma program_realizes (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (payload.program physical oracles) environment
      (conditionalAction (frame.stack ⟨width, by omega⟩) payload.action) :=
  GateSpec.realizesList_congrStep physical oracles _ payload.controlled.gates_step environment

/-- The original source word protects every actual address and stack position. -/
lemma action_preserves : frame.Preserves payload.action := by
  constructor
  · intro index state
    exact stepList_get_of_bitDisjoint payload.source _ (payload.sourceAddress index) state
  · intro index state
    exact stepList_get_of_bitDisjoint payload.source _ (payload.sourceStack index) state

/-- Every unused prefix flip commutes with the original native source action. -/
lemma action_independent : frame.IndependentPrefixes payload.action := by
  intro index state
  exact stepList_flip_comm_of_bitDisjoint payload.source _ (payload.sourceStack index.succ) state

/-- A selected original CNOT costs one Toffoli; an original Toffoli costs four. -/
lemma program_toffoli_count (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (payload.program physical oracles).eventCost =
      (payload.source.map cnotMultiplicity).sum +
        4 * (payload.source.map toffoliMultiplicity).sum := by
  rw [program, programList_toffoli_count_eq_sum, ControlledPayload.gates]
  exact listWithDirtyControl_toffoliMultiplicity_sum _ _ _ _ _ _

/-- Only source X instructions become actual CNOTs in the selected native callback. -/
lemma program_cnot_count (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (payload.program physical oracles).eventCost = (payload.source.map xMultiplicity).sum := by
  rw [program, programList_cnot_count_eq_sum, ControlledPayload.gates]
  exact listWithDirtyControl_cnotMultiplicity_sum _ _ _ _ _ _

/-- The native control lift emits no hidden single-qubit instruction. -/
lemma program_single_count (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (payload.program physical oracles).eventCost = 0 := by
  rw [program, programList_x_count_eq_sum, ControlledPayload.gates]
  exact listWithDirtyControl_xMultiplicity_sum _ _ _ _ _ _

/-- The true callback depth counts every native dirty-control instruction. -/
lemma program_quantumTime (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    (payload.program physical oracles).evaluatedEventDepth Resource.Event.quantumDuration =
      (payload.source.map dirtyControlCount).sum := by
  rw [program, programList_quantumTime, ControlledPayload.gates, listWithDirtyControl_length]
  rfl

end SelectedPayload

end

end QuantumAlg.EncodedBit.StreamedSelector
