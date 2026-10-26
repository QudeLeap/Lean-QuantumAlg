/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Resources
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive

/-!
# Actual quantum control of the complete P-256 modular-addition list

The original two words and reduction flag are retained. Two distinct caller
bits supply the quantum selector and clean control-lowering work. They must
be placed on actual caller-owned systems; this component allocates neither
bit. Every original gate is lowered to an actual controlled native list.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

namespace Controlled

noncomputable section

open QuantumAlg.EncodedBit GateSpec

abbrev SelectedRegisters := Registers × (Bool × Bool)

private def flagEncoding : BinaryLabelEncoding (Bool × Bool) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool

abbrev selectorEncoding : BinaryLabelEncoding SelectedRegisters :=
  BinaryLabelEncoding.prod encoding flagEncoding

/-- The two caller bits are included in the physical component width. -/
lemma controlledAddition_width : selectorEncoding.width = 515 := rfl

private def flagSelector : EncodedBit flagEncoding :=
  BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit

private def flagWork : EncodedBit flagEncoding :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit

def selectorBit : EncodedBit selectorEncoding :=
  BinaryLabelEncoding.prodRightBit encoding flagEncoding flagSelector

def controlWorkBit : EncodedBit selectorEncoding :=
  BinaryLabelEncoding.prodRightBit encoding flagEncoding flagWork

private def liftedAdditionGates : List (GateSpec selectorEncoding) :=
  additionGates.map (GateSpec.prodLeft flagEncoding)

private lemma selector_disjoint (gate : GateSpec selectorEncoding)
    (present : gate ∈ liftedAdditionGates) : bitDisjoint selectorBit gate := by
  obtain ⟨original, _present, rfl⟩ := List.mem_map.mp present
  exact bitDisjoint_prodLeft_rightBit encoding flagEncoding flagSelector original

private lemma work_disjoint (gate : GateSpec selectorEncoding)
    (present : gate ∈ liftedAdditionGates) : bitDisjoint controlWorkBit gate := by
  obtain ⟨original, _present, rfl⟩ := List.mem_map.mp present
  exact bitDisjoint_prodLeft_rightBit encoding flagEncoding flagWork original

private lemma selector_work_ne : selectorBit.wire ≠ controlWorkBit.wire := by
  intro same
  have positions := congrArg Fin.val same
  change encoding.width + 0 = encoding.width + 1 at positions
  omega

/-- The selector and work are actual native coordinates on the extended caller frame. -/
def controlledAdditionGates : List (GateSpec selectorEncoding) :=
  controlledListWithWorkGates selectorBit controlWorkBit liftedAdditionGates
    selector_disjoint work_disjoint selector_work_ne

def controlledAdditionProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical selectorEncoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty controlledAdditionGates

/-- Literal action on every incoming label, including work labels outside the clean contract. -/
def controlledAdditionStep : SelectedRegisters → SelectedRegisters :=
  stepList controlledAdditionGates

private lemma lifted_step (state : SelectedRegisters) :
    stepList liftedAdditionGates state = (additionStep state.1, state.2) := by
  rw [liftedAdditionGates, stepList_prodLeft, additionGates_step]

/-- Actual control lowering preserves every caller bit when its selector is false. -/
lemma controlledAddition_of_selector_false (state : SelectedRegisters)
    (disabled : state.2.1 = false) : controlledAdditionStep state = state :=
  controlledListWithWorkStep_eq_self_of_control_false selectorBit controlWorkBit
    liftedAdditionGates selector_disjoint work_disjoint selector_work_ne state disabled

/-- A true quantum selector and the supplied clean work execute the complete original body. -/
lemma controlledAddition_of_selector_true (state : SelectedRegisters)
    (selected : state.2.1 = true) (clean : state.2.2 = false) :
    controlledAdditionStep state = (additionStep state.1, state.2) := by
  have actual := controlledListWithWorkStep_eq_stepList_of_control_true
    selectorBit controlWorkBit liftedAdditionGates selector_disjoint work_disjoint
    selector_work_ne state selected clean
  exact actual.trans (lifted_step state)

/-- Both quantum words, the original reduction flag and control-lowering work have exact outputs. -/
lemma controlledAddition_clean_canonical (left right : Word)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right) (selected : Bool) :
    controlledAdditionStep (((left, right), false), (selected, false)) =
      (((left, if selected then modularSumWord left right else right), false),
        (selected, false)) := by
  cases selected with
  | false =>
      exact controlledAddition_of_selector_false _ rfl
  | true =>
      have actual := controlledAddition_of_selector_true
        (((left, right), false), (true, false)) rfl rfl
      rw [addition_clean_canonical left right leftCanonical rightCanonical] at actual
      exact actual

/-- The same actual list realizes its full-frame action with every relative phase retained. -/
lemma controlledAddition_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes selectorEncoding controlledAdditionProgram environment
      controlledAdditionStep :=
  realizesList (QubitLayout.canonical _) .empty controlledAdditionGates environment

private lemma lifted_eventCost :
    (programList (QubitLayout.canonical selectorEncoding.width) .empty
      liftedAdditionGates).eventCost = additionProgram.eventCost := by
  rw [programList_eventCost, additionProgram, programList_eventCost,
    liftedAdditionGates, map_event_prodLeft]

/-- External quantum control is charged gate by gate, including compute and uncompute. -/
lemma controlledAddition_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      controlledAdditionProgram.eventCost = 52346 := by
  rw [controlledAdditionProgram, programList_toffoli_count_eq_sum,
    controlledAdditionGates, controlledListWithWorkGates_toffoliMultiplicity_sum]
  have cnot : (liftedAdditionGates.map cnotMultiplicity).sum = 5102 := by
    rw [← programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical selectorEncoding.width) (oracles := .empty),
      lifted_eventCost]
    exact addition_cnot_count
  have toffoli : (liftedAdditionGates.map toffoliMultiplicity).sum = 15748 := by
    rw [← programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical selectorEncoding.width) (oracles := .empty),
      lifted_eventCost]
    exact addition_toffoli_count
  rw [cnot, toffoli]

end

end Controlled

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
