/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Components.QubitPrimitive
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.NormNum
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Encoded-bit swaps

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)
variable {environment : oracles.Interpretation}

/-- Three-CNOT swap of two encoded bits. -/
def swapGates
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    List (GateSpec encoding) :=
  [ GateSpec.cnot left right hleftRight
  , GateSpec.cnot right left (Ne.symm hleftRight)
  , GateSpec.cnot left right hleftRight ]

/-- Base-gate program for swapping two encoded bits. -/
def swapProgram
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (swapGates left right hleftRight)

/-- Folded semantic action of the three-CNOT bit swap. -/
def swapStep
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    Data -> Data :=
  GateSpec.stepList (swapGates left right hleftRight)

/-- The bit-swap base-gate program realizes its folded semantics. -/
lemma swap_realizes
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    UnitaryCircuit.Realizes encoding
      (swapProgram physical oracles left right hleftRight) environment
      (swapStep left right hleftRight) :=
  GateSpec.realizesList physical oracles (environment := environment) (swapGates left right
    hleftRight)

/-- Direct realization proof for swapping two encoded bits. -/
lemma swapWitness
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    UnitaryCircuit.Realizes encoding (swapProgram physical oracles left right hleftRight)
      environment
      (swapStep left right hleftRight) :=
  swap_realizes physical oracles left right hleftRight

/-- A three-CNOT bit swap returns the original right readout on the left. -/
lemma swapStep_get_left
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) (x : Data) :
    left.get (swapStep left right hleftRight x) = right.get x := by
  simp only [swapStep, swapGates, GateSpec.stepList, GateSpec.step, id_eq]
  rw [cnotStep_get_of_target_ne left right left (Ne.symm hleftRight)]
  rw [cnotStep_get_target]
  rw [cnotStep_get_of_target_ne left right left (Ne.symm hleftRight)]
  rw [cnotStep_get_target]
  cases left.get x <;> cases right.get x <;> simp

/-- A three-CNOT bit swap returns the original left readout on the right. -/
lemma swapStep_get_right
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) (x : Data) :
    right.get (swapStep left right hleftRight x) = left.get x := by
  simp only [swapStep, swapGates, GateSpec.stepList, GateSpec.step, id_eq]
  let y1 := cnotStep left right x
  let y2 := cnotStep right left y1
  change right.get (cnotStep left right y2) = left.get x
  rw [cnotStep_get_target]
  have hright : right.get y2 = right.get y1 := by
    exact cnotStep_get_of_target_ne right left right hleftRight y1
  have hleft : left.get y2 = (left.get y1 ^^ right.get y1) := by
    exact cnotStep_get_target right left y1
  have hleft1 : left.get y1 = left.get x := by
    exact cnotStep_get_of_target_ne left right left (Ne.symm hleftRight) x
  have hright1 : right.get y1 = (right.get x ^^ left.get x) := by
    exact cnotStep_get_target left right x
  rw [hright, hleft, hleft1, hright1]
  cases left.get x <;> cases right.get x <;> simp

/-- A three-CNOT bit swap preserves readouts away from its two targets. -/
lemma swapStep_get_observed_of_swap_ne
    (left right observed : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire)
    (hleftObserved : left.wire ≠ observed.wire)
    (hrightObserved : right.wire ≠ observed.wire) (x : Data) :
    observed.get (swapStep left right hleftRight x) = observed.get x := by
  simp only [swapStep, swapGates, GateSpec.stepList, GateSpec.step, id_eq]
  rw [cnotStep_get_of_target_ne left right observed hrightObserved]
  rw [cnotStep_get_of_target_ne right left observed hleftObserved]
  rw [cnotStep_get_of_target_ne left right observed hrightObserved]

/-- Three-Toffoli controlled swap of two encoded bits. -/
def controlledSwapGates
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    List (GateSpec encoding) :=
  [ GateSpec.toffoli control left right
      hcontrolLeft hcontrolRight hleftRight
  , GateSpec.toffoli control right left
      hcontrolRight hcontrolLeft (Ne.symm hleftRight)
  , GateSpec.toffoli control left right
      hcontrolLeft hcontrolRight hleftRight ]

/-- A controlled swap is disjoint from an observed bit when its control and
both swapped bits are disjoint from that observation. -/
lemma controlledSwapGates_bitDisjoint
    (control left right observed : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire)
    (hcontrolObserved : control.wire ≠ observed.wire)
    (hleftObserved : left.wire ≠ observed.wire)
    (hrightObserved : right.wire ≠ observed.wire) :
    ∀ gate,
      gate ∈ controlledSwapGates control left right hcontrolLeft
          hcontrolRight hleftRight →
        GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  simp only [controlledSwapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact ⟨hcontrolObserved, hleftObserved, hrightObserved⟩
  · exact ⟨hcontrolObserved, hrightObserved, hleftObserved⟩
  · exact ⟨hcontrolObserved, hleftObserved, hrightObserved⟩

/-- A controlled bit swap contains three physical leaves. -/
@[simp] lemma controlledSwapGates_length
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    (controlledSwapGates control left right hcontrolLeft hcontrolRight
      hleftRight).length = 3 := by
  simp [controlledSwapGates]

/-- A controlled bit swap contains no X gate. -/
@[simp] lemma controlledSwapGates_xMultiplicity_sum
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    ((controlledSwapGates control left right hcontrolLeft hcontrolRight
      hleftRight).map GateSpec.xMultiplicity).sum = 0 := by
  simp [controlledSwapGates]

/-- A controlled bit swap contains no CNOT gate. -/
@[simp] lemma controlledSwapGates_cnotMultiplicity_sum
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    ((controlledSwapGates control left right hcontrolLeft hcontrolRight
      hleftRight).map GateSpec.cnotMultiplicity).sum = 0 := by
  simp [controlledSwapGates]

/-- A controlled bit swap contains exactly three Toffoli gates. -/
@[simp] lemma controlledSwapGates_toffoliMultiplicity_sum
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    ((controlledSwapGates control left right hcontrolLeft hcontrolRight
      hleftRight).map GateSpec.toffoliMultiplicity).sum = 3 := by
  simp [controlledSwapGates]

/-- Base-gate program for a controlled swap of two encoded bits. -/
def controlledSwapProgram
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Folded semantic action of the controlled bit swap. -/
def controlledSwapStep
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    Data -> Data :=
  GateSpec.stepList
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- The controlled-swap base-gate program realizes its folded bit semantics. -/
lemma controlledSwap_realizes
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    UnitaryCircuit.Realizes encoding
      (controlledSwapProgram physical oracles control left right
        hcontrolLeft hcontrolRight hleftRight) environment
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) :=
  GateSpec.realizesList physical oracles (environment := environment)
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Direct realization proof for a controlled swap of two encoded bits. -/
lemma controlledSwapWitness
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    UnitaryCircuit.Realizes encoding
      (controlledSwapProgram physical oracles control left right
        hcontrolLeft hcontrolRight hleftRight) environment
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) :=
  controlledSwap_realizes physical oracles control left right
    hcontrolLeft hcontrolRight hleftRight

/-- A controlled bit swap preserves the control readout. -/
lemma controlledSwapStep_get_control
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) (x : Data) :
    control.get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      control.get x := by
  simp [controlledSwapStep, controlledSwapGates, GateSpec.stepList,
    GateSpec.step, toffoliStep_get_of_target_ne, Ne.symm hcontrolLeft,
    Ne.symm hcontrolRight]

/-- A controlled bit swap returns the original right readout on the left when
the control is set, and otherwise preserves the left readout. -/
lemma controlledSwapStep_get_left
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) (x : Data) :
    left.get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      if control.get x then right.get x else left.get x := by
  unfold controlledSwapStep controlledSwapGates
  simp only [GateSpec.stepList, GateSpec.step, id_eq]
  rw [toffoliStep_get_of_target_ne control left right left
    (Ne.symm hleftRight)]
  rw [toffoliStep_get_target]
  rw [toffoliStep_get_of_target_ne control left right control
    (Ne.symm hcontrolRight)]
  rw [toffoliStep_get_target]
  rw [toffoliStep_get_of_target_ne control left right left
    (Ne.symm hleftRight)]
  by_cases hcontrol : control.get x <;>
    by_cases hleft : left.get x <;>
    by_cases hright : right.get x <;>
    simp [hcontrol, hleft, hright]

/-- A controlled bit swap returns the original left readout on the right when
the control is set, and otherwise preserves the right readout. -/
lemma controlledSwapStep_get_right
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) (x : Data) :
    right.get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      if control.get x then left.get x else right.get x := by
  unfold controlledSwapStep controlledSwapGates
  simp only [GateSpec.stepList, GateSpec.step, id_eq]
  rw [toffoliStep_get_target]
  rw [toffoliStep_get_of_target_ne control right left right hleftRight]
  rw [toffoliStep_get_of_target_ne control right left control
    (Ne.symm hcontrolLeft)]
  rw [toffoliStep_get_target]
  rw [toffoliStep_get_of_target_ne control left right control
    (Ne.symm hcontrolRight)]
  rw [toffoliStep_get_target]
  rw [toffoliStep_get_of_target_ne control left right left
    (Ne.symm hleftRight)]
  by_cases hcontrol : control.get x <;>
    by_cases hleft : left.get x <;>
    by_cases hright : right.get x <;>
    simp [hcontrol, hleft, hright,
      toffoliStep_get_of_target_ne control left right control
        (Ne.symm hcontrolRight), toffoliStep_get_target]

/-- A controlled bit swap preserves any readout whose wire is distinct from
both swapped wires. -/
lemma controlledSwapStep_get_observed_of_swap_ne
    (control left right observed : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire)
    (hleftObserved : left.wire ≠ observed.wire)
    (hrightObserved : right.wire ≠ observed.wire) (x : Data) :
    observed.get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      observed.get x := by
  simp [controlledSwapStep, controlledSwapGates, GateSpec.stepList,
    GateSpec.step, toffoliStep_get_of_target_ne, hleftObserved,
    hrightObserved]

end EncodedBit

end

end QuantumAlg

end
