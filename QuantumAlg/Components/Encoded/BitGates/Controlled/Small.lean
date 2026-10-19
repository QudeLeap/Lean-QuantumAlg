/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive

/-!
# Native control of bit-gate lists on at most two target wires

An X becomes one CNOT and a CNOT becomes one Toffoli. Three distinct
Toffoli arguments cannot fit in the source carrier. The selecting wire
belongs to a separate existing field, and every other bit is retained.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Left Right : Type} {left : BinaryLabelEncoding Left}
  {right : BinaryLabelEncoding Right}

private lemma no_three_wires (small : right.width ≤ 2)
    (a b c : EncodedBit right) (ab : a.wire ≠ b.wire)
    (ac : a.wire ≠ c.wire) (bc : b.wire ≠ c.wire) : False := by
  have ha := a.wire.isLt
  have hb := b.wire.isLt
  have hc := c.wire.isLt
  have hab : a.wire.val ≠ b.wire.val := fun same => ab (Fin.ext same)
  have hac : a.wire.val ≠ c.wire.val := fun same => ac (Fin.ext same)
  have hbc : b.wire.val ≠ c.wire.val := fun same => bc (Fin.ext same)
  omega

/-- Compile one permitted small gate under an existing left-field control. -/
def controlSmall (control : EncodedBit left) (small : right.width ≤ 2) :
    GateSpec right → GateSpec (BinaryLabelEncoding.prod left right)
  | .x target =>
      .cnot (BinaryLabelEncoding.prodLeftBit left right control)
        (BinaryLabelEncoding.prodRightBit left right target)
        (prodRightBit_wire_ne_prodLeftBit_wire left right target control).symm
  | .cnot source target separated =>
      .toffoli (BinaryLabelEncoding.prodLeftBit left right control)
        (BinaryLabelEncoding.prodRightBit left right source)
        (BinaryLabelEncoding.prodRightBit left right target)
        (prodRightBit_wire_ne_prodLeftBit_wire left right source control).symm
        (prodRightBit_wire_ne_prodLeftBit_wire left right target control).symm
        (prodRightWire_ne left separated)
  | .toffoli a b c ab ac bc => False.elim (no_three_wires small a b c ab ac bc)

/-- Controlled small gates emit no single-qubit instruction. -/
@[simp] lemma controlSmall_xMultiplicity (control : EncodedBit left)
    (small : right.width ≤ 2) (gate : GateSpec right) :
    xMultiplicity (controlSmall control small gate) = 0 := by
  cases gate with
  | x => rfl
  | cnot => rfl
  | toffoli a b c ab ac bc => exact False.elim (no_three_wires small a b c ab ac bc)

/-- Each source X emits one CNOT. -/
@[simp] lemma controlSmall_cnotMultiplicity (control : EncodedBit left)
    (small : right.width ≤ 2) (gate : GateSpec right) :
    cnotMultiplicity (controlSmall control small gate) = xMultiplicity gate := by
  cases gate with
  | x => rfl
  | cnot => rfl
  | toffoli a b c ab ac bc => exact False.elim (no_three_wires small a b c ab ac bc)

/-- Each source CNOT emits one Toffoli. -/
@[simp] lemma controlSmall_toffoliMultiplicity (control : EncodedBit left)
    (small : right.width ≤ 2) (gate : GateSpec right) :
    toffoliMultiplicity (controlSmall control small gate) = cnotMultiplicity gate := by
  cases gate with
  | x => rfl
  | cnot => rfl
  | toffoli a b c ab ac bc => exact False.elim (no_three_wires small a b c ab ac bc)

/-- Both branches have their exact basis action, with every left-field bit retained. -/
lemma controlSmall_step (control : EncodedBit left) (small : right.width ≤ 2)
    (gate : GateSpec right) (state : Left × Right) :
    (controlSmall control small gate).step state =
      (state.1, if control.get state.1 then gate.step state.2 else state.2) := by
  cases gate with
  | x target =>
      cases selected : control.get state.1 <;>
        simp [controlSmall, step, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit, selected]
  | cnot source target separated =>
      cases selected : control.get state.1 <;> cases enabled : source.get state.2 <;>
        simp [controlSmall, step, EncodedBit.toffoliStep, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit, selected, enabled]
  | toffoli a b c ab ac bc => exact False.elim (no_three_wires small a b c ab ac bc)

/-- Literal control of the list preserves order and requires no additional work bit. -/
lemma controlSmallList_step (control : EncodedBit left) (small : right.width ≤ 2)
    (gates : List (GateSpec right)) (state : Left × Right) :
    stepList (gates.map (controlSmall control small)) state =
      (state.1, if control.get state.1 then stepList gates state.2 else state.2) := by
  induction gates generalizing state with
  | nil => simp [stepList]
  | cons gate rest ih =>
      change stepList (rest.map (controlSmall control small))
        ((controlSmall control small gate).step state) = _
      rw [controlSmall_step, ih]
      cases control.get state.1 <;> simp [stepList]

/-- The compiled word realizes the conditional action with exact phase. -/
lemma controlSmallList_realizes (control : EncodedBit left) (small : right.width ≤ 2)
    (physical : QubitLayout (left.width + right.width)) (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (gates : List (GateSpec right)) :
    UnitaryCircuit.Realizes (layout := physical) (BinaryLabelEncoding.prod left right)
      (programList physical oracles (gates.map (controlSmall control small))) environment
      (fun state => (state.1,
        if control.get state.1 then stepList gates state.2 else state.2)) :=
  realizesList_congrStep physical oracles _ (controlSmallList_step control small gates) environment

/-- One physical instruction is emitted for each source X or CNOT. -/
lemma controlSmallList_resources (control : EncodedBit left) (small : right.width ≤ 2)
    (physical : QubitLayout (left.width + right.width)) (oracles : OracleModel)
    (gates : List (GateSpec right)) :
    (programList physical oracles (gates.map (controlSmall control small))).eventCost.card =
        gates.length ∧
      (programList physical oracles (gates.map (controlSmall control small))).evaluatedEventDepth
        (fun _ => 1) = gates.length := by
  rw [programList_eventCost_card, programList_evaluatedEventDepth_unit, List.length_map]
  exact ⟨rfl, rfl⟩

end

end QuantumAlg.EncodedBit.GateSpec
