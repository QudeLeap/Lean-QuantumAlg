/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.BaseGateRealization
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Encoded bit-gate lifting

This module lifts addressed X, CNOT, and Toffoli base-gate programs from raw
wire labels to semantic data labels.  A semantic bit lens records the wire whose
computational-basis bit stores the semantic Boolean and the semantic update
corresponding to flipping that wire.  The resulting `Realizes` lemmas are the
bridge needed before word-level arithmetic networks can replace endpoint gates
by concrete Toffoli/CNOT/X programs; the reversible arithmetic route starts
from these Boolean gate primitives [VBE95, 9511018.tex:202-215], with plain
adder networks as the first arithmetic use case [VBE95,
9511018.tex:218-264,591-604].
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

/-- A semantic Boolean component of an encoded data type, tied to one concrete
wire of the binary basis-label encoding. -/
structure EncodedBit {Data : Type} (encoding : BinaryLabelEncoding Data) where
  /-- Wire containing this bit in the encoded computational-basis label. -/
  wire : Fin encoding.width
  /-- Semantic Boolean readout of the bit. -/
  get : Data -> Bool
  /-- Semantic update corresponding to flipping exactly this bit. -/
  flip : Data -> Data
  /-- The semantic readout agrees with the encoded basis bit. -/
  get_eq :
    ∀ x : Data,
      (encoding.encode x).val.testBit (WireAddress.bitIndex wire).val = get x
  /-- The semantic flip agrees with flipping the corresponding encoded wire. -/
  encode_flip :
    ∀ x : Data,
      encoding.encode (flip x) = WireAddress.flipBit wire (encoding.encode x)

namespace EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Semantic action of CNOT for encoded semantic bits. -/
def cnotStep (control target : EncodedBit encoding) (x : Data) : Data :=
  if control.get x then target.flip x else x

/-- Semantic action of Toffoli for encoded semantic bits. -/
def toffoliStep (controlA controlB target : EncodedBit encoding) (x : Data) :
    Data :=
  if controlA.get x && controlB.get x then target.flip x else x

/-- Flipping an encoded bit toggles its own semantic readout. -/
theorem get_flip_self (bit : EncodedBit encoding) (x : Data) :
    bit.get (bit.flip x) = !bit.get x := by
  rw [← bit.get_eq (bit.flip x), bit.encode_flip x]
  rw [WireAddress.bit_flipBit_self, bit.get_eq x]

/-- Flipping one encoded bit preserves the readout of a distinct wire. -/
theorem get_flip_of_wire_ne (target observed : EncodedBit encoding)
    (hne : target.wire ≠ observed.wire) (x : Data) :
    observed.get (target.flip x) = observed.get x := by
  rw [← observed.get_eq (target.flip x), target.encode_flip x]
  rw [WireAddress.bit_flipBit_of_ne hne, observed.get_eq x]

/-- CNOT toggles its target readout exactly when the control readout is true. -/
theorem cnotStep_get_target (control target : EncodedBit encoding) (x : Data) :
    target.get (cnotStep control target x) =
      (target.get x ^^ control.get x) := by
  by_cases hcontrol : control.get x
  · rw [cnotStep, if_pos hcontrol, get_flip_self, hcontrol]
    cases target.get x <;> rfl
  · rw [cnotStep, if_neg hcontrol]
    simp [hcontrol]

/-- CNOT preserves the readout of any encoded bit whose wire is not the
target wire. -/
theorem cnotStep_get_of_target_ne (control target observed : EncodedBit encoding)
    (hne : target.wire ≠ observed.wire) (x : Data) :
    observed.get (cnotStep control target x) = observed.get x := by
  unfold cnotStep
  by_cases hcontrol : control.get x
  · simp [hcontrol, get_flip_of_wire_ne target observed hne]
  · simp [hcontrol]

/-- Toffoli toggles its target readout exactly when both control readouts are
true. -/
theorem toffoliStep_get_target
    (controlA controlB target : EncodedBit encoding) (x : Data) :
    target.get (toffoliStep controlA controlB target x) =
      (target.get x ^^ (controlA.get x && controlB.get x)) := by
  by_cases hcontrols : controlA.get x && controlB.get x
  · rw [toffoliStep, if_pos hcontrols, get_flip_self, hcontrols]
    cases target.get x <;> rfl
  · rw [toffoliStep, if_neg hcontrols]
    simp [hcontrols]

/-- Toffoli preserves the readout of any encoded bit whose wire is not the
target wire. -/
theorem toffoliStep_get_of_target_ne
    (controlA controlB target observed : EncodedBit encoding)
    (hne : target.wire ≠ observed.wire) (x : Data) :
    observed.get (toffoliStep controlA controlB target x) =
      observed.get x := by
  unfold toffoliStep
  by_cases hcontrols : controlA.get x && controlB.get x
  · simp [hcontrols, get_flip_of_wire_ne target observed hne]
  · simp [hcontrols]

/-- Relabel an encoded bit along an equivalence of semantic label types. -/
def relabel {Other : Type} (bit : EncodedBit encoding) (layout : Other ≃ Data) :
    EncodedBit (encoding.relabel layout) where
  wire := bit.wire
  get := fun x => bit.get (layout x)
  flip := fun x => layout.symm (bit.flip (layout x))
  get_eq := by
    intro x
    simpa [BinaryLabelEncoding.relabel] using bit.get_eq (layout x)
  encode_flip := by
    intro x
    simpa [BinaryLabelEncoding.relabel] using bit.encode_flip (layout x)

/-- One addressed X/NOT gate realizes the semantic flip for an encoded bit. -/
theorem x_realizes (bit : EncodedBit encoding) :
    BaseGateProgram.Realizes encoding (BaseGateProgram.x bit.wire) bit.flip where
  applyLabel_eq := by
    intro x
    simpa [BaseGateProgram.applyLabel_x] using (bit.encode_flip x).symm

/-- One addressed CNOT gate realizes semantic controlled flip for encoded bits. -/
theorem cnot_realizes (control target : EncodedBit encoding)
    (hct : control.wire ≠ target.wire) :
    BaseGateProgram.Realizes encoding
      (BaseGateProgram.cnot control.wire target.wire hct)
      (cnotStep control target) where
  applyLabel_eq := by
    intro x
    by_cases hcontrol : control.get x
    · simp [BaseGateProgram.applyLabel_cnot, WireAddress.cnotMap,
        control.get_eq x, cnotStep, hcontrol, target.encode_flip]
    · simp [BaseGateProgram.applyLabel_cnot, WireAddress.cnotMap,
        control.get_eq x, cnotStep, hcontrol]

/-- One addressed Toffoli gate realizes semantic double-controlled flip for
encoded bits. -/
theorem toffoli_realizes (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire) (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    BaseGateProgram.Realizes encoding
      (BaseGateProgram.toffoli controlA.wire controlB.wire target.wire hab ha hb)
      (toffoliStep controlA controlB target) where
  applyLabel_eq := by
    intro x
    by_cases hcontrols : controlA.get x && controlB.get x
    · simp [BaseGateProgram.applyLabel_toffoli, WireAddress.toffoliMap,
        controlA.get_eq x, controlB.get_eq x, toffoliStep, hcontrols,
        target.encode_flip]
    · simp [BaseGateProgram.applyLabel_toffoli, WireAddress.toffoliMap,
        controlA.get_eq x, controlB.get_eq x, toffoliStep, hcontrols]

/-- Same-Circuit witness for the X/NOT semantic flip of an encoded bit. -/
def xWitness (bit : EncodedBit encoding) :
    BaseGateSameCircuitWitness Data bit.flip where
  encoding := encoding
  program := BaseGateProgram.x bit.wire
  realizes := x_realizes bit

/-- Same-Circuit witness for the CNOT semantic controlled flip of encoded bits. -/
def cnotWitness (control target : EncodedBit encoding)
    (hct : control.wire ≠ target.wire) :
    BaseGateSameCircuitWitness Data (cnotStep control target) where
  encoding := encoding
  program := BaseGateProgram.cnot control.wire target.wire hct
  realizes := cnot_realizes control target hct

/-- Same-Circuit witness for the Toffoli semantic double-controlled flip of
encoded bits. -/
def toffoliWitness (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire) (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    BaseGateSameCircuitWitness Data (toffoliStep controlA controlB target) where
  encoding := encoding
  program := BaseGateProgram.toffoli controlA.wire controlB.wire target.wire
    hab ha hb
  realizes := toffoli_realizes controlA controlB target hab ha hb

/-- Flipping an encoded bit twice restores the semantic state. -/
theorem flip_flip (bit : EncodedBit encoding) (x : Data) :
    bit.flip (bit.flip x) = x := by
  apply encoding.encode_injective
  rw [bit.encode_flip, bit.encode_flip, WireAddress.flipBit_flipBit]

/-- Semantic flips of encoded bits commute. -/
theorem flip_comm (left right : EncodedBit encoding) (x : Data) :
    left.flip (right.flip x) = right.flip (left.flip x) := by
  apply encoding.encode_injective
  rw [left.encode_flip, right.encode_flip, right.encode_flip,
    left.encode_flip, WireAddress.flipBit_comm]

/-- A semantic CNOT step is self-inverse. -/
theorem cnotStep_cnotStep
    (control target : EncodedBit encoding)
    (hct : control.wire ≠ target.wire) (x : Data) :
    cnotStep control target (cnotStep control target x) = x := by
  unfold cnotStep
  by_cases hcontrol : control.get x
  · rw [if_pos hcontrol]
    have hcontrol' : control.get (target.flip x) = true := by
      rw [get_flip_of_wire_ne target control (Ne.symm hct), hcontrol]
    rw [if_pos hcontrol']
    exact flip_flip target x
  · rw [if_neg hcontrol]
    rw [if_neg hcontrol]

/-- A semantic Toffoli step is self-inverse. -/
theorem toffoliStep_toffoliStep
    (controlA controlB target : EncodedBit encoding)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) (x : Data) :
    toffoliStep controlA controlB target
        (toffoliStep controlA controlB target x) = x := by
  have ha' : controlA.get (target.flip x) = controlA.get x := by
    rw [get_flip_of_wire_ne target controlA (Ne.symm ha)]
  have hb' : controlB.get (target.flip x) = controlB.get x := by
    rw [get_flip_of_wire_ne target controlB (Ne.symm hb)]
  unfold toffoliStep
  cases hA : controlA.get x <;>
    cases hB : controlB.get x <;>
    simp [hA, hB, ha', hb', flip_flip]

/-- One semantic encoded-bit base-gate operation, carrying the wire-disjointness
proofs required by the addressed `BaseGateProgram` atom. -/
inductive GateSpec (encoding : BinaryLabelEncoding Data) where
  /-- Flip one encoded semantic bit. -/
  | x (target : EncodedBit encoding)
  /-- Controlled flip between two encoded semantic bits. -/
  | cnot (control target : EncodedBit encoding)
      (hct : control.wire ≠ target.wire)
  /-- Double-controlled flip between three encoded semantic bits. -/
  | toffoli (controlA controlB target : EncodedBit encoding)
      (hab : controlA.wire ≠ controlB.wire)
      (ha : controlA.wire ≠ target.wire)
      (hb : controlB.wire ≠ target.wire)

namespace GateSpec

/-- Wire-addressed base-gate program for one encoded-bit operation. -/
def program : GateSpec encoding → BaseGateProgram encoding.width
  | x target => BaseGateProgram.x target.wire
  | cnot control target hct =>
      BaseGateProgram.cnot control.wire target.wire hct
  | toffoli controlA controlB target hab ha hb =>
      BaseGateProgram.toffoli controlA.wire controlB.wire target.wire hab ha hb

/-- Semantic action of one encoded-bit operation. -/
def step : GateSpec encoding → Data → Data
  | x target => target.flip
  | cnot control target _hct => cnotStep control target
  | toffoli controlA controlB target _hab _ha _hb =>
      toffoliStep controlA controlB target

/-- Every encoded-bit gate-spec semantic step is self-inverse. -/
theorem step_step (gate : GateSpec encoding) (x : Data) :
    gate.step (gate.step x) = x := by
  cases gate with
  | x target =>
      exact EncodedBit.flip_flip target x
  | cnot control target hct =>
      exact EncodedBit.cnotStep_cnotStep control target hct x
  | toffoli controlA controlB target _hab ha hb =>
      exact EncodedBit.toffoliStep_toffoliStep controlA controlB target ha hb x

/-- A gate preserves a projection when its target flip preserves that
projection.  Controls may be inspected, but only the target bit is written. -/
def targetFlipPreserves {α : Type} (project : Data → α) :
    GateSpec encoding → Prop
  | x target => ∀ y, project (target.flip y) = project y
  | cnot _ target _ => ∀ y, project (target.flip y) = project y
  | toffoli _ _ target _ _ _ => ∀ y, project (target.flip y) = project y

/-- One encoded-bit operation preserves a projection if its target flip
preserves that projection. -/
theorem step_preserves_of_targetFlipPreserves {α : Type}
    {project : Data → α} (gate : GateSpec encoding)
    (h : targetFlipPreserves project gate) (x : Data) :
    project (gate.step x) = project x := by
  cases gate with
  | x target =>
      exact h x
  | cnot control target hct =>
      unfold step cnotStep
      by_cases hcontrol : control.get x
      · simpa [hcontrol] using h x
      · simp [hcontrol]
  | toffoli controlA controlB target hab ha hb =>
      unfold step toffoliStep
      by_cases hcontrols : controlA.get x && controlB.get x
      · simpa [hcontrols] using h x
      · simp [hcontrols]

/-- A gate is wire-disjoint from an observed bit when the observed wire is none
of the wires the gate reads or writes. -/
def bitDisjoint (observed : EncodedBit encoding) :
    GateSpec encoding -> Prop
  | x target => target.wire ≠ observed.wire
  | cnot control target _ =>
      control.wire ≠ observed.wire ∧ target.wire ≠ observed.wire
  | toffoli controlA controlB target _ _ _ =>
      controlA.wire ≠ observed.wire ∧ controlB.wire ≠ observed.wire ∧
        target.wire ≠ observed.wire

/-- A gate whose read/write wires are disjoint from an observed bit commutes
with flipping that observed bit. -/
theorem step_flip_comm_of_bitDisjoint
    (gate : GateSpec encoding) (observed : EncodedBit encoding)
    (h : bitDisjoint observed gate) (x : Data) :
    gate.step (observed.flip x) =
      observed.flip (gate.step x) := by
  cases gate with
  | x target =>
      exact EncodedBit.flip_comm target observed x
  | cnot control target _hct =>
      rcases h with ⟨hcontrol, _htarget⟩
      have hcontrolGet :
          control.get (observed.flip x) = control.get x := by
        rw [EncodedBit.get_flip_of_wire_ne observed control
          (Ne.symm hcontrol)]
      change EncodedBit.cnotStep control target (observed.flip x) =
        observed.flip (EncodedBit.cnotStep control target x)
      unfold EncodedBit.cnotStep
      rw [hcontrolGet]
      by_cases hc : control.get x
      · simp [hc, EncodedBit.flip_comm target observed x]
      · simp [hc]
  | toffoli controlA controlB target _hab _ha _hb =>
      rcases h with ⟨hcontrolA, hcontrolB, _htarget⟩
      have hcontrolAGet :
          controlA.get (observed.flip x) = controlA.get x := by
        rw [EncodedBit.get_flip_of_wire_ne observed controlA
          (Ne.symm hcontrolA)]
      have hcontrolBGet :
          controlB.get (observed.flip x) = controlB.get x := by
        rw [EncodedBit.get_flip_of_wire_ne observed controlB
          (Ne.symm hcontrolB)]
      change EncodedBit.toffoliStep controlA controlB target
          (observed.flip x) =
        observed.flip (EncodedBit.toffoliStep controlA controlB target x)
      unfold EncodedBit.toffoliStep
      rw [hcontrolAGet, hcontrolBGet]
      by_cases hc : controlA.get x && controlB.get x
      · simp [hc, EncodedBit.flip_comm target observed x]
      · simp [hc]

/-- A gate whose read/write wires are disjoint from an observed bit preserves
that bit's readout. -/
theorem step_get_of_bitDisjoint
    (gate : GateSpec encoding) (observed : EncodedBit encoding)
    (h : bitDisjoint observed gate) (x : Data) :
    observed.get (gate.step x) = observed.get x := by
  cases gate with
  | x target =>
      exact EncodedBit.get_flip_of_wire_ne target observed h x
  | cnot control target _hct =>
      exact EncodedBit.cnotStep_get_of_target_ne control target observed h.2 x
  | toffoli controlA controlB target _hab _ha _hb =>
      exact EncodedBit.toffoliStep_get_of_target_ne
        controlA controlB target observed h.2.2 x

/-- One encoded-bit operation realizes its semantic action. -/
theorem realizes (gate : GateSpec encoding) :
    BaseGateProgram.Realizes encoding gate.program gate.step := by
  cases gate with
  | x target =>
      exact x_realizes target
  | cnot control target hct =>
      exact cnot_realizes control target hct
  | toffoli controlA controlB target hab ha hb =>
      exact toffoli_realizes controlA controlB target hab ha hb

/-- Wire-addressed base-gate program for a list of encoded-bit operations, in
list execution order. -/
def programList : List (GateSpec encoding) → BaseGateProgram encoding.width
  | [] => []
  | gate :: rest => BaseGateProgram.append gate.program (programList rest)

/-- Semantic action of a list of encoded-bit operations, in list execution
order. -/
def stepList : List (GateSpec encoding) → Data → Data
  | [] => id
  | gate :: rest => fun x => stepList rest (gate.step x)

/-- A gate list preserves a projection if every gate target flip preserves it. -/
theorem stepList_preserves_of_targetFlipPreserves {α : Type}
    {project : Data → α} (gates : List (GateSpec encoding))
    (h :
      ∀ gate, gate ∈ gates → targetFlipPreserves project gate)
    (x : Data) :
    project (stepList gates x) = project x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change project (stepList rest (gate.step x)) = project x
      calc
        project (stepList rest (gate.step x)) = project (gate.step x) :=
          ih (fun next hnext => h next (by simp [hnext])) (gate.step x)
        _ = project x :=
          step_preserves_of_targetFlipPreserves gate (h gate (by simp)) x

/-- A gate list whose read/write wires are all disjoint from an observed bit
commutes with flipping that observed bit. -/
theorem stepList_flip_comm_of_bitDisjoint
    (gates : List (GateSpec encoding)) (observed : EncodedBit encoding)
    (h : ∀ gate, gate ∈ gates -> bitDisjoint observed gate)
    (x : Data) :
    stepList gates (observed.flip x) =
      observed.flip (stepList gates x) := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change stepList rest (gate.step (observed.flip x)) =
        observed.flip (stepList rest (gate.step x))
      rw [step_flip_comm_of_bitDisjoint gate observed (h gate (by simp)) x]
      exact ih (fun next hnext => h next (by simp [hnext])) (gate.step x)

/-- Splitting a gate list at append corresponds to sequential semantic
composition in list execution order. -/
theorem stepList_append (first second : List (GateSpec encoding)) (x : Data) :
    stepList (first ++ second) x = stepList second (stepList first x) := by
  induction first generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [stepList, ih]

/-- Reversing a gate list gives a right inverse for its semantic step. -/
theorem stepList_reverse_stepList
    (gates : List (GateSpec encoding)) (x : Data) :
    stepList gates.reverse (stepList gates x) = x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp only [List.reverse_cons]
      rw [stepList_append]
      change gate.step (stepList rest.reverse (stepList rest (gate.step x))) = x
      rw [ih (gate.step x)]
      exact step_step gate x

/-- The recursive gate-list semantics agrees with a left fold over gates. -/
theorem stepList_eq_foldl (gates : List (GateSpec encoding)) (x : Data) :
    stepList gates x = gates.foldl (fun y gate => gate.step y) x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [stepList, ih]

/-- A list of encoded-bit operations realizes its folded semantic action. -/
theorem realizesList (gates : List (GateSpec encoding)) :
    BaseGateProgram.Realizes encoding (programList gates) (stepList gates) := by
  induction gates with
  | nil =>
      simpa [programList, stepList] using BaseGateProgram.Realizes.id encoding
  | cons gate rest ih =>
      simpa [programList, stepList] using
        BaseGateProgram.Realizes.append
          (firstStep := gate.step) (secondStep := stepList rest)
          (realizes gate) ih

/-- A gate list realizes any step pointwise equal to its folded semantic
action. -/
theorem realizesList_congrStep (gates : List (GateSpec encoding))
    {step : Data -> Data}
    (hstep : ∀ x, stepList gates x = step x) :
    BaseGateProgram.Realizes encoding (programList gates) step where
  applyLabel_eq := by
    intro x
    rw [(realizesList gates).applyLabel_eq x]
    rw [hstep x]

/-- Same-Circuit witness for a list of encoded-bit operations. -/
def witnessList (gates : List (GateSpec encoding)) :
    BaseGateSameCircuitWitness Data (stepList gates) where
  encoding := encoding
  program := programList gates
  realizes := realizesList gates

/-- A clean-work controlled version of one encoded-bit gate.  X becomes CNOT,
CNOT becomes Toffoli, and Toffoli is implemented by compute-control-uncompute
through the supplied work bit. -/
def controlledWithWorkGates
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    List (GateSpec encoding) :=
  match gate with
  | x target =>
      [GateSpec.cnot control target (Ne.symm hcontrol)]
  | cnot source target hsourceTarget =>
      [GateSpec.toffoli control source target (Ne.symm hcontrol.1)
        (Ne.symm hcontrol.2) hsourceTarget]
  | toffoli sourceA sourceB target hsourceAB _hsourceATarget _hsourceBTarget =>
      [ GateSpec.toffoli sourceA sourceB work
          hsourceAB hwork.1 hwork.2.1
      , GateSpec.toffoli control work target
          hcontrolWork (Ne.symm hcontrol.2.2) (Ne.symm hwork.2.2)
      , GateSpec.toffoli sourceA sourceB work
          hsourceAB hwork.1 hwork.2.1 ]

/-- Semantic action of `controlledWithWorkGates`. -/
def controlledWithWorkStep
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    Data -> Data :=
  stepList (controlledWithWorkGates control work gate hcontrol hwork
    hcontrolWork)

/-- Same-Circuit witness for one clean-work controlled encoded-bit gate. -/
def controlledWithWorkWitness
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    BaseGateSameCircuitWitness Data
      (controlledWithWorkStep control work gate hcontrol hwork
        hcontrolWork) :=
  witnessList (controlledWithWorkGates control work gate hcontrol hwork
    hcontrolWork)

/-- If the extra control is false, the clean-work controlled gate is a no-op. -/
theorem controlledWithWorkStep_eq_self_of_control_false
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolFalse : control.get x = false) :
    controlledWithWorkStep control work gate hcontrol hwork hcontrolWork x =
      x := by
  cases gate with
  | x target =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.cnotStep, hcontrolFalse]
  | cnot source target hsourceTarget =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.toffoliStep, hcontrolFalse]
  | toffoli sourceA sourceB target hsourceAB hsourceATarget hsourceBTarget =>
      simp only [controlledWithWorkStep, controlledWithWorkGates, stepList,
        step, id_eq]
      let y := EncodedBit.toffoliStep sourceA sourceB work x
      have hcontrolY : control.get y = false := by
        dsimp [y]
        rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
          control (Ne.symm hcontrolWork)]
        exact hcontrolFalse
      change
        EncodedBit.toffoliStep sourceA sourceB work
          (EncodedBit.toffoliStep control work target y) = x
      have hmiddle : EncodedBit.toffoliStep control work target y = y := by
        unfold EncodedBit.toffoliStep
        rw [if_neg (by simp [hcontrolY])]
      rw [hmiddle]
      dsimp [y]
      exact EncodedBit.toffoliStep_toffoliStep sourceA sourceB work
        hwork.1 hwork.2.1 x

/-- If the extra control is true and the work bit starts clean, the clean-work
controlled gate acts like the original gate. -/
theorem controlledWithWorkStep_eq_step_of_control_true
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolTrue : control.get x = true)
    (hworkClean : work.get x = false) :
    controlledWithWorkStep control work gate hcontrol hwork hcontrolWork x =
      gate.step x := by
  cases gate with
  | x target =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.cnotStep, hcontrolTrue]
  | cnot source target hsourceTarget =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.cnotStep, EncodedBit.toffoliStep, hcontrolTrue]
  | toffoli sourceA sourceB target hsourceAB hsourceATarget hsourceBTarget =>
      simp only [controlledWithWorkStep, controlledWithWorkGates, stepList,
        step, id_eq]
      let y := EncodedBit.toffoliStep sourceA sourceB work x
      have hcontrolY : control.get y = true := by
        dsimp [y]
        rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
          control (Ne.symm hcontrolWork)]
        exact hcontrolTrue
      have hworkY :
          work.get y = (sourceA.get x && sourceB.get x) := by
        dsimp [y]
        rw [EncodedBit.toffoliStep_get_target]
        cases sourceA.get x <;> cases sourceB.get x <;> simp [hworkClean]
      change
        EncodedBit.toffoliStep sourceA sourceB work
          (EncodedBit.toffoliStep control work target y) =
        EncodedBit.toffoliStep sourceA sourceB target x
      by_cases hcontrols : sourceA.get x && sourceB.get x
      · have hmiddle :
            EncodedBit.toffoliStep control work target y = target.flip y := by
          unfold EncodedBit.toffoliStep
          rw [if_pos (by simp [hcontrolY, hworkY, hcontrols])]
        have htargetWork :
            EncodedBit.toffoliStep sourceA sourceB work (target.flip y) =
              work.flip (target.flip y) := by
          unfold EncodedBit.toffoliStep
          have ha :
              sourceA.get (target.flip y) = sourceA.get x := by
            rw [EncodedBit.get_flip_of_wire_ne target sourceA
              (Ne.symm hsourceATarget)]
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceA (Ne.symm hwork.1)]
          have hb :
              sourceB.get (target.flip y) = sourceB.get x := by
            rw [EncodedBit.get_flip_of_wire_ne target sourceB
              (Ne.symm hsourceBTarget)]
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceB (Ne.symm hwork.2.1)]
          rw [if_pos (by simpa [ha, hb] using hcontrols)]
        have horig :
            EncodedBit.toffoliStep sourceA sourceB target x =
              target.flip x := by
          unfold EncodedBit.toffoliStep
          rw [if_pos hcontrols]
        rw [hmiddle, htargetWork, horig]
        rw [EncodedBit.flip_comm work target y]
        have hworkUndo : work.flip y = x := by
          have hsourceAY : sourceA.get y = sourceA.get x := by
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceA (Ne.symm hwork.1)]
          have hsourceBY : sourceB.get y = sourceB.get x := by
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceB (Ne.symm hwork.2.1)]
          have hcontrolsY : sourceA.get y && sourceB.get y := by
            simpa [hsourceAY, hsourceBY] using hcontrols
          have htoffoliY :
              EncodedBit.toffoliStep sourceA sourceB work y =
                work.flip y := by
            unfold EncodedBit.toffoliStep
            rw [if_pos hcontrolsY]
          rw [← htoffoliY]
          dsimp [y]
          exact EncodedBit.toffoliStep_toffoliStep sourceA sourceB work
            hwork.1 hwork.2.1 x
        rw [hworkUndo]
      · have hmiddle :
            EncodedBit.toffoliStep control work target y = y := by
          unfold EncodedBit.toffoliStep
          rw [if_neg (by simp [hcontrolY, hworkY, hcontrols])]
        rw [hmiddle]
        have houter :
            EncodedBit.toffoliStep sourceA sourceB work y = x := by
          dsimp [y]
          exact EncodedBit.toffoliStep_toffoliStep sourceA sourceB work
            hwork.1 hwork.2.1 x
        have horig :
            EncodedBit.toffoliStep sourceA sourceB target x = x := by
          unfold EncodedBit.toffoliStep
          rw [if_neg hcontrols]
        rw [houter, horig]

/-- Clean-work controlled version of a list of encoded-bit gates. -/
def controlledListWithWorkGates
    (control work : EncodedBit encoding) :
    (gates : List (GateSpec encoding)) ->
    (∀ gate, gate ∈ gates -> bitDisjoint control gate) ->
    (∀ gate, gate ∈ gates -> bitDisjoint work gate) ->
    (hcontrolWork : control.wire ≠ work.wire) ->
    List (GateSpec encoding)
  | [], _hcontrol, _hwork, _hcontrolWork => []
  | gate :: rest, hcontrol, hwork, hcontrolWork =>
      controlledWithWorkGates control work gate
        (hcontrol gate (by simp)) (hwork gate (by simp)) hcontrolWork ++
      controlledListWithWorkGates control work rest
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))
        hcontrolWork

/-- Semantic action of a clean-work controlled gate list. -/
def controlledListWithWorkStep
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    Data -> Data :=
  stepList (controlledListWithWorkGates control work gates hcontrol hwork
    hcontrolWork)

/-- Same-Circuit witness for a clean-work controlled gate list. -/
def controlledListWithWorkWitness
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    BaseGateSameCircuitWitness Data
      (controlledListWithWorkStep control work gates hcontrol hwork
        hcontrolWork) :=
  witnessList (controlledListWithWorkGates control work gates hcontrol hwork
    hcontrolWork)

/-- If the extra control is false, the clean-work controlled gate list is a
no-op. -/
theorem controlledListWithWorkStep_eq_self_of_control_false
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolFalse : control.get x = false) :
    controlledListWithWorkStep control work gates hcontrol hwork
      hcontrolWork x = x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        stepList
          (controlledWithWorkGates control work gate
              (hcontrol gate (by simp)) (hwork gate (by simp))
              hcontrolWork ++
            controlledListWithWorkGates control work rest
              (fun next hnext => hcontrol next (by simp [hnext]))
              (fun next hnext => hwork next (by simp [hnext]))
              hcontrolWork) x = x
      rw [stepList_append]
      have hhead :
          stepList
              (controlledWithWorkGates control work gate
                (hcontrol gate (by simp)) (hwork gate (by simp))
                hcontrolWork) x = x := by
        simpa [controlledWithWorkStep] using
          controlledWithWorkStep_eq_self_of_control_false control work gate
            (hcontrol gate (by simp)) (hwork gate (by simp))
            hcontrolWork x hcontrolFalse
      rw [hhead]
      exact ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))
        x hcontrolFalse

/-- If the extra control is true and the work bit starts clean, the clean-work
controlled gate list acts like the original gate list. -/
theorem controlledListWithWorkStep_eq_stepList_of_control_true
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolTrue : control.get x = true)
    (hworkClean : work.get x = false) :
    controlledListWithWorkStep control work gates hcontrol hwork
      hcontrolWork x = stepList gates x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        stepList
          (controlledWithWorkGates control work gate
              (hcontrol gate (by simp)) (hwork gate (by simp))
              hcontrolWork ++
            controlledListWithWorkGates control work rest
              (fun next hnext => hcontrol next (by simp [hnext]))
              (fun next hnext => hwork next (by simp [hnext]))
              hcontrolWork) x =
        stepList rest (gate.step x)
      rw [stepList_append]
      have hhead :
          stepList
              (controlledWithWorkGates control work gate
                (hcontrol gate (by simp)) (hwork gate (by simp))
                hcontrolWork) x = gate.step x := by
        simpa [controlledWithWorkStep] using
          controlledWithWorkStep_eq_step_of_control_true control work gate
            (hcontrol gate (by simp)) (hwork gate (by simp))
            hcontrolWork x hcontrolTrue hworkClean
      rw [hhead]
      have hcontrolNext : control.get (gate.step x) = true := by
        rw [step_get_of_bitDisjoint gate control (hcontrol gate (by simp)) x]
        exact hcontrolTrue
      have hworkNext : work.get (gate.step x) = false := by
        rw [step_get_of_bitDisjoint gate work (hwork gate (by simp)) x]
        exact hworkClean
      exact ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))
        (gate.step x) hcontrolNext hworkNext

end GateSpec

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
    BaseGateProgram encoding.width :=
  GateSpec.programList (swapGates left right hleftRight)

/-- Folded semantic action of the three-CNOT bit swap. -/
def swapStep
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    Data -> Data :=
  GateSpec.stepList (swapGates left right hleftRight)

/-- The bit-swap base-gate program realizes its folded semantics. -/
theorem swap_realizes
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    BaseGateProgram.Realizes encoding
      (swapProgram left right hleftRight)
      (swapStep left right hleftRight) :=
  GateSpec.realizesList (swapGates left right hleftRight)

/-- Same-Circuit witness for swapping two encoded bits. -/
def swapWitness
    (left right : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire) :
    BaseGateSameCircuitWitness Data (swapStep left right hleftRight) where
  encoding := encoding
  program := swapProgram left right hleftRight
  realizes := swap_realizes left right hleftRight

/-- A three-CNOT bit swap returns the original right readout on the left. -/
theorem swapStep_get_left
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
theorem swapStep_get_right
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
theorem swapStep_get_observed_of_swap_ne
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

/-- Base-gate program for a controlled swap of two encoded bits. -/
def controlledSwapProgram
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList
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
theorem controlledSwap_realizes
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    BaseGateProgram.Realizes encoding
      (controlledSwapProgram control left right
        hcontrolLeft hcontrolRight hleftRight)
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) :=
  GateSpec.realizesList
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Same-Circuit witness for a controlled swap of two encoded bits. -/
def controlledSwapWitness
    (control left right : EncodedBit encoding)
    (hcontrolLeft : control.wire ≠ left.wire)
    (hcontrolRight : control.wire ≠ right.wire)
    (hleftRight : left.wire ≠ right.wire) :
    BaseGateSameCircuitWitness Data
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) where
  encoding := encoding
  program :=
    controlledSwapProgram control left right
      hcontrolLeft hcontrolRight hleftRight
  realizes :=
    controlledSwap_realizes control left right
      hcontrolLeft hcontrolRight hleftRight

/-- A controlled bit swap preserves the control readout. -/
theorem controlledSwapStep_get_control
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
theorem controlledSwapStep_get_left
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
theorem controlledSwapStep_get_right
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
theorem controlledSwapStep_get_observed_of_swap_ne
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

/-- A fixed-width semantic word represented by encoded bit lenses over one
shared binary label encoding.  This records only the bit-level accessors; word
arithmetic semantics are supplied by the arithmetic modules that instantiate
the lenses. -/
structure Word (encoding : BinaryLabelEncoding Data) (width : Nat) where
  /-- Semantic bit lens for one word position. -/
  bit : Fin width → EncodedBit encoding

namespace Word

variable {width : Nat}

/-- The lower endpoint of an adjacent pair inside a word. -/
def adjacentLeftIndex (width : Nat) (i : Fin (width - 1)) : Fin width :=
  ⟨i.val, by omega⟩

/-- The upper endpoint of an adjacent pair inside a word. -/
def adjacentRightIndex (width : Nat) (i : Fin (width - 1)) : Fin width :=
  ⟨i.val + 1, by omega⟩

/-- Adjacent endpoints are distinct. -/
theorem adjacentLeftIndex_ne_adjacentRightIndex
    (width : Nat) (i : Fin (width - 1)) :
    adjacentLeftIndex width i ≠ adjacentRightIndex width i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [adjacentLeftIndex, adjacentRightIndex] at hv
  omega

/-- CNOT gates that xor each source word bit into the corresponding target
word bit. -/
def xorIntoGates (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    List (GateSpec encoding) :=
  List.ofFn fun i => GateSpec.cnot (source.bit i) (target.bit i) (hdisjoint i)

/-- Base-gate program for bitwise xor from one encoded word into another. -/
def xorIntoProgram (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList (xorIntoGates source target hdisjoint)

/-- Semantic action of the bitwise xor-into program. -/
def xorIntoStep (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    Data → Data :=
  GateSpec.stepList (xorIntoGates source target hdisjoint)

/-- The bitwise xor-into program realizes its folded semantic action. -/
theorem xorInto_realizes (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    BaseGateProgram.Realizes encoding
      (xorIntoProgram source target hdisjoint)
      (xorIntoStep source target hdisjoint) :=
  GateSpec.realizesList (xorIntoGates source target hdisjoint)

/-- Same-Circuit witness for bitwise xor from one encoded word into another. -/
def xorIntoWitness (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    BaseGateSameCircuitWitness Data (xorIntoStep source target hdisjoint) where
  encoding := encoding
  program := xorIntoProgram source target hdisjoint
  realizes := xorInto_realizes source target hdisjoint

/-- Folded semantic action for word xor over an explicit list of indices. -/
def xorIntoIndicesStep (source target : Word encoding width)
    (indices : List (Fin width)) : Data -> Data :=
  fun x =>
    indices.foldl
      (fun y i => cnotStep (source.bit i) (target.bit i) y) x

/-- The concrete `List.ofFn` word-xor gate list agrees with the indexed fold
semantics. -/
theorem xorIntoStep_eq_indicesStep (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    xorIntoStep source target hdisjoint =
      xorIntoIndicesStep source target (List.ofFn fun i : Fin width => i) := by
  funext x
  rw [xorIntoStep, xorIntoGates, xorIntoIndicesStep,
    GateSpec.stepList_eq_foldl]
  let gateOfIndex : Fin width -> GateSpec encoding := fun i =>
    GateSpec.cnot (source.bit i) (target.bit i) (hdisjoint i)
  change
    List.foldl (fun y gate => gate.step y) x (List.ofFn gateOfIndex) =
      List.foldl (fun y i => (gateOfIndex i).step y) x
        (List.ofFn fun i : Fin width => i)
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun i : Fin width => i).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun i : Fin width => i) gateOfIndex)]
  generalize List.ofFn (fun i : Fin width => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp [ih]

/-- A word-xor fold preserves any observed readout whose wire is distinct from
every folded target bit. -/
theorem xorIntoIndicesStep_get_observed_of_target_ne
    (source target : Word encoding width) (indices : List (Fin width))
    (observed : EncodedBit encoding)
    (hne : ∀ i, i ∈ indices -> (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get (xorIntoIndicesStep source target indices x) =
      observed.get x := by
  unfold xorIntoIndicesStep
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        observed.get
            (rest.foldl
              (fun y i => cnotStep (source.bit i) (target.bit i) y)
              (cnotStep (source.bit i) (target.bit i) x)) =
          observed.get x
      rw [ih]
      · exact cnotStep_get_of_target_ne (source.bit i) (target.bit i)
          observed (hne i (by simp)) x
      · intro j hj
        exact hne j (by simp [hj])

/-- A word-xor fold toggles a target bit exactly when its index is present in
the folded index list. -/
theorem xorIntoIndicesStep_get_target
    (source target : Word encoding width) (indices : List (Fin width))
    (hnodup : indices.Nodup) (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get (xorIntoIndicesStep source target indices x) =
      ((target.bit i).get x ^^
        (if i ∈ indices then (source.bit i).get x else false)) := by
  induction indices generalizing x with
  | nil =>
      simp [xorIntoIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold xorIntoIndicesStep at *
      change
        (target.bit i).get
            (rest.foldl
              (fun y j => cnotStep (source.bit j) (target.bit j) y)
              (cnotStep (source.bit j) (target.bit j) x)) =
          ((target.bit i).get x ^^
            (if i ∈ j :: rest then (source.bit i).get x else false))
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (target.bit i).get
                (rest.foldl
                  (fun y j => cnotStep (source.bit j) (target.bit j) y)
                  (cnotStep (source.bit i) (target.bit i) x)) =
              (target.bit i).get
                (cnotStep (source.bit i) (target.bit i) x) := by
          simpa [xorIntoIndicesStep] using
            xorIntoIndicesStep_get_observed_of_target_ne
              source target rest (target.bit i)
              (fun k hk =>
                htargetTarget k
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (cnotStep (source.bit i) (target.bit i) x)
        rw [hpreserve, cnotStep_get_target]
        simp [hjNotMem]
      · have htail := ih hrestNodup (cnotStep
            (source.bit j) (target.bit j) x)
        rw [htail]
        have htarget :
            (target.bit i).get
                (cnotStep (source.bit j) (target.bit j) x) =
              (target.bit i).get x :=
          cnotStep_get_of_target_ne (source.bit j) (target.bit j)
            (target.bit i) (htargetTarget j hji) x
        have hsource :
            (source.bit i).get
                (cnotStep (source.bit j) (target.bit j) x) =
              (source.bit i).get x :=
          cnotStep_get_of_target_ne (source.bit j) (target.bit j)
            (source.bit i) (htargetSource j) x
        rw [htarget, hsource]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest
        · simp [hji', himem]
        · simp [hji', himem]

/-- The complete word-xor fold preserves an observed readout whose wire is
distinct from every target bit. -/
theorem xorIntoStep_get_observed_of_target_ne
    (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (observed : EncodedBit encoding)
    (hne : ∀ i, (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get (xorIntoStep source target hdisjoint x) =
      observed.get x := by
  rw [xorIntoStep_eq_indicesStep]
  exact
    xorIntoIndicesStep_get_observed_of_target_ne
      source target (List.ofFn fun i : Fin width => i) observed
      (fun i _ => hne i) x

/-- The complete word-xor fold toggles each target bit by the corresponding
source bit. -/
theorem xorIntoStep_get_target
    (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get (xorIntoStep source target hdisjoint x) =
      ((target.bit i).get x ^^ (source.bit i).get x) := by
  rw [xorIntoStep_eq_indicesStep]
  have hnodup : (List.ofFn fun i : Fin width => i).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    xorIntoIndicesStep_get_target source target
      (List.ofFn fun j : Fin width => j) hnodup i htargetTarget
      htargetSource x

/-- Gates for swapping one adjacent pair of word bits. -/
def adjacentSwapGates
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    List (GateSpec encoding) :=
  EncodedBit.swapGates
    (word.bit (adjacentLeftIndex width i))
    (word.bit (adjacentRightIndex width i))
    (hword (adjacentLeftIndex width i) (adjacentRightIndex width i)
      (adjacentLeftIndex_ne_adjacentRightIndex width i))

/-- CNOT gate list for the cyclic shift obtained by sweeping adjacent swaps
from low index to high index. -/
def adjacentShiftLeftGates
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun i : Fin (width - 1) => i).flatMap
    (adjacentSwapGates word hword)

/-- CNOT gate list for the inverse cyclic shift, sweeping adjacent swaps from
high index back to low index. -/
def adjacentShiftRightGates
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (adjacentShiftLeftGates word hword).reverse

/-- Base-gate program for the adjacent-swap cyclic shift. -/
def adjacentShiftLeftProgram
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList (adjacentShiftLeftGates word hword)

/-- Folded semantic action for the adjacent-swap cyclic shift. -/
def adjacentShiftLeftStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList (adjacentShiftLeftGates word hword)

/-- Base-gate program for the inverse adjacent-swap cyclic shift. -/
def adjacentShiftRightProgram
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList (adjacentShiftRightGates word hword)

/-- Folded semantic action for the inverse adjacent-swap cyclic shift. -/
def adjacentShiftRightStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList (adjacentShiftRightGates word hword)

/-- Source-index permutation induced by executing adjacent swaps in list order.
If `p := adjacentSwapIndexPerm width indices`, then after running those swaps,
the readout at target index `i` is the original readout at source index
`p i`. -/
def adjacentSwapIndexPerm (width : Nat) :
    List (Fin (width - 1)) -> Equiv.Perm (Fin width)
  | [] => Equiv.refl _
  | i :: rest =>
      (adjacentSwapIndexPerm width rest).trans
        (Equiv.swap (adjacentLeftIndex width i) (adjacentRightIndex width i))

/-- Appending one adjacent-swap index composes that swap before the source
permutation represented by the preceding list. -/
theorem adjacentSwapIndexPerm_concat (width : Nat)
    (indices : List (Fin (width - 1))) (i : Fin (width - 1)) :
    adjacentSwapIndexPerm width (indices.concat i) =
      (Equiv.swap (adjacentLeftIndex width i) (adjacentRightIndex width i)).trans
        (adjacentSwapIndexPerm width indices) := by
  induction indices with
  | nil =>
      ext target
      simp [adjacentSwapIndexPerm]
  | cons j rest ih =>
      ext target
      simp only [List.concat_eq_append, List.cons_append, adjacentSwapIndexPerm,
        Equiv.trans_apply]
      rw [show adjacentSwapIndexPerm width (rest ++ [i]) target =
          adjacentSwapIndexPerm width rest
            ((Equiv.swap (adjacentLeftIndex width i)
              (adjacentRightIndex width i)) target) by
        simpa [List.concat_eq_append, Equiv.trans_apply] using
          congrArg (fun p : Equiv.Perm (Fin width) => p target) ih]

/-- Extending every adjacent-swap index by `Fin.castSucc` preserves the action
on non-last target indices. -/
theorem adjacentSwapIndexPerm_map_castSucc_apply_castSucc
    (tail : Nat) (indices : List (Fin tail)) (target : Fin tail.succ) :
    adjacentSwapIndexPerm tail.succ.succ (indices.map Fin.castSucc)
        (Fin.castSucc target) =
      Fin.castSucc (adjacentSwapIndexPerm tail.succ indices target) := by
  induction indices generalizing target with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.map_cons, adjacentSwapIndexPerm, Equiv.trans_apply]
      rw [ih]
      by_cases hleft :
          adjacentSwapIndexPerm tail.succ rest target =
            adjacentLeftIndex tail.succ i
      · rw [hleft]
        simp [adjacentLeftIndex, adjacentRightIndex]
      · by_cases hright :
          adjacentSwapIndexPerm tail.succ rest target =
            adjacentRightIndex tail.succ i
        · rw [hright]
          simp [adjacentLeftIndex, adjacentRightIndex]
        · rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
          rw [Equiv.swap_apply_of_ne_of_ne]
          · intro h
            apply hleft
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa [adjacentLeftIndex] using hv
          · intro h
            apply hright
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa [adjacentRightIndex] using hv

/-- Extending every adjacent-swap index by `Fin.castSucc` leaves the new last
target index fixed. -/
theorem adjacentSwapIndexPerm_map_castSucc_apply_last
    (tail : Nat) (indices : List (Fin tail)) :
    adjacentSwapIndexPerm tail.succ.succ (indices.map Fin.castSucc)
        (Fin.last tail.succ) =
      Fin.last tail.succ := by
  induction indices with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.map_cons, adjacentSwapIndexPerm, Equiv.trans_apply]
      rw [ih]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro h
        have hv := congrArg Fin.val h
        simp [adjacentLeftIndex] at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        simp [adjacentRightIndex] at hv
        omega

/-- The full low-to-high adjacent-swap sweep induces `finRotate` as its
source-index permutation on a nonempty word. -/
theorem adjacentSwapIndexPerm_ofFn_eq_finRotate_succ (tail : Nat) :
    adjacentSwapIndexPerm tail.succ
        (List.ofFn fun i : Fin tail =>
          (Fin.cast (by omega) i : Fin (tail.succ - 1))) =
      finRotate tail.succ := by
  induction tail with
  | zero =>
      ext target
      fin_cases target
      rfl
  | succ tail ih =>
      rw [show
          List.ofFn
              (fun i : Fin tail.succ =>
                (Fin.cast (by omega) i : Fin (tail.succ.succ - 1))) =
            (List.ofFn fun i : Fin tail =>
              (Fin.cast (by omega) (Fin.castSucc i) :
                Fin (tail.succ.succ - 1))).concat
              (Fin.cast (by omega) (Fin.last tail) :
                Fin (tail.succ.succ - 1)) by
        rw [List.ofFn_succ']]
      rw [adjacentSwapIndexPerm_concat]
      ext target
      have hih :
          adjacentSwapIndexPerm tail.succ (List.ofFn fun i : Fin tail => i) =
            finRotate tail.succ := by
        simpa using ih
      refine Fin.lastCases ?last ?cast target
      · have hq :=
          adjacentSwapIndexPerm_map_castSucc_apply_castSucc tail
            (List.ofFn fun i : Fin tail => i) (Fin.last tail)
        have hleft :
            adjacentLeftIndex (tail + 1).succ
                (Fin.cast (by omega) (Fin.last tail)) =
              Fin.castSucc (Fin.last tail) := by
          ext
          simp [adjacentLeftIndex]
        have hright :
            adjacentRightIndex (tail + 1).succ
                (Fin.cast (by omega) (Fin.last tail)) =
              Fin.last (tail + 1) := by
          ext
          simp [adjacentRightIndex]
        have hswap :
            (Equiv.swap
                (adjacentLeftIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail)))
                (adjacentRightIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail))))
              (Fin.last (tail + 1)) =
            Fin.castSucc (Fin.last tail) := by
          rw [hleft, hright, Equiv.swap_apply_right]
        rw [Equiv.trans_apply, hswap]
        have hih_last := congrArg
          (fun p : Equiv.Perm (Fin tail.succ) =>
            Fin.castSucc (p (Fin.last tail))) hih
        have hq' := hq.trans hih_last
        have hqv := congrArg (fun q : Fin (tail + 1 + 1) => q.val) hq'
        simpa [List.ofFn_comp', Function.comp_def, finRotate_last] using hqv
      · intro k
        by_cases hlast : k = Fin.last tail
        · subst k
          have hq :=
            adjacentSwapIndexPerm_map_castSucc_apply_last tail
              (List.ofFn fun i : Fin tail => i)
          have hleft :
              adjacentLeftIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail)) =
                Fin.castSucc (Fin.last tail) := by
            ext
            simp [adjacentLeftIndex]
          have hright :
              adjacentRightIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail)) =
                Fin.last (tail + 1) := by
            ext
            simp [adjacentRightIndex]
          have hswap :
              (Equiv.swap
                  (adjacentLeftIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)))
                  (adjacentRightIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail))))
                (Fin.castSucc (Fin.last tail)) =
              Fin.last (tail + 1) := by
            rw [hleft, hright, Equiv.swap_apply_left]
          rw [Equiv.trans_apply, hswap]
          have hqv := congrArg (fun q : Fin (tail + 1 + 1) => q.val) hq
          simpa [List.ofFn_comp', Function.comp_def] using hqv
        · have hq :=
            adjacentSwapIndexPerm_map_castSucc_apply_castSucc tail
              (List.ofFn fun i : Fin tail => i) k
          have hswap :
              (Equiv.swap
                  (adjacentLeftIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)))
                  (adjacentRightIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail))))
                (Fin.castSucc k) =
              Fin.castSucc k := by
            have hleft :
                adjacentLeftIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)) =
                  Fin.castSucc (Fin.last tail) := by
              ext
              simp [adjacentLeftIndex]
            have hright :
                adjacentRightIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)) =
                  Fin.last (tail + 1) := by
              ext
              simp [adjacentRightIndex]
            rw [hleft, hright]
            rw [Equiv.swap_apply_of_ne_of_ne]
            · intro h
              apply hlast
              exact Fin.castSucc_injective _ h
            · intro h
              have hv := congrArg Fin.val h
              simp at hv
              omega
          rw [Equiv.trans_apply, hswap]
          have hih_k := congrArg
            (fun p : Equiv.Perm (Fin tail.succ) => Fin.castSucc (p k)) hih
          have hq' := hq.trans hih_k
          have hqv := congrArg (fun q : Fin (tail + 1 + 1) => q.val) hq'
          have hkadd : ((k + 1 : Fin tail.succ) : Nat) = k.val + 1 := by
            exact Fin.val_add_one_of_lt (Fin.val_lt_last hlast)
          simpa [List.ofFn_comp', Function.comp_def, hkadd] using hqv

/-- The full low-to-high adjacent-swap sweep induces `finRotate` as its
source-index permutation. -/
theorem adjacentSwapIndexPerm_ofFn_eq_finRotate (width : Nat) :
    adjacentSwapIndexPerm width (List.ofFn fun i : Fin (width - 1) => i) =
      finRotate width := by
  cases width with
  | zero =>
      ext target
      exact Fin.elim0 target
  | succ tail =>
      simpa using adjacentSwapIndexPerm_ofFn_eq_finRotate_succ tail

/-- A single adjacent swap implements the corresponding source-index
permutation on word-bit readouts. -/
theorem adjacentSwapStep_get_indexPerm
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) (target : Fin width) (x : Data) :
    (word.bit target).get
        (EncodedBit.swapStep
          (word.bit (adjacentLeftIndex width i))
          (word.bit (adjacentRightIndex width i))
          (hword _ _ (adjacentLeftIndex_ne_adjacentRightIndex width i))
          x) =
      (word.bit
        ((Equiv.swap (adjacentLeftIndex width i) (adjacentRightIndex width i))
          target)).get x := by
  by_cases hleft : target = adjacentLeftIndex width i
  · subst target
    rw [EncodedBit.swapStep_get_left]
    simp
  · by_cases hright : target = adjacentRightIndex width i
    · subst target
      rw [EncodedBit.swapStep_get_right]
      simp
    · calc
        (word.bit target).get
            (EncodedBit.swapStep
              (word.bit (adjacentLeftIndex width i))
              (word.bit (adjacentRightIndex width i))
              (hword _ _ (adjacentLeftIndex_ne_adjacentRightIndex width i))
              x) =
          (word.bit target).get x := by
            exact EncodedBit.swapStep_get_observed_of_swap_ne
              (word.bit (adjacentLeftIndex width i))
              (word.bit (adjacentRightIndex width i))
              (word.bit target)
              (hword _ _ (adjacentLeftIndex_ne_adjacentRightIndex width i))
              (hword _ _ (Ne.symm hleft))
              (hword _ _ (Ne.symm hright))
              x
        _ =
          (word.bit
            ((Equiv.swap (adjacentLeftIndex width i)
              (adjacentRightIndex width i)) target)).get x := by
            simp [Equiv.swap_apply_of_ne_of_ne hleft hright]

/-- An indexed adjacent-swap gate list implements its source-index
permutation on word-bit readouts. -/
theorem adjacentSwapIndexListStep_get
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (indices : List (Fin (width - 1))) (target : Fin width) (x : Data) :
    (word.bit target).get
        (GateSpec.stepList (indices.flatMap (adjacentSwapGates word hword))
          x) =
      (word.bit (adjacentSwapIndexPerm width indices target)).get x := by
  induction indices generalizing target x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons, GateSpec.stepList_append]
      calc
        (word.bit target).get
            (GateSpec.stepList (rest.flatMap (adjacentSwapGates word hword))
              (GateSpec.stepList (adjacentSwapGates word hword i) x)) =
          (word.bit (adjacentSwapIndexPerm width rest target)).get
              (GateSpec.stepList (adjacentSwapGates word hword i) x) := by
            exact ih target (GateSpec.stepList (adjacentSwapGates word hword i)
              x)
        _ =
          (word.bit
              ((Equiv.swap (adjacentLeftIndex width i)
                (adjacentRightIndex width i))
                (adjacentSwapIndexPerm width rest target))).get x := by
            simpa [adjacentSwapGates, EncodedBit.swapStep] using
              adjacentSwapStep_get_indexPerm word hword i
                (adjacentSwapIndexPerm width rest target) x
        _ =
          (word.bit (adjacentSwapIndexPerm width (i :: rest) target)).get x :=
            rfl

/-- The low-to-high adjacent-swap cyclic shift implements the corresponding
source-index permutation on word-bit readouts. -/
theorem adjacentShiftLeftStep_get_indexPerm
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin width) (x : Data) :
    (word.bit target).get (adjacentShiftLeftStep word hword x) =
      (word.bit
        (adjacentSwapIndexPerm width
          (List.ofFn fun i : Fin (width - 1) => i) target)).get x := by
  simpa [adjacentShiftLeftStep, adjacentShiftLeftGates] using
    adjacentSwapIndexListStep_get word hword
      (List.ofFn fun i : Fin (width - 1) => i) target x

/-- The low-to-high adjacent-swap cyclic shift reads each non-last target from
the next higher source bit. -/
theorem adjacentShiftLeftStep_get_castSucc
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin tail) (x : Data) :
    (word.bit (Fin.castSucc target)).get
        (adjacentShiftLeftStep word hword x) =
      (word.bit target.succ).get x := by
  have h :=
    adjacentShiftLeftStep_get_indexPerm word hword (Fin.castSucc target) x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  simpa [finRotate_apply] using h

/-- The low-to-high adjacent-swap cyclic shift wraps the last target bit from
source bit zero. -/
theorem adjacentShiftLeftStep_get_last
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    (word.bit (Fin.last tail)).get (adjacentShiftLeftStep word hword x) =
      (word.bit 0).get x := by
  have h := adjacentShiftLeftStep_get_indexPerm word hword (Fin.last tail) x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  simpa [finRotate_last] using h

/-- The adjacent-swap cyclic-shift program realizes its folded semantics. -/
theorem adjacentShiftLeft_realizes
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram.Realizes encoding
      (adjacentShiftLeftProgram word hword)
      (adjacentShiftLeftStep word hword) :=
  GateSpec.realizesList (adjacentShiftLeftGates word hword)

/-- The inverse adjacent-swap cyclic-shift program realizes its folded
semantics. -/
theorem adjacentShiftRight_realizes
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram.Realizes encoding
      (adjacentShiftRightProgram word hword)
      (adjacentShiftRightStep word hword) :=
  GateSpec.realizesList (adjacentShiftRightGates word hword)

/-- Same-Circuit witness for the adjacent-swap cyclic shift. -/
def adjacentShiftLeftWitness
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateSameCircuitWitness Data (adjacentShiftLeftStep word hword) where
  encoding := encoding
  program := adjacentShiftLeftProgram word hword
  realizes := adjacentShiftLeft_realizes word hword

/-- Same-Circuit witness for the inverse adjacent-swap cyclic shift. -/
def adjacentShiftRightWitness
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateSameCircuitWitness Data (adjacentShiftRightStep word hword) where
  encoding := encoding
  program := adjacentShiftRightProgram word hword
  realizes := adjacentShiftRight_realizes word hword

/-- The inverse adjacent-swap cyclic shift undoes the low-to-high sweep. -/
theorem adjacentShiftRightStep_adjacentShiftLeftStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    adjacentShiftRightStep word hword
        (adjacentShiftLeftStep word hword x) =
      x := by
  simpa [adjacentShiftRightStep, adjacentShiftLeftStep,
    adjacentShiftRightGates] using
      GateSpec.stepList_reverse_stepList (adjacentShiftLeftGates word hword) x

/-- The low-to-high adjacent-swap cyclic shift undoes the inverse sweep. -/
theorem adjacentShiftLeftStep_adjacentShiftRightStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    adjacentShiftLeftStep word hword
        (adjacentShiftRightStep word hword x) =
      x := by
  have h :=
    GateSpec.stepList_reverse_stepList
      (gates := (adjacentShiftLeftGates word hword).reverse) x
  simpa [adjacentShiftRightStep, adjacentShiftLeftStep,
    adjacentShiftRightGates] using h

/-- The high-to-low inverse adjacent-swap cyclic shift implements the inverse
source-index permutation on word-bit readouts. -/
theorem adjacentShiftRightStep_get_indexPerm
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin width) (x : Data) :
    (word.bit target).get (adjacentShiftRightStep word hword x) =
      (word.bit
        ((adjacentSwapIndexPerm width
          (List.ofFn fun i : Fin (width - 1) => i)).symm target)).get x := by
  let p : Equiv.Perm (Fin width) :=
    adjacentSwapIndexPerm width (List.ofFn fun i : Fin (width - 1) => i)
  have h :=
    adjacentShiftLeftStep_get_indexPerm word hword (p.symm target)
      (adjacentShiftRightStep word hword x)
  rw [adjacentShiftLeftStep_adjacentShiftRightStep] at h
  simpa [p] using h.symm

/-- The high-to-low inverse adjacent-swap cyclic shift wraps target bit zero
from the last source bit. -/
theorem adjacentShiftRightStep_get_zero
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    (word.bit 0).get (adjacentShiftRightStep word hword x) =
      (word.bit (Fin.last tail)).get x := by
  have h := adjacentShiftRightStep_get_indexPerm word hword 0 x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  have hlast : (-1 : Fin tail.succ) = Fin.last tail := by
    ext
    simp [Fin.coe_neg_one]
  simpa [finRotate_symm_apply, hlast] using h

/-- The high-to-low inverse adjacent-swap cyclic shift reads each successor
target bit from the previous lower source bit. -/
theorem adjacentShiftRightStep_get_succ
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin tail) (x : Data) :
    (word.bit target.succ).get (adjacentShiftRightStep word hword x) =
      (word.bit (Fin.castSucc target)).get x := by
  have h := adjacentShiftRightStep_get_indexPerm word hword target.succ x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  have hpred : (target.succ - 1 : Fin tail.succ) = Fin.castSucc target := by
    ext
    simp [Fin.val_sub_one_of_ne_zero]
  simpa [finRotate_symm_apply, hpred] using h

/-- Gates for swapping one adjacent pair of word bits under a single encoded
control bit. -/
def controlledAdjacentSwapGates
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    List (GateSpec encoding) :=
  EncodedBit.controlledSwapGates control
    (word.bit (adjacentLeftIndex width i))
    (word.bit (adjacentRightIndex width i))
    (hcontrol (adjacentLeftIndex width i))
    (hcontrol (adjacentRightIndex width i))
    (hword (adjacentLeftIndex width i) (adjacentRightIndex width i)
      (adjacentLeftIndex_ne_adjacentRightIndex width i))

/-- Gate list for a single-control cyclic shift obtained by sweeping
controlled adjacent swaps from low index to high index. -/
def controlledAdjacentShiftLeftGates
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun i : Fin (width - 1) => i).flatMap
    (controlledAdjacentSwapGates control word hcontrol hword)

/-- Gate list for the inverse single-control cyclic shift, sweeping controlled
adjacent swaps from high index back to low index. -/
def controlledAdjacentShiftRightGates
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (controlledAdjacentShiftLeftGates control word hcontrol hword).reverse

/-- Base-gate program for the single-control adjacent-swap cyclic shift. -/
def controlledAdjacentShiftLeftProgram
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList
    (controlledAdjacentShiftLeftGates control word hcontrol hword)

/-- Folded semantic action for the single-control adjacent-swap cyclic shift. -/
def controlledAdjacentShiftLeftStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList
    (controlledAdjacentShiftLeftGates control word hcontrol hword)

/-- Base-gate program for the inverse single-control adjacent-swap cyclic
shift. -/
def controlledAdjacentShiftRightProgram
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList
    (controlledAdjacentShiftRightGates control word hcontrol hword)

/-- Folded semantic action for the inverse single-control adjacent-swap cyclic
shift. -/
def controlledAdjacentShiftRightStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList
    (controlledAdjacentShiftRightGates control word hcontrol hword)

/-- The single-control adjacent-swap cyclic-shift program realizes its folded
semantics. -/
theorem controlledAdjacentShiftLeft_realizes
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram.Realizes encoding
      (controlledAdjacentShiftLeftProgram control word hcontrol hword)
      (controlledAdjacentShiftLeftStep control word hcontrol hword) :=
  GateSpec.realizesList
    (controlledAdjacentShiftLeftGates control word hcontrol hword)

/-- The inverse single-control adjacent-swap cyclic-shift program realizes its
folded semantics. -/
theorem controlledAdjacentShiftRight_realizes
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateProgram.Realizes encoding
      (controlledAdjacentShiftRightProgram control word hcontrol hword)
      (controlledAdjacentShiftRightStep control word hcontrol hword) :=
  GateSpec.realizesList
    (controlledAdjacentShiftRightGates control word hcontrol hword)

/-- Same-Circuit witness for the single-control adjacent-swap cyclic shift. -/
def controlledAdjacentShiftLeftWitness
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateSameCircuitWitness Data
      (controlledAdjacentShiftLeftStep control word hcontrol hword) where
  encoding := encoding
  program := controlledAdjacentShiftLeftProgram control word hcontrol hword
  realizes := controlledAdjacentShiftLeft_realizes control word hcontrol hword

/-- Same-Circuit witness for the inverse single-control adjacent-swap cyclic
shift. -/
def controlledAdjacentShiftRightWitness
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    BaseGateSameCircuitWitness Data
      (controlledAdjacentShiftRightStep control word hcontrol hword) where
  encoding := encoding
  program := controlledAdjacentShiftRightProgram control word hcontrol hword
  realizes := controlledAdjacentShiftRight_realizes control word hcontrol hword

/-- The inverse single-control adjacent-swap cyclic shift undoes the
low-to-high controlled sweep. -/
theorem controlledAdjacentShiftRightStep_controlledAdjacentShiftLeftStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    controlledAdjacentShiftRightStep control word hcontrol hword
        (controlledAdjacentShiftLeftStep control word hcontrol hword x) =
      x := by
  simpa [controlledAdjacentShiftRightStep, controlledAdjacentShiftLeftStep,
    controlledAdjacentShiftRightGates] using
      GateSpec.stepList_reverse_stepList
        (controlledAdjacentShiftLeftGates control word hcontrol hword) x

/-- The low-to-high controlled sweep undoes the inverse single-control
adjacent-swap cyclic shift. -/
theorem controlledAdjacentShiftLeftStep_controlledAdjacentShiftRightStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    controlledAdjacentShiftLeftStep control word hcontrol hword
        (controlledAdjacentShiftRightStep control word hcontrol hword x) =
      x := by
  have h :=
    GateSpec.stepList_reverse_stepList
      (gates := (controlledAdjacentShiftLeftGates control word hcontrol
        hword).reverse) x
  simpa [controlledAdjacentShiftRightStep, controlledAdjacentShiftLeftStep,
    controlledAdjacentShiftRightGates] using h

/-- Three-Toffoli controlled swaps for every bit of two encoded words. -/
def controlledSwapGates (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun i : Fin width => i).flatMap fun i =>
    EncodedBit.controlledSwapGates control (left.bit i) (right.bit i)
      (hcontrolLeft i) (hcontrolRight i) (hleftRight i)

/-- Base-gate program for controlled bitwise swap of two encoded words. -/
def controlledSwapProgram (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Semantic action of controlled bitwise swap of two encoded words. -/
def controlledSwapStep (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    Data → Data :=
  GateSpec.stepList
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Folded semantic action for controlled word swap over an explicit list of
indices. -/
def controlledSwapIndicesStep (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) :
    Data -> Data :=
  fun x =>
    indices.foldl
      (fun y i =>
        EncodedBit.controlledSwapStep control (left.bit i) (right.bit i)
          (hcontrolLeft i) (hcontrolRight i) (hleftRight i) y) x

/-- The concrete word-swap gate list agrees with the indexed fold semantics. -/
theorem controlledSwapStep_eq_indicesStep (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight =
      controlledSwapIndicesStep control left right
        hcontrolLeft hcontrolRight hleftRight
        (List.ofFn fun i : Fin width => i) := by
  funext x
  rw [controlledSwapStep, controlledSwapGates, controlledSwapIndicesStep,
    GateSpec.stepList_eq_foldl]
  generalize List.ofFn (fun i : Fin width => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simpa [List.flatMap, EncodedBit.controlledSwapStep,
        GateSpec.stepList_eq_foldl] using
        ih
          (List.foldl (fun y gate => gate.step y) x
            (EncodedBit.controlledSwapGates control (left.bit i)
              (right.bit i) (hcontrolLeft i) (hcontrolRight i)
              (hleftRight i)))

/-- A controlled word-swap fold preserves any observed readout whose wire is
distinct from every folded left and right target bit. -/
theorem controlledSwapIndicesStep_get_observed_of_swap_ne
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (observed : EncodedBit encoding)
    (hleftObserved :
      ∀ i, i ∈ indices -> (left.bit i).wire ≠ observed.wire)
    (hrightObserved :
      ∀ i, i ∈ indices -> (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledSwapIndicesStep control left right
          hcontrolLeft hcontrolRight hleftRight indices x) =
      observed.get x := by
  induction indices generalizing x with
  | nil =>
      simp [controlledSwapIndicesStep]
  | cons i rest ih =>
      unfold controlledSwapIndicesStep
      change
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x)) =
          observed.get x
      calc
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x))
            =
          observed.get
            (EncodedBit.controlledSwapStep control (left.bit i)
              (right.bit i) (hcontrolLeft i) (hcontrolRight i)
              (hleftRight i) x) := by
            simpa [controlledSwapIndicesStep] using
              ih
                (fun j hj => hleftObserved j (by simp [hj]))
                (fun j hj => hrightObserved j (by simp [hj]))
                (EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) x)
        _ = observed.get x := by
          exact EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit i) (right.bit i) observed
            (hcontrolLeft i) (hcontrolRight i) (hleftRight i)
            (hleftObserved i (by simp)) (hrightObserved i (by simp)) x

/-- The complete controlled word swap preserves an observed readout whose wire
is distinct from every left and right target bit. -/
theorem controlledSwapStep_get_observed_of_swap_ne
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (observed : EncodedBit encoding)
    (hleftObserved : ∀ i, (left.bit i).wire ≠ observed.wire)
    (hrightObserved : ∀ i, (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      observed.get x := by
  rw [controlledSwapStep_eq_indicesStep]
  exact
    controlledSwapIndicesStep_get_observed_of_swap_ne
      control left right hcontrolLeft hcontrolRight hleftRight
      (List.ofFn fun i : Fin width => i) observed
      (fun i _ => hleftObserved i)
      (fun i _ => hrightObserved i)
      x

/-- A controlled word-swap fold sends the original right readout to the selected
left bit exactly when the control is set and the selected index is present. -/
theorem controlledSwapIndicesStep_get_left
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ∈ indices -> j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft :
      ∀ j, j ∈ indices -> (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved :
      ∀ j, j ∈ indices -> (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ∈ indices -> j ≠ i -> (right.bit j).wire ≠
        (right.bit i).wire)
    (x : Data) :
    (left.bit i).get
        (controlledSwapIndicesStep control left right
          hcontrolLeft hcontrolRight hleftRight indices x) =
      if i ∈ indices then
        if control.get x then (right.bit i).get x else (left.bit i).get x
      else
        (left.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      simp [controlledSwapIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledSwapIndicesStep at *
      change
        (left.bit i).get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit j)
                (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                (hleftRight j) x)) =
          if i ∈ j :: rest then
            if control.get x then (right.bit i).get x
            else (left.bit i).get x
          else
            (left.bit i).get x
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (left.bit i).get
                (rest.foldl
                  (fun y j =>
                    EncodedBit.controlledSwapStep control (left.bit j)
                      (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                      (hleftRight j) y)
                  (EncodedBit.controlledSwapStep control (left.bit i)
                    (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                    (hleftRight i) x)) =
              (left.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) x) := by
          simpa [controlledSwapIndicesStep] using
            controlledSwapIndicesStep_get_observed_of_swap_ne
              control left right hcontrolLeft hcontrolRight hleftRight
              rest (left.bit i)
              (fun k hk =>
                hleftLeft k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (fun k hk => hrightLeft k (by simp [hk]))
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x)
        rw [hpreserve]
        rw [EncodedBit.controlledSwapStep_get_left]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => hleftLeft k (by simp [hk]) hki)
            (fun k hk => hrightLeft k (by simp [hk]))
            (fun k hk => hleftRightObserved k (by simp [hk]))
            (fun k hk hki => hrightRight k (by simp [hk]) hki)
            (EncodedBit.controlledSwapStep control (left.bit j)
              (right.bit j) (hcontrolLeft j) (hcontrolRight j)
              (hleftRight j) x)
        rw [htail]
        have hcontrol :
            control.get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              control.get x :=
          EncodedBit.controlledSwapStep_get_control control (left.bit j)
            (right.bit j) (hcontrolLeft j) (hcontrolRight j)
            (hleftRight j) x
        have hleft :
            (left.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (left.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (left.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftLeft j (by simp) hji) (hrightLeft j (by simp)) x
        have hright :
            (right.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (right.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (right.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftRightObserved j (by simp))
            (hrightRight j (by simp) hji) x
        rw [hcontrol, hleft, hright]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest <;> simp [hji', himem]

/-- A controlled word-swap fold sends the original left readout to the selected
right bit exactly when the control is set and the selected index is present. -/
theorem controlledSwapIndicesStep_get_right
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ∈ indices -> j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft :
      ∀ j, j ∈ indices -> (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved :
      ∀ j, j ∈ indices -> (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ∈ indices -> j ≠ i -> (right.bit j).wire ≠
        (right.bit i).wire)
    (x : Data) :
    (right.bit i).get
        (controlledSwapIndicesStep control left right
          hcontrolLeft hcontrolRight hleftRight indices x) =
      if i ∈ indices then
        if control.get x then (left.bit i).get x else (right.bit i).get x
      else
        (right.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      simp [controlledSwapIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledSwapIndicesStep at *
      change
        (right.bit i).get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit j)
                (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                (hleftRight j) x)) =
          if i ∈ j :: rest then
            if control.get x then (left.bit i).get x
            else (right.bit i).get x
          else
            (right.bit i).get x
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (right.bit i).get
                (rest.foldl
                  (fun y j =>
                    EncodedBit.controlledSwapStep control (left.bit j)
                      (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                      (hleftRight j) y)
                  (EncodedBit.controlledSwapStep control (left.bit i)
                    (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                    (hleftRight i) x)) =
              (right.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) x) := by
          simpa [controlledSwapIndicesStep] using
            controlledSwapIndicesStep_get_observed_of_swap_ne
              control left right hcontrolLeft hcontrolRight hleftRight
              rest (right.bit i)
              (fun k hk => hleftRightObserved k (by simp [hk]))
              (fun k hk =>
                hrightRight k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x)
        rw [hpreserve]
        rw [EncodedBit.controlledSwapStep_get_right]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => hleftLeft k (by simp [hk]) hki)
            (fun k hk => hrightLeft k (by simp [hk]))
            (fun k hk => hleftRightObserved k (by simp [hk]))
            (fun k hk hki => hrightRight k (by simp [hk]) hki)
            (EncodedBit.controlledSwapStep control (left.bit j)
              (right.bit j) (hcontrolLeft j) (hcontrolRight j)
              (hleftRight j) x)
        rw [htail]
        have hcontrol :
            control.get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              control.get x :=
          EncodedBit.controlledSwapStep_get_control control (left.bit j)
            (right.bit j) (hcontrolLeft j) (hcontrolRight j)
            (hleftRight j) x
        have hleft :
            (left.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (left.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (left.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftLeft j (by simp) hji) (hrightLeft j (by simp)) x
        have hright :
            (right.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (right.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (right.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftRightObserved j (by simp))
            (hrightRight j (by simp) hji) x
        rw [hcontrol, hleft, hright]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest <;> simp [hji', himem]

/-- The complete controlled word swap sends the original right readout to the
selected left bit when the control is set. -/
theorem controlledSwapStep_get_left
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft : ∀ j, (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved : ∀ j, (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ≠ i -> (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (left.bit i).get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      if control.get x then (right.bit i).get x else (left.bit i).get x := by
  rw [controlledSwapStep_eq_indicesStep]
  have hnodup : (List.ofFn fun j : Fin width => j).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    controlledSwapIndicesStep_get_left control left right
      hcontrolLeft hcontrolRight hleftRight
      (List.ofFn fun j : Fin width => j) hnodup i
      (fun j _ hj => hleftLeft j hj)
      (fun j _ => hrightLeft j)
      (fun j _ => hleftRightObserved j)
      (fun j _ hj => hrightRight j hj)
      x

/-- The complete controlled word swap sends the original left readout to the
selected right bit when the control is set. -/
theorem controlledSwapStep_get_right
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft : ∀ j, (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved : ∀ j, (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ≠ i -> (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (right.bit i).get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      if control.get x then (left.bit i).get x else (right.bit i).get x := by
  rw [controlledSwapStep_eq_indicesStep]
  have hnodup : (List.ofFn fun j : Fin width => j).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    controlledSwapIndicesStep_get_right control left right
      hcontrolLeft hcontrolRight hleftRight
      (List.ofFn fun j : Fin width => j) hnodup i
      (fun j _ hj => hleftLeft j hj)
      (fun j _ => hrightLeft j)
      (fun j _ => hleftRightObserved j)
      (fun j _ hj => hrightRight j hj)
      x

/-- The controlled word-swap program realizes its folded semantic action. -/
theorem controlledSwap_realizes (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    BaseGateProgram.Realizes encoding
      (controlledSwapProgram control left right
        hcontrolLeft hcontrolRight hleftRight)
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) :=
  GateSpec.realizesList
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Same-Circuit witness for controlled bitwise swap of two encoded words. -/
def controlledSwapWitness (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    BaseGateSameCircuitWitness Data
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) where
  encoding := encoding
  program :=
    controlledSwapProgram control left right
      hcontrolLeft hcontrolRight hleftRight
  realizes :=
    controlledSwap_realizes control left right
      hcontrolLeft hcontrolRight hleftRight

/-- Toffoli gates that xor each source word bit into the corresponding target
word bit when the shared control bit is set. -/
def controlledXorIntoGates (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    List (GateSpec encoding) :=
  List.ofFn fun i =>
    GateSpec.toffoli control (source.bit i) (target.bit i)
      (hcontrolSource i) (hcontrolTarget i) (hsourceTarget i)

/-- Base-gate program for controlled bitwise xor from one encoded word into
another. -/
def controlledXorIntoProgram (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    BaseGateProgram encoding.width :=
  GateSpec.programList
    (controlledXorIntoGates control source target
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Semantic action of controlled bitwise xor from one encoded word into
another. -/
def controlledXorIntoStep (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    Data → Data :=
  GateSpec.stepList
    (controlledXorIntoGates control source target
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Folded semantic action for controlled word xor over an explicit list of
indices. -/
def controlledXorIntoIndicesStep (control : EncodedBit encoding)
    (source target : Word encoding width) (indices : List (Fin width)) :
    Data -> Data :=
  fun x =>
    indices.foldl
      (fun y i => toffoliStep control (source.bit i) (target.bit i) y) x

/-- The concrete `List.ofFn` controlled-xor gate list agrees with the indexed
fold semantics. -/
theorem controlledXorIntoStep_eq_indicesStep (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    controlledXorIntoStep control source target
        hcontrolSource hcontrolTarget hsourceTarget =
      controlledXorIntoIndicesStep control source target
        (List.ofFn fun i : Fin width => i) := by
  funext x
  rw [controlledXorIntoStep, controlledXorIntoGates,
    controlledXorIntoIndicesStep, GateSpec.stepList_eq_foldl]
  let gateOfIndex : Fin width -> GateSpec encoding := fun i =>
    GateSpec.toffoli control (source.bit i) (target.bit i)
      (hcontrolSource i) (hcontrolTarget i) (hsourceTarget i)
  change
    List.foldl (fun y gate => gate.step y) x (List.ofFn gateOfIndex) =
      List.foldl (fun y i => (gateOfIndex i).step y) x
        (List.ofFn fun i : Fin width => i)
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun i : Fin width => i).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun i : Fin width => i) gateOfIndex)]
  generalize List.ofFn (fun i : Fin width => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp [ih]

/-- A controlled word-xor fold preserves any observed readout whose wire is
distinct from every folded target bit. -/
theorem controlledXorIntoIndicesStep_get_observed_of_target_ne
    (control : EncodedBit encoding) (source target : Word encoding width)
    (indices : List (Fin width)) (observed : EncodedBit encoding)
    (hne : ∀ i, i ∈ indices -> (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledXorIntoIndicesStep control source target indices x) =
      observed.get x := by
  unfold controlledXorIntoIndicesStep
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        observed.get
            (rest.foldl
              (fun y i => toffoliStep control (source.bit i) (target.bit i) y)
              (toffoliStep control (source.bit i) (target.bit i) x)) =
          observed.get x
      rw [ih]
      · exact toffoliStep_get_of_target_ne control (source.bit i)
          (target.bit i) observed (hne i (by simp)) x
      · intro j hj
        exact hne j (by simp [hj])

/-- A controlled word-xor fold toggles a target bit exactly when its index is
present in the folded index list.  The extra hypotheses state that target wires
are independent of this observed target, the shared control, and the matching
source bit throughout the fold. -/
theorem controlledXorIntoIndicesStep_get_target
    (control : EncodedBit encoding) (source target : Word encoding width)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl : ∀ j, (target.bit j).wire ≠ control.wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (controlledXorIntoIndicesStep control source target indices x) =
      ((target.bit i).get x ^^
        (if i ∈ indices then control.get x && (source.bit i).get x else false)) := by
  induction indices generalizing x with
  | nil =>
      simp [controlledXorIntoIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledXorIntoIndicesStep at *
      change
        (target.bit i).get
            (rest.foldl
              (fun y j => toffoliStep control (source.bit j) (target.bit j) y)
              (toffoliStep control (source.bit j) (target.bit j) x)) =
          ((target.bit i).get x ^^
            (if i ∈ j :: rest then
              control.get x && (source.bit i).get x
            else false))
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (target.bit i).get
                (rest.foldl
                  (fun y j =>
                    toffoliStep control (source.bit j) (target.bit j) y)
                  (toffoliStep control (source.bit i) (target.bit i) x)) =
              (target.bit i).get
                (toffoliStep control (source.bit i) (target.bit i) x) := by
          simpa [controlledXorIntoIndicesStep] using
            controlledXorIntoIndicesStep_get_observed_of_target_ne
              control source target rest (target.bit i)
              (fun k hk =>
                htargetTarget k
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (toffoliStep control (source.bit i) (target.bit i) x)
        rw [hpreserve, toffoliStep_get_target]
        simp [hjNotMem]
      · have htail := ih hrestNodup
            (toffoliStep control (source.bit j) (target.bit j) x)
        rw [htail]
        have htarget :
            (target.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (target.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (target.bit i) (htargetTarget j hji) x
        have hcontrol :
            control.get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              control.get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) control (htargetControl j) x
        have hsource :
            (source.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (source.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (source.bit i) (htargetSource j) x
        rw [htarget, hcontrol, hsource]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest
        · simp [hji', himem]
        · simp [hji', himem]

/-- A controlled word-xor fold toggles a target bit exactly when its index is
present in the folded index list.  This variant only requires the target-wire
separation hypotheses for indices actually present in the folded list, which
is useful for filtered arithmetic networks whose target word is only injective
on the selected index set. -/
theorem controlledXorIntoIndicesStep_get_target_of_mem
    (control : EncodedBit encoding) (source target : Word encoding width)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ∈ indices → j ≠ i → (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl :
      ∀ j, j ∈ indices → (target.bit j).wire ≠ control.wire)
    (htargetSource :
      ∀ j, j ∈ indices → (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (controlledXorIntoIndicesStep control source target indices x) =
      ((target.bit i).get x ^^
        (if i ∈ indices then control.get x && (source.bit i).get x else false)) := by
  induction indices generalizing x with
  | nil =>
      simp [controlledXorIntoIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledXorIntoIndicesStep at *
      change
        (target.bit i).get
            (rest.foldl
              (fun y j => toffoliStep control (source.bit j) (target.bit j) y)
              (toffoliStep control (source.bit j) (target.bit j) x)) =
          ((target.bit i).get x ^^
            (if i ∈ j :: rest then
              control.get x && (source.bit i).get x
            else false))
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (target.bit i).get
                (rest.foldl
                  (fun y j =>
                    toffoliStep control (source.bit j) (target.bit j) y)
                  (toffoliStep control (source.bit i) (target.bit i) x)) =
              (target.bit i).get
                (toffoliStep control (source.bit i) (target.bit i) x) := by
          simpa [controlledXorIntoIndicesStep] using
            controlledXorIntoIndicesStep_get_observed_of_target_ne
              control source target rest (target.bit i)
              (fun k hk =>
                htargetTarget k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (toffoliStep control (source.bit i) (target.bit i) x)
        rw [hpreserve, toffoliStep_get_target]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => htargetTarget k (by simp [hk]) hki)
            (fun k hk => htargetControl k (by simp [hk]))
            (fun k hk => htargetSource k (by simp [hk]))
            (toffoliStep control (source.bit j) (target.bit j) x)
        rw [htail]
        have htarget :
            (target.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (target.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (target.bit i)
            (htargetTarget j (by simp) hji) x
        have hcontrol :
            control.get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              control.get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) control (htargetControl j (by simp)) x
        have hsource :
            (source.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (source.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (source.bit i) (htargetSource j (by simp)) x
        rw [htarget, hcontrol, hsource]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest
        · simp [hji', himem]
        · simp [hji', himem]

/-- The complete controlled word-xor fold preserves an observed readout whose
wire is distinct from every target bit. -/
theorem controlledXorIntoStep_get_observed_of_target_ne
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (observed : EncodedBit encoding)
    (hne : ∀ i, (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledXorIntoStep control source target
          hcontrolSource hcontrolTarget hsourceTarget x) =
      observed.get x := by
  rw [controlledXorIntoStep_eq_indicesStep]
  exact
    controlledXorIntoIndicesStep_get_observed_of_target_ne
      control source target (List.ofFn fun i : Fin width => i) observed
      (fun i _ => hne i) x

/-- The complete controlled word-xor fold toggles each target bit by the
corresponding controlled source bit. -/
theorem controlledXorIntoStep_get_target
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl : ∀ j, (target.bit j).wire ≠ control.wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (controlledXorIntoStep control source target
          hcontrolSource hcontrolTarget hsourceTarget x) =
      ((target.bit i).get x ^^
        (control.get x && (source.bit i).get x)) := by
  rw [controlledXorIntoStep_eq_indicesStep]
  have hnodup : (List.ofFn fun i : Fin width => i).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    controlledXorIntoIndicesStep_get_target control source target
      (List.ofFn fun j : Fin width => j) hnodup i
      htargetTarget htargetControl htargetSource x

/-- The reversed controlled word-xor gate list agrees with the indexed fold
over the reversed index list. -/
theorem controlledXorIntoGates_reverse_stepList_eq_indicesStep
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    GateSpec.stepList
        (controlledXorIntoGates control source target
          hcontrolSource hcontrolTarget hsourceTarget).reverse =
      controlledXorIntoIndicesStep control source target
        (List.ofFn fun i : Fin width => i).reverse := by
  funext x
  rw [controlledXorIntoGates, controlledXorIntoIndicesStep,
    GateSpec.stepList_eq_foldl]
  let gateOfIndex : Fin width -> GateSpec encoding := fun i =>
    GateSpec.toffoli control (source.bit i) (target.bit i)
      (hcontrolSource i) (hcontrolTarget i) (hsourceTarget i)
  change
    List.foldl (fun y gate => gate.step y) x
        (List.ofFn gateOfIndex).reverse =
      List.foldl (fun y i => (gateOfIndex i).step y) x
        (List.ofFn fun i : Fin width => i).reverse
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun i : Fin width => i).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun i : Fin width => i) gateOfIndex)]
  rw [← List.map_reverse]
  generalize (List.ofFn fun i : Fin width => i).reverse = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp [ih]

/-- The reversed controlled word-xor gate list preserves any observed readout
whose wire is distinct from every target bit. -/
theorem controlledXorIntoGates_reverse_get_observed_of_target_ne
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (observed : EncodedBit encoding)
    (hne : ∀ i, (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (GateSpec.stepList
          (controlledXorIntoGates control source target
            hcontrolSource hcontrolTarget hsourceTarget).reverse x) =
      observed.get x := by
  rw [controlledXorIntoGates_reverse_stepList_eq_indicesStep]
  exact
    controlledXorIntoIndicesStep_get_observed_of_target_ne
      control source target (List.ofFn fun i : Fin width => i).reverse
      observed
      (fun i _ => hne i)
      x

/-- The reversed controlled word-xor gate list toggles each target bit by the
corresponding controlled source bit. -/
theorem controlledXorIntoGates_reverse_get_target
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl : ∀ j, (target.bit j).wire ≠ control.wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (GateSpec.stepList
          (controlledXorIntoGates control source target
            hcontrolSource hcontrolTarget hsourceTarget).reverse x) =
      ((target.bit i).get x ^^
        (control.get x && (source.bit i).get x)) := by
  rw [controlledXorIntoGates_reverse_stepList_eq_indicesStep]
  have hnodup :
      ((List.ofFn fun j : Fin width => j).reverse).Nodup := by
    exact List.nodup_reverse.mpr
      (List.nodup_ofFn_ofInjective (fun _ _ h => h))
  have hmem : i ∈ (List.ofFn fun j : Fin width => j).reverse := by
    simp
  simpa [hmem] using
    controlledXorIntoIndicesStep_get_target control source target
      (List.ofFn fun j : Fin width => j).reverse hnodup i
      htargetTarget htargetControl htargetSource x

/-- The controlled bitwise xor program realizes its folded semantic action. -/
theorem controlledXorInto_realizes (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    BaseGateProgram.Realizes encoding
      (controlledXorIntoProgram control source target
        hcontrolSource hcontrolTarget hsourceTarget)
      (controlledXorIntoStep control source target
        hcontrolSource hcontrolTarget hsourceTarget) :=
  GateSpec.realizesList
    (controlledXorIntoGates control source target
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Same-Circuit witness for controlled bitwise xor from one encoded word into
another. -/
def controlledXorIntoWitness (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    BaseGateSameCircuitWitness Data
      (controlledXorIntoStep control source target
        hcontrolSource hcontrolTarget hsourceTarget) where
  encoding := encoding
  program :=
    controlledXorIntoProgram control source target
      hcontrolSource hcontrolTarget hsourceTarget
  realizes :=
    controlledXorInto_realizes control source target
      hcontrolSource hcontrolTarget hsourceTarget

end Word

end EncodedBit

namespace BinaryLabelEncoding

/-- The single Boolean bit stored by the canonical Boolean encoding. -/
def boolBit : EncodedBit bool where
  wire := ⟨0, by decide⟩
  get := id
  flip := fun b => !b
  get_eq := by
    intro b
    cases b <;> decide
  encode_flip := by
    intro b
    cases b <;> decide

/-! ### Exact-layout bit lenses -/

/-- Bit lens induced by an exact binary-register layout equivalence.  This is
the safe way to expose individual wires for raw label spaces where every
bit-flip is still a semantic label. -/
def ofEquivBit {Data : Type} {n : Nat} (layout : Data ≃ Fin (2 ^ n))
    (wire : Fin n) : EncodedBit (ofEquiv layout) where
  wire := wire
  get := fun x => (layout x).val.testBit (WireAddress.bitIndex wire).val
  flip := fun x => layout.symm (WireAddress.flipBit wire (layout x))
  get_eq := by
    intro x
    rfl
  encode_flip := by
    intro x
    simp [ofEquiv]

/-- Bit lens for the raw identity encoding of an `n`-qubit basis-label space. -/
def finIdentityBit (n : Nat) (wire : Fin n) :
    EncodedBit (finIdentity n) :=
  ofEquivBit (Equiv.refl (Fin (2 ^ n))) wire

/-- Word lens for the raw identity encoding of an `n`-qubit basis-label space. -/
def finIdentityWord (n : Nat) : EncodedBit.Word (finIdentity n) n where
  bit := finIdentityBit n

/-! ### Product-encoding bit readout helpers -/

/-- Wire of a bit inherited from the left component of a product encoding. -/
def prodLeftWire {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (wire : Fin left.width) :
    Fin (prod left right).width :=
  ⟨wire.val, by
    change wire.val < left.width + right.width
    omega⟩

/-- Wire of a bit inherited from the right component of a product encoding. -/
def prodRightWire {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (wire : Fin right.width) :
    Fin (prod left right).width :=
  ⟨left.width + wire.val, by
    change left.width + wire.val < left.width + right.width
    omega⟩

@[simp] theorem prodLeftWire_val {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin left.width) :
    (prodLeftWire left right wire).val = wire.val :=
  rfl

@[simp] theorem prodRightWire_val {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin right.width) :
    (prodRightWire left right wire).val = left.width + wire.val :=
  rfl

theorem bitIndex_prodLeftWire {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin left.width) :
    (WireAddress.bitIndex (prodLeftWire left right wire)).val =
      right.width + (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodLeftWire]
  omega

theorem bitIndex_prodRightWire {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin right.width) :
    (WireAddress.bitIndex (prodRightWire left right wire)).val =
      (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodRightWire]
  omega

/-- Bit readout inherited from the left component of a product encoding. -/
theorem prodLeft_get_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (bit : EncodedBit left) (x : Left × Right) :
    ((prod left right).encode x).val.testBit
        (WireAddress.bitIndex (prodLeftWire left right bit.wire)).val =
      bit.get x.1 := by
  rw [bitIndex_prodLeftWire]
  change
    (prodEquiv (m := left.width) (n := right.width)
        (left.encode x.1, right.encode x.2)).val.testBit
        (right.width + (WireAddress.bitIndex bit.wire).val) =
      bit.get x.1
  rw [prodEquiv_testBit_left]
  exact bit.get_eq x.1

/-- Bit readout inherited from the right component of a product encoding. -/
theorem prodRight_get_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (bit : EncodedBit right) (x : Left × Right) :
    ((prod left right).encode x).val.testBit
        (WireAddress.bitIndex (prodRightWire left right bit.wire)).val =
      bit.get x.2 := by
  rw [bitIndex_prodRightWire]
  change
    (prodEquiv (m := left.width) (n := right.width)
        (left.encode x.1, right.encode x.2)).val.testBit
        (WireAddress.bitIndex bit.wire).val =
      bit.get x.2
  rw [prodEquiv_testBit_right]
  exact bit.get_eq x.2

/-- Flipping a left-component wire is the same as flipping its corresponding
wire in the product encoding. -/
theorem prodEquiv_flip_left {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin left.width) (leftLabel : Fin (2 ^ left.width))
    (rightLabel : Fin (2 ^ right.width)) :
    prodEquiv (m := left.width) (n := right.width)
        (WireAddress.flipBit wire leftLabel, rightLabel) =
      WireAddress.flipBit (prodLeftWire left right wire)
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, rightLabel)) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hiWidth : i < left.width + right.width
  · by_cases hlow : i < right.width
    · let bit : Fin right.width := ⟨i, hlow⟩
      have hleft :=
        prodEquiv_testBit_right
          (left := WireAddress.flipBit wire leftLabel) (right := rightLabel) bit
      have hbase :=
        prodEquiv_testBit_right (left := leftLabel) (right := rightLabel) bit
      have hne :
          ¬ (WireAddress.bitIndex (prodLeftWire left right wire)).val =
            bit.val := by
        rw [bitIndex_prodLeftWire]
        dsimp [bit]
        omega
      rw [hleft]
      change rightLabel.val.testBit bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodLeftWire left right wire)).val).testBit bit.val
      rw [Nat.testBit_xor, Nat.testBit_two_pow, hbase]
      have hdec :
          decide ((WireAddress.bitIndex (prodLeftWire left right wire)).val =
            bit.val) = false := by
        rw [decide_eq_false_iff_not]
        exact hne
      rw [hdec]
      simp
    · push Not at hlow
      let bit : Fin left.width := ⟨i - right.width, by omega⟩
      have hidx : right.width + bit.val = i := by
        dsimp [bit]
        omega
      have hleft :=
        prodEquiv_testBit_left
          (left := WireAddress.flipBit wire leftLabel)
          (right := rightLabel) bit
      have hbase :=
        prodEquiv_testBit_left (left := leftLabel) (right := rightLabel) bit
      rw [← hidx, hleft]
      change (leftLabel.val ^^^ 2 ^ (WireAddress.bitIndex wire).val).testBit
          bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodLeftWire left right wire)).val).testBit
          (right.width + bit.val)
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [hbase]
      congr 1
      rw [decide_eq_decide, bitIndex_prodLeftWire]
      omega
  · push Not at hiWidth
    have hleftLt :
        (prodEquiv (m := left.width) (n := right.width)
          (WireAddress.flipBit wire leftLabel, rightLabel)).val < 2 ^ i :=
      lt_of_lt_of_le
        (prodEquiv (m := left.width) (n := right.width)
          (WireAddress.flipBit wire leftLabel, rightLabel)).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    have hrightLt :
        (WireAddress.flipBit (prodLeftWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).val < 2 ^ i :=
      lt_of_lt_of_le
        (WireAddress.flipBit (prodLeftWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    rw [Nat.testBit_lt_two_pow hleftLt, Nat.testBit_lt_two_pow hrightLt]

/-- Flipping a right-component wire is the same as flipping its corresponding
wire in the product encoding. -/
theorem prodEquiv_flip_right {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin right.width) (leftLabel : Fin (2 ^ left.width))
    (rightLabel : Fin (2 ^ right.width)) :
    prodEquiv (m := left.width) (n := right.width)
        (leftLabel, WireAddress.flipBit wire rightLabel) =
      WireAddress.flipBit (prodRightWire left right wire)
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, rightLabel)) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hiWidth : i < left.width + right.width
  · by_cases hlow : i < right.width
    · let bit : Fin right.width := ⟨i, hlow⟩
      have hleft :=
        prodEquiv_testBit_right (left := leftLabel)
          (right := WireAddress.flipBit wire rightLabel) bit
      have hbase :=
        prodEquiv_testBit_right (left := leftLabel) (right := rightLabel) bit
      rw [hleft]
      change (rightLabel.val ^^^ 2 ^ (WireAddress.bitIndex wire).val).testBit
          bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodRightWire left right wire)).val).testBit bit.val
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [hbase]
      congr 1
      rw [decide_eq_decide, bitIndex_prodRightWire]
    · push Not at hlow
      let bit : Fin left.width := ⟨i - right.width, by omega⟩
      have hidx : right.width + bit.val = i := by
        dsimp [bit]
        omega
      have hleft :=
        prodEquiv_testBit_left (left := leftLabel)
          (right := WireAddress.flipBit wire rightLabel) bit
      have hbase :=
        prodEquiv_testBit_left (left := leftLabel) (right := rightLabel) bit
      have hne :
          ¬ (WireAddress.bitIndex (prodRightWire left right wire)).val =
            right.width + bit.val := by
        rw [bitIndex_prodRightWire]
        omega
      rw [← hidx, hleft]
      change leftLabel.val.testBit bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodRightWire left right wire)).val).testBit
          (right.width + bit.val)
      rw [Nat.testBit_xor, Nat.testBit_two_pow, hbase]
      have hdec :
          decide ((WireAddress.bitIndex (prodRightWire left right wire)).val =
            right.width + bit.val) = false := by
        rw [decide_eq_false_iff_not]
        exact hne
      rw [hdec]
      simp
  · push Not at hiWidth
    have hleftLt :
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, WireAddress.flipBit wire rightLabel)).val < 2 ^ i :=
      lt_of_lt_of_le
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, WireAddress.flipBit wire rightLabel)).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    have hrightLt :
        (WireAddress.flipBit (prodRightWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).val < 2 ^ i :=
      lt_of_lt_of_le
        (WireAddress.flipBit (prodRightWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    rw [Nat.testBit_lt_two_pow hleftLt, Nat.testBit_lt_two_pow hrightLt]

/-- Lift an encoded bit from the left component to the product encoding. -/
def prodLeftBit {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (bit : EncodedBit left) :
    EncodedBit (prod left right) where
  wire := prodLeftWire left right bit.wire
  get := fun x => bit.get x.1
  flip := fun x => (bit.flip x.1, x.2)
  get_eq := by
    intro x
    exact prodLeft_get_eq left right bit x
  encode_flip := by
    intro x
    simp only [prod_encode]
    rw [bit.encode_flip x.1]
    exact prodEquiv_flip_left left right bit.wire (left.encode x.1)
      (right.encode x.2)

/-- Lift an encoded bit from the right component to the product encoding. -/
def prodRightBit {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (bit : EncodedBit right) :
    EncodedBit (prod left right) where
  wire := prodRightWire left right bit.wire
  get := fun x => bit.get x.2
  flip := fun x => (x.1, bit.flip x.2)
  get_eq := by
    intro x
    exact prodRight_get_eq left right bit x
  encode_flip := by
    intro x
    simp only [prod_encode]
    rw [bit.encode_flip x.2]
    exact prodEquiv_flip_right left right bit.wire (left.encode x.1)
      (right.encode x.2)

end BinaryLabelEncoding

namespace EncodedBit
namespace GateSpec

/-! ### Raw base-gate programs as identity-encoded gate specs -/

/-- View one raw base-gate operation as an encoded-bit gate specification under
the identity basis-label encoding. -/
def ofBaseGateOp {n : Nat} : BaseGateOp n ->
    GateSpec (BinaryLabelEncoding.finIdentity n)
  | BaseGateOp.x target =>
      GateSpec.x (BinaryLabelEncoding.finIdentityBit n target)
  | BaseGateOp.cnot control target hct =>
      GateSpec.cnot (BinaryLabelEncoding.finIdentityBit n control)
        (BinaryLabelEncoding.finIdentityBit n target) hct
  | BaseGateOp.toffoli controlA controlB target hab ha hb =>
      GateSpec.toffoli (BinaryLabelEncoding.finIdentityBit n controlA)
        (BinaryLabelEncoding.finIdentityBit n controlB)
        (BinaryLabelEncoding.finIdentityBit n target) hab ha hb

/-- View a raw base-gate program as identity-encoded gate specifications. -/
def ofBaseGateProgram {n : Nat} (program : BaseGateProgram n) :
    List (GateSpec (BinaryLabelEncoding.finIdentity n)) :=
  program.map ofBaseGateOp

/-- Converting a raw program to identity-encoded gate specifications preserves
the folded base-gate program. -/
theorem programList_ofBaseGateProgram {n : Nat}
    (program : BaseGateProgram n) :
    programList (ofBaseGateProgram program) = program := by
  induction program with
  | nil =>
      rfl
  | cons op rest ih =>
      cases op with
      | x target =>
          change BaseGateOp.x target ::
              programList (ofBaseGateProgram rest) =
            BaseGateOp.x target :: rest
          rw [ih]
      | cnot control target hct =>
          change BaseGateOp.cnot control target hct ::
              programList (ofBaseGateProgram rest) =
            BaseGateOp.cnot control target hct :: rest
          rw [ih]
      | toffoli controlA controlB target hab ha hb =>
          change BaseGateOp.toffoli controlA controlB target hab ha hb ::
              programList (ofBaseGateProgram rest) =
            BaseGateOp.toffoli controlA controlB target hab ha hb :: rest
          rw [ih]

/-- The identity-encoded gate-spec semantics of a raw program is exactly the
raw basis-label action. -/
theorem stepList_ofBaseGateProgram {n : Nat} (program : BaseGateProgram n)
    (label : Fin (2 ^ n)) :
    stepList (ofBaseGateProgram program) label =
      BaseGateProgram.applyLabel program label := by
  have hrealizes :=
    realizesList (encoding := BinaryLabelEncoding.finIdentity n)
      (ofBaseGateProgram program)
  have hprogram := programList_ofBaseGateProgram program
  have h := hrealizes.applyLabel_eq label
  rw [hprogram] at h
  simpa [BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv,
    BaseGateProgram.applyLabel] using h.symm

variable {Left Right : Type} {left : BinaryLabelEncoding Left}

/-- Distinct wires remain distinct after lifting encoded bits to the left
field of a product encoding. -/
theorem prodLeftWire_ne (right : BinaryLabelEncoding Right)
    {a b : EncodedBit left} (h : a.wire ≠ b.wire) :
    (BinaryLabelEncoding.prodLeftBit left right a).wire ≠
      (BinaryLabelEncoding.prodLeftBit left right b).wire := by
  intro hwire
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hwire
  simpa [BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodLeftWire] using hval

/-- Lift an encoded-bit gate so it acts on the left field of a product
encoding and preserves the right field. -/
def prodLeft (right : BinaryLabelEncoding Right) :
    GateSpec left -> GateSpec (BinaryLabelEncoding.prod left right)
  | x target =>
      GateSpec.x (BinaryLabelEncoding.prodLeftBit left right target)
  | cnot control target hct =>
      GateSpec.cnot
        (BinaryLabelEncoding.prodLeftBit left right control)
        (BinaryLabelEncoding.prodLeftBit left right target)
        (prodLeftWire_ne right hct)
  | toffoli controlA controlB target hab ha hb =>
      GateSpec.toffoli
        (BinaryLabelEncoding.prodLeftBit left right controlA)
        (BinaryLabelEncoding.prodLeftBit left right controlB)
        (BinaryLabelEncoding.prodLeftBit left right target)
        (prodLeftWire_ne right hab)
        (prodLeftWire_ne right ha)
        (prodLeftWire_ne right hb)

/-- A lifted left-product gate has exactly the original semantic action on the
left field and leaves the right field untouched. -/
theorem step_prodLeft (right : BinaryLabelEncoding Right)
    (gate : GateSpec left) (x : Left × Right) :
    (prodLeft right gate).step x = (gate.step x.1, x.2) := by
  cases gate with
  | x target =>
      rfl
  | cnot control target hct =>
      by_cases hcontrol : control.get x.1
      · simp [prodLeft, step, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodLeftBit, hcontrol]
      · simp [prodLeft, step, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodLeftBit, hcontrol]
  | toffoli controlA controlB target hab ha hb =>
      by_cases hcontrols : controlA.get x.1 && controlB.get x.1
      · simp [prodLeft, step, EncodedBit.toffoliStep,
          BinaryLabelEncoding.prodLeftBit, hcontrols]
      · simp [prodLeft, step, EncodedBit.toffoliStep,
          BinaryLabelEncoding.prodLeftBit, hcontrols]

/-- A lifted left-product gate list has exactly the original folded semantic
action on the left field and leaves the right field untouched. -/
theorem stepList_prodLeft (right : BinaryLabelEncoding Right) :
    ∀ (gates : List (GateSpec left)) (x : Left × Right),
      stepList (gates.map (prodLeft right)) x =
        (stepList gates x.1, x.2)
  | [], _state => rfl
  | gate :: rest, state => by
      change stepList (rest.map (prodLeft right))
          ((prodLeft right gate).step state) =
        (stepList rest (gate.step state.1), state.2)
      rw [step_prodLeft right gate state]
      exact stepList_prodLeft right rest (gate.step state.1, state.2)

end GateSpec
end EncodedBit

namespace BaseGateOp

/-! ### Raw wire-disjointness -/

/-- A raw operation is wire-disjoint from an observed wire when it neither
reads nor writes that wire. -/
def wireDisjoint {n : Nat} (observed : Fin n) : BaseGateOp n -> Prop
  | x target => target ≠ observed
  | cnot control target _ => control ≠ observed ∧ target ≠ observed
  | toffoli controlA controlB target _ _ _ =>
      controlA ≠ observed ∧ controlB ≠ observed ∧ target ≠ observed

/-- Raw wire-disjointness agrees with `GateSpec.bitDisjoint` after viewing the
operation under the identity basis-label encoding. -/
theorem bitDisjoint_ofBaseGateOp {n : Nat} (observed : Fin n)
    (op : BaseGateOp n) :
    EncodedBit.GateSpec.bitDisjoint
        (BinaryLabelEncoding.finIdentityBit n observed)
        (EncodedBit.GateSpec.ofBaseGateOp op) =
      wireDisjoint observed op := by
  cases op <;> rfl

/-! ### Product-register lifting for raw basis-label programs -/

/-- Wire inherited from the left field of an `m + n` product register. -/
def prodLeftWire {m n : Nat} (wire : Fin m) : Fin (m + n) :=
  ⟨wire.val, by omega⟩

/-- Wire inherited from the right field of an `m + n` product register. -/
def prodRightWire {m n : Nat} (wire : Fin n) : Fin (m + n) :=
  ⟨m + wire.val, by omega⟩

@[simp] theorem prodLeftWire_val {m n : Nat} (wire : Fin m) :
    (prodLeftWire (n := n) wire).val = wire.val :=
  rfl

@[simp] theorem prodRightWire_val {m n : Nat} (wire : Fin n) :
    (prodRightWire (m := m) wire).val = m + wire.val :=
  rfl

theorem bitIndex_prodLeftWire {m n : Nat} (wire : Fin m) :
    (WireAddress.bitIndex (prodLeftWire (n := n) wire)).val =
      n + (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodLeftWire]
  omega

theorem bitIndex_prodRightWire {m n : Nat} (wire : Fin n) :
    (WireAddress.bitIndex (prodRightWire (m := m) wire)).val =
      (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodRightWire]
  omega

/-- Flipping a left-field wire commutes with product-label packing. -/
theorem prodEquiv_flip_left {m n : Nat} (wire : Fin m)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    prodEquiv (m := m) (n := n)
        (WireAddress.flipBit wire leftLabel, rightLabel) =
      WireAddress.flipBit (prodLeftWire (n := n) wire)
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) := by
  have h :=
    BinaryLabelEncoding.prodEquiv_flip_left
      (BinaryLabelEncoding.finIdentity m) (BinaryLabelEncoding.finIdentity n)
      wire leftLabel rightLabel
  exact h.trans (by
    congr 1)

/-- Flipping a right-field wire commutes with product-label packing. -/
theorem prodEquiv_flip_right {m n : Nat} (wire : Fin n)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    prodEquiv (m := m) (n := n)
        (leftLabel, WireAddress.flipBit wire rightLabel) =
      WireAddress.flipBit (prodRightWire (m := m) wire)
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) := by
  have h :=
    BinaryLabelEncoding.prodEquiv_flip_right
      (BinaryLabelEncoding.finIdentity m) (BinaryLabelEncoding.finIdentity n)
      wire leftLabel rightLabel
  exact h.trans (by
    congr 1)

/-- Lift a base-gate operation on the left field into an `m + n` register. -/
def prodLeft {m n : Nat} : BaseGateOp m -> BaseGateOp (m + n)
  | x target =>
      x (prodLeftWire (n := n) target)
  | cnot control target hct =>
      cnot (prodLeftWire (n := n) control) (prodLeftWire (n := n) target)
        (by
          intro h
          apply hct
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)
  | toffoli controlA controlB target hab ha hb =>
      toffoli (prodLeftWire (n := n) controlA) (prodLeftWire (n := n) controlB)
        (prodLeftWire (n := n) target)
        (by
          intro h
          apply hab
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)
        (by
          intro h
          apply ha
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)
        (by
          intro h
          apply hb
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)

/-- Lift a base-gate operation on the right field into an `m + n` register. -/
def prodRight {m n : Nat} : BaseGateOp n -> BaseGateOp (m + n)
  | x target =>
      x (prodRightWire (m := m) target)
  | cnot control target hct =>
      cnot (prodRightWire (m := m) control) (prodRightWire (m := m) target)
        (by
          intro h
          apply hct
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)
  | toffoli controlA controlB target hab ha hb =>
      toffoli (prodRightWire (m := m) controlA)
        (prodRightWire (m := m) controlB) (prodRightWire (m := m) target)
        (by
          intro h
          apply hab
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)
        (by
          intro h
          apply ha
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)
        (by
          intro h
          apply hb
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)

/-- Lifting an operation to the left field preserves disjointness from a lifted
left-field observed wire. -/
theorem wireDisjoint_prodLeft_of_wireDisjoint {m n : Nat}
    {observed : Fin m} {op : BaseGateOp m}
    (h : wireDisjoint observed op) :
    wireDisjoint (prodLeftWire (n := n) observed) (prodLeft (n := n) op) := by
  cases op with
  | x target =>
      intro heq
      apply h
      apply Fin.ext
      simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
  | cnot control target hct =>
      rcases h with ⟨hcontrol, htarget⟩
      constructor
      · intro heq
        apply hcontrol
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
      · intro heq
        apply htarget
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
  | toffoli controlA controlB target hab ha hb =>
      rcases h with ⟨hcontrolA, hcontrolB, htarget⟩
      constructor
      · intro heq
        apply hcontrolA
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
      constructor
      · intro heq
        apply hcontrolB
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
      · intro heq
        apply htarget
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq

/-- Lifting an operation to the right field preserves disjointness from a
lifted right-field observed wire. -/
theorem wireDisjoint_prodRight_of_wireDisjoint {m n : Nat}
    {observed : Fin n} {op : BaseGateOp n}
    (h : wireDisjoint observed op) :
    wireDisjoint (prodRightWire (m := m) observed)
      (prodRight (m := m) op) := by
  cases op with
  | x target =>
      intro heq
      apply h
      apply Fin.ext
      have hv := congrArg Fin.val heq
      simp [prodRightWire] at hv
      omega
  | cnot control target hct =>
      rcases h with ⟨hcontrol, htarget⟩
      constructor
      · intro heq
        apply hcontrol
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
      · intro heq
        apply htarget
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
  | toffoli controlA controlB target hab ha hb =>
      rcases h with ⟨hcontrolA, hcontrolB, htarget⟩
      constructor
      · intro heq
        apply hcontrolA
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
      constructor
      · intro heq
        apply hcontrolB
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
      · intro heq
        apply htarget
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega

/-- A left-field observed wire is disjoint from any operation lifted from the
right field. -/
theorem wireDisjoint_prodRight_leftWire {m n : Nat}
    (observed : Fin m) (op : BaseGateOp n) :
    wireDisjoint (prodLeftWire (n := n) observed)
      (prodRight (m := m) op) := by
  cases op with
  | x target =>
      intro heq
      have hv := congrArg Fin.val heq
      simp [prodLeftWire, prodRightWire] at hv
      omega
  | cnot control target hct =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
  | toffoli controlA controlB target hab ha hb =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega

/-- A right-field observed wire is disjoint from any operation lifted from the
left field. -/
theorem wireDisjoint_prodLeft_rightWire {m n : Nat}
    (observed : Fin n) (op : BaseGateOp m) :
    wireDisjoint (prodRightWire (m := m) observed)
      (prodLeft (n := n) op) := by
  cases op with
  | x target =>
      intro heq
      have hv := congrArg Fin.val heq
      simp [prodLeftWire, prodRightWire] at hv
      omega
  | cnot control target hct =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
  | toffoli controlA controlB target hab ha hb =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega

/-- Wire map that inserts a middle field between the left and right fields of
an existing product register.  Left-field wires keep their address, while
right-field wires are shifted past the inserted middle field. -/
def insertMiddleWire {leftWidth middleWidth rightWidth : Nat}
    (wire : Fin (leftWidth + rightWidth)) :
    Fin (leftWidth + middleWidth + rightWidth) :=
  if h : wire.val < leftWidth then
    ⟨wire.val, by omega⟩
  else
    ⟨wire.val + middleWidth, by
      have hlt := wire.isLt
      omega⟩

theorem insertMiddleWire_injective {leftWidth middleWidth rightWidth : Nat}
    {left right : Fin (leftWidth + rightWidth)}
    (h :
      insertMiddleWire (middleWidth := middleWidth) left =
        insertMiddleWire (middleWidth := middleWidth) right) :
    left = right := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  by_cases hleft : left.val < leftWidth <;>
    by_cases hright : right.val < leftWidth <;>
      simp [insertMiddleWire, hleft, hright] at hv <;> omega

theorem insertMiddleWire_ne {leftWidth middleWidth rightWidth : Nat}
    {left right : Fin (leftWidth + rightWidth)}
    (h : left ≠ right) :
    insertMiddleWire (middleWidth := middleWidth) left ≠
      insertMiddleWire (middleWidth := middleWidth) right := by
  intro hmap
  exact h (insertMiddleWire_injective hmap)

/-- Lift a base-gate operation across an inserted middle register. -/
def insertMiddle {leftWidth middleWidth rightWidth : Nat} :
    BaseGateOp (leftWidth + rightWidth) ->
      BaseGateOp (leftWidth + middleWidth + rightWidth)
  | x target =>
      x (insertMiddleWire (middleWidth := middleWidth) target)
  | cnot control target hct =>
      cnot (insertMiddleWire (middleWidth := middleWidth) control)
        (insertMiddleWire (middleWidth := middleWidth) target)
        (insertMiddleWire_ne (middleWidth := middleWidth) hct)
  | toffoli controlA controlB target hab ha hb =>
      toffoli (insertMiddleWire (middleWidth := middleWidth) controlA)
        (insertMiddleWire (middleWidth := middleWidth) controlB)
        (insertMiddleWire (middleWidth := middleWidth) target)
        (insertMiddleWire_ne (middleWidth := middleWidth) hab)
        (insertMiddleWire_ne (middleWidth := middleWidth) ha)
        (insertMiddleWire_ne (middleWidth := middleWidth) hb)

theorem applyLabel_prodLeft {m n : Nat} (op : BaseGateOp m)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    (op.prodLeft (n := n)).applyLabel
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) =
      prodEquiv (m := m) (n := n)
        (op.applyLabel leftLabel, rightLabel) := by
  cases op with
  | x target =>
      simpa [prodLeft, applyLabel] using
        (prodEquiv_flip_left (n := n) target leftLabel rightLabel).symm
  | cnot control target hct =>
      unfold prodLeft applyLabel WireAddress.cnotMap
      simp only [bitIndex_prodLeftWire, prodEquiv_testBit_left]
      split
      · exact (prodEquiv_flip_left (n := n) target leftLabel rightLabel).symm
      · rfl
  | toffoli controlA controlB target hab ha hb =>
      unfold prodLeft applyLabel WireAddress.toffoliMap
      simp only [bitIndex_prodLeftWire, prodEquiv_testBit_left]
      split
      · exact (prodEquiv_flip_left (n := n) target leftLabel rightLabel).symm
      · rfl

theorem applyLabel_prodRight {m n : Nat} (op : BaseGateOp n)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    (op.prodRight (m := m)).applyLabel
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) =
      prodEquiv (m := m) (n := n)
        (leftLabel, op.applyLabel rightLabel) := by
  cases op with
  | x target =>
      simpa [prodRight, applyLabel] using
        (prodEquiv_flip_right (m := m) target leftLabel rightLabel).symm
  | cnot control target hct =>
      unfold prodRight applyLabel WireAddress.cnotMap
      simp only [bitIndex_prodRightWire, prodEquiv_testBit_right]
      split
      · exact (prodEquiv_flip_right (m := m) target leftLabel rightLabel).symm
      · rfl
  | toffoli controlA controlB target hab ha hb =>
      unfold prodRight applyLabel WireAddress.toffoliMap
      simp only [bitIndex_prodRightWire, prodEquiv_testBit_right]
      split
      · exact (prodEquiv_flip_right (m := m) target leftLabel rightLabel).symm
      · rfl

end BaseGateOp

namespace BaseGateProgram

/-! ### Clean-work control lift for raw programs -/

/-- Clean-work controlled version of a raw base-gate program.  The construction
views the raw program under the identity basis-label encoding and reuses the
encoded-bit clean-work control decomposition. -/
def controlledWithCleanWork {n : Nat} (control work : Fin n)
    (program : BaseGateProgram n)
    (hcontrol :
      ∀ op, op ∈ program -> BaseGateOp.wireDisjoint control op)
    (hwork :
      ∀ op, op ∈ program -> BaseGateOp.wireDisjoint work op)
    (hcontrolWork : control ≠ work) : BaseGateProgram n :=
  EncodedBit.GateSpec.programList
    (EncodedBit.GateSpec.controlledListWithWorkGates
      (BinaryLabelEncoding.finIdentityBit n control)
      (BinaryLabelEncoding.finIdentityBit n work)
      (EncodedBit.GateSpec.ofBaseGateProgram program)
      (by
        intro gate hgate
        simp only [EncodedBit.GateSpec.ofBaseGateProgram] at hgate
        rcases List.mem_map.mp hgate with ⟨op, hop, rfl⟩
        rw [BaseGateOp.bitDisjoint_ofBaseGateOp]
        exact hcontrol op hop)
      (by
        intro gate hgate
        simp only [EncodedBit.GateSpec.ofBaseGateProgram] at hgate
        rcases List.mem_map.mp hgate with ⟨op, hop, rfl⟩
        rw [BaseGateOp.bitDisjoint_ofBaseGateOp]
        exact hwork op hop)
      hcontrolWork)

/-- If the extra control wire is false, the clean-work controlled raw program
acts as the identity on basis labels. -/
theorem applyLabel_controlledWithCleanWork_of_control_false {n : Nat}
    (control work : Fin n) (program : BaseGateProgram n)
    (hcontrol :
      ∀ op, op ∈ program -> BaseGateOp.wireDisjoint control op)
    (hwork :
      ∀ op, op ∈ program -> BaseGateOp.wireDisjoint work op)
    (hcontrolWork : control ≠ work) (label : Fin (2 ^ n))
    (hcontrolFalse :
      label.val.testBit (WireAddress.bitIndex control).val = false) :
    applyLabel
        (controlledWithCleanWork control work program hcontrol hwork
          hcontrolWork) label =
      label := by
  let controlBit := BinaryLabelEncoding.finIdentityBit n control
  let workBit := BinaryLabelEncoding.finIdentityBit n work
  let gates := EncodedBit.GateSpec.ofBaseGateProgram program
  have hcontrolGates :
      ∀ gate, gate ∈ gates ->
        EncodedBit.GateSpec.bitDisjoint controlBit gate := by
    intro gate hgate
    simp only [gates, EncodedBit.GateSpec.ofBaseGateProgram] at hgate
    rcases List.mem_map.mp hgate with ⟨op, hop, rfl⟩
    rw [BaseGateOp.bitDisjoint_ofBaseGateOp]
    exact hcontrol op hop
  have hworkGates :
      ∀ gate, gate ∈ gates ->
        EncodedBit.GateSpec.bitDisjoint workBit gate := by
    intro gate hgate
    simp only [gates, EncodedBit.GateSpec.ofBaseGateProgram] at hgate
    rcases List.mem_map.mp hgate with ⟨op, hop, rfl⟩
    rw [BaseGateOp.bitDisjoint_ofBaseGateOp]
    exact hwork op hop
  have hstep :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates
            controlBit workBit gates hcontrolGates hworkGates hcontrolWork)
          label =
        label := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        controlBit workBit gates hcontrolGates hworkGates hcontrolWork label
        (by simpa [controlBit, BinaryLabelEncoding.finIdentityBit,
          BinaryLabelEncoding.ofEquivBit] using hcontrolFalse)
  have hrealizes :=
    EncodedBit.GateSpec.realizesList
      (encoding := BinaryLabelEncoding.finIdentity n)
      (EncodedBit.GateSpec.controlledListWithWorkGates
        controlBit workBit gates hcontrolGates hworkGates hcontrolWork)
  have happly := hrealizes.applyLabel_eq label
  rw [hstep] at happly
  simpa [controlledWithCleanWork, controlBit, workBit, gates,
    EncodedBit.GateSpec.controlledListWithWorkStep,
    BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv,
    BaseGateProgram.applyLabel] using happly

/-- If the extra control wire is true and the supplied work wire starts clean,
the clean-work controlled raw program acts like the original raw program on
basis labels. -/
theorem applyLabel_controlledWithCleanWork_of_control_true {n : Nat}
    (control work : Fin n) (program : BaseGateProgram n)
    (hcontrol :
      ∀ op, op ∈ program -> BaseGateOp.wireDisjoint control op)
    (hwork :
      ∀ op, op ∈ program -> BaseGateOp.wireDisjoint work op)
    (hcontrolWork : control ≠ work) (label : Fin (2 ^ n))
    (hcontrolTrue :
      label.val.testBit (WireAddress.bitIndex control).val = true)
    (hworkClean :
      label.val.testBit (WireAddress.bitIndex work).val = false) :
    applyLabel
        (controlledWithCleanWork control work program hcontrol hwork
          hcontrolWork) label =
      applyLabel program label := by
  let controlBit := BinaryLabelEncoding.finIdentityBit n control
  let workBit := BinaryLabelEncoding.finIdentityBit n work
  let gates := EncodedBit.GateSpec.ofBaseGateProgram program
  have hcontrolGates :
      ∀ gate, gate ∈ gates ->
        EncodedBit.GateSpec.bitDisjoint controlBit gate := by
    intro gate hgate
    simp only [gates, EncodedBit.GateSpec.ofBaseGateProgram] at hgate
    rcases List.mem_map.mp hgate with ⟨op, hop, rfl⟩
    rw [BaseGateOp.bitDisjoint_ofBaseGateOp]
    exact hcontrol op hop
  have hworkGates :
      ∀ gate, gate ∈ gates ->
        EncodedBit.GateSpec.bitDisjoint workBit gate := by
    intro gate hgate
    simp only [gates, EncodedBit.GateSpec.ofBaseGateProgram] at hgate
    rcases List.mem_map.mp hgate with ⟨op, hop, rfl⟩
    rw [BaseGateOp.bitDisjoint_ofBaseGateOp]
    exact hwork op hop
  have hstep :
      EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates
            controlBit workBit gates hcontrolGates hworkGates hcontrolWork)
          label =
        EncodedBit.GateSpec.stepList gates label := by
    simpa [EncodedBit.GateSpec.controlledListWithWorkStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
        controlBit workBit gates hcontrolGates hworkGates hcontrolWork label
        (by simpa [controlBit, BinaryLabelEncoding.finIdentityBit,
          BinaryLabelEncoding.ofEquivBit] using hcontrolTrue)
        (by simpa [workBit, BinaryLabelEncoding.finIdentityBit,
          BinaryLabelEncoding.ofEquivBit] using hworkClean)
  have hraw :=
    EncodedBit.GateSpec.stepList_ofBaseGateProgram program label
  have hrealizes :=
    EncodedBit.GateSpec.realizesList
      (encoding := BinaryLabelEncoding.finIdentity n)
      (EncodedBit.GateSpec.controlledListWithWorkGates
        controlBit workBit gates hcontrolGates hworkGates hcontrolWork)
  have happly := hrealizes.applyLabel_eq label
  rw [hstep] at happly
  change EncodedBit.GateSpec.stepList gates label =
    applyLabel program label at hraw
  rw [hraw] at happly
  simpa [controlledWithCleanWork, controlBit, workBit, gates,
    EncodedBit.GateSpec.controlledListWithWorkStep,
    BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv,
    BaseGateProgram.applyLabel] using happly

/-- Lift a base-gate program on the left field into an `m + n` register. -/
def prodLeft {m n : Nat} (program : BaseGateProgram m) :
    BaseGateProgram (m + n) :=
  program.map (BaseGateOp.prodLeft (n := n))

/-- Lift a base-gate program on the right field into an `m + n` register. -/
def prodRight {m n : Nat} (program : BaseGateProgram n) :
    BaseGateProgram (m + n) :=
  program.map (BaseGateOp.prodRight (m := m))

/-- Insert a middle register between the left and right fields addressed by a
program over an existing product register. -/
def insertMiddle {leftWidth middleWidth rightWidth : Nat}
    (program : BaseGateProgram (leftWidth + rightWidth)) :
    BaseGateProgram (leftWidth + middleWidth + rightWidth) :=
  program.map (BaseGateOp.insertMiddle (middleWidth := middleWidth))

/-- Pack a source product label and a middle label into the corresponding
three-field label where the middle field sits between source-left and
source-right. -/
def insertMiddleLabel
    (leftWidth middleWidth rightWidth : Nat)
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    Fin (2 ^ (leftWidth + middleWidth + rightWidth)) :=
  let sourceParts :=
    (prodEquiv (m := leftWidth) (n := rightWidth)).symm source
  prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)
    (prodEquiv (m := leftWidth) (n := middleWidth)
      (sourceParts.1, middleLabel), sourceParts.2)

@[simp] theorem insertMiddleLabel_prodEquiv
    {leftWidth middleWidth rightWidth : Nat}
    (leftLabel : Fin (2 ^ leftWidth))
    (middleLabel : Fin (2 ^ middleWidth))
    (rightLabel : Fin (2 ^ rightWidth)) :
    insertMiddleLabel leftWidth middleWidth rightWidth
        (prodEquiv (m := leftWidth) (n := rightWidth)
          (leftLabel, rightLabel))
        middleLabel =
      prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)
        (prodEquiv (m := leftWidth) (n := middleWidth)
          (leftLabel, middleLabel), rightLabel) := by
  simp [insertMiddleLabel]

theorem insertMiddleLabel_flipBit
    {leftWidth middleWidth rightWidth : Nat}
    (wire : Fin (leftWidth + rightWidth))
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    WireAddress.flipBit
        (BaseGateOp.insertMiddleWire (middleWidth := middleWidth) wire)
        (insertMiddleLabel leftWidth middleWidth rightWidth source
          middleLabel) =
      insertMiddleLabel leftWidth middleWidth rightWidth
        (WireAddress.flipBit wire source) middleLabel := by
  rcases hparts :
      (prodEquiv (m := leftWidth) (n := rightWidth)).symm source with
    ⟨leftLabel, rightLabel⟩
  have hsource :
      prodEquiv (m := leftWidth) (n := rightWidth)
          (leftLabel, rightLabel) = source := by
    rw [← hparts]
    exact Equiv.apply_symm_apply
      (prodEquiv (m := leftWidth) (n := rightWidth)) source
  rw [← hsource]
  by_cases hleft : wire.val < leftWidth
  · let leftWire : Fin leftWidth := ⟨wire.val, hleft⟩
    have hwireSource :
        wire = BaseGateOp.prodLeftWire (n := rightWidth) leftWire := by
      apply Fin.ext
      simp [leftWire, BaseGateOp.prodLeftWire]
    have hwireTarget :
        BaseGateOp.insertMiddleWire (middleWidth := middleWidth) wire =
          BaseGateOp.prodLeftWire (n := rightWidth)
            (BaseGateOp.prodLeftWire (n := middleWidth) leftWire) := by
      apply Fin.ext
      simp [BaseGateOp.insertMiddleWire, hleft, leftWire,
        BaseGateOp.prodLeftWire]
    rw [hwireTarget, insertMiddleLabel_prodEquiv]
    rw [← BaseGateOp.prodEquiv_flip_left (n := rightWidth)
      (BaseGateOp.prodLeftWire (n := middleWidth) leftWire)
      (prodEquiv (m := leftWidth) (n := middleWidth)
        (leftLabel, middleLabel)) rightLabel]
    rw [← BaseGateOp.prodEquiv_flip_left (n := middleWidth)
      leftWire leftLabel middleLabel]
    rw [hwireSource]
    rw [← BaseGateOp.prodEquiv_flip_left (n := rightWidth)
      leftWire leftLabel rightLabel]
    rw [insertMiddleLabel_prodEquiv]
  · let rightWire : Fin rightWidth := ⟨wire.val - leftWidth, by
        have hlt := wire.isLt
        omega⟩
    have hwireSource :
        wire = BaseGateOp.prodRightWire (m := leftWidth) rightWire := by
      apply Fin.ext
      simp [rightWire, BaseGateOp.prodRightWire]
      omega
    have hwireTarget :
        BaseGateOp.insertMiddleWire (middleWidth := middleWidth) wire =
          BaseGateOp.prodRightWire (m := leftWidth + middleWidth)
            rightWire := by
      apply Fin.ext
      simp [BaseGateOp.insertMiddleWire, hleft, rightWire,
        BaseGateOp.prodRightWire]
      omega
    rw [hwireTarget, insertMiddleLabel_prodEquiv]
    rw [← BaseGateOp.prodEquiv_flip_right (m := leftWidth + middleWidth)
      rightWire
      (prodEquiv (m := leftWidth) (n := middleWidth)
        (leftLabel, middleLabel)) rightLabel]
    rw [hwireSource]
    rw [← BaseGateOp.prodEquiv_flip_right (m := leftWidth)
      rightWire leftLabel rightLabel]
    rw [insertMiddleLabel_prodEquiv]

theorem insertMiddleLabel_get_source_bit
    {leftWidth middleWidth rightWidth : Nat}
    (wire : Fin (leftWidth + rightWidth))
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    (insertMiddleLabel leftWidth middleWidth rightWidth source
        middleLabel).val.testBit
        (WireAddress.bitIndex
          (BaseGateOp.insertMiddleWire
            (middleWidth := middleWidth) wire)).val =
      source.val.testBit (WireAddress.bitIndex wire).val := by
  rcases hparts :
      (prodEquiv (m := leftWidth) (n := rightWidth)).symm source with
    ⟨leftLabel, rightLabel⟩
  have hsource :
      prodEquiv (m := leftWidth) (n := rightWidth)
          (leftLabel, rightLabel) = source := by
    rw [← hparts]
    exact Equiv.apply_symm_apply
      (prodEquiv (m := leftWidth) (n := rightWidth)) source
  rw [← hsource]
  by_cases hleft : wire.val < leftWidth
  · let leftWire : Fin leftWidth := ⟨wire.val, hleft⟩
    have hwireSource :
        wire = BaseGateOp.prodLeftWire (n := rightWidth) leftWire := by
      apply Fin.ext
      simp [leftWire, BaseGateOp.prodLeftWire]
    have hwireTarget :
        BaseGateOp.insertMiddleWire (middleWidth := middleWidth) wire =
          BaseGateOp.prodLeftWire (n := rightWidth)
            (BaseGateOp.prodLeftWire (n := middleWidth) leftWire) := by
      apply Fin.ext
      simp [BaseGateOp.insertMiddleWire, hleft, leftWire,
        BaseGateOp.prodLeftWire]
    rw [hwireTarget, hwireSource, insertMiddleLabel_prodEquiv]
    rw [BaseGateOp.bitIndex_prodLeftWire]
    rw [prodEquiv_testBit_left]
    rw [BaseGateOp.bitIndex_prodLeftWire]
    rw [prodEquiv_testBit_left]
    rw [BaseGateOp.bitIndex_prodLeftWire]
    rw [prodEquiv_testBit_left]
  · let rightWire : Fin rightWidth := ⟨wire.val - leftWidth, by
        have hlt := wire.isLt
        omega⟩
    have hwireSource :
        wire = BaseGateOp.prodRightWire (m := leftWidth) rightWire := by
      apply Fin.ext
      simp [rightWire, BaseGateOp.prodRightWire]
      omega
    have hwireTarget :
        BaseGateOp.insertMiddleWire (middleWidth := middleWidth) wire =
          BaseGateOp.prodRightWire (m := leftWidth + middleWidth)
            rightWire := by
      apply Fin.ext
      simp [BaseGateOp.insertMiddleWire, hleft, rightWire,
        BaseGateOp.prodRightWire]
      omega
    rw [hwireTarget, hwireSource, insertMiddleLabel_prodEquiv]
    simp [BaseGateOp.bitIndex_prodRightWire, prodEquiv_testBit_right]

theorem applyLabel_prodLeft {m n : Nat} (program : BaseGateProgram m)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    BaseGateProgram.applyLabel (prodLeft (n := n) program)
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) =
      prodEquiv (m := m) (n := n)
        (BaseGateProgram.applyLabel program leftLabel, rightLabel) := by
  induction program generalizing leftLabel with
  | nil =>
      rfl
  | cons op rest ih =>
      simp only [prodLeft, List.map_cons, applyLabel_cons]
      rw [BaseGateOp.applyLabel_prodLeft]
      exact ih (op.applyLabel leftLabel)

theorem applyLabel_prodRight {m n : Nat} (program : BaseGateProgram n)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    BaseGateProgram.applyLabel (prodRight (m := m) program)
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) =
      prodEquiv (m := m) (n := n)
        (leftLabel, BaseGateProgram.applyLabel program rightLabel) := by
  induction program generalizing rightLabel with
  | nil =>
      rfl
  | cons op rest ih =>
      simp only [prodRight, List.map_cons, applyLabel_cons]
      rw [BaseGateOp.applyLabel_prodRight]
      exact ih (op.applyLabel rightLabel)

theorem applyLabel_insertMiddleOp
    {leftWidth middleWidth rightWidth : Nat}
    (op : BaseGateOp (leftWidth + rightWidth))
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    (op.insertMiddle (middleWidth := middleWidth)).applyLabel
        (insertMiddleLabel leftWidth middleWidth rightWidth source
          middleLabel) =
      insertMiddleLabel leftWidth middleWidth rightWidth
        (op.applyLabel source) middleLabel := by
  cases op with
  | x target =>
      simpa [BaseGateOp.insertMiddle, BaseGateOp.applyLabel] using
        insertMiddleLabel_flipBit target source middleLabel
  | cnot control target hct =>
      by_cases hcontrol :
          source.val.testBit (WireAddress.bitIndex control).val = true
      · have hcontrolLift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) control)).val = true := by
          rw [insertMiddleLabel_get_source_bit, hcontrol]
        simp [BaseGateOp.insertMiddle, BaseGateOp.applyLabel,
          WireAddress.cnotMap, hcontrol, hcontrolLift,
          insertMiddleLabel_flipBit target source middleLabel]
      · have hcontrolFalse :
            source.val.testBit (WireAddress.bitIndex control).val = false :=
          Bool.eq_false_iff.mpr hcontrol
        have hcontrolLift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) control)).val = false := by
          rw [insertMiddleLabel_get_source_bit, hcontrolFalse]
        simp [BaseGateOp.insertMiddle, BaseGateOp.applyLabel,
          WireAddress.cnotMap, hcontrolFalse, hcontrolLift]
  | toffoli controlA controlB target hab ha hb =>
      by_cases hcontrolA :
          source.val.testBit (WireAddress.bitIndex controlA).val = true <;>
        by_cases hcontrolB :
          source.val.testBit (WireAddress.bitIndex controlB).val = true
      · have hcontrolALift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlA)).val = true := by
          rw [insertMiddleLabel_get_source_bit, hcontrolA]
        have hcontrolBLift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlB)).val = true := by
          rw [insertMiddleLabel_get_source_bit, hcontrolB]
        simp [BaseGateOp.insertMiddle, BaseGateOp.applyLabel,
          WireAddress.toffoliMap, hcontrolA, hcontrolB, hcontrolALift,
          hcontrolBLift, insertMiddleLabel_flipBit target source middleLabel]
      · have hcontrolALift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlA)).val = true := by
          rw [insertMiddleLabel_get_source_bit, hcontrolA]
        have hcontrolBFalse :
            source.val.testBit (WireAddress.bitIndex controlB).val = false :=
          Bool.eq_false_iff.mpr hcontrolB
        have hcontrolBLift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlB)).val = false := by
          rw [insertMiddleLabel_get_source_bit, hcontrolBFalse]
        simp [BaseGateOp.insertMiddle, BaseGateOp.applyLabel,
          WireAddress.toffoliMap, hcontrolA, hcontrolBFalse,
          hcontrolALift, hcontrolBLift]
      · have hcontrolAFalse :
            source.val.testBit (WireAddress.bitIndex controlA).val = false :=
          Bool.eq_false_iff.mpr hcontrolA
        have hcontrolALift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlA)).val = false := by
          rw [insertMiddleLabel_get_source_bit, hcontrolAFalse]
        have hcontrolBLift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlB)).val = true := by
          rw [insertMiddleLabel_get_source_bit, hcontrolB]
        simp [BaseGateOp.insertMiddle, BaseGateOp.applyLabel,
          WireAddress.toffoliMap, hcontrolAFalse, hcontrolB,
          hcontrolALift, hcontrolBLift]
      · have hcontrolAFalse :
            source.val.testBit (WireAddress.bitIndex controlA).val = false :=
          Bool.eq_false_iff.mpr hcontrolA
        have hcontrolBFalse :
            source.val.testBit (WireAddress.bitIndex controlB).val = false :=
          Bool.eq_false_iff.mpr hcontrolB
        have hcontrolALift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlA)).val = false := by
          rw [insertMiddleLabel_get_source_bit, hcontrolAFalse]
        have hcontrolBLift :
            (insertMiddleLabel leftWidth middleWidth rightWidth source
                middleLabel).val.testBit
                (WireAddress.bitIndex
                  (BaseGateOp.insertMiddleWire
                    (middleWidth := middleWidth) controlB)).val = false := by
          rw [insertMiddleLabel_get_source_bit, hcontrolBFalse]
        simp [BaseGateOp.insertMiddle, BaseGateOp.applyLabel,
          WireAddress.toffoliMap, hcontrolAFalse, hcontrolBFalse,
          hcontrolALift, hcontrolBLift]

theorem applyLabel_insertMiddle
    {leftWidth middleWidth rightWidth : Nat}
    (program : BaseGateProgram (leftWidth + rightWidth))
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    BaseGateProgram.applyLabel
        (insertMiddle (middleWidth := middleWidth) program)
        (insertMiddleLabel leftWidth middleWidth rightWidth source
          middleLabel) =
      insertMiddleLabel leftWidth middleWidth rightWidth
        (BaseGateProgram.applyLabel program source) middleLabel := by
  induction program generalizing source with
  | nil =>
      rfl
  | cons op rest ih =>
      simp only [insertMiddle, List.map_cons, applyLabel_cons]
      rw [applyLabel_insertMiddleOp]
      exact ih (op.applyLabel source)

namespace Realizes

/-- Lift a realized program on the left component of a product encoding. -/
theorem prodLeft {Left Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    {program : BaseGateProgram left.width} {step : Left -> Left}
    (h : Realizes left program step) :
    Realizes (BinaryLabelEncoding.prod left right)
      (BaseGateProgram.prodLeft (m := left.width) (n := right.width) program)
      (fun x : Prod Left Right => (step x.1, x.2)) where
  applyLabel_eq := by
    intro x
    rcases x with ⟨l, r⟩
    change BaseGateProgram.applyLabel
        (BaseGateProgram.prodLeft
          (m := left.width) (n := right.width) program)
        (prodEquiv (m := left.width) (n := right.width)
          (left.encode l, right.encode r)) =
      prodEquiv (m := left.width) (n := right.width)
        (left.encode (step l), right.encode r)
    rw [BaseGateProgram.applyLabel_prodLeft]
    rw [h.applyLabel_eq l]

/-- Lift a realized program on the right component of a product encoding. -/
theorem prodRight {Left Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    {program : BaseGateProgram right.width} {step : Right -> Right}
    (h : Realizes right program step) :
    Realizes (BinaryLabelEncoding.prod left right)
      (BaseGateProgram.prodRight (m := left.width) (n := right.width) program)
      (fun x : Prod Left Right => (x.1, step x.2)) where
  applyLabel_eq := by
    intro x
    rcases x with ⟨l, r⟩
    change BaseGateProgram.applyLabel
        (BaseGateProgram.prodRight
          (m := left.width) (n := right.width) program)
        (prodEquiv (m := left.width) (n := right.width)
          (left.encode l, right.encode r)) =
      prodEquiv (m := left.width) (n := right.width)
        (left.encode l, right.encode (step r))
    rw [BaseGateProgram.applyLabel_prodRight]
    rw [h.applyLabel_eq r]

/-- Lift a realized program on the outer left/right product across an inserted
middle component.  The lifted program updates the original left/right pair and
preserves the inserted middle component. -/
theorem insertMiddle {Left Middle Right : Type}
    {left : BinaryLabelEncoding Left}
    {middle : BinaryLabelEncoding Middle}
    {right : BinaryLabelEncoding Right}
    {program : BaseGateProgram (left.width + right.width)}
    {step : Left × Right -> Left × Right}
    (h : Realizes (BinaryLabelEncoding.prod left right) program step) :
    Realizes (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod left middle) right)
      (BaseGateProgram.insertMiddle
        (leftWidth := left.width) (middleWidth := middle.width)
        (rightWidth := right.width) program)
      (fun x : (Left × Middle) × Right =>
        let y := step (x.1.1, x.2)
        ((y.1, x.1.2), y.2)) where
  applyLabel_eq := by
    intro x
    rcases x with ⟨⟨l, m⟩, r⟩
    let y := step (l, r)
    change
      BaseGateProgram.applyLabel
          (BaseGateProgram.insertMiddle
            (leftWidth := left.width) (middleWidth := middle.width)
            (rightWidth := right.width) program)
          ((BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left middle) right).encode
              ((l, m), r)) =
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod left middle) right).encode
            ((y.1, m), y.2)
    have hstart :
        (BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left middle) right).encode
            ((l, m), r) =
          BaseGateProgram.insertMiddleLabel left.width middle.width right.width
            ((BinaryLabelEncoding.prod left right).encode (l, r))
            (middle.encode m) := by
      simp [BaseGateProgram.insertMiddleLabel, BinaryLabelEncoding.prod]
    have hend :
        (BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod left middle) right).encode
            ((y.1, m), y.2) =
          BaseGateProgram.insertMiddleLabel left.width middle.width right.width
            ((BinaryLabelEncoding.prod left right).encode y)
            (middle.encode m) := by
      rcases y with ⟨yl, yr⟩
      simp [BaseGateProgram.insertMiddleLabel, BinaryLabelEncoding.prod]
    rw [hstart, hend]
    rw [BaseGateProgram.applyLabel_insertMiddle]
    have hrealized :
        BaseGateProgram.applyLabel program
            (prodEquiv (m := left.width) (n := right.width)
              (left.encode l, right.encode r)) =
          (BinaryLabelEncoding.prod left right).encode y := by
      simpa [y, BinaryLabelEncoding.prod] using h.applyLabel_eq (l, r)
    change
      BaseGateProgram.insertMiddleLabel left.width middle.width right.width
          (BaseGateProgram.applyLabel program
            (prodEquiv (m := left.width) (n := right.width)
              (left.encode l, right.encode r)))
          (middle.encode m) =
        BaseGateProgram.insertMiddleLabel left.width middle.width right.width
          ((BinaryLabelEncoding.prod left right).encode y)
          (middle.encode m)
    rw [hrealized]

end Realizes

end BaseGateProgram

namespace BaseGateSameCircuitWitness

/-- Lift a same-Circuit witness on the left component of a product encoding. -/
def prodLeft {Left Right : Type} {step : Left -> Left}
    (w : BaseGateSameCircuitWitness Left step)
    (right : BinaryLabelEncoding Right) :
    BaseGateSameCircuitWitness (Left × Right)
      (fun x : Left × Right => (step x.1, x.2)) where
  encoding := BinaryLabelEncoding.prod w.encoding right
  program :=
    BaseGateProgram.prodLeft (m := w.encoding.width) (n := right.width) w.program
  realizes :=
    BaseGateProgram.Realizes.prodLeft (left := w.encoding) (right := right)
      w.realizes

/-- Lift a same-Circuit witness on the right component of a product encoding. -/
def prodRight {Left Right : Type} (left : BinaryLabelEncoding Left)
    {step : Right -> Right} (w : BaseGateSameCircuitWitness Right step) :
    BaseGateSameCircuitWitness (Left × Right)
      (fun x : Left × Right => (x.1, step x.2)) where
  encoding := BinaryLabelEncoding.prod left w.encoding
  program :=
    BaseGateProgram.prodRight (m := left.width) (n := w.encoding.width)
      w.program
  realizes :=
    BaseGateProgram.Realizes.prodRight (left := left) (right := w.encoding)
      w.realizes

/-- Lift a same-Circuit witness on an existing left/right product across an
inserted middle component, preserving that middle component. -/
def insertMiddle {Left Middle Right : Type}
    {step : Left × Right -> Left × Right}
    (w : BaseGateSameCircuitWitness (Left × Right) step)
    (left : BinaryLabelEncoding Left)
    (middle : BinaryLabelEncoding Middle)
    (right : BinaryLabelEncoding Right)
    (hencoding : w.encoding = BinaryLabelEncoding.prod left right) :
    BaseGateSameCircuitWitness ((Left × Middle) × Right)
      (fun x : (Left × Middle) × Right =>
        let y := step (x.1.1, x.2)
        ((y.1, x.1.2), y.2)) := by
  cases w with
  | mk encoding program realizes =>
      dsimp at hencoding
      subst encoding
      exact
        { encoding :=
            BinaryLabelEncoding.prod
              (BinaryLabelEncoding.prod left middle) right
          program :=
            BaseGateProgram.insertMiddle
              (leftWidth := left.width) (middleWidth := middle.width)
              (rightWidth := right.width) program
          realizes :=
            BaseGateProgram.Realizes.insertMiddle
              (middle := middle) realizes }

end BaseGateSameCircuitWitness

end

end QuantumAlg
