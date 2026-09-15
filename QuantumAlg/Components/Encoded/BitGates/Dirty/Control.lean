/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl

/-!
# Actual list control with one arbitrary restored work bit

An additional control changes X to CNOT and CNOT to Toffoli. An existing
Toffoli uses the three-control instance of the actual balanced dirty-bit
construction. Its four Toffolis cancel the arbitrary initial work value
by the toggle principle [G17, paper.tex:278-293].

The resulting complete gate list conditionally performs the original
list on every encoded data value. Neither work initialization nor a
separation assumption is required. Its exact elementary length counts
one gate for each original X or CNOT and four for each original Toffoli.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private def threeBits (control first second : EncodedBit encoding) : Word encoding 3 where
  bit index := if index.val = 0 then control else if index.val = 1 then first else second

private def threeControlLayout (control first second target work : EncodedBit encoding)
    (cf : control.wire ≠ first.wire) (cs : control.wire ≠ second.wire)
    (ct : control.wire ≠ target.wire) (cw : control.wire ≠ work.wire)
    (fs : first.wire ≠ second.wire) (ft : first.wire ≠ target.wire)
    (st : second.wire ≠ target.wire) (fw : first.wire ≠ work.wire)
    (sw : second.wire ≠ work.wire) (wt : work.wire ≠ target.wire) :
    Word.OneDirtyLayout (encoding := encoding) 3 where
  source := threeBits control first second
  output := target
  work := work
  source_injective := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all [threeBits]
  source_output_ne := by
    intro index
    fin_cases index <;> simp_all [threeBits]
  source_work_ne := by
    intro index
    fin_cases index <;> simp_all [threeBits]
  work_output_ne := wt

private theorem threeBits_all (control first second : EncodedBit encoding) (state : Data) :
    (∀ index, ((threeBits control first second).bit index).get state = true) ↔
      control.get state = true ∧ first.get state = true ∧ second.get state = true := by
  constructor
  · intro allBits
    exact ⟨allBits 0, allBits 1, allBits 2⟩
  · rintro ⟨selected, left, right⟩ index
    fin_cases index
    · exact selected
    · exact left
    · exact right

/-- A literal controlled elementary gate, using arbitrary work only for three controls. -/
def withDirtyControl (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate) (hwork : bitDisjoint work gate)
    (different : control.wire ≠ work.wire) : List (GateSpec encoding) :=
  match gate with
  | .x target => [.cnot control target hcontrol.symm]
  | .cnot source target separated =>
      [.toffoli control source target hcontrol.1.symm hcontrol.2.symm separated]
  | .toffoli first second target fs ft st =>
      (threeControlLayout control first second target work hcontrol.1.symm
        hcontrol.2.1.symm hcontrol.2.2.symm different fs ft st
        hwork.1 hwork.2.1 hwork.2.2.symm).gates

/-- Exact complete action for arbitrary work, with no additional initialization premise. -/
theorem withDirtyControl_step (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate) (hwork : bitDisjoint work gate)
    (different : control.wire ≠ work.wire) (state : Data) :
    stepList (withDirtyControl control work gate hcontrol hwork different) state =
      if control.get state then gate.step state else state := by
  cases gate with
  | x target => rfl
  | cnot source target separated =>
      change (if control.get state && source.get state then target.flip state else state) =
        if control.get state then
          (if source.get state then target.flip state else state) else state
      cases control.get state <;> cases source.get state <;> rfl
  | toffoli first second target fs ft st =>
      rw [withDirtyControl, Word.OneDirtyLayout.gates_step]
      change (if ∀ index, ((threeBits control first second).bit index).get state = true
        then target.flip state else state) =
        if control.get state then
          (if first.get state && second.get state then target.flip state else state) else state
      simp only [threeBits_all]
      cases control.get state <;> cases first.get state <;> cases second.get state <;> rfl

/-- The actual expansion weight for an original elementary gate. -/
def dirtyControlCount : GateSpec encoding → Nat
  | .x _ => 1
  | .cnot _ _ _ => 1
  | .toffoli _ _ _ _ _ _ => 4

/-- Three controls use exactly four Toffolis in the already constructed dirty-bit list. -/
theorem withDirtyControl_length (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate) (hwork : bitDisjoint work gate)
    (different : control.wire ≠ work.wire) :
    (withDirtyControl control work gate hcontrol hwork different).length =
      dirtyControlCount gate := by
  cases gate with
  | x target => rfl
  | cnot source target separated => rfl
  | toffoli first second target fs ft st =>
      rw [withDirtyControl, Word.OneDirtyLayout.gates_length_of_large _ (by decide)]
      rfl

/-- Apply the same true dirty-work control construction to every original gate in order. -/
def listWithDirtyControl (control work : EncodedBit encoding) :
    (gates : List (GateSpec encoding)) →
    (∀ gate, gate ∈ gates → bitDisjoint control gate) →
    (∀ gate, gate ∈ gates → bitDisjoint work gate) →
    (control.wire ≠ work.wire) → List (GateSpec encoding)
  | [], _, _, _ => []
  | gate :: rest, hcontrol, hwork, different =>
      withDirtyControl control work gate (hcontrol gate (by simp))
        (hwork gate (by simp)) different ++
      listWithDirtyControl control work rest
        (fun next present => hcontrol next (by simp [present]))
        (fun next present => hwork next (by simp [present])) different

/-- The whole actual list performs precisely the original list selected by the retained control. -/
theorem listWithDirtyControl_step (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) (state : Data) :
    stepList (listWithDirtyControl control work gates hcontrol hwork different) state =
      if control.get state then stepList gates state else state := by
  induction gates generalizing state with
  | nil =>
      change state = if control.get state then state else state
      split <;> rfl
  | cons gate rest ih =>
      rw [listWithDirtyControl, stepList_append, withDirtyControl_step]
      by_cases selected : control.get state = true
      · rw [if_pos selected, ih,
          step_get_of_bitDisjoint gate control (hcontrol gate (by simp)), if_pos selected,
          if_pos selected]
        rfl
      · rw [if_neg selected, ih, if_neg selected, if_neg selected]

/-- Arbitrary borrowed work is restored by the entire actual controlled program. -/
theorem listWithDirtyControl_work (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) (state : Data) :
    work.get (stepList (listWithDirtyControl control work gates hcontrol hwork different) state) =
      work.get state := by
  rw [listWithDirtyControl_step]
  split
  · exact stepList_get_of_bitDisjoint gates work hwork state
  · rfl

/-- The selecting control keeps its exact value on every input. -/
theorem listWithDirtyControl_control (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) (state : Data) :
    control.get
        (stepList (listWithDirtyControl control work gates hcontrol hwork different) state) =
      control.get state := by
  rw [listWithDirtyControl_step]
  split
  · exact stepList_get_of_bitDisjoint gates control hcontrol state
  · rfl

/-- Exact elementary length of this implementation, derived from its emitted gate list. -/
theorem listWithDirtyControl_length (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) :
    (listWithDirtyControl control work gates hcontrol hwork different).length =
      (gates.map dirtyControlCount).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [listWithDirtyControl, List.length_append, withDirtyControl_length, ih]
      rfl

/-- The actual compiled native program has the same complete conditional action. -/
theorem listWithDirtyControl_realizes (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) :
    UnitaryCircuit.Realizes encoding
      (programList (listWithDirtyControl control work gates hcontrol hwork different))
      (fun state => if control.get state then stepList gates state else state) :=
  realizesList_congrStep _
    (listWithDirtyControl_step control work gates hcontrol hwork different)

end

end QuantumAlg.EncodedBit.GateSpec
