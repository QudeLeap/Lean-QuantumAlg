/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Placement

/-!
# Actual HRS increment and inverse on existing high and low clock bits

The real controlled HRS gate sequence is applied to the complete Work2
borrowed word and the counter formed by the two existing Work1 positions
followed by the old low shift [HRS16, paper.tex:219-226,232-260].
Its literal elementary trace is retained under the proved complete
field placement. The inverse is that actual circuit's dagger.

Every full frame is covered, including arbitrary Work2 and arbitrary
incoming high-counter bits. Only the target clock changes when Phase2
is set. Main Work1, its last bit, all lengths and flags, and the entire
borrowed Work2 are retained exactly. No terminal zero-bit condition is
used by the gate realization, and no additional physical wire appears
[LYL+26, sec_EEA/sub_regshare.tex:16-26].

Selecting these native assignments in the complete repaired phase loop,
proving the active high-bit invariant, and connecting the full terminal
schedule are separate obligations. The original native microstep is not
silently replaced by this component.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockIncrement

noncomputable section

open ExtendedClockRegisters NumberTheory.SharedEEA

private def sourceInput (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width)) :
    Addition.HRS.BridgeRegisters (Fin (2 ^ (extra width + clockWidth width)))
      (clockWidth width) :=
  ((finCongr (congrArg (fun count => 2 ^ count) (extra_add_clockWidth width).symm) state.1.1,
    state.1.2), state.2)

private def sourceIndex (width : Nat) :
    (Qubits (Addition.HRS.bridgeEncoding (extra width + clockWidth width)
      (clockWidth width)).width).Index ≃
      (Qubits (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width).Index :=
  finCongr (congrArg (fun count : Nat => 2 ^ count)
    (congrArg (fun count => count + clockWidth width + 1) (extra_add_clockWidth width)))

private theorem sourceIndex_input (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width)) :
    sourceIndex width
      ((Addition.HRS.bridgeEncoding (extra width + clockWidth width) (clockWidth width)).encode
        (sourceInput width state)) =
      (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).encode state := by
  apply Fin.ext
  rfl

private theorem sourceIndex_output (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width)) :
    sourceIndex width
      ((Addition.HRS.bridgeEncoding (extra width + clockWidth width) (clockWidth width)).encode
        (Addition.HRS.bridgeIncrementStep (sourceInput width state))) =
      (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).encode
        (Addition.HRS.bridgeIncrementStep state) := by
  rcases state with ⟨⟨work, target⟩, control⟩
  cases control <;> apply Fin.ext <;> rfl

/-- Actual HRS controlled arithmetic with only a proved equality of the borrowed-word width. -/
def focusedProgram (width : Nat) :
    UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width) :=
  UnitaryCircuit.reindex (sourceIndex width)
    (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width))

private theorem focused_realizes (width : Nat) :
    UnitaryCircuit.Realizes (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width))
      (focusedProgram width) Addition.HRS.bridgeIncrementStep where
  apply_encoded_ket := by
    intro state
    have original := (Addition.HRS.hrsPlacedIncrement_realizes
      (extra width) (clockWidth width)).apply_encoded_ket (sourceInput width state)
    have transported := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits ((extra width + clockWidth width) + clockWidth width + 1))
      (S := Qubits ((width + 3) + clockWidth width + 1))
      (sourceIndex width) (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width))
        _ _ original
    have inputKet := congrArg
      (fun label : (Qubits ((width + 3) + clockWidth width + 1)).Index =>
        NormalizedVector.ket (R := Qubits ((width + 3) + clockWidth width + 1)) label)
      (sourceIndex_input width state)
    have outputKet := congrArg
      (fun label : (Qubits ((width + 3) + clockWidth width + 1)).Index =>
        NormalizedVector.ket (R := Qubits ((width + 3) + clockWidth width + 1)) label)
      (sourceIndex_output width state)
    exact (congrArg (focusedProgram width).applyNormalized inputKet.symm).trans
      (transported.trans outputKet)

private theorem focused_range (width : Nat) :
    (focusedProgram width).physical_idx ⊆ List.range (width + 3 + clockWidth width + 1) := by
  have original := Addition.HRS.hrsPlacedIncrement_physical_range (extra width) (clockWidth width)
  change (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width)).physical_idx ⊆ _
  simpa only [extra_add_clockWidth] using original

private def groupedProgram (width : Nat) :
    UnitaryCircuit (Qubits (ExtendedClockPlacement.groupedEncoding width).width) :=
  UnitaryCircuit.prodLeft (n := (ExtendedClockPlacement.remainderEncoding width).width)
    (focusedProgram width)

private theorem grouped_range (width : Nat) :
    (groupedProgram width).physical_idx ⊆
      List.range (ExtendedClockPlacement.groupedEncoding width).width := by
  unfold groupedProgram UnitaryCircuit.prodLeft
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · intro wire present
    have bound := List.mem_range.mp (focused_range width present)
    apply List.mem_range.mpr
    rw [ExtendedClockPlacement.grouped_width]
    omega
  · simp only [UnitaryCircuit.identity, List.nil_subset]

/-- The same actual HRS program placed on all original source fields. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (ExtendedClockPlacement.placement width).place (groupedProgram width) (grouped_range width)

/-- Complete finite increment of the two physical high bits and low counter under Phase2. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  if state.flags.second then
    let pair := PaddingClock.increment (state.firstWord, state.shift)
    { state with firstWord := pair.1, shift := pair.2 }
  else state

private theorem increment_word {width : Nat} (word : BitVec width) :
    BitVec.equivFin.symm (Addition.HRS.incrementWord (BitVec.equivFin word)) = word + 1 := by
  apply BitVec.eq_of_toNat_eq
  change (word.toNat + 1) % 2 ^ width = (word.toNat + 1 % 2 ^ width) % 2 ^ width
  exact (Nat.add_mod_mod word.toNat 1 (2 ^ width)).symm

private theorem placed_step (width : Nat) (state : Registers width) :
    (grouping width).symm
      (Addition.HRS.bridgeIncrementStep (grouping width state).1, (grouping width state).2) =
      step state := by
  by_cases chosen : state.flags.second
  · have action : Addition.HRS.bridgeIncrementStep (grouping width state).1 =
        (((grouping width state).1.1.1,
          Addition.HRS.incrementWord (grouping width state).1.1.2), true) := by
      change (if state.flags.second then _ else _) = _
      rw [if_pos chosen]
      exact congrArg (fun control => (_, control)) (show state.flags.second = true from chosen)
    rw [action]
    unfold step
    rw [if_pos chosen]
    let current : BitVec (2 + width.size) :=
      PaddingClock.high state.firstWord ++ state.shift
    have value := increment_word current
    change { state with
      firstWord := (PaddingClock.join ((PaddingClock.main state.firstWord,
        PaddingClock.last state.firstWord), BitVec.equivFin.symm
          (Addition.HRS.incrementWord (BitVec.equivFin current)))).1
      shift := (PaddingClock.join ((PaddingClock.main state.firstWord,
        PaddingClock.last state.firstWord), BitVec.equivFin.symm
          (Addition.HRS.incrementWord (BitVec.equivFin current)))).2
      flags := ⟨state.flags.first, true, state.flags.sign, state.flags.iteration⟩ } = _
    rw [value]
    have flags : (⟨state.flags.first, true, state.flags.sign, state.flags.iteration⟩ :
        PhaseControl.Flags) = state.flags := by
      rw [← chosen]
    rw [flags]
    rfl
  · have action : Addition.HRS.bridgeIncrementStep (grouping width state).1 =
        (grouping width state).1 := by
      change (if state.flags.second then _ else _) = _
      exact if_neg chosen
    rw [action, (grouping width).symm_apply_apply, step, if_neg chosen]

/-- Exact full-frame action preserves all borrowed and complementary amplitudes and correlations. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) step :=
  ((ExtendedClockPlacement.placement width).place_realizes (grouped_range width)
    ((focused_realizes width).prodLeft
      (right := ExtendedClockPlacement.remainderEncoding width))).congrStep (placed_step width)

/-- The inverse finite assignment uses exactly the same retained control and physical clock. -/
def inverseStep {width : Nat} (state : Registers width) : Registers width :=
  if state.flags.second then
    let pair := PaddingClock.decrement (state.firstWord, state.shift)
    { state with firstWord := pair.1, shift := pair.2 }
  else state

private theorem step_inverseStep (width : Nat) (state : Registers width) :
    step (inverseStep state) = state := by
  by_cases chosen : state.flags.second
  · simp only [step, inverseStep, chosen, if_true]
    exact congrArg
      (fun pair : BitVec (width + 3) × BitVec width.size =>
        { state with firstWord := pair.1, shift := pair.2 })
      (PaddingClock.increment_decrement (state.firstWord, state.shift))
  · simp only [step, inverseStep, chosen, Bool.false_eq_true, if_false]

/-- The literal native dagger implements the full physical decrement and restores borrowed Work2. -/
theorem inverse_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width).dagger inverseStep :=
  (program_realizes width).dagger_of_rightInverse (step_inverseStep width)

/-- The physical footprint is exactly the original frame, with no added high-counter workspace. -/
theorem program_physical (width : Nat) :
    (program width).physical_idx = List.range (encoding width).width :=
  (ExtendedClockPlacement.placement width).place_physical
    (groupedProgram width) (grouped_range width)

/-- Every real HRS elementary event is retained in its literal original order. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width)).eventTrace := by
  rw [program, EncodedBit.FullPlacement.place_eventTrace, groupedProgram,
    UnitaryCircuit.prodLeft_eventTrace, focusedProgram, UnitaryCircuit.reindex_eventTrace]

/-- The inverse executes the actual reversed HRS elementary-event list. -/
theorem inverse_eventTrace (width : Nat) :
    (program width).dagger.eventTrace =
      (Addition.HRS.placedIncrementProgram (extra width)
        (clockWidth width)).eventTrace.reverse := by
  rw [UnitaryCircuit.dagger_eventTrace, program_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockIncrement
