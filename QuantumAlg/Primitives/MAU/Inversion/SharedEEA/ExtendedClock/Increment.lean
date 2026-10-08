/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

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

private theorem focusedWidth (width : Nat) :
    (Addition.HRS.bridgeEncoding (extra width + clockWidth width)
      (clockWidth width)).width =
      (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width := by
  rw [Addition.HRS.hrsBridgeEncoding_width, Addition.HRS.hrsBridgeEncoding_width,
    extra_add_clockWidth]

private def sourceInput (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width)) :
    Addition.HRS.BridgeRegisters
      (Fin (2 ^ (extra width + clockWidth width))) (clockWidth width) :=
  ((finCongr (congrArg (fun count => 2 ^ count)
    (extra_add_clockWidth width).symm) state.1.1, state.1.2), state.2)

private theorem bridgeEncoding_cast {low target high : Nat} (same : low = target)
    (sameWidth : (Addition.HRS.bridgeEncoding low high).width =
      (Addition.HRS.bridgeEncoding target high).width)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ target)) high) :
    UnitaryCircuit.castQubitWidthIndex sameWidth
      ((Addition.HRS.bridgeEncoding low high).encode
        ((finCongr (congrArg (fun count => 2 ^ count) same.symm) state.1.1,
          state.1.2), state.2)) =
      (Addition.HRS.bridgeEncoding target high).encode state := by
  cases same
  cases sameWidth
  rfl

private theorem bridgeOutput_cast {low target high : Nat} (same : low = target)
    (sameWidth : (Addition.HRS.bridgeEncoding low high).width =
      (Addition.HRS.bridgeEncoding target high).width)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ target)) high) :
    UnitaryCircuit.castQubitWidthIndex sameWidth
      ((Addition.HRS.bridgeEncoding low high).encode
        (Addition.HRS.bridgeIncrementStep
          ((finCongr (congrArg (fun count => 2 ^ count) same.symm) state.1.1,
            state.1.2), state.2))) =
      (Addition.HRS.bridgeEncoding target high).encode
        (Addition.HRS.bridgeIncrementStep state) := by
  cases same
  cases sameWidth
  rfl

private theorem sourceInput_encode (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width)) :
    UnitaryCircuit.castQubitWidthIndex (focusedWidth width)
      ((Addition.HRS.bridgeEncoding (extra width + clockWidth width)
        (clockWidth width)).encode (sourceInput width state)) =
      (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).encode state := by
  exact bridgeEncoding_cast (extra_add_clockWidth width) (focusedWidth width) state

private theorem sourceOutput_encode (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width)) :
    UnitaryCircuit.castQubitWidthIndex (focusedWidth width)
      ((Addition.HRS.bridgeEncoding (extra width + clockWidth width)
        (clockWidth width)).encode
          (Addition.HRS.bridgeIncrementStep (sourceInput width state))) =
      (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).encode
        (Addition.HRS.bridgeIncrementStep state) := by
  exact bridgeOutput_cast (extra_add_clockWidth width) (focusedWidth width) state

/-- Actual HRS controlled arithmetic with only a proved equality of the borrowed-word width. -/
def focusedProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width).toQuantum :=
  UnitaryCircuit.castCanonicalQubitWidth (focusedWidth width)
    (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width))

private theorem focused_realizes (width : Nat) :
    UnitaryCircuit.Realizes (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width))
      (focusedProgram width) Addition.HRS.bridgeIncrementStep where
  apply_encoded_ket := by
    intro state
    have original := (Addition.HRS.hrsPlacedIncrement_realizes
      (extra width) (clockWidth width)).apply_encoded_ket (sourceInput width state)
    have inputKet :
        focusedWidth width ▸ NormalizedVector.ket
          ((QubitLayout.canonical
            (Addition.HRS.bridgeEncoding (extra width + clockWidth width)
              (clockWidth width)).width).basisEquiv.symm
            ((Addition.HRS.bridgeEncoding (extra width + clockWidth width)
              (clockWidth width)).encode (sourceInput width state))) =
          NormalizedVector.ket
            ((QubitLayout.canonical
              (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width).basisEquiv.symm
              ((Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).encode state)) := by
      rw [UnitaryCircuit.castCanonicalQubitWidth_ket]
      exact congrArg (fun label => NormalizedVector.ket
        ((QubitLayout.canonical
          (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width).basisEquiv.symm
          label)) (sourceInput_encode width state)
    have outputKet :
        focusedWidth width ▸ NormalizedVector.ket
          ((QubitLayout.canonical
            (Addition.HRS.bridgeEncoding (extra width + clockWidth width)
              (clockWidth width)).width).basisEquiv.symm
            ((Addition.HRS.bridgeEncoding (extra width + clockWidth width)
              (clockWidth width)).encode
                (Addition.HRS.bridgeIncrementStep (sourceInput width state)))) =
          NormalizedVector.ket
            ((QubitLayout.canonical
              (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width).basisEquiv.symm
              ((Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).encode
                (Addition.HRS.bridgeIncrementStep state))) := by
      rw [UnitaryCircuit.castCanonicalQubitWidth_ket]
      exact congrArg (fun label => NormalizedVector.ket
        ((QubitLayout.canonical
          (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width)).width).basisEquiv.symm
          label)) (sourceOutput_encode width state)
    calc
      _ = (focusedProgram width).applyNormalized
          (focusedWidth width ▸ NormalizedVector.ket
            ((QubitLayout.canonical
              (Addition.HRS.bridgeEncoding (extra width + clockWidth width)
                (clockWidth width)).width).basisEquiv.symm
              ((Addition.HRS.bridgeEncoding (extra width + clockWidth width)
                (clockWidth width)).encode (sourceInput width state)))) :=
        congrArg (focusedProgram width).applyNormalized inputKet.symm
      _ = focusedWidth width ▸
          (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width)).applyNormalized
            (NormalizedVector.ket
              ((QubitLayout.canonical
                (Addition.HRS.bridgeEncoding (extra width + clockWidth width)
                  (clockWidth width)).width).basisEquiv.symm
                ((Addition.HRS.bridgeEncoding (extra width + clockWidth width)
                  (clockWidth width)).encode (sourceInput width state)))) :=
        UnitaryCircuit.castCanonicalQubitWidth_applyNormalized _ _ _
      _ = focusedWidth width ▸ NormalizedVector.ket
          ((QubitLayout.canonical
            (Addition.HRS.bridgeEncoding (extra width + clockWidth width)
              (clockWidth width)).width).basisEquiv.symm
            ((Addition.HRS.bridgeEncoding (extra width + clockWidth width)
              (clockWidth width)).encode
                (Addition.HRS.bridgeIncrementStep (sourceInput width state)))) :=
        congrArg (fun vector => focusedWidth width ▸ vector) original
      _ = _ := outputKet

private def groupedProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ExtendedClockPlacement.groupedEncoding width).width).toQuantum :=
  UnitaryCircuit.prodLeft (n := (ExtendedClockPlacement.remainderEncoding width).width)
    (focusedProgram width)

private theorem grouped_realizes (width : Nat) :
    UnitaryCircuit.Realizes (ExtendedClockPlacement.groupedEncoding width)
      (groupedProgram width)
      (fun pair => (Addition.HRS.bridgeIncrementStep pair.1, pair.2)) := by
  simpa only [groupedProgram, UnitaryCircuit.prodLeft,
    ExtendedClockPlacement.groupedEncoding] using
    (focused_realizes width).onBinaryPrefix
      (right := ExtendedClockPlacement.remainderEncoding width)

/-- The same actual HRS program placed on all original source fields. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (ExtendedClockPlacement.placement width).place (groupedProgram width)

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
    UnitaryCircuit.Realizes (encoding width) (program width) step := by
  apply ((ExtendedClockPlacement.placement width).place_realizes
    (grouped_realizes width)).congrStep
  intro state
  simpa only [EncodedBit.FullPlacement.step,
    ExtendedClockPlacement.placement_grouping_eq] using placed_step width state

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
    UnitaryCircuit.Realizes (encoding width)
      ((program width).dagger (AlgorithmGate.oracleFreeAdjoints .empty)) inverseStep := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse (program_realizes width)
  · rw [UnitaryCircuit.dagger_matrix]
    exact Unitary.star_eq_inv _
  · exact step_inverseStep width

/-- Every real HRS elementary event is retained in its literal original order. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width)).eventTrace := by
  calc
    _ = (groupedProgram width).eventTrace :=
      EncodedBit.FullPlacement.place_eventTrace _ _
    _ = (focusedProgram width).eventTrace := by rfl
    _ = _ := UnitaryCircuit.castCanonicalQubitWidth_eventTrace _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockIncrement
