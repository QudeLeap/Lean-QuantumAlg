/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Placement

/-!
# Actual HRS arithmetic on the original low shift register

The existing HRS controlled incrementer borrows the low counter-width
bits of Work1 and restores the complete word. The target is the actual
finite shift field and the control is the actual Phase2 wire
[HRS16, paper.tex:219-224; LYL+26, sec_EEA/sub_opt.tex:37-40,68-70].

Only a proved equality of the same Work1 width precedes the full physical
placement. All incoming source fields, including the borrowed Work1 and
the control, are arbitrary. The inverse is the actual circuit dagger and
therefore retains the literal reversed elementary events. These operations
are on the original low counter; terminal high-bit integration remains a
separate controlled operation on the already identified Work1 positions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LowShiftIncrement

noncomputable section

open LowShiftRegisters

private def sourceInput (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size) :
    Addition.HRS.BridgeRegisters (Fin (2 ^ (extra width + width.size))) width.size :=
  ((finCongr (congrArg (fun count => 2 ^ count) (extra_add_length width).symm) state.1.1,
    state.1.2), state.2)

private def sourceIndex (width : Nat) :
    (Qubits (Addition.HRS.bridgeEncoding (extra width + width.size) width.size).width).Index ≃
      (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width).Index :=
  finCongr (congrArg (fun count : Nat => 2 ^ count)
    (congrArg (fun count => count + width.size + 1) (extra_add_length width)))

private theorem sourceIndex_input (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size) :
    sourceIndex width
      ((Addition.HRS.bridgeEncoding (extra width + width.size) width.size).encode
        (sourceInput width state)) =
      (Addition.HRS.bridgeEncoding (width + 3) width.size).encode state := by
  apply Fin.ext
  rfl

private theorem sourceIndex_output (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size) :
    sourceIndex width
      ((Addition.HRS.bridgeEncoding (extra width + width.size) width.size).encode
        (Addition.HRS.bridgeIncrementStep (sourceInput width state))) =
      (Addition.HRS.bridgeEncoding (width + 3) width.size).encode
        (Addition.HRS.bridgeIncrementStep state) := by
  rcases state with ⟨⟨work, shift⟩, control⟩
  cases control <;> apply Fin.ext <;> rfl

/-- The actual HRS prefix/borrowed/target circuit, at the exact original source field widths. -/
def focusedProgram (width : Nat) :
    UnitaryCircuit (Qubits (Addition.HRS.bridgeEncoding (width + 3) width.size).width) :=
  UnitaryCircuit.reindex (sourceIndex width)
    (Addition.HRS.placedIncrementProgram (extra width) width.size)

private theorem focused_realizes (width : Nat) :
    UnitaryCircuit.Realizes (Addition.HRS.bridgeEncoding (width + 3) width.size)
      (focusedProgram width) Addition.HRS.bridgeIncrementStep where
  apply_encoded_ket := by
    intro state
    have original := (Addition.HRS.hrsPlacedIncrement_realizes
      (extra width) width.size).apply_encoded_ket (sourceInput width state)
    have transported := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits ((extra width + width.size) + width.size + 1))
      (S := Qubits ((width + 3) + width.size + 1))
      (sourceIndex width) (Addition.HRS.placedIncrementProgram (extra width) width.size)
        _ _ original
    have inputKet := congrArg
      (fun label : (Qubits ((width + 3) + width.size + 1)).Index =>
        NormalizedVector.ket (R := Qubits ((width + 3) + width.size + 1)) label)
      (sourceIndex_input width state)
    have outputKet := congrArg
      (fun label : (Qubits ((width + 3) + width.size + 1)).Index =>
        NormalizedVector.ket (R := Qubits ((width + 3) + width.size + 1)) label)
      (sourceIndex_output width state)
    exact (congrArg (focusedProgram width).applyNormalized inputKet.symm).trans
      (transported.trans outputKet)

private theorem focused_range (width : Nat) :
    (focusedProgram width).physical_idx ⊆ List.range (width + 3 + width.size + 1) := by
  have original := Addition.HRS.hrsPlacedIncrement_physical_range (extra width) width.size
  change (Addition.HRS.placedIncrementProgram (extra width) width.size).physical_idx ⊆ _
  simpa only [extra_add_length] using original

/-- Execute the native HRS circuit on the same complete shared frame and its actual addresses. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  LowShiftPlacement.place width (focusedProgram width) (focused_range width)

/-- The finite source counter is incremented exactly when its actual Phase2 control is set. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  if state.flags.second then { state with shift := state.shift + 1 } else state

private theorem increment_word {width : Nat} (word : BitVec width) :
    BitVec.equivFin.symm (Addition.HRS.incrementWord (BitVec.equivFin word)) = word + 1 := by
  apply BitVec.eq_of_toNat_eq
  change (word.toNat + 1) % 2 ^ width = (word.toNat + 1 % 2 ^ width) % 2 ^ width
  exact (Nat.add_mod_mod word.toNat 1 (2 ^ width)).symm

private theorem placed_step (width : Nat) (state : Registers width) :
    LowShiftPlacement.placedStep Addition.HRS.bridgeIncrementStep state = step state := by
  have actual : LowShiftPlacement.placedStep Addition.HRS.bridgeIncrementStep state =
      if state.flags.second then
        { state with shift :=
          BitVec.equivFin.symm (Addition.HRS.incrementWord (BitVec.equivFin state.shift)) }
      else state := by
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iter⟩, control⟩
    cases p2 <;> rfl
  rw [actual, increment_word]
  rfl

/-- Exact full-frame action restores every borrowed bit, including arbitrary joint coherences. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) step :=
  (LowShiftPlacement.place_realizes width (focused_range width)
    (focused_realizes width)).congrStep (placed_step width)

/-- The inverse decrements the same original finite register under the same preserved control. -/
def inverseStep {width : Nat} (state : Registers width) : Registers width :=
  if state.flags.second then { state with shift := state.shift - 1 } else state

private theorem step_inverseStep (width : Nat) (state : Registers width) :
    step (inverseStep state) = state := by
  by_cases chosen : state.flags.second
  · simp only [inverseStep, chosen, if_true, step, BitVec.sub_add_cancel]
  · simp only [inverseStep, chosen, Bool.false_eq_true, if_false, step]

/-- The actual dagger circuit realizes finite decrement, rather than replacing it by a callback. -/
theorem inverse_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width).dagger inverseStep :=
  (program_realizes width).dagger_of_rightInverse (step_inverseStep width)

/-- The complete live footprint contains exactly the already present source registers. -/
theorem program_physical (width : Nat) :
    (program width).physical_idx = List.range (encoding width).width :=
  LowShiftPlacement.place_physical width (focusedProgram width) (focused_range width)

/-- The native HRS trace survives the actual field-width transport and source placement. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      (Addition.HRS.placedIncrementProgram (extra width) width.size).eventTrace := by
  rw [program, LowShiftPlacement.place_eventTrace, focusedProgram,
    UnitaryCircuit.reindex_eventTrace]

/-- The decrement executes the literal reversed original elementary trace. -/
theorem inverse_eventTrace (width : Nat) :
    (program width).dagger.eventTrace =
      (Addition.HRS.placedIncrementProgram (extra width) width.size).eventTrace.reverse := by
  rw [UnitaryCircuit.dagger_eventTrace, program_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.LowShiftIncrement
