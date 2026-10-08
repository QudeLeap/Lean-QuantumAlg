/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Actual HRS arithmetic on the original low shift register

The existing HRS controlled incrementer borrows the low counter-width
bits of Work1 and restores the complete word. The target is the actual
finite shift field and the control is the actual Phase2 wire
[HRS16, paper.tex:219-224; LYL+26, sec_EEA/sub_opt.tex:37-40,68-70].

Only a proved equality of the same Work1 width precedes the full physical
placement. All incoming source fields, including the borrowed Work1 and
the control, are arbitrary. The inverse is the actual generated circuit dagger.
These operations
are on the original low counter; terminal high-bit integration remains a
separate controlled operation on the already identified Work1 positions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LowShiftIncrement

noncomputable section

open LowShiftRegisters

private theorem focusedWidth (width : Nat) :
    (Addition.HRS.bridgeEncoding (extra width + width.size)
      (width.size)).width =
      (Addition.HRS.bridgeEncoding (width + 3) (width.size)).width := by
  rw [Addition.HRS.hrsBridgeEncoding_width, Addition.HRS.hrsBridgeEncoding_width,
    extra_add_length]

private def sourceInput (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (width.size)) :
    Addition.HRS.BridgeRegisters
      (Fin (2 ^ (extra width + width.size))) (width.size) :=
  ((finCongr (congrArg (fun count => 2 ^ count)
    (extra_add_length width).symm) state.1.1, state.1.2), state.2)

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
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (width.size)) :
    UnitaryCircuit.castQubitWidthIndex (focusedWidth width)
      ((Addition.HRS.bridgeEncoding (extra width + width.size)
        (width.size)).encode (sourceInput width state)) =
      (Addition.HRS.bridgeEncoding (width + 3) (width.size)).encode state := by
  exact bridgeEncoding_cast (extra_add_length width) (focusedWidth width) state

private theorem sourceOutput_encode (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (width.size)) :
    UnitaryCircuit.castQubitWidthIndex (focusedWidth width)
      ((Addition.HRS.bridgeEncoding (extra width + width.size)
        (width.size)).encode
          (Addition.HRS.bridgeIncrementStep (sourceInput width state))) =
      (Addition.HRS.bridgeEncoding (width + 3) (width.size)).encode
        (Addition.HRS.bridgeIncrementStep state) := by
  exact bridgeOutput_cast (extra_add_length width) (focusedWidth width) state

/-- Actual HRS controlled arithmetic with only a proved equality of the borrowed-word width. -/
def focusedProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (Addition.HRS.bridgeEncoding (width + 3) (width.size)).width).toQuantum :=
  UnitaryCircuit.castCanonicalQubitWidth (focusedWidth width)
    (Addition.HRS.placedIncrementProgram (extra width) (width.size))

private theorem focused_realizes (width : Nat) :
    UnitaryCircuit.Realizes (Addition.HRS.bridgeEncoding (width + 3) (width.size))
      (focusedProgram width) Addition.HRS.bridgeIncrementStep where
  apply_encoded_ket := by
    intro state
    have original := (Addition.HRS.hrsPlacedIncrement_realizes
      (extra width) (width.size)).apply_encoded_ket (sourceInput width state)
    have inputKet :
        focusedWidth width ▸ NormalizedVector.ket
          ((QubitLayout.canonical
            (Addition.HRS.bridgeEncoding (extra width + width.size)
              (width.size)).width).basisEquiv.symm
            ((Addition.HRS.bridgeEncoding (extra width + width.size)
              (width.size)).encode (sourceInput width state))) =
          NormalizedVector.ket
            ((QubitLayout.canonical
              (Addition.HRS.bridgeEncoding (width + 3) (width.size)).width).basisEquiv.symm
              ((Addition.HRS.bridgeEncoding (width + 3) (width.size)).encode state)) := by
      rw [UnitaryCircuit.castCanonicalQubitWidth_ket]
      exact congrArg (fun label => NormalizedVector.ket
        ((QubitLayout.canonical
          (Addition.HRS.bridgeEncoding (width + 3) (width.size)).width).basisEquiv.symm
          label)) (sourceInput_encode width state)
    have outputKet :
        focusedWidth width ▸ NormalizedVector.ket
          ((QubitLayout.canonical
            (Addition.HRS.bridgeEncoding (extra width + width.size)
              (width.size)).width).basisEquiv.symm
            ((Addition.HRS.bridgeEncoding (extra width + width.size)
              (width.size)).encode
                (Addition.HRS.bridgeIncrementStep (sourceInput width state)))) =
          NormalizedVector.ket
            ((QubitLayout.canonical
              (Addition.HRS.bridgeEncoding (width + 3) (width.size)).width).basisEquiv.symm
              ((Addition.HRS.bridgeEncoding (width + 3) (width.size)).encode
                (Addition.HRS.bridgeIncrementStep state))) := by
      rw [UnitaryCircuit.castCanonicalQubitWidth_ket]
      exact congrArg (fun label => NormalizedVector.ket
        ((QubitLayout.canonical
          (Addition.HRS.bridgeEncoding (width + 3) (width.size)).width).basisEquiv.symm
          label)) (sourceOutput_encode width state)
    calc
      _ = (focusedProgram width).applyNormalized
          (focusedWidth width ▸ NormalizedVector.ket
            ((QubitLayout.canonical
              (Addition.HRS.bridgeEncoding (extra width + width.size)
                (width.size)).width).basisEquiv.symm
              ((Addition.HRS.bridgeEncoding (extra width + width.size)
                (width.size)).encode (sourceInput width state)))) :=
        congrArg (focusedProgram width).applyNormalized inputKet.symm
      _ = focusedWidth width ▸
          (Addition.HRS.placedIncrementProgram (extra width) (width.size)).applyNormalized
            (NormalizedVector.ket
              ((QubitLayout.canonical
                (Addition.HRS.bridgeEncoding (extra width + width.size)
                  (width.size)).width).basisEquiv.symm
                ((Addition.HRS.bridgeEncoding (extra width + width.size)
                  (width.size)).encode (sourceInput width state)))) :=
        UnitaryCircuit.castCanonicalQubitWidth_applyNormalized _ _ _
      _ = focusedWidth width ▸ NormalizedVector.ket
          ((QubitLayout.canonical
            (Addition.HRS.bridgeEncoding (extra width + width.size)
              (width.size)).width).basisEquiv.symm
            ((Addition.HRS.bridgeEncoding (extra width + width.size)
              (width.size)).encode
                (Addition.HRS.bridgeIncrementStep (sourceInput width state)))) :=
        congrArg (fun vector => focusedWidth width ▸ vector) original
      _ = _ := outputKet

private def groupedProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (LowShiftPlacement.groupedEncoding width).width).toQuantum :=
  UnitaryCircuit.prodLeft (n := (LowShiftPlacement.remainderEncoding width).width)
    (focusedProgram width)

private theorem grouped_realizes (width : Nat) :
    UnitaryCircuit.Realizes (LowShiftPlacement.groupedEncoding width)
      (groupedProgram width)
      (fun pair => (Addition.HRS.bridgeIncrementStep pair.1, pair.2)) := by
  simpa only [groupedProgram, UnitaryCircuit.prodLeft,
    LowShiftPlacement.groupedEncoding] using
    (focused_realizes width).onBinaryPrefix
      (right := LowShiftPlacement.remainderEncoding width)

/-- The same actual HRS program placed on all original source fields. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (LowShiftPlacement.placement width).place (groupedProgram width)

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
    UnitaryCircuit.Realizes (encoding width) (program width) step := by
  apply ((LowShiftPlacement.placement width).place_realizes
    (grouped_realizes width)).congrStep
  intro state
  simpa only [EncodedBit.FullPlacement.step, LowShiftPlacement.placement_grouping_eq,
    LowShiftPlacement.placedStep] using placed_step width state

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
    UnitaryCircuit.Realizes (encoding width)
      ((program width).dagger (AlgorithmGate.oracleFreeAdjoints .empty)) inverseStep := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse (program_realizes width)
  · rw [UnitaryCircuit.dagger_matrix]
    exact Unitary.star_eq_inv _
  · exact step_inverseStep width

/-- The native HRS trace survives the actual field-width transport and source placement. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      (Addition.HRS.placedIncrementProgram (extra width) width.size).eventTrace := by
  calc
    _ = (groupedProgram width).eventTrace :=
      EncodedBit.FullPlacement.place_eventTrace _ _
    _ = (focusedProgram width).eventTrace := by rfl
    _ = _ := UnitaryCircuit.castCanonicalQubitWidth_eventTrace _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.LowShiftIncrement
