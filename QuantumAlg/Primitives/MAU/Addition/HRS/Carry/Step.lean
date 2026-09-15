/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Util.Nat.Binary.Arithmetic

/-!
# Local gates for the optimized HRS dirty carry

The lowest pair of input bits uses the source's elimination of `g_0`:
there is no first dirty bit, and the lowest constant bit selects either
zero or one Toffoli. Higher stages put two Toffolis around the lower
carry computation, so only the change of the predecessor dirty bit is
observed [HRS16, paper.tex:187-205].

The hypotheses below concern the wires of actual gate lists. They impose
no initialization or basis-value promise on any data or borrowed bit.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Optimized first carry stage: borrow no `g_0` wire. -/
def baseCarryGates (low high output : EncodedBit encoding)
    (hlh : low.wire ≠ high.wire) (hlo : low.wire ≠ output.wire)
    (hho : high.wire ≠ output.wire) (constantLow constantHigh : Bool) :
    List (EncodedBit.GateSpec encoding) :=
  (if constantHigh then [.cnot high output hho, .x high] else []) ++
    (if constantLow then [.toffoli low high output hlh hlo hho] else []) ++
    (if constantHigh then [.x high] else [])

/-- The first stage writes exactly the two-bit carry and restores both inputs. -/
theorem hrsBaseCarry_step (low high output : EncodedBit encoding)
    (hlh : low.wire ≠ high.wire) (hlo : low.wire ≠ output.wire)
    (hho : high.wire ≠ output.wire) (constantLow constantHigh : Bool) (state : Data) :
    stepList (baseCarryGates low high output hlh hlo hho constantLow constantHigh) state =
      if Bool.carry (high.get state) constantHigh (low.get state && constantLow)
        then output.flip state else state := by
  have hlowOutput := EncodedBit.get_flip_of_wire_ne output low hlo.symm
  have hhighOutput := EncodedBit.get_flip_of_wire_ne output high hho.symm
  have hlowHigh := EncodedBit.get_flip_of_wire_ne high low hlh.symm
  have hcomm := EncodedBit.flip_comm high output
  cases constantLow <;> cases constantHigh <;>
    cases hlow : low.get state <;> cases hhigh : high.get state <;>
    simp [baseCarryGates, stepList, step,
      EncodedBit.cnotStep, EncodedBit.toffoliStep, Bool.carry,
      hlowOutput, hhighOutput, hlowHigh, hcomm,
      EncodedBit.get_flip_self, EncodedBit.flip_flip, hlow, hhigh]

/-- Propagate a dirty predecessor's toggle through one input/constant bit. -/
def propagateCarryGates (input previous output : EncodedBit encoding)
    (hip : input.wire ≠ previous.wire) (hio : input.wire ≠ output.wire)
    (hpo : previous.wire ≠ output.wire) (constant : Bool)
    (lower : List (EncodedBit.GateSpec encoding)) : List (EncodedBit.GateSpec encoding) :=
  let toffoli := EncodedBit.GateSpec.toffoli input previous output hip hio hpo
  (if constant then [.cnot input output hio, .x input] else []) ++
    [toffoli] ++ lower ++ [toffoli] ++ (if constant then [.x input] else [])

/-- The paired Toffolis cancel the unknown predecessor value. The lower
computation remains executed once; only the propagated output flip is added. -/
theorem hrsPropagateCarry_step (input previous output : EncodedBit encoding)
    (hip : input.wire ≠ previous.wire) (hio : input.wire ≠ output.wire)
    (hpo : previous.wire ≠ output.wire) (constant : Bool)
    (lower : List (EncodedBit.GateSpec encoding))
    (hinput : ∀ gate, gate ∈ lower → bitDisjoint input gate)
    (houtput : ∀ gate, gate ∈ lower → bitDisjoint output gate) (state : Data) :
    stepList (propagateCarryGates input previous output hip hio hpo constant lower) state =
      if Bool.carry (input.get state) constant
          (previous.get state ^^ previous.get (stepList lower state))
        then output.flip (stepList lower state) else stepList lower state := by
  have hlowerInput := stepList_flip_comm_of_bitDisjoint lower input hinput
  have hlowerOutput := stepList_flip_comm_of_bitDisjoint lower output houtput
  have hinputLower := stepList_get_of_bitDisjoint lower input hinput
  have hpreviousInput := EncodedBit.get_flip_of_wire_ne input previous hip
  have hpreviousOutput := EncodedBit.get_flip_of_wire_ne output previous hpo.symm
  have hinputOutput := EncodedBit.get_flip_of_wire_ne output input hio.symm
  have hcomm := EncodedBit.flip_comm input output
  cases constant <;> cases hinitial : input.get state <;>
    cases hprevious : previous.get state <;>
    cases hlower : previous.get (stepList lower state) <;>
    simp [propagateCarryGates, stepList_append, stepList, step,
      EncodedBit.cnotStep, EncodedBit.toffoliStep, Bool.carry,
      hlowerInput, hlowerOutput, hinputLower,
      hpreviousInput, hpreviousOutput, hinputOutput, hcomm,
      EncodedBit.get_flip_self, EncodedBit.flip_flip,
      hinitial, hprevious, hlower]

/-- Reversing the lower carry computation retains the output toggle while
restoring all other joint input components. No output-wire gate is reversed. -/
theorem hrsCarry_uncompute_lower (output : EncodedBit encoding)
    (lower : List (EncodedBit.GateSpec encoding))
    (houtput : ∀ gate, gate ∈ lower → bitDisjoint output gate)
    (toggle : Bool) (state : Data) :
    stepList lower.reverse
        (if toggle then output.flip (stepList lower state) else stepList lower state) =
      if toggle then output.flip state else state := by
  cases toggle with
  | false => simpa using stepList_reverse_stepList lower state
  | true =>
      simp only [if_true]
      rw [stepList_flip_comm_of_bitDisjoint lower.reverse output
        (fun gate hgate => houtput gate (List.mem_reverse.mp hgate)),
        stepList_reverse_stepList]

end

end QuantumAlg.MAU.Addition.HRS
