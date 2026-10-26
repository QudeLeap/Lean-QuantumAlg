/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Reflection.Program
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive

/-!
# Actual coherent constant reflection with an existing dirty work bit

The selector and borrowed work bit are in the retained caller component.
Each native controlled instruction restores that same arbitrary work bit.
The disabled branch is the identity on every complete binary state; the
enabled clean-workspace branch performs the generic finite reflection.
-/

namespace QuantumAlg.MAU.Addition.TTK.Reflection.Controlled

noncomputable section

open EncodedBit GateSpec

variable {Rest : Type} (rest : BinaryLabelEncoding Rest)

abbrev encoding (width : Nat) : BinaryLabelEncoding (Registers width × Rest) :=
  .prod (TTK.encoding width) rest

def retainedBit (width : Nat) (bit : EncodedBit rest) : EncodedBit (encoding rest width) :=
  BinaryLabelEncoding.prodRightBit (TTK.encoding width) rest bit

private lemma retained_ne (width : Nat) (first second : EncodedBit rest)
    (different : first.wire ≠ second.wire) :
    (retainedBit rest width first).wire ≠ (retainedBit rest width second).wire := by
  intro same
  apply different
  apply Fin.ext
  have positions := congrArg Fin.val same
  change (TTK.encoding width).width + first.wire.val =
    (TTK.encoding width).width + second.wire.val at positions
  omega

private lemma lifted_disjoint (width : Nat) (bit : EncodedBit rest)
    (constant : Fin (2 ^ width)) :
    ∀ gate, gate ∈ (Reflection.gates width constant).map (GateSpec.prodLeft rest) →
      bitDisjoint (retainedBit rest width bit) gate := by
  intro gate present
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp present
  exact bitDisjoint_prodLeft_rightBit (TTK.encoding width) rest bit source

/-- Every instruction, including the constant masks, receives the same real coherent control. -/
def gates (width : Nat) (constant : Fin (2 ^ width)) (control work : EncodedBit rest)
    (different : control.wire ≠ work.wire) : List (GateSpec (encoding rest width)) :=
  listWithDirtyControl (retainedBit rest width control) (retainedBit rest width work)
    ((Reflection.gates width constant).map (GateSpec.prodLeft rest))
    (lifted_disjoint rest width control constant) (lifted_disjoint rest width work constant)
    (retained_ne rest width control work different)

def program (width : Nat) (constant : Fin (2 ^ width)) (control work : EncodedBit rest)
    (different : control.wire ≠ work.wire) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding rest width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates rest width constant control work different)

/-- Complete raw action retains every caller coordinate and its original arbitrary dirty work. -/
lemma gates_step (width : Nat) (constant : Fin (2 ^ width)) (control work : EncodedBit rest)
    (different : control.wire ≠ work.wire) (state : Registers width × Rest) :
    stepList (gates rest width constant control work different) state =
      if control.get state.2 then (stepList (Reflection.gates width constant) state.1, state.2)
        else state := by
  rw [gates, listWithDirtyControl_step, stepList_prodLeft]
  rfl

/-- An inactive selector admits arbitrary whole binary operands, workspace and caller metadata. -/
lemma gates_inactive (width : Nat) (constant : Fin (2 ^ width)) (control work : EncodedBit rest)
    (different : control.wire ≠ work.wire) (state : Registers width × Rest)
    (inactive : control.get state.2 = false) :
    stepList (gates rest width constant control work different) state = state := by
  rw [gates_step, inactive]
  rfl

/-- The real clean first word returns to zero on either branch, with no residue assumption. -/
lemma gates_clean (width : Nat) (constant input : Fin (2 ^ width))
    (control work : EncodedBit rest) (different : control.wire ≠ work.wire) (retained : Rest) :
    stepList (gates rest width constant control work different)
      ((Reflection.zero width, input), retained) =
        ((Reflection.zero width,
          if control.get retained then reflected constant input else input), retained) := by
  rw [gates_step, Reflection.gates_clean]
  cases control.get retained <;> rfl

/-- The actual native program preserves coherent selected/inactive sectors and relative phases. -/
lemma program_realizes (width : Nat) (constant : Fin (2 ^ width)) (control work : EncodedBit rest)
    (different : control.wire ≠ work.wire) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding rest width)
      (program rest width constant control work different) environment
      (fun state => if control.get state.2 then
        (stepList (Reflection.gates width constant) state.1, state.2) else state) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step rest width constant control work different) environment

end

end QuantumAlg.MAU.Addition.TTK.Reflection.Controlled
