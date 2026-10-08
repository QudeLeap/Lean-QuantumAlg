/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Actual constant XOR on the complete first shared word

A fixed classical mask selects literal X gates at the original Work1
coordinates. The complete word changes by finite XOR while every other
field is preserved for arbitrary incoming values. This is the common
physical constant-load and unload kernel for the shared EEA's initial
and terminal layouts [LYL+26, sec_EEA/sub_4phase.tex:104-117;
LYL+26, sec_point_add/sec_point_add.tex:51-79].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Work1Constant

noncomputable section

open EncodedBit

private def word (width : Nat) : Word (encoding width) (width + 3) :=
  ⟨fun index => firstWordBit width index.rev⟩

private theorem word_distinct (width : Nat) (left right : Fin (width + 3))
    (different : left ≠ right) :
    ((word width).bit left).wire ≠ ((word width).bit right).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  change (firstWordBit width left.rev).wire.val = (firstWordBit width right.rev).wire.val at values
  rw [firstWordBit_wire, firstWordBit_wire] at values
  apply different
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  simp only [Fin.val_rev] at values
  omega

private theorem word_get (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    ((word width).bit index).get state = state.firstWord.getLsbD index.val := by
  change (firstWordBit width index.rev).get state = _
  rw [firstWordBit_get]
  have position : width + 3 - 1 - index.rev.val = index.val := by
    have within := index.isLt
    simp only [Fin.val_rev]
    omega
  simp only [BitVec.getMsbD_eq_getLsbD, index.rev.isLt, decide_true, Bool.true_and, position]

/-- A literal X on each selected numerical bit of the supplied fixed constant. -/
def gates (width : Nat) (constant : Fin (2 ^ (width + 3))) : List (GateSpec (encoding width)) :=
  Word.xorConstantGates (word width) constant

private def withoutWorkspace {width : Nat} (state : Registers width) : Registers width :=
  { state with firstWord := 0#(width + 3) }

private theorem gates_complement (width : Nat) (constant : Fin (2 ^ (width + 3)))
    (state : Registers width) :
    withoutWorkspace (GateSpec.stepList (gates width constant) state) = withoutWorkspace state := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate member
  rw [gates, Word.xorConstantGates] at member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  exact fun _ => rfl

private theorem gates_word (width : Nat) (constant : Fin (2 ^ (width + 3)))
    (state : Registers width) :
    (GateSpec.stepList (gates width constant) state).firstWord =
      state.firstWord ^^^ BitVec.ofFin constant := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have actual := Word.xorConstantStep_get_target (word width) constant
    ⟨index, within⟩ (fun other different => word_distinct width other _ different) state
  rw [word_get, word_get] at actual
  change (GateSpec.stepList (gates width constant) state).firstWord.getLsbD index =
    (state.firstWord.getLsbD index ^^
      (BitVec.ofFin constant).getLsbD index) at actual
  rw [BitVec.getLsbD_xor]
  exact actual

/-- Constant unloading is an actual all-label XOR and retains all other complete fields. -/
theorem gates_step (width : Nat) (constant : Fin (2 ^ (width + 3))) (state : Registers width) :
    GateSpec.stepList (gates width constant) state =
      { state with firstWord := state.firstWord ^^^ BitVec.ofFin constant } := by
  let after := GateSpec.stepList (gates width constant) state
  calc
    after = { withoutWorkspace after with firstWord := after.firstWord } := rfl
    _ = _ := by
      rw [gates_complement, gates_word]
      rfl

/-- Execute precisely the selected native X list on the original source frame. -/
def program (width : Nat) (constant : Fin (2 ^ (width + 3))) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width constant)

/-- Exact complete-data semantics of the native constant load or unload. -/
theorem program_realizes (width : Nat) (constant : Fin (2 ^ (width + 3))) :
    UnitaryCircuit.Realizes (encoding width) (program width constant)
      (fun state => { state with firstWord := state.firstWord ^^^ BitVec.ofFin constant }) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step width constant)

/-- Exactly one X is emitted per selected bit of the fixed numerical constant. -/
theorem gates_length (width : Nat) (constant : Fin (2 ^ (width + 3))) :
    (gates width constant).length = (Word.constantOneIndices constant).length :=
  Word.xorConstantGates_length (word width) constant

end

end QuantumAlg.MAU.Inversion.SharedEEA.Work1Constant
