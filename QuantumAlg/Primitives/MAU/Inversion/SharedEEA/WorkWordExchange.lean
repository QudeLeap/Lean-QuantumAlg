/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Native controlled exchange of the two actual shared words

The source exchanges the complete Work1 and Work2 at an iteration boundary
[LYL+26, sec_EEA/sub_opt.tex:81-84]. This kernel executes the existing
three-Toffoli controlled swap on every corresponding pair of actual word
wires. Its control is the existing Ctrl field; computing and cleaning the
boundary predicate, refreshing the lengths, and toggling Iter are separate
operations. The result below preserves every field outside both words.

No initial value, padding condition, or separability condition is imposed
on either word. In particular the two reused terminal counter positions
are included in the complete exchange, rather than silently retained at
their former locations. The source low-counter kernel and the repaired
terminal schedule must select this operation through their actual controls.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.WorkWordExchange

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit

/-- The first complete shared word in its physical most-significant-first order. -/
def leftWord (width : Nat) : Word (encoding width) (width + 3) := ⟨firstWordBit width⟩

/-- The second complete shared word in the matching physical order. -/
def rightWord (width : Nat) : Word (encoding width) (width + 3) := ⟨secondWordBit width⟩

private lemma control_left (width : Nat) (index : Fin (width + 3)) :
    (controlBit width).wire ≠ ((leftWord width).bit index).wire := by
  intro same
  have values := congrArg Fin.val same
  change (controlBit width).wire.val = (firstWordBit width index).wire.val at values
  rw [controlBit_wire, firstWordBit_wire] at values
  have within := index.isLt
  omega

private lemma control_right (width : Nat) (index : Fin (width + 3)) :
    (controlBit width).wire ≠ ((rightWord width).bit index).wire := by
  intro same
  have values := congrArg Fin.val same
  change (controlBit width).wire.val = (secondWordBit width index).wire.val at values
  rw [controlBit_wire, secondWordBit_wire] at values
  have within := index.isLt
  omega

private lemma left_right (width : Nat) (left right : Fin (width + 3)) :
    ((leftWord width).bit left).wire ≠ ((rightWord width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (firstWordBit width left).wire.val = (secondWordBit width right).wire.val at values
  rw [firstWordBit_wire, secondWordBit_wire] at values
  have within := left.isLt
  omega

private lemma left_distinct (width : Nat) (left right : Fin (width + 3))
    (different : left ≠ right) :
    ((leftWord width).bit left).wire ≠ ((leftWord width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (firstWordBit width left).wire.val = (firstWordBit width right).wire.val at values
  rw [firstWordBit_wire, firstWordBit_wire] at values
  exact different (Fin.ext values)

private lemma right_distinct (width : Nat) (left right : Fin (width + 3))
    (different : left ≠ right) :
    ((rightWord width).bit left).wire ≠ ((rightWord width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (secondWordBit width left).wire.val = (secondWordBit width right).wire.val at values
  rw [secondWordBit_wire, secondWordBit_wire] at values
  exact different (Fin.ext (by omega))

/-- Three actual Toffoli gates per pair of complete shared-word positions. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.controlledSwapGates (controlBit width) (leftWord width) (rightWord width)
    (control_left width) (control_right width) (fun index => left_right width index index)

private def withoutWords {width : Nat} (state : Registers width) : Registers width :=
  { state with firstWord := 0#(width + 3), secondWord := 0#(width + 3) }

private lemma withoutWords_left (width : Nat) (controlA controlB : EncodedBit (encoding width))
    (index : Fin (width + 3)) (state : Registers width) :
    withoutWords (toffoliStep controlA controlB (firstWordBit width index) state) =
      withoutWords state := by
  unfold toffoliStep
  split <;> rfl

private lemma withoutWords_right (width : Nat) (controlA controlB : EncodedBit (encoding width))
    (index : Fin (width + 3)) (state : Registers width) :
    withoutWords (toffoliStep controlA controlB (secondWordBit width index) state) =
      withoutWords state := by
  unfold toffoliStep
  split <;> rfl

private lemma withoutWords_pair (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    withoutWords (GateSpec.stepList
      (EncodedBit.controlledSwapGates (controlBit width)
        ((leftWord width).bit index) ((rightWord width).bit index)
        (control_left width index) (control_right width index) (left_right width index index))
      state) = withoutWords state := by
  simp only [EncodedBit.controlledSwapGates, GateSpec.stepList, GateSpec.step, id_eq,
    leftWord, rightWord, withoutWords_left, withoutWords_right]

private lemma withoutWords_indices (width : Nat) (indices : List (Fin (width + 3)))
    (state : Registers width) :
    withoutWords (GateSpec.stepList
      (indices.flatMap fun index => EncodedBit.controlledSwapGates (controlBit width)
        ((leftWord width).bit index) ((rightWord width).bit index)
        (control_left width index) (control_right width index) (left_right width index index))
      state) = withoutWords state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, ih, withoutWords_pair]

private lemma gates_preserve_complement (width : Nat) (state : Registers width) :
    withoutWords (GateSpec.stepList (gates width) state) = withoutWords state :=
  withoutWords_indices width _ state

private lemma gates_left_word (width : Nat) (state : Registers width) :
    (GateSpec.stepList (gates width) state).firstWord =
      if state.control then state.secondWord else state.firstWord := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have entry := Word.controlledSwapStep_get_left
    (controlBit width) (leftWord width) (rightWord width)
    (control_left width) (control_right width) (fun index => left_right width index index)
    ⟨index, within⟩ (fun j different => left_distinct width j _ different)
    (fun j => (left_right width _ j).symm) (fun j => left_right width j _)
    (fun j different => right_distinct width j _ different) state
  change (firstWordBit width ⟨index, within⟩).get (GateSpec.stepList (gates width) state) =
    if state.control then (secondWordBit width ⟨index, within⟩).get state
      else (firstWordBit width ⟨index, within⟩).get state at entry
  rw [firstWordBit_get, secondWordBit_get, firstWordBit_get] at entry
  cases selected : state.control <;>
    simpa only [selected, Bool.false_eq_true, if_false, if_true] using entry

private lemma gates_right_word (width : Nat) (state : Registers width) :
    (GateSpec.stepList (gates width) state).secondWord =
      if state.control then state.firstWord else state.secondWord := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have entry := Word.controlledSwapStep_get_right
    (controlBit width) (leftWord width) (rightWord width)
    (control_left width) (control_right width) (fun index => left_right width index index)
    ⟨index, within⟩ (fun j different => left_distinct width j _ different)
    (fun j => (left_right width _ j).symm) (fun j => left_right width j _)
    (fun j different => right_distinct width j _ different) state
  change (secondWordBit width ⟨index, within⟩).get (GateSpec.stepList (gates width) state) =
    if state.control then (firstWordBit width ⟨index, within⟩).get state
      else (secondWordBit width ⟨index, within⟩).get state at entry
  rw [secondWordBit_get, firstWordBit_get, secondWordBit_get] at entry
  cases selected : state.control <;>
    simpa only [selected, Bool.false_eq_true, if_false, if_true] using entry

/-- Complete shared-word exchange on the selected branch; all other fields are retained. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  { state with
    firstWord := if state.control then state.secondWord else state.firstWord
    secondWord := if state.control then state.firstWord else state.secondWord }

/-- The literal native list implements that complete frame equality without input promises. -/
lemma gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state = step state := by
  let result := GateSpec.stepList (gates width) state
  calc
    result = { withoutWords result with
        firstWord := result.firstWord, secondWord := result.secondWord } := rfl
    _ = _ := by
      rw [gates_preserve_complement, gates_left_word, gates_right_word]
      rfl

/-- Compile the same actual Toffoli list, without allocating any additional system. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width)

/-- Exact all-label circuit action, and hence preservation of arbitrary relative phases. -/
lemma program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment step :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width) (gates_step width) environment

/-- Both complete words return after a second selected exchange, with all other fields retained. -/
lemma step_twice {width : Nat} (state : Registers width) : step (step state) = state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, flags, control⟩
  cases control <;> rfl

/-- The actual inverse circuit implements the same complete controlled exchange. -/
lemma inverse_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width)
      ((program width).dagger (AlgorithmGate.oracleFreeAdjoints .empty)) environment step := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse (program_realizes width)
  · rw [UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]
    exact Unitary.star_eq_inv _
  · exact step_twice

private lemma indices_trace (width : Nat) (indices : List (Fin (width + 3))) :
    (indices.flatMap fun index => EncodedBit.controlledSwapGates (controlBit width)
      ((leftWord width).bit index) ((rightWord width).bit index)
      (control_left width index) (control_right width index) (left_right width index index)).map
        (GateSpec.event .empty) = List.replicate (3 * indices.length) (.gate .toffoli) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [List.flatMap_cons, List.map_append, ih]
      simp only [EncodedBit.controlledSwapGates, List.map_cons, List.map_nil,
        GateSpec.event, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (3 * rest.length) 3, List.replicate_add]
      rfl

/-- Every original word position contributes its three literal Toffoli events. -/
lemma program_eventTrace (width : Nat) :
    (program width).eventTrace =
      List.replicate (3 * (width + 3)) (.gate .toffoli) := by
  rw [program, GateSpec.programList_eventTrace]
  change ((List.ofFn fun index : Fin (width + 3) => index).flatMap fun index =>
    EncodedBit.controlledSwapGates (controlBit width)
      ((leftWord width).bit index) ((rightWord width).bit index)
      (control_left width index) (control_right width index) (left_right width index index)).map
        (GateSpec.event .empty) = _
  rw [indices_trace, List.length_ofFn]

end

end QuantumAlg.MAU.Inversion.SharedEEA.WorkWordExchange
