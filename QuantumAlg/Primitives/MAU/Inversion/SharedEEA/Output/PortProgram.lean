/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Reverse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Work1Constant
import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Padding

/-!
# Actual output-port reversal and constant unloading on the original shared words

The in-place division interface needs the inverse on the original input
port and the large workspace clear, while the small EEA history remains
available for the same adjoint [LYL+26, sec_point_add/sec_point_add.tex:51-79].
Here a real symmetric SWAP list reverses all Work2 positions. A real X
list then xors the known terminal Work1 word `reverse_n(p) ++ 001`.
Its two high-clock positions have zero mask bits; they are not erased.

The complete action is proved for every incoming frame. The original
prime-input domain supplies the separate reachable-state facts that the
reusable n-bit workspace and final constant-one bit become zero. No
additional output bank or free physical permutation is introduced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.OutputPortProgram

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def outputWord (width : Nat) : Word (encoding width) (width + 3) :=
  ⟨secondWordBit width⟩

private theorem output_distinct (width : Nat) (left right : Fin (width + 3))
    (different : left ≠ right) :
    ((outputWord width).bit left).wire ≠ ((outputWord width).bit right).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  change (secondWordBit width left).wire.val = (secondWordBit width right).wire.val at values
  rw [secondWordBit_wire, secondWordBit_wire] at values
  exact different (Fin.ext (by omega))

private def withoutOutput {width : Nat} (state : Registers width) : Registers width :=
  { state with secondWord := 0#(width + 3) }

/-- Every output position is physically swapped with its symmetric counterpart. -/
def orientationGates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.reverseGates (outputWord width) (output_distinct width)

private theorem orientation_word (width : Nat) (state : Registers width) :
    (GateSpec.stepList (orientationGates width) state).secondWord = state.secondWord.reverse := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := Word.reverseStep_get (outputWord width) (output_distinct width)
    ⟨index, within⟩ state
  change (secondWordBit width ⟨index, within⟩).get
    (GateSpec.stepList (orientationGates width) state) =
      (secondWordBit width (Fin.rev ⟨index, within⟩)).get state at actual
  rw [secondWordBit_get, secondWordBit_get] at actual
  have position : width + 3 - 1 - (Fin.rev (⟨index, within⟩ : Fin (width + 3))).val =
      index := by
    simp only [Fin.val_rev]
    omega
  apply actual.trans
  rw [BitVec.getMsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  simp only [(Fin.rev (⟨index, within⟩ : Fin (width + 3))).isLt,
    decide_true, Bool.true_and, position]

private theorem orientation_complement (width : Nat) (state : Registers width) :
    withoutOutput (GateSpec.stepList (orientationGates width) state) = withoutOutput state :=
  Word.reverseStep_preserves_projection (outputWord width) (output_distinct width)
    withoutOutput (fun _ _ => rfl) state

/-- Exact full-frame action of the emitted output reversal, including arbitrary dirty fields. -/
theorem orientation_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (orientationGates width) state =
      { state with secondWord := state.secondWord.reverse } := by
  let after := GateSpec.stepList (orientationGates width) state
  calc
    after = { withoutOutput after with secondWord := after.secondWord } := rfl
    _ = _ := by
      rw [orientation_complement, orientation_word]
      rfl

private def constant (modulus : Nat) : Fin (2 ^ (modulus.size + 3)) :=
  BitVec.equivFin (TerminalPadding.terminalWord modulus)

/-- A literal X on each set bit of the fixed full terminal word. -/
def unloadGates (modulus : Nat) : List (GateSpec (encoding modulus.size)) :=
  Work1Constant.gates modulus.size (constant modulus)

/-- Constant unloading is an actual all-label XOR and retains all other complete fields. -/
theorem unload_step (modulus : Nat) (state : Registers modulus.size) :
    GateSpec.stepList (unloadGates modulus) state =
      { state with firstWord := state.firstWord ^^^ TerminalPadding.terminalWord modulus } :=
  Work1Constant.gates_step modulus.size (constant modulus) state

/-- The exact same output reversal and fixed X list, with no additional register. -/
def gates (modulus : Nat) : List (GateSpec (encoding modulus.size)) :=
  orientationGates modulus.size ++ unloadGates modulus

/-- Only original Work1 and Work2 wires occur in this emitted program. -/
def program (modulus : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates modulus)

/-- The complete physical frame action, defined without a reached-state restriction. -/
def step (modulus : Nat) (state : Registers modulus.size) : Registers modulus.size :=
  { state with
    firstWord := state.firstWord ^^^ TerminalPadding.terminalWord modulus
    secondWord := state.secondWord.reverse }

/-- Full actual gate-list semantics changes precisely the two explicitly stated words. -/
theorem gates_step (modulus : Nat) (state : Registers modulus.size) :
    GateSpec.stepList (gates modulus) state = step modulus state := by
  rw [gates, GateSpec.stepList_append, orientation_step, unload_step]
  rfl

/-- The real native program realizes the complete action, including every retained history bit. -/
theorem program_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (program modulus) (step modulus) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step modulus)

/-- Literal gate count, including the real symmetric swaps and set-bit constant unload. -/
theorem gates_length (modulus : Nat) :
    (gates modulus).length = 3 * ((modulus.size + 3) / 2) +
      (Word.constantOneIndices (constant modulus)).length := by
  rw [gates, List.length_append, orientationGates, Word.reverseGates_length,
    unloadGates, Work1Constant.gates_length]

/-- An input-independent bound charges every emitted gate, without a zero-payload discount. -/
theorem program_resources (modulus : Nat) :
    (program modulus).eventCost.card ≤ 3 * ((modulus.size + 3) / 2) + modulus.size + 3 ∧
      (program modulus).evaluatedEventDepth (fun _ => 1) ≤
        3 * ((modulus.size + 3) / 2) + modulus.size + 3 := by
  have bound := Word.constantOneIndices_length_le (constant modulus)
  rw [program, GateSpec.programList_eventCost_card,
    GateSpec.programList_evaluatedEventDepth_unit, gates_length]
  constructor <;> omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.OutputPortProgram
