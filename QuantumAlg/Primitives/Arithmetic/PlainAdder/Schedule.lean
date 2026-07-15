/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.Arithmetic.BitSlice
public import QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
public import Mathlib.Data.List.TakeDrop
public import Mathlib.GroupTheory.Perm.Finite

/-!
# Folded plain-adder schedule shells

This module assembles already-certified encoded bit-slice blocks into folded
`BaseGateProgram`/semantic-step objects.  It deliberately does not prove that a
folded step is the word-level `PlainAdder.Data.addIntoRight` map.  A closing
word-level adder proof must still supply the carry invariant connecting the
selected schedule and layout to the `ZMod (2^n)` endpoint.

The local carry/sum ingredients are the kind used by the VBE plain-adder
network, whose full schedule uses a temporary carry register rather than the
single-carry shell below [VBE95, 9511018.tex:237-264,596-618].
-/

@[expose] public section

namespace QuantumAlg
namespace PlainAdder
namespace Schedule

noncomputable section

variable {Carrier : Type} {encoding : BinaryLabelEncoding Carrier}

/-- Concatenate staged encoded-bit gate lists while preserving stage order. -/
def concatStages (stages : List (List (EncodedBit.GateSpec encoding))) :
    List (EncodedBit.GateSpec encoding) :=
  stages.foldr (fun gates rest => gates ++ rest) []

/-- Membership in concatenated stages is membership in one component stage. -/
theorem mem_concatStages
    {stages : List (List (EncodedBit.GateSpec encoding))}
    {gate : EncodedBit.GateSpec encoding} :
    gate ∈ concatStages stages ↔
      ∃ stage, stage ∈ stages ∧ gate ∈ stage := by
  induction stages with
  | nil =>
      simp [concatStages]
  | cons stage rest ih =>
      constructor
      · intro h
        change gate ∈ stage ++ concatStages rest at h
        rw [List.mem_append] at h
        rcases h with hstage | hrest
        · exact ⟨stage, by simp, hstage⟩
        · rcases ih.mp hrest with ⟨found, hfound, hgate⟩
          exact ⟨found, by simp [hfound], hgate⟩
      · intro h
        rcases h with ⟨found, hfound, hgate⟩
        change gate ∈ stage ++ concatStages rest
        rw [List.mem_append]
        simp only [List.mem_cons] at hfound
        rcases hfound with hfound | hfound
        · subst found
          exact Or.inl hgate
        · exact Or.inr (ih.mpr ⟨found, hfound, hgate⟩)

/-- The semantic action of concatenated stages is the left-to-right fold of
the individual stage actions. -/
theorem stepList_concatStages
    (stages : List (List (EncodedBit.GateSpec encoding))) (x : Carrier) :
    EncodedBit.GateSpec.stepList (concatStages stages) x =
      stages.foldl
        (fun y gates => EncodedBit.GateSpec.stepList gates y) x := by
  induction stages generalizing x with
  | nil =>
      rfl
  | cons gates rest ih =>
      change
        EncodedBit.GateSpec.stepList (gates ++ concatStages rest) x =
          rest.foldl
            (fun y gates => EncodedBit.GateSpec.stepList gates y)
            (EncodedBit.GateSpec.stepList gates x)
      rw [EncodedBit.GateSpec.stepList_append]
      exact ih (EncodedBit.GateSpec.stepList gates x)

/-- Word lenses and disjointness hypotheses for a folded single-carry schedule
shell.  This is only a bit-layout package; it is not a word-level correctness
witness. -/
structure SingleCarryLayout (n : Nat) where
  /-- Left/source word bit lenses. -/
  left : EncodedBit.Word encoding n
  /-- Right/target word bit lenses. -/
  right : EncodedBit.Word encoding n
  /-- Carry bit lens used by each local slice in this schedule shell. -/
  carry : EncodedBit encoding
  /-- Matching left/right bit positions occupy distinct wires. -/
  leftRight_ne : ∀ i, (left.bit i).wire ≠ (right.bit i).wire
  /-- Left word bits are distinct from the carry wire. -/
  leftCarry_ne : ∀ i, (left.bit i).wire ≠ carry.wire
  /-- Right word bits are distinct from the carry wire. -/
  rightCarry_ne : ∀ i, (right.bit i).wire ≠ carry.wire

namespace SingleCarryLayout

variable {n : Nat} (layout : SingleCarryLayout (encoding := encoding) n)

/-- Forward majority-style carry stage, in increasing bit-index order. -/
def majorityStage : List (EncodedBit.GateSpec encoding) :=
  concatStages (List.ofFn fun i : Fin n =>
    BitSlice.Encoded.majorityGates (layout.left.bit i) (layout.right.bit i)
      layout.carry (layout.leftRight_ne i) (layout.leftCarry_ne i)
      (layout.rightCarry_ne i))

/-- Pointwise sum/xor stage, in increasing bit-index order. -/
def sumStage : List (EncodedBit.GateSpec encoding) :=
  concatStages (List.ofFn fun i : Fin n =>
    BitSlice.Encoded.sumGates (layout.left.bit i) layout.carry
      (layout.right.bit i) (layout.leftRight_ne i)
      (Ne.symm (layout.rightCarry_ne i)))

/-- Reverse cleanup stage, in decreasing bit-index order. -/
def reverseCleanupStage : List (EncodedBit.GateSpec encoding) :=
  concatStages ((List.ofFn fun i : Fin n =>
    BitSlice.Encoded.unmajorityGates (layout.left.bit i) (layout.right.bit i)
      layout.carry (layout.leftRight_ne i) (layout.leftCarry_ne i)
      (layout.rightCarry_ne i)).reverse)

/-- Folded schedule shell built from forward carry, sum, and reverse cleanup
stages.  Its endpoint semantics are the folded bit-lens action below, not yet
the plain-adder word theorem. -/
def gates : List (EncodedBit.GateSpec encoding) :=
  majorityStage layout ++ sumStage layout ++ reverseCleanupStage layout

/-- Base-gate program for the folded schedule shell. -/
def program : BaseGateProgram encoding.width :=
  EncodedBit.GateSpec.programList (gates layout)

/-- Folded semantic action of the schedule shell. -/
def step : Carrier -> Carrier :=
  EncodedBit.GateSpec.stepList (gates layout)

/-- The folded schedule shell is realized by the same base-gate program object
whose resource profile is later projected. -/
theorem realizes :
    BaseGateProgram.Realizes encoding (program layout) (step layout) :=
  EncodedBit.GateSpec.realizesList (gates layout)

/-- Same-Circuit witness for the folded schedule shell. -/
def sameCircuit : BaseGateSameCircuitWitness Carrier (step layout) where
  encoding := encoding
  program := program layout
  realizes := realizes layout

/-- Package this folded schedule as a plain-adder structured witness once a
separate word-level invariant proves that its folded step is `addIntoRight`. -/
def toStructuredWitness
    {encoding : BinaryLabelEncoding (Data n)}
    (layout : SingleCarryLayout (encoding := encoding) n)
    (hstep : step layout = Data.addIntoRight) :
    StructuredWitness n where
  encoding := encoding
  program := program layout
  realizes := by
    simpa [program, hstep] using realizes layout

end SingleCarryLayout

/-- Word lenses and wire-disjointness hypotheses for a full carry-work layout.
This fixes the register shape used by the VBE-style route: data words, one
data carry flag, and `n - 1` temporary carry wires.  It is still only a layout
package; the word-level carry invariant is supplied separately. -/
structure CarryWorkLayout (n : Nat) where
  /-- Left/source word bit lenses. -/
  left : EncodedBit.Word encoding n
  /-- Right/target word bit lenses. -/
  right : EncodedBit.Word encoding n
  /-- Data carry flag used as the clean carry-in convention. -/
  carryIn : EncodedBit encoding
  /-- Temporary carry-work bit lenses. -/
  workCarry : EncodedBit.Word encoding (n - 1)
  /-- Distinct left/source positions occupy distinct wires. -/
  leftLeft_ne :
    forall i j, i ≠ j -> (left.bit i).wire ≠ (left.bit j).wire
  /-- Distinct right/target positions occupy distinct wires. -/
  rightRight_ne :
    forall i j, i ≠ j -> (right.bit i).wire ≠ (right.bit j).wire
  /-- Matching left/right bit positions occupy distinct wires. -/
  leftRight_ne : forall i j, (left.bit i).wire ≠ (right.bit j).wire
  /-- Left word bits are distinct from the data carry wire. -/
  leftCarryIn_ne : forall i, (left.bit i).wire ≠ carryIn.wire
  /-- Right word bits are distinct from the data carry wire. -/
  rightCarryIn_ne : forall i, (right.bit i).wire ≠ carryIn.wire
  /-- Left word bits are distinct from temporary carry-work wires. -/
  leftWork_ne :
    forall i j, (left.bit i).wire ≠ (workCarry.bit j).wire
  /-- Right word bits are distinct from temporary carry-work wires. -/
  rightWork_ne :
    forall i j, (right.bit i).wire ≠ (workCarry.bit j).wire
  /-- The data carry wire is distinct from temporary carry-work wires. -/
  carryInWork_ne :
    forall j, carryIn.wire ≠ (workCarry.bit j).wire
  /-- Distinct carry-work positions occupy distinct wires. -/
  workWork_ne :
    forall i j, i ≠ j -> (workCarry.bit i).wire ≠ (workCarry.bit j).wire

namespace CarryWorkLayout

variable {n : Nat} (layout : CarryWorkLayout (encoding := encoding) n)

/-- The low-word index associated with a temporary carry-work position. -/
def lowIndex (j : Fin (n - 1)) : Fin n :=
  ⟨j.val, by
    have hj := j.isLt
    omega⟩

/-- The low-word index keeps the same numeric value as its carry-work index. -/
@[simp] theorem lowIndex_val (j : Fin (n - 1)) :
    (lowIndex j).val = j.val :=
  rfl

/-- Previous temporary carry-work position for a nonzero carry index. -/
@[nolint unusedArguments]
def previousWorkIndex (j : Fin (n - 1)) (_h : j.val ≠ 0) : Fin (n - 1) :=
  ⟨j.val - 1, by
    have hj := j.isLt
    omega⟩

@[simp] theorem previousWorkIndex_val (j : Fin (n - 1))
    (h : j.val ≠ 0) :
    (previousWorkIndex j h).val = j.val - 1 :=
  rfl

/-- Carry input for the stage that computes temporary carry `j`: the data
carry-in for `j = 0`, and the previous temporary carry otherwise. -/
def carryInput (j : Fin (n - 1)) : EncodedBit encoding :=
  if h : j.val = 0 then layout.carryIn
  else layout.workCarry.bit (previousWorkIndex j h)

theorem left_carryInput_ne (j : Fin (n - 1)) :
    (layout.left.bit (lowIndex j)).wire ≠ (carryInput layout j).wire := by
  unfold carryInput
  by_cases h : j.val = 0
  · simpa [h] using layout.leftCarryIn_ne (lowIndex j)
  · simpa [h] using
      layout.leftWork_ne (lowIndex j) (previousWorkIndex j h)

theorem right_carryInput_ne (j : Fin (n - 1)) :
    (layout.right.bit (lowIndex j)).wire ≠ (carryInput layout j).wire := by
  unfold carryInput
  by_cases h : j.val = 0
  · simpa [h] using layout.rightCarryIn_ne (lowIndex j)
  · simpa [h] using
      layout.rightWork_ne (lowIndex j) (previousWorkIndex j h)

theorem carryInput_work_ne (j : Fin (n - 1)) :
    (carryInput layout j).wire ≠ (layout.workCarry.bit j).wire := by
  unfold carryInput
  by_cases h : j.val = 0
  · simpa [h] using layout.carryInWork_ne j
  · have hprev : previousWorkIndex j h ≠ j := by
      intro hp
      have hv := congrArg Fin.val hp
      dsimp [previousWorkIndex] at hv
      omega
    simpa [h] using layout.workWork_ne (previousWorkIndex j h) j hprev

/-- Carry bit available before summing word position `i`. -/
def carryBeforeSum (i : Fin n) : EncodedBit encoding :=
  if h : i.val = 0 then layout.carryIn
  else layout.workCarry.bit ⟨i.val - 1, by
    have hi := i.isLt
    omega⟩

theorem carryBeforeSum_right_ne (i : Fin n) :
    (carryBeforeSum layout i).wire ≠ (layout.right.bit i).wire := by
  unfold carryBeforeSum
  by_cases h : i.val = 0
  · exact Ne.symm (by simpa [h] using layout.rightCarryIn_ne i)
  · exact Ne.symm (by
      simpa [h] using layout.rightWork_ne i ⟨i.val - 1, by
        have hi := i.isLt
        omega⟩)

/-- Carry-work gates for one low-word position.  The folded action is local
bit-lens semantics only; word-level carry correctness is proved separately. -/
def carryOutGatesAt (j : Fin (n - 1)) :
    List (EncodedBit.GateSpec encoding) :=
  BitSlice.Encoded.carryOutGates
    (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
    (carryInput layout j) (layout.workCarry.bit j)
    (layout.leftRight_ne (lowIndex j) (lowIndex j))
    (left_carryInput_ne layout j)
    (layout.leftWork_ne (lowIndex j) j)
    (right_carryInput_ne layout j)
    (layout.rightWork_ne (lowIndex j) j)
    (carryInput_work_ne layout j)

/-- The local carry-work stage at index `j` writes the full-adder carry into a
clean temporary carry wire. -/
theorem carryOutGatesAt_get_workCarry_clean (j : Fin (n - 1)) (x : Carrier)
    (hclean : (layout.workCarry.bit j).get x = false) :
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      Bool.carry ((layout.left.bit (lowIndex j)).get x)
        ((layout.right.bit (lowIndex j)).get x)
        ((carryInput layout j).get x) := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_carryOut_clean
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) x hclean

/-- The local carry-work stage preserves the selected left readout. -/
theorem carryOutGatesAt_get_left (j : Fin (n - 1)) (x : Carrier) :
    (layout.left.bit (lowIndex j)).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      (layout.left.bit (lowIndex j)).get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_left
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) x

/-- The local carry-work stage preserves the selected right readout. -/
theorem carryOutGatesAt_get_right (j : Fin (n - 1)) (x : Carrier) :
    (layout.right.bit (lowIndex j)).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      (layout.right.bit (lowIndex j)).get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_right
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) x

/-- The local carry-work stage preserves its carry-input readout. -/
theorem carryOutGatesAt_get_carryInput (j : Fin (n - 1)) (x : Carrier) :
    (carryInput layout j).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      (carryInput layout j).get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_carryIn
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) x

/-- A local carry-work stage preserves every other temporary carry readout. -/
theorem carryOutGatesAt_get_workCarry_of_ne
    (j k : Fin (n - 1)) (hne : j ≠ k) (x : Carrier) :
    (layout.workCarry.bit k).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      (layout.workCarry.bit k).get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) (layout.workCarry.bit k)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (layout.workWork_ne j k hne) x

/-- A local carry-work stage preserves every left readout. -/
theorem carryOutGatesAt_get_left_any
    (j : Fin (n - 1)) (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      (layout.left.bit i).get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) (layout.left.bit i)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (Ne.symm (layout.leftWork_ne i j)) x

/-- A local carry-work stage preserves every right readout. -/
theorem carryOutGatesAt_get_right_any
    (j : Fin (n - 1)) (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      (layout.right.bit i).get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) (layout.right.bit i)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (Ne.symm (layout.rightWork_ne i j)) x

/-- A local carry-work stage preserves the data carry-in readout. -/
theorem carryOutGatesAt_get_dataCarry (j : Fin (n - 1)) (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      layout.carryIn.get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) layout.carryIn
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (Ne.symm (layout.carryInWork_ne j)) x

/-- A local carry-work stage preserves any readout whose wire is not the
selected work-carry output wire. -/
theorem carryOutGatesAt_get_of_work_ne
    (j : Fin (n - 1)) (observed : EncodedBit encoding)
    (hne : (layout.workCarry.bit j).wire ≠ observed.wire) (x : Carrier) :
    observed.get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x) =
      observed.get x := by
  simpa [carryOutGatesAt, BitSlice.Encoded.carryOutStep] using
    BitSlice.Encoded.carryOutStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) observed
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) hne x

/-- Reverse cleanup gates for one low-word carry position.  These gates clear
the selected work carry when the corresponding left/right/carry-input controls
still have the values used to compute it [VBE95, 9511018.tex:254-264,596-618]. -/
def carryOutCleanupGatesAt (j : Fin (n - 1)) :
    List (EncodedBit.GateSpec encoding) :=
  BitSlice.Encoded.carryOutCleanupGates
    (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
    (carryInput layout j) (layout.workCarry.bit j)
    (layout.leftRight_ne (lowIndex j) (lowIndex j))
    (left_carryInput_ne layout j)
    (layout.leftWork_ne (lowIndex j) j)
    (right_carryInput_ne layout j)
    (layout.rightWork_ne (lowIndex j) j)
    (carryInput_work_ne layout j)

/-- The reverse local carry block clears the selected work carry when that
work bit stores the full-adder carry for the still-preserved controls. -/
theorem carryOutCleanupGatesAt_get_workCarry_computed
    (j : Fin (n - 1)) (x : Carrier)
    (hcomputed : (layout.workCarry.bit j).get x =
      Bool.carry ((layout.left.bit (lowIndex j)).get x)
        ((layout.right.bit (lowIndex j)).get x)
        ((carryInput layout j).get x)) :
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList
          (carryOutCleanupGatesAt layout j) x) = false := by
  simpa [carryOutCleanupGatesAt, BitSlice.Encoded.carryOutCleanupStep] using
    BitSlice.Encoded.carryOutCleanupStep_get_carryOut_computed
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) x hcomputed

/-- A local carry cleanup block preserves every left readout. -/
theorem carryOutCleanupGatesAt_get_left_any
    (j : Fin (n - 1)) (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList
          (carryOutCleanupGatesAt layout j) x) =
      (layout.left.bit i).get x := by
  simpa [carryOutCleanupGatesAt, BitSlice.Encoded.carryOutCleanupStep] using
    BitSlice.Encoded.carryOutCleanupStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) (layout.left.bit i)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (Ne.symm (layout.leftWork_ne i j)) x

/-- A local carry cleanup block preserves every right readout. -/
theorem carryOutCleanupGatesAt_get_right_any
    (j : Fin (n - 1)) (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList
          (carryOutCleanupGatesAt layout j) x) =
      (layout.right.bit i).get x := by
  simpa [carryOutCleanupGatesAt, BitSlice.Encoded.carryOutCleanupStep] using
    BitSlice.Encoded.carryOutCleanupStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) (layout.right.bit i)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (Ne.symm (layout.rightWork_ne i j)) x

/-- A local carry cleanup block preserves the data carry-in readout. -/
theorem carryOutCleanupGatesAt_get_dataCarry
    (j : Fin (n - 1)) (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList
          (carryOutCleanupGatesAt layout j) x) =
      layout.carryIn.get x := by
  simpa [carryOutCleanupGatesAt, BitSlice.Encoded.carryOutCleanupStep] using
    BitSlice.Encoded.carryOutCleanupStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) layout.carryIn
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (Ne.symm (layout.carryInWork_ne j)) x

/-- A local carry cleanup block preserves every other temporary carry readout. -/
theorem carryOutCleanupGatesAt_get_workCarry_of_ne
    (j k : Fin (n - 1)) (hne : j ≠ k) (x : Carrier) :
    (layout.workCarry.bit k).get
        (EncodedBit.GateSpec.stepList
          (carryOutCleanupGatesAt layout j) x) =
      (layout.workCarry.bit k).get x := by
  simpa [carryOutCleanupGatesAt, BitSlice.Encoded.carryOutCleanupStep] using
    BitSlice.Encoded.carryOutCleanupStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) (layout.workCarry.bit k)
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) (layout.workWork_ne j k hne) x

/-- A local carry cleanup block preserves any readout whose wire is not the
selected work-carry output wire. -/
theorem carryOutCleanupGatesAt_get_of_work_ne
    (j : Fin (n - 1)) (observed : EncodedBit encoding)
    (hne : (layout.workCarry.bit j).wire ≠ observed.wire) (x : Carrier) :
    observed.get
        (EncodedBit.GateSpec.stepList
          (carryOutCleanupGatesAt layout j) x) =
      observed.get x := by
  simpa [carryOutCleanupGatesAt, BitSlice.Encoded.carryOutCleanupStep] using
    BitSlice.Encoded.carryOutCleanupStep_get_of_carryOut_ne
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) observed
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j) (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j) (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j) hne x

/-- Indices used by the forward carry-work stage. -/
def carryStageIndices : List (Fin (n - 1)) :=
  List.ofFn fun j : Fin (n - 1) => j

/-- Indexed local carry-work stages, in increasing temporary carry index
order. -/
def carryStageStages : List (List (EncodedBit.GateSpec encoding)) :=
  (carryStageIndices (n := n)).map fun j => carryOutGatesAt layout j

/-- Forward carry-work stage, in increasing temporary carry index order. -/
def carryStage : List (EncodedBit.GateSpec encoding) :=
  concatStages (carryStageStages layout)

/-- Folded semantic action of the forward carry-work stage over the index
list. -/
def carryStageIndexStep : Carrier -> Carrier :=
  (carryStageIndices (n := n)).foldl
    (fun y j => EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)

/-- Prefix of the forward carry-work stage, retaining the concrete increasing
`List.ofFn` order. -/
def carryStagePrefixStep (t : Nat) : Carrier -> Carrier :=
  ((carryStageIndices (n := n)).take t).foldl
    (fun y j => EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)

/-- Any fold of local carry-output stages preserves a work bit whose index is
absent from the folded stage list. -/
theorem foldl_carryOutGatesAt_get_workCarry_of_forall_ne
    (indices : List (Fin (n - 1))) (k : Fin (n - 1))
    (hne : forall j, j ∈ indices -> j ≠ k) (x : Carrier) :
    (layout.workCarry.bit k).get
        (indices.foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (carryOutGatesAt layout j) y) x) =
      (layout.workCarry.bit k).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.workCarry.bit k).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          (layout.workCarry.bit k).get x
      rw [ih]
      · exact carryOutGatesAt_get_workCarry_of_ne layout j k
          (hne j (by simp)) x
      · intro i hi
        exact hne i (by simp [hi])

/-- Any fold of local carry-output stages preserves an observed readout whose
wire is distinct from every folded work-carry target. -/
theorem foldl_carryOutGatesAt_get_observed_of_work_ne
    (indices : List (Fin (n - 1))) (observed : EncodedBit encoding)
    (hne : forall j, j ∈ indices ->
      (layout.workCarry.bit j).wire ≠ observed.wire) (x : Carrier) :
    observed.get
        (indices.foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (carryOutGatesAt layout j) y) x) =
      observed.get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        observed.get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          observed.get x
      rw [ih]
      · exact carryOutGatesAt_get_of_work_ne layout j observed
          (hne j (by simp)) x
      · intro i hi
        exact hne i (by simp [hi])

/-- Any fold of local carry-output stages preserves every left readout. -/
theorem foldl_carryOutGatesAt_get_left
    (indices : List (Fin (n - 1))) (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (indices.foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (carryOutGatesAt layout j) y) x) =
      (layout.left.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.left.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          (layout.left.bit i).get x
      rw [ih]
      exact carryOutGatesAt_get_left_any layout j i x

/-- Any fold of local carry-output stages preserves every right readout. -/
theorem foldl_carryOutGatesAt_get_right
    (indices : List (Fin (n - 1))) (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (indices.foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (carryOutGatesAt layout j) y) x) =
      (layout.right.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.right.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          (layout.right.bit i).get x
      rw [ih]
      exact carryOutGatesAt_get_right_any layout j i x

/-- Any fold of local carry-output stages preserves the data carry-in readout. -/
theorem foldl_carryOutGatesAt_get_dataCarry
    (indices : List (Fin (n - 1))) (x : Carrier) :
    layout.carryIn.get
        (indices.foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (carryOutGatesAt layout j) y) x) =
      layout.carryIn.get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        layout.carryIn.get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          layout.carryIn.get x
      rw [ih]
      exact carryOutGatesAt_get_dataCarry layout j x

@[simp] theorem carryStageIndices_length :
    (carryStageIndices (n := n)).length = n - 1 := by
  simp [carryStageIndices]

theorem carryStageIndices_getElem_val {i : Nat}
    (hi : i < (carryStageIndices (n := n)).length) :
    ((carryStageIndices (n := n))[i]'hi).val = i := by
  simp [carryStageIndices]

/-- Every member of the first `j.val` carry-stage indices is strictly before
`j`.  This is the order fact needed to know that stage `j` has not touched its
own clean work bit before the `j`-th local carry write. -/
theorem carryStageIndices_mem_take_val_lt {j k : Fin (n - 1)}
    (hmem : k ∈ (carryStageIndices (n := n)).take j.val) :
    k.val < j.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hki⟩
  have htakeLen :
      ((carryStageIndices (n := n)).take j.val).length = j.val := by
    rw [List.length_take, carryStageIndices_length]
    exact Nat.min_eq_left (le_of_lt j.isLt)
  have hij : i < j.val :=
    by simpa [htakeLen] using hi
  have hiOrig : i < (carryStageIndices (n := n)).length := by
    rw [carryStageIndices_length]
    exact lt_trans hij j.isLt
  rw [← List.getElem_take' hiOrig hij] at hki
  have hkval : k.val = i := by
    rw [← hki]
    exact carryStageIndices_getElem_val (n := n) hiOrig
  omega

/-- Every member of the suffix after index `j` is strictly after `j`. -/
theorem carryStageIndices_mem_drop_succ_val_gt {j k : Fin (n - 1)}
    (hmem : k ∈ (carryStageIndices (n := n)).drop (j.val + 1)) :
    j.val < k.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hki⟩
  have hiOrig : j.val + 1 + i < (carryStageIndices (n := n)).length := by
    have h := hi
    have hjLe : j.val + 1 <= n - 1 := Nat.succ_le_of_lt j.isLt
    rw [carryStageIndices_length]
    rw [List.length_drop, carryStageIndices_length] at h
    omega
  rw [List.getElem_drop] at hki
  have hkval : k.val = j.val + 1 + i := by
    rw [← hki]
    exact carryStageIndices_getElem_val (n := n) hiOrig
  omega

theorem carryStagePrefixStep_get_left
    (t : Nat) (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get (carryStagePrefixStep layout t x) =
      (layout.left.bit i).get x := by
  unfold carryStagePrefixStep
  exact foldl_carryOutGatesAt_get_left layout
    ((carryStageIndices (n := n)).take t) i x

theorem carryStagePrefixStep_get_right
    (t : Nat) (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (carryStagePrefixStep layout t x) =
      (layout.right.bit i).get x := by
  unfold carryStagePrefixStep
  exact foldl_carryOutGatesAt_get_right layout
    ((carryStageIndices (n := n)).take t) i x

theorem carryStagePrefixStep_get_dataCarry
    (t : Nat) (x : Carrier) :
    layout.carryIn.get (carryStagePrefixStep layout t x) =
      layout.carryIn.get x := by
  unfold carryStagePrefixStep
  exact foldl_carryOutGatesAt_get_dataCarry layout
    ((carryStageIndices (n := n)).take t) x

theorem carryStagePrefixStep_get_workCarry_before
    (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get (carryStagePrefixStep layout j.val x) =
      (layout.workCarry.bit j).get x := by
  unfold carryStagePrefixStep
  exact foldl_carryOutGatesAt_get_workCarry_of_forall_ne layout
    ((carryStageIndices (n := n)).take j.val) j
    (by
      intro k hmem hkj
      have hklt : k.val < j.val :=
        carryStageIndices_mem_take_val_lt (n := n) hmem
      have hval := congrArg Fin.val hkj
      omega)
    x

/-- After the prefix ending at stage `j`, the selected work bit stores the
local full-adder carry for that stage, assuming the work register was initially
clean.  This is the ordered-prefix form of the VBE forward carry pass
[VBE95, 9511018.tex:237-264,596-618]. -/
theorem carryStagePrefixStep_get_workCarry_current
    (j : Fin (n - 1)) (x : Carrier)
    (hclean : forall k, (layout.workCarry.bit k).get x = false) :
    (layout.workCarry.bit j).get
        (carryStagePrefixStep layout (j.val + 1) x) =
      Bool.carry
        ((layout.left.bit (lowIndex j)).get x)
        ((layout.right.bit (lowIndex j)).get x)
        ((carryInput layout j).get (carryStagePrefixStep layout j.val x)) := by
  have hjLt : j.val < (carryStageIndices (n := n)).length := by
    rw [carryStageIndices_length]
    exact j.isLt
  have hget : (carryStageIndices (n := n))[j.val]'hjLt = j := by
    apply Fin.ext
    exact carryStageIndices_getElem_val (n := n) hjLt
  have htake :
      (carryStageIndices (n := n)).take (j.val + 1) =
        (carryStageIndices (n := n)).take j.val ++ [j] := by
    rw [← List.take_concat_get' (carryStageIndices (n := n)) j.val hjLt]
    rw [hget]
  have hcleanBefore :
      (layout.workCarry.bit j).get (carryStagePrefixStep layout j.val x) =
        false := by
    rw [carryStagePrefixStep_get_workCarry_before]
    exact hclean j
  have hlocal :=
    carryOutGatesAt_get_workCarry_clean layout j
      (carryStagePrefixStep layout j.val x) hcleanBefore
  rw [carryStagePrefixStep_get_left, carryStagePrefixStep_get_right] at hlocal
  change
    (layout.workCarry.bit j).get
        (((carryStageIndices (n := n)).take (j.val + 1)).foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (carryOutGatesAt layout j) y) x) =
      Bool.carry
        ((layout.left.bit (lowIndex j)).get x)
        ((layout.right.bit (lowIndex j)).get x)
        ((carryInput layout j).get (carryStagePrefixStep layout j.val x))
  rw [htake, List.foldl_append]
  change
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j)
          (carryStagePrefixStep layout j.val x)) =
      Bool.carry
        ((layout.left.bit (lowIndex j)).get x)
        ((layout.right.bit (lowIndex j)).get x)
        ((carryInput layout j).get (carryStagePrefixStep layout j.val x))
  simpa [List.foldl] using hlocal

/-- The suffix after stage `j` does not modify work bit `j`. -/
theorem carryStageIndexStep_get_workCarry_from_prefix
    (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get (carryStageIndexStep layout x) =
      (layout.workCarry.bit j).get
        (carryStagePrefixStep layout (j.val + 1) x) := by
  unfold carryStageIndexStep carryStagePrefixStep
  nth_rw 1 [← List.take_append_drop (j.val + 1)
    (carryStageIndices (n := n))]
  rw [List.foldl_append]
  exact foldl_carryOutGatesAt_get_workCarry_of_forall_ne layout
    ((carryStageIndices (n := n)).drop (j.val + 1)) j
    (by
      intro k hmem hkj
      have hkgt : j.val < k.val :=
        carryStageIndices_mem_drop_succ_val_gt (n := n) hmem
      have hval := congrArg Fin.val hkj
      omega)
    (((carryStageIndices (n := n)).take (j.val + 1)).foldl
      (fun y j => EncodedBit.GateSpec.stepList
        (carryOutGatesAt layout j) y) x)

/-- Full forward carry-stage readout for work bit `j`, stated with the
carry-input at the prefix time.  This is the ordered forward-pass recurrence
needed before the final word-level adder invariant [VBE95,
9511018.tex:237-264,596-618]. -/
theorem carryStageIndexStep_get_workCarry_prefix_recurrence
    (j : Fin (n - 1)) (x : Carrier)
    (hclean : forall k, (layout.workCarry.bit k).get x = false) :
    (layout.workCarry.bit j).get (carryStageIndexStep layout x) =
      Bool.carry
        ((layout.left.bit (lowIndex j)).get x)
        ((layout.right.bit (lowIndex j)).get x)
        ((carryInput layout j).get (carryStagePrefixStep layout j.val x)) := by
  rw [carryStageIndexStep_get_workCarry_from_prefix]
  exact carryStagePrefixStep_get_workCarry_current layout j x hclean

/-- The carry input used at stage `j` has the same readout at the prefix time
and after the full forward carry pass. -/
theorem carryStagePrefixStep_carryInput_eq_indexStep
    (j : Fin (n - 1)) (x : Carrier) :
    (carryInput layout j).get (carryStagePrefixStep layout j.val x) =
      (carryInput layout j).get (carryStageIndexStep layout x) := by
  unfold carryInput
  by_cases h : j.val = 0
  · have hfull :
        layout.carryIn.get (carryStageIndexStep layout x) =
          layout.carryIn.get x := by
      unfold carryStageIndexStep
      exact foldl_carryOutGatesAt_get_dataCarry layout
        (carryStageIndices (n := n)) x
    simp [h, carryStagePrefixStep_get_dataCarry, hfull]
  · have hp :
        (previousWorkIndex j h).val + 1 = j.val := by
      dsimp [previousWorkIndex]
      omega
    have hfull :=
      carryStageIndexStep_get_workCarry_from_prefix layout
        (previousWorkIndex j h) x
    rw [hp] at hfull
    simpa [h] using hfull.symm

/-- Full forward carry-stage recurrence for each temporary carry bit.  The
resource and correctness object is still the same ordered gate list; this
theorem identifies the work-bit value it computes [VBE95,
9511018.tex:237-264,596-618]. -/
theorem carryStageIndexStep_get_workCarry_recurrence
    (j : Fin (n - 1)) (x : Carrier)
    (hclean : forall k, (layout.workCarry.bit k).get x = false) :
    (layout.workCarry.bit j).get (carryStageIndexStep layout x) =
      Bool.carry
        ((layout.left.bit (lowIndex j)).get x)
        ((layout.right.bit (lowIndex j)).get x)
        ((carryInput layout j).get (carryStageIndexStep layout x)) := by
  rw [carryStageIndexStep_get_workCarry_prefix_recurrence layout j x hclean]
  rw [carryStagePrefixStep_carryInput_eq_indexStep]

/-- Folded semantic action of the forward carry-work stage as a fold over its
local carry stages. -/
theorem carryStage_stepList_eq_fold (x : Carrier) :
    EncodedBit.GateSpec.stepList (carryStage layout) x =
      (carryStageStages layout).foldl
        (fun y gates => EncodedBit.GateSpec.stepList gates y) x := by
  exact stepList_concatStages (carryStageStages layout) x

/-- Folded semantic action of the forward carry-work stage as a fold over the
stage indices. -/
theorem carryStage_stepList_eq_indexStep (x : Carrier) :
    EncodedBit.GateSpec.stepList (carryStage layout) x =
      carryStageIndexStep layout x := by
  rw [carryStage_stepList_eq_fold]
  unfold carryStageStages carryStageIndexStep
  generalize carryStageIndices = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)

/-- The complete forward carry-work stage preserves every left readout. -/
theorem carryStageIndexStep_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get (carryStageIndexStep layout x) =
      (layout.left.bit i).get x := by
  unfold carryStageIndexStep carryStageIndices
  generalize List.ofFn (fun j : Fin (n - 1) => j) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.left.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          (layout.left.bit i).get x
      rw [ih]
      exact carryOutGatesAt_get_left_any layout j i x

/-- The complete forward carry-work stage preserves every right readout. -/
theorem carryStageIndexStep_get_right (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (carryStageIndexStep layout x) =
      (layout.right.bit i).get x := by
  unfold carryStageIndexStep carryStageIndices
  generalize List.ofFn (fun j : Fin (n - 1) => j) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.right.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          (layout.right.bit i).get x
      rw [ih]
      exact carryOutGatesAt_get_right_any layout j i x

/-- The complete forward carry-work stage preserves the data carry-in readout. -/
theorem carryStageIndexStep_get_dataCarry (x : Carrier) :
    layout.carryIn.get (carryStageIndexStep layout x) =
      layout.carryIn.get x := by
  unfold carryStageIndexStep carryStageIndices
  generalize List.ofFn (fun j : Fin (n - 1) => j) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        layout.carryIn.get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (carryOutGatesAt layout j) x)) =
          layout.carryIn.get x
      rw [ih]
      exact carryOutGatesAt_get_dataCarry layout j x

/-- The complete forward carry-work stage preserves an observed readout whose
wire is distinct from every work-carry target. -/
theorem carryStageIndexStep_get_observed_of_work_ne
    (observed : EncodedBit encoding)
    (hne : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get (carryStageIndexStep layout x) = observed.get x := by
  unfold carryStageIndexStep carryStageIndices
  exact foldl_carryOutGatesAt_get_observed_of_work_ne layout
    (List.ofFn fun j : Fin (n - 1) => j) observed
    (by intro j _; exact hne j) x

/-- The complete forward carry-work gate list preserves every left readout. -/
theorem carryStage_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList (carryStage layout) x) =
      (layout.left.bit i).get x := by
  rw [carryStage_stepList_eq_indexStep]
  exact carryStageIndexStep_get_left layout i x

/-- The complete forward carry-work gate list preserves every right readout. -/
theorem carryStage_get_right (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (carryStage layout) x) =
      (layout.right.bit i).get x := by
  rw [carryStage_stepList_eq_indexStep]
  exact carryStageIndexStep_get_right layout i x

/-- The complete forward carry-work gate list preserves the data carry-in
readout. -/
theorem carryStage_get_dataCarry (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (carryStage layout) x) =
      layout.carryIn.get x := by
  rw [carryStage_stepList_eq_indexStep]
  exact carryStageIndexStep_get_dataCarry layout x

/-- The complete forward carry-work gate list preserves an observed readout
whose wire is distinct from every work-carry target. -/
theorem carryStage_get_observed_of_work_ne
    (observed : EncodedBit encoding)
    (hne : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get (EncodedBit.GateSpec.stepList (carryStage layout) x) =
      observed.get x := by
  rw [carryStage_stepList_eq_indexStep]
  exact carryStageIndexStep_get_observed_of_work_ne layout observed hne x

/-- Sum gates for one target word position. -/
def sumGatesAt (i : Fin n) : List (EncodedBit.GateSpec encoding) :=
  BitSlice.Encoded.sumGates (layout.left.bit i) (carryBeforeSum layout i)
    (layout.right.bit i) (layout.leftRight_ne i i)
    (carryBeforeSum_right_ne layout i)

/-- A local sum stage xors the selected left and carry readouts into the
selected right/target readout. -/
theorem sumGatesAt_get_right (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x) := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_target
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      (layout.leftRight_ne i i) (carryBeforeSum_right_ne layout i) x

/-- A local sum stage preserves the selected left readout. -/
theorem sumGatesAt_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      (layout.left.bit i).get x := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_left
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      (layout.leftRight_ne i i) (carryBeforeSum_right_ne layout i) x

/-- A local sum stage preserves its carry readout. -/
theorem sumGatesAt_get_carryBeforeSum (i : Fin n) (x : Carrier) :
    (carryBeforeSum layout i).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      (carryBeforeSum layout i).get x := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_carry
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      (layout.leftRight_ne i i) (carryBeforeSum_right_ne layout i) x

/-- A local sum stage preserves every left readout. -/
theorem sumGatesAt_get_left_any (i j : Fin n) (x : Carrier) :
    (layout.left.bit j).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      (layout.left.bit j).get x := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_of_target_ne
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      (layout.left.bit j) (layout.leftRight_ne i i)
      (carryBeforeSum_right_ne layout i)
      (Ne.symm (layout.leftRight_ne j i)) x

/-- A local sum stage preserves every other right readout. -/
theorem sumGatesAt_get_right_of_ne
    (i j : Fin n) (hne : i ≠ j) (x : Carrier) :
    (layout.right.bit j).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      (layout.right.bit j).get x := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_of_target_ne
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      (layout.right.bit j) (layout.leftRight_ne i i)
      (carryBeforeSum_right_ne layout i)
      (layout.rightRight_ne i j hne) x

/-- A local sum stage preserves the data carry-in readout. -/
theorem sumGatesAt_get_dataCarry (i : Fin n) (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      layout.carryIn.get x := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_of_target_ne
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      layout.carryIn (layout.leftRight_ne i i)
      (carryBeforeSum_right_ne layout i) (layout.rightCarryIn_ne i) x

/-- A local sum stage preserves every temporary carry-work readout. -/
theorem sumGatesAt_get_workCarry
    (i : Fin n) (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      (layout.workCarry.bit j).get x := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_of_target_ne
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      (layout.workCarry.bit j) (layout.leftRight_ne i i)
      (carryBeforeSum_right_ne layout i) (layout.rightWork_ne i j) x

/-- A local sum stage preserves any observed readout whose wire is not the
selected right/target wire. -/
theorem sumGatesAt_get_observed_of_right_ne
    (i : Fin n) (observed : EncodedBit encoding)
    (hne : (layout.right.bit i).wire ≠ observed.wire) (x : Carrier) :
    observed.get (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      observed.get x := by
  simpa [sumGatesAt, BitSlice.Encoded.sumStep] using
    BitSlice.Encoded.sumStep_get_of_target_ne
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      observed (layout.leftRight_ne i i) (carryBeforeSum_right_ne layout i)
      hne x

/-- A local sum stage preserves the carry-input readout used by any carry-work
stage. -/
theorem sumGatesAt_get_carryInput
    (i : Fin n) (j : Fin (n - 1)) (x : Carrier) :
    (carryInput layout j).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
      (carryInput layout j).get x := by
  unfold carryInput
  by_cases h : j.val = 0
  · simpa [h] using sumGatesAt_get_dataCarry layout i x
  · simpa [h] using
      sumGatesAt_get_workCarry layout i (previousWorkIndex j h) x

/-- Indices used by the sum stage. -/
def sumStageIndices : List (Fin n) :=
  List.ofFn fun i : Fin n => i

/-- Indexed local sum stages, in increasing target-word index order. -/
def sumStageStages : List (List (EncodedBit.GateSpec encoding)) :=
  (sumStageIndices (n := n)).map fun i => sumGatesAt layout i

/-- Sum stage over all target word bits, using the preceding carry bit for
each position. -/
def sumStage : List (EncodedBit.GateSpec encoding) :=
  concatStages (sumStageStages layout)

/-- Folded semantic action of the sum stage over the index list. -/
def sumStageIndexStep : Carrier -> Carrier :=
  (sumStageIndices (n := n)).foldl
    (fun y i => EncodedBit.GateSpec.stepList (sumGatesAt layout i) y)

/-- Prefix of the sum stage, retaining the concrete increasing `List.ofFn`
target-bit order. -/
def sumStagePrefixStep (t : Nat) : Carrier -> Carrier :=
  ((sumStageIndices (n := n)).take t).foldl
    (fun y i => EncodedBit.GateSpec.stepList (sumGatesAt layout i) y)

/-- Any fold of local sum stages preserves a right bit whose index is absent
from the folded stage list. -/
theorem foldl_sumGatesAt_get_right_of_forall_ne
    (indices : List (Fin n)) (i : Fin n)
    (hne : forall j, j ∈ indices -> j ≠ i) (x : Carrier) :
    (layout.right.bit i).get
        (indices.foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (sumGatesAt layout j) y) x) =
      (layout.right.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.right.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout j) x)) =
          (layout.right.bit i).get x
      rw [ih]
      · exact sumGatesAt_get_right_of_ne layout j i (hne j (by simp)) x
      · intro k hk
        exact hne k (by simp [hk])

/-- Any fold of local sum stages preserves an observed readout whose wire is
distinct from every folded right/target wire. -/
theorem foldl_sumGatesAt_get_observed_of_right_ne
    (indices : List (Fin n)) (observed : EncodedBit encoding)
    (hne : forall i, i ∈ indices ->
      (layout.right.bit i).wire ≠ observed.wire) (x : Carrier) :
    observed.get
        (indices.foldl
          (fun y i => EncodedBit.GateSpec.stepList
            (sumGatesAt layout i) y) x) =
      observed.get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x)) =
          observed.get x
      rw [ih]
      · exact sumGatesAt_get_observed_of_right_ne layout i observed
          (hne i (by simp)) x
      · intro j hj
        exact hne j (by simp [hj])

@[simp] theorem sumStageIndices_length :
    (sumStageIndices (n := n)).length = n := by
  simp [sumStageIndices]

theorem sumStageIndices_getElem_val {i : Nat}
    (hi : i < (sumStageIndices (n := n)).length) :
    ((sumStageIndices (n := n))[i]'hi).val = i := by
  simp [sumStageIndices]

/-- Every member of the first `i.val` sum-stage indices is strictly before
`i`, so it has not targeted right bit `i`. -/
theorem sumStageIndices_mem_take_val_lt {i j : Fin n}
    (hmem : j ∈ (sumStageIndices (n := n)).take i.val) :
    j.val < i.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨k, hk, hji⟩
  have htakeLen :
      ((sumStageIndices (n := n)).take i.val).length = i.val := by
    rw [List.length_take, sumStageIndices_length]
    exact Nat.min_eq_left (le_of_lt i.isLt)
  have hki : k < i.val :=
    by simpa [htakeLen] using hk
  have hkOrig : k < (sumStageIndices (n := n)).length := by
    rw [sumStageIndices_length]
    exact lt_trans hki i.isLt
  rw [← List.getElem_take' hkOrig hki] at hji
  have hjval : j.val = k := by
    rw [← hji]
    exact sumStageIndices_getElem_val (n := n) hkOrig
  omega

/-- Every member of the suffix after index `i` is strictly after `i`. -/
theorem sumStageIndices_mem_drop_succ_val_gt {i j : Fin n}
    (hmem : j ∈ (sumStageIndices (n := n)).drop (i.val + 1)) :
    i.val < j.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨k, hk, hji⟩
  have hkOrig : i.val + 1 + k < (sumStageIndices (n := n)).length := by
    have h := hk
    have hiLe : i.val + 1 <= n := Nat.succ_le_of_lt i.isLt
    rw [sumStageIndices_length]
    rw [List.length_drop, sumStageIndices_length] at h
    omega
  rw [List.getElem_drop] at hji
  have hjval : j.val = i.val + 1 + k := by
    rw [← hji]
    exact sumStageIndices_getElem_val (n := n) hkOrig
  omega

/-- The prefix before sum stage `i` preserves right bit `i`. -/
theorem sumStagePrefixStep_get_right_before (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (sumStagePrefixStep layout i.val x) =
      (layout.right.bit i).get x := by
  unfold sumStagePrefixStep
  exact foldl_sumGatesAt_get_right_of_forall_ne layout
    ((sumStageIndices (n := n)).take i.val) i
    (by
      intro j hmem hji
      have hjlt : j.val < i.val :=
        sumStageIndices_mem_take_val_lt (n := n) hmem
      have hval := congrArg Fin.val hji
      omega)
    x

theorem sumStagePrefixStep_get_left
    (t : Nat) (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get (sumStagePrefixStep layout t x) =
      (layout.left.bit i).get x := by
  unfold sumStagePrefixStep
  induction (sumStageIndices (n := n)).take t generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.left.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout j) x)) =
          (layout.left.bit i).get x
      rw [ih]
      exact sumGatesAt_get_left_any layout j i x

theorem sumStagePrefixStep_get_dataCarry
    (t : Nat) (x : Carrier) :
    layout.carryIn.get (sumStagePrefixStep layout t x) =
      layout.carryIn.get x := by
  unfold sumStagePrefixStep
  induction (sumStageIndices (n := n)).take t generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        layout.carryIn.get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout j) x)) =
          layout.carryIn.get x
      rw [ih]
      exact sumGatesAt_get_dataCarry layout j x

theorem sumStagePrefixStep_get_workCarry
    (t : Nat) (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get (sumStagePrefixStep layout t x) =
      (layout.workCarry.bit j).get x := by
  unfold sumStagePrefixStep
  induction (sumStageIndices (n := n)).take t generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        (layout.workCarry.bit j).get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x)) =
          (layout.workCarry.bit j).get x
      rw [ih]
      exact sumGatesAt_get_workCarry layout i j x

theorem sumStagePrefixStep_get_carryBeforeSum
    (t : Nat) (i : Fin n) (x : Carrier) :
    (carryBeforeSum layout i).get (sumStagePrefixStep layout t x) =
      (carryBeforeSum layout i).get x := by
  unfold carryBeforeSum
  by_cases h : i.val = 0
  · simp [h, sumStagePrefixStep_get_dataCarry]
  · simp [h, sumStagePrefixStep_get_workCarry]

/-- After the prefix ending at sum stage `i`, right bit `i` stores the local
xor-sum of its original right bit, left bit, and selected carry bit. -/
theorem sumStagePrefixStep_get_right_current (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (sumStagePrefixStep layout (i.val + 1) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x) := by
  have hiLt : i.val < (sumStageIndices (n := n)).length := by
    rw [sumStageIndices_length]
    exact i.isLt
  have hget : (sumStageIndices (n := n))[i.val]'hiLt = i := by
    apply Fin.ext
    exact sumStageIndices_getElem_val (n := n) hiLt
  have htake :
      (sumStageIndices (n := n)).take (i.val + 1) =
        (sumStageIndices (n := n)).take i.val ++ [i] := by
    rw [← List.take_concat_get' (sumStageIndices (n := n)) i.val hiLt]
    rw [hget]
  have hlocal :=
    sumGatesAt_get_right layout i (sumStagePrefixStep layout i.val x)
  rw [sumStagePrefixStep_get_right_before, sumStagePrefixStep_get_left,
    sumStagePrefixStep_get_carryBeforeSum] at hlocal
  change
    (layout.right.bit i).get
        (((sumStageIndices (n := n)).take (i.val + 1)).foldl
          (fun y i => EncodedBit.GateSpec.stepList
            (sumGatesAt layout i) y) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x)
  rw [htake, List.foldl_append]
  change
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (sumGatesAt layout i)
          (sumStagePrefixStep layout i.val x)) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x)
  simpa [List.foldl] using hlocal

/-- The suffix after sum stage `i` does not modify right bit `i`. -/
theorem sumStageIndexStep_get_right_from_prefix
    (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (sumStageIndexStep layout x) =
      (layout.right.bit i).get
        (sumStagePrefixStep layout (i.val + 1) x) := by
  unfold sumStageIndexStep sumStagePrefixStep
  nth_rw 1 [← List.take_append_drop (i.val + 1)
    (sumStageIndices (n := n))]
  rw [List.foldl_append]
  exact foldl_sumGatesAt_get_right_of_forall_ne layout
    ((sumStageIndices (n := n)).drop (i.val + 1)) i
    (by
      intro j hmem hji
      have hjgt : i.val < j.val :=
        sumStageIndices_mem_drop_succ_val_gt (n := n) hmem
      have hval := congrArg Fin.val hji
      omega)
    (((sumStageIndices (n := n)).take (i.val + 1)).foldl
      (fun y i => EncodedBit.GateSpec.stepList
        (sumGatesAt layout i) y) x)

/-- Closed-form readout of each target bit after the complete sum stage. -/
theorem sumStageIndexStep_get_right (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (sumStageIndexStep layout x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x) := by
  rw [sumStageIndexStep_get_right_from_prefix]
  exact sumStagePrefixStep_get_right_current layout i x

/-- Folded semantic action of the sum stage as a fold over its local stages. -/
theorem sumStage_stepList_eq_fold (x : Carrier) :
    EncodedBit.GateSpec.stepList (sumStage layout) x =
      (sumStageStages layout).foldl
        (fun y gates => EncodedBit.GateSpec.stepList gates y) x := by
  exact stepList_concatStages (sumStageStages layout) x

/-- Folded semantic action of the sum stage as a fold over the stage indices. -/
theorem sumStage_stepList_eq_indexStep (x : Carrier) :
    EncodedBit.GateSpec.stepList (sumStage layout) x =
      sumStageIndexStep layout x := by
  rw [sumStage_stepList_eq_fold]
  unfold sumStageStages sumStageIndexStep
  generalize sumStageIndices = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x)

/-- The complete sum stage preserves every left readout. -/
theorem sumStageIndexStep_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get (sumStageIndexStep layout x) =
      (layout.left.bit i).get x := by
  unfold sumStageIndexStep sumStageIndices
  generalize List.ofFn (fun j : Fin n => j) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.left.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout j) x)) =
          (layout.left.bit i).get x
      rw [ih]
      exact sumGatesAt_get_left_any layout j i x

/-- The complete sum stage preserves the data carry-in readout. -/
theorem sumStageIndexStep_get_dataCarry (x : Carrier) :
    layout.carryIn.get (sumStageIndexStep layout x) =
      layout.carryIn.get x := by
  unfold sumStageIndexStep sumStageIndices
  generalize List.ofFn (fun j : Fin n => j) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        layout.carryIn.get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout j) x)) =
          layout.carryIn.get x
      rw [ih]
      exact sumGatesAt_get_dataCarry layout j x

/-- The complete sum stage preserves every temporary carry-work readout. -/
theorem sumStageIndexStep_get_workCarry (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get (sumStageIndexStep layout x) =
      (layout.workCarry.bit j).get x := by
  unfold sumStageIndexStep sumStageIndices
  generalize List.ofFn (fun i : Fin n => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        (layout.workCarry.bit j).get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList (sumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x)) =
          (layout.workCarry.bit j).get x
      rw [ih]
      exact sumGatesAt_get_workCarry layout i j x

/-- The complete sum gate list preserves every left readout. -/
theorem sumStage_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList (sumStage layout) x) =
      (layout.left.bit i).get x := by
  rw [sumStage_stepList_eq_indexStep]
  exact sumStageIndexStep_get_left layout i x

/-- The complete sum gate list preserves the data carry-in readout. -/
theorem sumStage_get_dataCarry (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (sumStage layout) x) =
      layout.carryIn.get x := by
  rw [sumStage_stepList_eq_indexStep]
  exact sumStageIndexStep_get_dataCarry layout x

/-- The complete sum gate list preserves every temporary carry-work readout. -/
theorem sumStage_get_workCarry (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList (sumStage layout) x) =
      (layout.workCarry.bit j).get x := by
  rw [sumStage_stepList_eq_indexStep]
  exact sumStageIndexStep_get_workCarry layout j x

/-- The temporary carry cleared immediately after summing a nonzero target
position in the cleanup-aware pass. -/
def cleanupWorkIndex (i : Fin n) (_h : i.val ≠ 0) : Fin (n - 1) :=
  ⟨i.val - 1, by
    have hi : i.val < n := i.isLt
    omega⟩

@[simp] theorem cleanupWorkIndex_val (i : Fin n) (h : i.val ≠ 0) :
    (cleanupWorkIndex i h).val = i.val - 1 :=
  rfl

/-- The low word position whose carry is cleared after summing a nonzero
position is strictly below that summed position. -/
theorem cleanupWorkIndex_lowIndex_ne (i : Fin n) (h : i.val ≠ 0) :
    i ≠ lowIndex (cleanupWorkIndex i h) := by
  intro heq
  have hv := congrArg Fin.val heq
  simp [cleanupWorkIndex] at hv
  omega

/-- Target bit whose cleanup-aware stage clears temporary carry `j`. -/
def cleanupTargetIndex (j : Fin (n - 1)) : Fin n :=
  ⟨j.val + 1, by
    have hj := j.isLt
    omega⟩

@[simp] theorem cleanupTargetIndex_val (j : Fin (n - 1)) :
    (cleanupTargetIndex j).val = j.val + 1 :=
  rfl

theorem cleanupTargetIndex_ne_zero (j : Fin (n - 1)) :
    (cleanupTargetIndex j).val ≠ 0 := by
  simp [cleanupTargetIndex]

theorem cleanupWorkIndex_cleanupTargetIndex (j : Fin (n - 1)) :
    cleanupWorkIndex (cleanupTargetIndex j)
        (cleanupTargetIndex_ne_zero (n := n) j) = j := by
  apply Fin.ext
  simp [cleanupWorkIndex, cleanupTargetIndex]

/-- Local stage used by the cleanup-aware plain-adder schedule.  It first writes
the target sum bit, then, except at bit zero, immediately clears the preceding
temporary carry while its controls still match that carry's computation
[VBE95, 9511018.tex:254-264,596-618]. -/
def cleanupSumGatesAt (i : Fin n) : List (EncodedBit.GateSpec encoding) :=
  if h : i.val = 0 then
    sumGatesAt layout i
  else
    sumGatesAt layout i ++ carryOutCleanupGatesAt layout
      (cleanupWorkIndex i h)

/-- A local cleanup-aware sum stage preserves every left readout. -/
theorem cleanupSumGatesAt_get_left_any
    (i j : Fin n) (x : Carrier) :
    (layout.left.bit j).get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x) =
      (layout.left.bit j).get x := by
  unfold cleanupSumGatesAt
  by_cases h : i.val = 0
  · simpa [h] using sumGatesAt_get_left_any layout i j x
  · simp [h, EncodedBit.GateSpec.stepList_append,
      carryOutCleanupGatesAt_get_left_any, sumGatesAt_get_left_any]

/-- A local cleanup-aware sum stage preserves the data carry-in readout. -/
theorem cleanupSumGatesAt_get_dataCarry
    (i : Fin n) (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x) =
      layout.carryIn.get x := by
  unfold cleanupSumGatesAt
  by_cases h : i.val = 0
  · simpa [h] using sumGatesAt_get_dataCarry layout i x
  · simp [h, EncodedBit.GateSpec.stepList_append,
      carryOutCleanupGatesAt_get_dataCarry, sumGatesAt_get_dataCarry]

/-- A local cleanup-aware sum stage writes the selected target bit exactly as
the corresponding local sum stage does. -/
theorem cleanupSumGatesAt_get_right
    (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x) := by
  unfold cleanupSumGatesAt
  by_cases h : i.val = 0
  · simpa [h] using sumGatesAt_get_right layout i x
  · simp [h, EncodedBit.GateSpec.stepList_append,
      carryOutCleanupGatesAt_get_right_any, sumGatesAt_get_right]

/-- A local cleanup-aware sum stage preserves every non-target right readout. -/
theorem cleanupSumGatesAt_get_right_of_ne
    (i j : Fin n) (hne : i ≠ j) (x : Carrier) :
    (layout.right.bit j).get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x) =
      (layout.right.bit j).get x := by
  unfold cleanupSumGatesAt
  by_cases h : i.val = 0
  · simpa [h] using sumGatesAt_get_right_of_ne layout i j hne x
  · simp [h, EncodedBit.GateSpec.stepList_append,
      carryOutCleanupGatesAt_get_right_any, sumGatesAt_get_right_of_ne,
      hne]

/-- A local cleanup-aware sum stage preserves a temporary carry readout that is
not the one cleared by this stage. -/
theorem cleanupSumGatesAt_get_workCarry_of_ne
    (i : Fin n) (k : Fin (n - 1))
    (hne : ∀ h : i.val ≠ 0, cleanupWorkIndex i h ≠ k) (x : Carrier) :
    (layout.workCarry.bit k).get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x) =
      (layout.workCarry.bit k).get x := by
  unfold cleanupSumGatesAt
  by_cases h : i.val = 0
  · simpa [h] using sumGatesAt_get_workCarry layout i k x
  · simp [h, EncodedBit.GateSpec.stepList_append,
      carryOutCleanupGatesAt_get_workCarry_of_ne,
      sumGatesAt_get_workCarry, hne h]

/-- A local cleanup-aware sum stage preserves an observed readout whose wire is
neither the selected right/target wire nor any work-carry cleanup target. -/
theorem cleanupSumGatesAt_get_observed_of_right_work_ne
    (i : Fin n) (observed : EncodedBit encoding)
    (hright : (layout.right.bit i).wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x) =
      observed.get x := by
  unfold cleanupSumGatesAt
  by_cases h : i.val = 0
  · simpa [h] using
      sumGatesAt_get_observed_of_right_ne layout i observed hright x
  · simp only [h, ↓reduceDIte, EncodedBit.GateSpec.stepList_append]
    rw [carryOutCleanupGatesAt_get_of_work_ne layout
      (cleanupWorkIndex i h) observed (hwork (cleanupWorkIndex i h))
      (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x)]
    exact sumGatesAt_get_observed_of_right_ne layout i observed hright x

/-- If the preceding temporary carry still stores the full-adder carry for its
unchanged controls, the local cleanup-aware stage clears that carry. -/
theorem cleanupSumGatesAt_get_cleanupWorkCarry_computed
    (i : Fin n) (h : i.val ≠ 0) (x : Carrier)
    (hcomputed :
      (layout.workCarry.bit (cleanupWorkIndex i h)).get x =
        Bool.carry
          ((layout.left.bit (lowIndex (cleanupWorkIndex i h))).get x)
          ((layout.right.bit (lowIndex (cleanupWorkIndex i h))).get x)
          ((carryInput layout (cleanupWorkIndex i h)).get x)) :
    (layout.workCarry.bit (cleanupWorkIndex i h)).get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x) =
      false := by
  let j := cleanupWorkIndex i h
  have hrightNe : i ≠ lowIndex j := by
    simpa [j] using cleanupWorkIndex_lowIndex_ne i h
  have hcomputedAfter :
      (layout.workCarry.bit j).get
          (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x) =
        Bool.carry
          ((layout.left.bit (lowIndex j)).get
            (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x))
          ((layout.right.bit (lowIndex j)).get
            (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x))
          ((carryInput layout j).get
            (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x)) := by
    rw [sumGatesAt_get_workCarry, sumGatesAt_get_left_any,
      sumGatesAt_get_right_of_ne layout i (lowIndex j) hrightNe,
      sumGatesAt_get_carryInput]
    simpa [j] using hcomputed
  have hclear :=
    carryOutCleanupGatesAt_get_workCarry_computed layout j
      (EncodedBit.GateSpec.stepList (sumGatesAt layout i) x)
      hcomputedAfter
  simpa [cleanupSumGatesAt, h, j, EncodedBit.GateSpec.stepList_append,
    cleanupWorkIndex] using hclear

/-- Indices for the cleanup-aware sum pass, in decreasing target-bit order. -/
def cleanupSumStageIndices : List (Fin n) :=
  (sumStageIndices (n := n)).reverse

/-- Indexed cleanup-aware sum stages. -/
def cleanupSumStageStages : List (List (EncodedBit.GateSpec encoding)) :=
  (cleanupSumStageIndices (n := n)).map fun i => cleanupSumGatesAt layout i

/-- Cleanup-aware sum stage.  This is the VBE-style order used to preserve the
controls needed by each local reverse carry cleanup [VBE95,
9511018.tex:254-264,596-618]. -/
def cleanupSumStage : List (EncodedBit.GateSpec encoding) :=
  concatStages (cleanupSumStageStages layout)

/-- Folded semantic action of the cleanup-aware sum stage over the index list. -/
def cleanupSumStageIndexStep : Carrier -> Carrier :=
  (cleanupSumStageIndices (n := n)).foldl
    (fun y i => EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) y)

/-- Prefix of the cleanup-aware sum stage, retaining the concrete decreasing
target-bit order. -/
def cleanupSumStagePrefixStep (t : Nat) : Carrier -> Carrier :=
  ((cleanupSumStageIndices (n := n)).take t).foldl
    (fun y i => EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) y)

/-- Any fold of local cleanup-aware sum stages preserves a right bit whose
index is absent from the folded stage list. -/
theorem foldl_cleanupSumGatesAt_get_right_of_forall_ne
    (indices : List (Fin n)) (i : Fin n)
    (hne : forall j, j ∈ indices -> j ≠ i) (x : Carrier) :
    (layout.right.bit i).get
        (indices.foldl
          (fun y j => EncodedBit.GateSpec.stepList
            (cleanupSumGatesAt layout j) y) x) =
      (layout.right.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.right.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList
                (cleanupSumGatesAt layout j) x)) =
          (layout.right.bit i).get x
      rw [ih]
      · exact cleanupSumGatesAt_get_right_of_ne layout j i
          (hne j (by simp)) x
      · intro k hk
        exact hne k (by simp [hk])

/-- Any fold of local cleanup-aware sum stages preserves a work-carry bit when
no folded stage clears that bit. -/
theorem foldl_cleanupSumGatesAt_get_workCarry_of_forall_ne
    (indices : List (Fin n)) (k : Fin (n - 1))
    (hne : ∀ i, i ∈ indices ->
      ∀ h : i.val ≠ 0, cleanupWorkIndex i h ≠ k)
    (x : Carrier) :
    (layout.workCarry.bit k).get
        (indices.foldl
          (fun y i => EncodedBit.GateSpec.stepList
            (cleanupSumGatesAt layout i) y) x) =
      (layout.workCarry.bit k).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        (layout.workCarry.bit k).get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList
                (cleanupSumGatesAt layout i) x)) =
          (layout.workCarry.bit k).get x
      rw [ih]
      · exact cleanupSumGatesAt_get_workCarry_of_ne layout i k
          (hne i (by simp)) x
      · intro j hj
        exact hne j (by simp [hj])

/-- Any fold of cleanup-aware sum stages preserves an observed readout whose
wire is distinct from every folded right/target wire and every work-carry
cleanup target. -/
theorem foldl_cleanupSumGatesAt_get_observed_of_right_work_ne
    (indices : List (Fin n)) (observed : EncodedBit encoding)
    (hright : forall i, i ∈ indices ->
      (layout.right.bit i).wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get
        (indices.foldl
          (fun y i => EncodedBit.GateSpec.stepList
            (cleanupSumGatesAt layout i) y) x) =
      observed.get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList
                (cleanupSumGatesAt layout i) x)) =
          observed.get x
      rw [ih]
      · exact cleanupSumGatesAt_get_observed_of_right_work_ne layout i
          observed (hright i (by simp)) hwork x
      · intro j hj
        exact hright j (by simp [hj])

@[simp] theorem cleanupSumStageIndices_length :
    (cleanupSumStageIndices (n := n)).length = n := by
  simp [cleanupSumStageIndices]

theorem cleanupSumStageIndices_getElem_val {i : Nat}
    (hi : i < (cleanupSumStageIndices (n := n)).length) :
    ((cleanupSumStageIndices (n := n))[i]'hi).val = n - 1 - i := by
  simp [cleanupSumStageIndices, sumStageIndices]

/-- Position of target bit `i` in the decreasing cleanup-aware sum pass. -/
def cleanupSumStagePosition (i : Fin n) : Nat :=
  n - 1 - i.val

theorem cleanupSumStagePosition_lt_length (i : Fin n) :
    cleanupSumStagePosition i <
      (cleanupSumStageIndices (n := n)).length := by
  rw [cleanupSumStageIndices_length]
  unfold cleanupSumStagePosition
  have hi := i.isLt
  omega

theorem cleanupSumStageIndices_get_position (i : Fin n)
    (hpos :
      cleanupSumStagePosition i <
        (cleanupSumStageIndices (n := n)).length) :
    ((cleanupSumStageIndices (n := n))[cleanupSumStagePosition i]'hpos) =
      i := by
  apply Fin.ext
  have hval :=
    cleanupSumStageIndices_getElem_val (n := n) hpos
  have hi := i.isLt
  have hcalc : n - 1 - (n - 1 - i.val) = i.val := by
    omega
  simpa [cleanupSumStagePosition, hcalc] using hval

/-- Every member before target `i` in the decreasing cleanup-aware pass is a
higher word position. -/
theorem cleanupSumStageIndices_mem_take_position_val_gt {i j : Fin n}
    (hmem : j ∈ (cleanupSumStageIndices (n := n)).take
      (cleanupSumStagePosition i)) :
    i.val < j.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨k, hk, hji⟩
  have hposLt := cleanupSumStagePosition_lt_length (n := n) i
  have htakeLen :
      ((cleanupSumStageIndices (n := n)).take
        (cleanupSumStagePosition i)).length =
        cleanupSumStagePosition i := by
    rw [List.length_take]
    exact Nat.min_eq_left (le_of_lt hposLt)
  have hkpos : k < cleanupSumStagePosition i := by
    simpa [htakeLen] using hk
  have hkOrig : k < (cleanupSumStageIndices (n := n)).length :=
    lt_trans hkpos hposLt
  rw [← List.getElem_take' hkOrig hkpos] at hji
  have hjval : j.val = n - 1 - k := by
    rw [← hji]
    exact cleanupSumStageIndices_getElem_val (n := n) hkOrig
  unfold cleanupSumStagePosition at hkpos
  have hi := i.isLt
  omega

/-- Every member after target `i` in the decreasing cleanup-aware pass is a
lower word position. -/
theorem cleanupSumStageIndices_mem_drop_succ_position_val_lt
    {i j : Fin n}
    (hmem : j ∈ (cleanupSumStageIndices (n := n)).drop
      (cleanupSumStagePosition i + 1)) :
    j.val < i.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨k, hk, hji⟩
  have hdropLen :
      ((cleanupSumStageIndices (n := n)).drop
        (cleanupSumStagePosition i + 1)).length = i.val := by
    rw [List.length_drop, cleanupSumStageIndices_length]
    unfold cleanupSumStagePosition
    have hi := i.isLt
    omega
  have hkBound : k < i.val := by
    simpa [hdropLen] using hk
  have hkOrig :
      cleanupSumStagePosition i + 1 + k <
        (cleanupSumStageIndices (n := n)).length := by
    rw [cleanupSumStageIndices_length]
    unfold cleanupSumStagePosition
    have hi := i.isLt
    omega
  rw [List.getElem_drop] at hji
  have hjval : j.val =
      n - 1 - (cleanupSumStagePosition i + 1 + k) := by
    rw [← hji]
    exact cleanupSumStageIndices_getElem_val (n := n) hkOrig
  unfold cleanupSumStagePosition at hjval
  have hi := i.isLt
  omega

/-- A prefix of the cleanup-aware sum stage preserves every left readout. -/
theorem cleanupSumStagePrefixStep_get_left
    (t : Nat) (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get (cleanupSumStagePrefixStep layout t x) =
      (layout.left.bit i).get x := by
  unfold cleanupSumStagePrefixStep
  induction (cleanupSumStageIndices (n := n)).take t generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.left.bit i).get
            (rest.foldl
              (fun y j =>
                EncodedBit.GateSpec.stepList
                  (cleanupSumGatesAt layout j) y)
              (EncodedBit.GateSpec.stepList
                (cleanupSumGatesAt layout j) x)) =
          (layout.left.bit i).get x
      rw [ih]
      exact cleanupSumGatesAt_get_left_any layout j i x

/-- A prefix of the cleanup-aware sum stage preserves the data carry-in readout. -/
theorem cleanupSumStagePrefixStep_get_dataCarry
    (t : Nat) (x : Carrier) :
    layout.carryIn.get (cleanupSumStagePrefixStep layout t x) =
      layout.carryIn.get x := by
  unfold cleanupSumStagePrefixStep
  induction (cleanupSumStageIndices (n := n)).take t generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        layout.carryIn.get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList
                  (cleanupSumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList
                (cleanupSumGatesAt layout i) x)) =
          layout.carryIn.get x
      rw [ih]
      exact cleanupSumGatesAt_get_dataCarry layout i x

/-- A prefix of the cleanup-aware sum stage preserves a temporary carry readout
when no stage in the prefix clears that carry. -/
theorem cleanupSumStagePrefixStep_get_workCarry_of_forall_ne
    (t : Nat) (k : Fin (n - 1))
    (hne : ∀ i, i ∈ (cleanupSumStageIndices (n := n)).take t ->
      ∀ h : i.val ≠ 0, cleanupWorkIndex i h ≠ k)
    (x : Carrier) :
    (layout.workCarry.bit k).get
        (cleanupSumStagePrefixStep layout t x) =
      (layout.workCarry.bit k).get x := by
  unfold cleanupSumStagePrefixStep
  exact foldl_cleanupSumGatesAt_get_workCarry_of_forall_ne layout
    ((cleanupSumStageIndices (n := n)).take t) k hne x

/-- The prefix before summing target `i` preserves right bit `i`. -/
theorem cleanupSumStagePrefixStep_get_right_before
    (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (cleanupSumStagePrefixStep layout (cleanupSumStagePosition i) x) =
      (layout.right.bit i).get x := by
  unfold cleanupSumStagePrefixStep
  exact foldl_cleanupSumGatesAt_get_right_of_forall_ne layout
    ((cleanupSumStageIndices (n := n)).take (cleanupSumStagePosition i)) i
    (by
      intro j hmem hji
      have hjgt :
          i.val < j.val :=
        cleanupSumStageIndices_mem_take_position_val_gt
          (n := n) hmem
      have hval := congrArg Fin.val hji
      omega)
    x

/-- The prefix before summing target `i` preserves the carry selected for
that target. -/
theorem cleanupSumStagePrefixStep_get_carryBeforeSum_before
    (i : Fin n) (x : Carrier) :
    (carryBeforeSum layout i).get
        (cleanupSumStagePrefixStep layout (cleanupSumStagePosition i) x) =
      (carryBeforeSum layout i).get x := by
  unfold carryBeforeSum
  by_cases h : i.val = 0
  · simp [h, cleanupSumStagePrefixStep_get_dataCarry]
  · simp [h]
    exact cleanupSumStagePrefixStep_get_workCarry_of_forall_ne layout
      (cleanupSumStagePosition i) (cleanupWorkIndex i h)
      (by
        intro j hmem hj hEq
        have hjgt :
            i.val < j.val :=
          cleanupSumStageIndices_mem_take_position_val_gt
            (n := n) hmem
        have hv := congrArg Fin.val hEq
        simp [cleanupWorkIndex] at hv
        omega)
      x

/-- The prefix before target `i` preserves every lower right readout. -/
theorem cleanupSumStagePrefixStep_get_right_before_of_lt
    (i j : Fin n) (hjlt : j.val < i.val) (x : Carrier) :
    (layout.right.bit j).get
        (cleanupSumStagePrefixStep layout (cleanupSumStagePosition i) x) =
      (layout.right.bit j).get x := by
  unfold cleanupSumStagePrefixStep
  exact foldl_cleanupSumGatesAt_get_right_of_forall_ne layout
    ((cleanupSumStageIndices (n := n)).take (cleanupSumStagePosition i)) j
    (by
      intro k hmem hkj
      have hkgt :
          i.val < k.val :=
        cleanupSumStageIndices_mem_take_position_val_gt
          (n := n) hmem
      have hval := congrArg Fin.val hkj
      omega)
    x

/-- The prefix before target `i` preserves every lower temporary carry readout. -/
theorem cleanupSumStagePrefixStep_get_workCarry_before_of_lt
    (i : Fin n) (k : Fin (n - 1)) (hklt : k.val < i.val)
    (x : Carrier) :
    (layout.workCarry.bit k).get
        (cleanupSumStagePrefixStep layout (cleanupSumStagePosition i) x) =
      (layout.workCarry.bit k).get x := by
  exact cleanupSumStagePrefixStep_get_workCarry_of_forall_ne layout
    (cleanupSumStagePosition i) k
    (by
      intro j hmem hj hEq
      have hjgt :
          i.val < j.val :=
        cleanupSumStageIndices_mem_take_position_val_gt
          (n := n) hmem
      have hv := congrArg Fin.val hEq
      simp [cleanupWorkIndex] at hv
      omega)
    x

/-- The prefix before the cleanup target for work carry `j` preserves that work
carry. -/
theorem cleanupSumStagePrefixStep_get_workCarry_before_cleanupTarget
    (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition (cleanupTargetIndex j)) x) =
      (layout.workCarry.bit j).get x := by
  exact cleanupSumStagePrefixStep_get_workCarry_before_of_lt layout
    (cleanupTargetIndex j) j (by simp [cleanupTargetIndex]) x

/-- The prefix before the cleanup target for work carry `j` preserves the
right-control bit used to compute that work carry. -/
theorem cleanupSumStagePrefixStep_get_right_lowIndex_before_cleanupTarget
    (j : Fin (n - 1)) (x : Carrier) :
    (layout.right.bit (lowIndex j)).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition (cleanupTargetIndex j)) x) =
      (layout.right.bit (lowIndex j)).get x := by
  exact cleanupSumStagePrefixStep_get_right_before_of_lt layout
    (cleanupTargetIndex j) (lowIndex j)
    (by simp [cleanupTargetIndex])
    x

/-- The prefix before the cleanup target for work carry `j` preserves the
carry-input control used to compute that work carry. -/
theorem cleanupSumStagePrefixStep_get_carryInput_before_cleanupTarget
    (j : Fin (n - 1)) (x : Carrier) :
    (carryInput layout j).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition (cleanupTargetIndex j)) x) =
      (carryInput layout j).get x := by
  unfold carryInput
  by_cases h : j.val = 0
  · simpa [h] using
      cleanupSumStagePrefixStep_get_dataCarry layout
        (cleanupSumStagePosition (cleanupTargetIndex j)) x
  · simpa [h] using
      cleanupSumStagePrefixStep_get_workCarry_before_of_lt layout
      (cleanupTargetIndex j) (previousWorkIndex j h)
      (by simp [cleanupTargetIndex, previousWorkIndex])
      x

/-- After the cleanup-aware prefix ending at target `i`, right bit `i` stores
the local xor-sum of its original right bit, left bit, and selected carry bit. -/
theorem cleanupSumStagePrefixStep_get_right_current
    (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition i + 1) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x) := by
  have hposLt := cleanupSumStagePosition_lt_length (n := n) i
  have hget :
      ((cleanupSumStageIndices (n := n))[cleanupSumStagePosition i]'hposLt) =
        i :=
    cleanupSumStageIndices_get_position (n := n) i hposLt
  have htake :
      (cleanupSumStageIndices (n := n)).take
          (cleanupSumStagePosition i + 1) =
        (cleanupSumStageIndices (n := n)).take
          (cleanupSumStagePosition i) ++ [i] := by
    rw [← List.take_concat_get'
      (cleanupSumStageIndices (n := n)) (cleanupSumStagePosition i) hposLt]
    rw [hget]
  have hlocal :=
    cleanupSumGatesAt_get_right layout i
      (cleanupSumStagePrefixStep layout (cleanupSumStagePosition i) x)
  rw [cleanupSumStagePrefixStep_get_right_before,
    cleanupSumStagePrefixStep_get_left,
    cleanupSumStagePrefixStep_get_carryBeforeSum_before] at hlocal
  change
    (layout.right.bit i).get
        (((cleanupSumStageIndices (n := n)).take
            (cleanupSumStagePosition i + 1)).foldl
          (fun y i => EncodedBit.GateSpec.stepList
            (cleanupSumGatesAt layout i) y) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x)
  rw [htake, List.foldl_append]
  change
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i)
          (cleanupSumStagePrefixStep layout
            (cleanupSumStagePosition i) x)) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x)
  simpa [List.foldl] using hlocal

/-- The cleanup-aware suffix after target `i` does not modify right bit `i`. -/
theorem cleanupSumStageIndexStep_get_right_from_prefix
    (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (cleanupSumStageIndexStep layout x) =
      (layout.right.bit i).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition i + 1) x) := by
  unfold cleanupSumStageIndexStep cleanupSumStagePrefixStep
  nth_rw 1 [← List.take_append_drop (cleanupSumStagePosition i + 1)
    (cleanupSumStageIndices (n := n))]
  rw [List.foldl_append]
  exact foldl_cleanupSumGatesAt_get_right_of_forall_ne layout
    ((cleanupSumStageIndices (n := n)).drop
      (cleanupSumStagePosition i + 1)) i
    (by
      intro j hmem hji
      have hjlt :
          j.val < i.val :=
        cleanupSumStageIndices_mem_drop_succ_position_val_lt
          (n := n) hmem
      have hval := congrArg Fin.val hji
      omega)
    (((cleanupSumStageIndices (n := n)).take
      (cleanupSumStagePosition i + 1)).foldl
        (fun y i => EncodedBit.GateSpec.stepList
          (cleanupSumGatesAt layout i) y) x)

/-- Closed-form readout of each target bit after the complete cleanup-aware
sum stage. -/
theorem cleanupSumStageIndexStep_get_right
    (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get (cleanupSumStageIndexStep layout x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x) := by
  rw [cleanupSumStageIndexStep_get_right_from_prefix]
  exact cleanupSumStagePrefixStep_get_right_current layout i x

/-- If the prefix before `cleanupTargetIndex j` still presents work carry `j`
as the computed local full-adder carry, the prefix including that target clears
work carry `j`. -/
theorem cleanupSumStagePrefixStep_get_workCarry_cleanupTarget_computed
    (j : Fin (n - 1)) (x : Carrier)
    (hcomputed :
      (layout.workCarry.bit j).get
          (cleanupSumStagePrefixStep layout
            (cleanupSumStagePosition (cleanupTargetIndex j)) x) =
        Bool.carry
          ((layout.left.bit (lowIndex j)).get
            (cleanupSumStagePrefixStep layout
              (cleanupSumStagePosition (cleanupTargetIndex j)) x))
          ((layout.right.bit (lowIndex j)).get
            (cleanupSumStagePrefixStep layout
              (cleanupSumStagePosition (cleanupTargetIndex j)) x))
          ((carryInput layout j).get
            (cleanupSumStagePrefixStep layout
              (cleanupSumStagePosition (cleanupTargetIndex j)) x))) :
    (layout.workCarry.bit j).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition (cleanupTargetIndex j) + 1) x) =
      false := by
  let i := cleanupTargetIndex j
  have hnz : i.val ≠ 0 := by
    simp [i, cleanupTargetIndex]
  have hidx : cleanupWorkIndex i hnz = j := by
    simpa [i] using cleanupWorkIndex_cleanupTargetIndex (n := n) j
  have hposLt := cleanupSumStagePosition_lt_length (n := n) i
  have hget :
      ((cleanupSumStageIndices (n := n))[cleanupSumStagePosition i]'hposLt) =
        i :=
    cleanupSumStageIndices_get_position (n := n) i hposLt
  have htake :
      (cleanupSumStageIndices (n := n)).take
          (cleanupSumStagePosition i + 1) =
        (cleanupSumStageIndices (n := n)).take
          (cleanupSumStagePosition i) ++ [i] := by
    rw [← List.take_concat_get'
      (cleanupSumStageIndices (n := n)) (cleanupSumStagePosition i) hposLt]
    rw [hget]
  have hlocal :=
    cleanupSumGatesAt_get_cleanupWorkCarry_computed layout i hnz
      (cleanupSumStagePrefixStep layout (cleanupSumStagePosition i) x)
      (by
        simpa [i, hidx] using hcomputed)
  change
    (layout.workCarry.bit j).get
        (((cleanupSumStageIndices (n := n)).take
            (cleanupSumStagePosition i + 1)).foldl
          (fun y i => EncodedBit.GateSpec.stepList
            (cleanupSumGatesAt layout i) y) x) =
      false
  rw [htake, List.foldl_append]
  change
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i)
          (cleanupSumStagePrefixStep layout
            (cleanupSumStagePosition i) x)) =
      false
  simpa [List.foldl, hidx] using hlocal

/-- If work carry `j` is computed at the start of the cleanup-aware sum pass,
then the prefix including its cleanup target clears it. -/
theorem cleanupSumStagePrefixStep_get_workCarry_cleanupTarget_of_computed
    (j : Fin (n - 1)) (x : Carrier)
    (hcomputed :
      (layout.workCarry.bit j).get x =
        Bool.carry
          ((layout.left.bit (lowIndex j)).get x)
          ((layout.right.bit (lowIndex j)).get x)
          ((carryInput layout j).get x)) :
    (layout.workCarry.bit j).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition (cleanupTargetIndex j) + 1) x) =
      false := by
  apply cleanupSumStagePrefixStep_get_workCarry_cleanupTarget_computed
  rw [cleanupSumStagePrefixStep_get_workCarry_before_cleanupTarget,
    cleanupSumStagePrefixStep_get_left,
    cleanupSumStagePrefixStep_get_right_lowIndex_before_cleanupTarget,
    cleanupSumStagePrefixStep_get_carryInput_before_cleanupTarget]
  exact hcomputed

/-- After the cleanup target for work carry `j`, the remaining lower target
stages do not modify work carry `j`. -/
theorem cleanupSumStageIndexStep_get_workCarry_from_cleanupTarget
    (j : Fin (n - 1)) (x : Carrier) :
    (layout.workCarry.bit j).get (cleanupSumStageIndexStep layout x) =
      (layout.workCarry.bit j).get
        (cleanupSumStagePrefixStep layout
          (cleanupSumStagePosition (cleanupTargetIndex j) + 1) x) := by
  let i := cleanupTargetIndex j
  unfold cleanupSumStageIndexStep cleanupSumStagePrefixStep
  nth_rw 1 [← List.take_append_drop (cleanupSumStagePosition i + 1)
    (cleanupSumStageIndices (n := n))]
  rw [List.foldl_append]
  exact foldl_cleanupSumGatesAt_get_workCarry_of_forall_ne layout
    ((cleanupSumStageIndices (n := n)).drop
      (cleanupSumStagePosition i + 1)) j
    (by
      intro k hmem hk hEq
      have hklt :
          k.val < i.val :=
        cleanupSumStageIndices_mem_drop_succ_position_val_lt
          (n := n) hmem
      have hv := congrArg Fin.val hEq
      simp [cleanupWorkIndex] at hv
      have hi : i.val = j.val + 1 := by
        simp [i, cleanupTargetIndex]
      omega)
    (((cleanupSumStageIndices (n := n)).take
      (cleanupSumStagePosition i + 1)).foldl
        (fun y i => EncodedBit.GateSpec.stepList
          (cleanupSumGatesAt layout i) y) x)

/-- The complete cleanup-aware sum stage clears work carry `j` when that work
carry is a computed local full-adder carry at the start of the cleanup pass. -/
theorem cleanupSumStageIndexStep_get_workCarry_clean_of_computed
    (j : Fin (n - 1)) (x : Carrier)
    (hcomputed :
      (layout.workCarry.bit j).get x =
        Bool.carry
          ((layout.left.bit (lowIndex j)).get x)
          ((layout.right.bit (lowIndex j)).get x)
          ((carryInput layout j).get x)) :
    (layout.workCarry.bit j).get (cleanupSumStageIndexStep layout x) =
      false := by
  rw [cleanupSumStageIndexStep_get_workCarry_from_cleanupTarget]
  exact cleanupSumStagePrefixStep_get_workCarry_cleanupTarget_of_computed
    layout j x hcomputed

/-- Folded semantic action of the cleanup-aware sum stage as a fold over its
local stages. -/
theorem cleanupSumStage_stepList_eq_fold (x : Carrier) :
    EncodedBit.GateSpec.stepList (cleanupSumStage layout) x =
      (cleanupSumStageStages layout).foldl
        (fun y gates => EncodedBit.GateSpec.stepList gates y) x := by
  exact stepList_concatStages (cleanupSumStageStages layout) x

/-- Folded semantic action of the cleanup-aware sum stage as a fold over the
stage indices. -/
theorem cleanupSumStage_stepList_eq_indexStep (x : Carrier) :
    EncodedBit.GateSpec.stepList (cleanupSumStage layout) x =
      cleanupSumStageIndexStep layout x := by
  rw [cleanupSumStage_stepList_eq_fold]
  unfold cleanupSumStageStages cleanupSumStageIndexStep
  generalize cleanupSumStageIndices = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) x)

/-- The complete cleanup-aware sum stage preserves every left readout. -/
theorem cleanupSumStageIndexStep_get_left
    (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get (cleanupSumStageIndexStep layout x) =
      (layout.left.bit i).get x := by
  unfold cleanupSumStageIndexStep cleanupSumStageIndices sumStageIndices
  generalize (List.ofFn fun i : Fin n => i).reverse = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.left.bit i).get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList
                (cleanupSumGatesAt layout j) x)) =
          (layout.left.bit i).get x
      rw [ih]
      exact cleanupSumGatesAt_get_left_any layout j i x

/-- The complete cleanup-aware sum stage preserves the data carry-in readout. -/
theorem cleanupSumStageIndexStep_get_dataCarry
    (x : Carrier) :
    layout.carryIn.get (cleanupSumStageIndexStep layout x) =
      layout.carryIn.get x := by
  unfold cleanupSumStageIndexStep cleanupSumStageIndices sumStageIndices
  generalize (List.ofFn fun i : Fin n => i).reverse = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        layout.carryIn.get
            (rest.foldl
              (fun y i =>
                EncodedBit.GateSpec.stepList (cleanupSumGatesAt layout i) y)
              (EncodedBit.GateSpec.stepList
                (cleanupSumGatesAt layout i) x)) =
          layout.carryIn.get x
      rw [ih]
      exact cleanupSumGatesAt_get_dataCarry layout i x

/-- The complete cleanup-aware sum stage preserves an observed readout whose
wire is distinct from every right/target wire and every work-carry target. -/
theorem cleanupSumStageIndexStep_get_observed_of_right_work_ne
    (observed : EncodedBit encoding)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get (cleanupSumStageIndexStep layout x) = observed.get x := by
  unfold cleanupSumStageIndexStep cleanupSumStageIndices sumStageIndices
  exact foldl_cleanupSumGatesAt_get_observed_of_right_work_ne layout
    (List.ofFn fun i : Fin n => i).reverse observed
    (by intro i _; exact hright i) hwork x

/-- The complete cleanup-aware sum gate list preserves every left readout. -/
theorem cleanupSumStage_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList (cleanupSumStage layout) x) =
      (layout.left.bit i).get x := by
  rw [cleanupSumStage_stepList_eq_indexStep]
  exact cleanupSumStageIndexStep_get_left layout i x

/-- The complete cleanup-aware sum gate list preserves the data carry-in
readout. -/
theorem cleanupSumStage_get_dataCarry (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (cleanupSumStage layout) x) =
      layout.carryIn.get x := by
  rw [cleanupSumStage_stepList_eq_indexStep]
  exact cleanupSumStageIndexStep_get_dataCarry layout x

/-- The complete cleanup-aware sum gate list preserves an observed readout
whose wire is distinct from every right/target wire and every work-carry
target. -/
theorem cleanupSumStage_get_observed_of_right_work_ne
    (observed : EncodedBit encoding)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get (EncodedBit.GateSpec.stepList (cleanupSumStage layout) x) =
      observed.get x := by
  rw [cleanupSumStage_stepList_eq_indexStep]
  exact cleanupSumStageIndexStep_get_observed_of_right_work_ne layout
    observed hright hwork x

/-- Closed-form readout of each target bit after the complete cleanup-aware
sum gate list. -/
theorem cleanupSumStage_get_right (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (cleanupSumStage layout) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get x) := by
  rw [cleanupSumStage_stepList_eq_indexStep]
  exact cleanupSumStageIndexStep_get_right layout i x

/-- Cleanup-aware carry/sum gate list for the carry-work layout.  The endpoint
proof is separate; this definition only fixes the concrete gate object whose
resources and semantics will be connected by later invariants [VBE95,
9511018.tex:237-264,596-618]. -/
def cleanCarrySumGates : List (EncodedBit.GateSpec encoding) :=
  carryStage layout ++ cleanupSumStage layout

/-- A carry input is disjoint from an observed bit when both the data carry and
all temporary carry-work bits are disjoint from it. -/
theorem carryInput_wire_ne_of_observed
    (observed : EncodedBit encoding)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (j : Fin (n - 1)) :
    (carryInput layout j).wire ≠ observed.wire := by
  unfold carryInput
  by_cases h : j.val = 0
  · simpa [h] using hcarryIn
  · simpa [h] using hwork (previousWorkIndex j h)

/-- A carry-before-sum bit is disjoint from an observed bit when both the data
carry and all temporary carry-work bits are disjoint from it. -/
theorem carryBeforeSum_wire_ne_of_observed
    (observed : EncodedBit encoding)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (i : Fin n) :
    (carryBeforeSum layout i).wire ≠ observed.wire := by
  unfold carryBeforeSum
  by_cases h : i.val = 0
  · simpa [h] using hcarryIn
  · simpa [h] using hwork ⟨i.val - 1, by
      have hi := i.isLt
      omega⟩

/-- One local carry-work stage is disjoint from an observed bit when every
layout wire it may read or write is disjoint from that observed bit. -/
theorem carryOutGatesAt_bitDisjoint
    (j : Fin (n - 1)) (observed : EncodedBit encoding)
    (hleft : ∀ i : Fin n, (layout.left.bit i).wire ≠ observed.wire)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ k : Fin (n - 1),
      (layout.workCarry.bit k).wire ≠ observed.wire) :
    ∀ gate, gate ∈ carryOutGatesAt layout j ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  simpa [carryOutGatesAt] using
    BitSlice.Encoded.carryOutGates_bitDisjoint
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) observed
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j)
      (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j)
      (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j)
      (hleft (lowIndex j)) (hright (lowIndex j))
      (carryInput_wire_ne_of_observed layout observed hcarryIn hwork j)
      (hwork j)

/-- One local reverse carry-cleanup stage is disjoint from an observed bit when
every layout wire it may read or write is disjoint from that observed bit. -/
theorem carryOutCleanupGatesAt_bitDisjoint
    (j : Fin (n - 1)) (observed : EncodedBit encoding)
    (hleft : ∀ i : Fin n, (layout.left.bit i).wire ≠ observed.wire)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ k : Fin (n - 1),
      (layout.workCarry.bit k).wire ≠ observed.wire) :
    ∀ gate, gate ∈ carryOutCleanupGatesAt layout j ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  simpa [carryOutCleanupGatesAt] using
    BitSlice.Encoded.carryOutCleanupGates_bitDisjoint
      (layout.left.bit (lowIndex j)) (layout.right.bit (lowIndex j))
      (carryInput layout j) (layout.workCarry.bit j) observed
      (layout.leftRight_ne (lowIndex j) (lowIndex j))
      (left_carryInput_ne layout j)
      (layout.leftWork_ne (lowIndex j) j)
      (right_carryInput_ne layout j)
      (layout.rightWork_ne (lowIndex j) j)
      (carryInput_work_ne layout j)
      (hleft (lowIndex j)) (hright (lowIndex j))
      (carryInput_wire_ne_of_observed layout observed hcarryIn hwork j)
      (hwork j)

/-- One local sum stage is disjoint from an observed bit when every layout wire
it may read or write is disjoint from that observed bit. -/
theorem sumGatesAt_bitDisjoint
    (i : Fin n) (observed : EncodedBit encoding)
    (hleft : ∀ k : Fin n, (layout.left.bit k).wire ≠ observed.wire)
    (hright : ∀ k : Fin n, (layout.right.bit k).wire ≠ observed.wire)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ k : Fin (n - 1),
      (layout.workCarry.bit k).wire ≠ observed.wire) :
    ∀ gate, gate ∈ sumGatesAt layout i ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  simpa [sumGatesAt] using
    BitSlice.Encoded.sumGates_bitDisjoint
      (layout.left.bit i) (carryBeforeSum layout i) (layout.right.bit i)
      observed (layout.leftRight_ne i i) (carryBeforeSum_right_ne layout i)
      (hleft i)
      (carryBeforeSum_wire_ne_of_observed layout observed hcarryIn hwork i)
      (hright i)

/-- One cleanup-aware local sum stage is disjoint from an observed bit when
every layout wire it may read or write is disjoint from that observed bit. -/
theorem cleanupSumGatesAt_bitDisjoint
    (i : Fin n) (observed : EncodedBit encoding)
    (hleft : ∀ k : Fin n, (layout.left.bit k).wire ≠ observed.wire)
    (hright : ∀ k : Fin n, (layout.right.bit k).wire ≠ observed.wire)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ k : Fin (n - 1),
      (layout.workCarry.bit k).wire ≠ observed.wire) :
    ∀ gate, gate ∈ cleanupSumGatesAt layout i ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  unfold cleanupSumGatesAt at hmem
  by_cases h : i.val = 0
  · exact sumGatesAt_bitDisjoint layout i observed hleft hright hcarryIn
      hwork gate (by simpa [h] using hmem)
  · simp only [h, ↓reduceDIte, List.mem_append] at hmem
    rcases hmem with hsum | hcleanup
    · exact sumGatesAt_bitDisjoint layout i observed hleft hright hcarryIn
        hwork gate hsum
    · exact carryOutCleanupGatesAt_bitDisjoint layout (cleanupWorkIndex i h)
        observed hleft hright hcarryIn hwork gate hcleanup

/-- The forward carry stage is disjoint from an observed bit when every layout
wire it may read or write is disjoint from that observed bit. -/
theorem carryStage_bitDisjoint
    (observed : EncodedBit encoding)
    (hleft : ∀ i : Fin n, (layout.left.bit i).wire ≠ observed.wire)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire) :
    ∀ gate, gate ∈ carryStage layout ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  rw [carryStage, mem_concatStages] at hmem
  rcases hmem with ⟨stage, hstage, hgate⟩
  simp only [carryStageStages, List.mem_map] at hstage
  rcases hstage with ⟨j, _hj, rfl⟩
  exact carryOutGatesAt_bitDisjoint layout j observed hleft hright
    hcarryIn hwork gate hgate

/-- The cleanup-aware sum stage is disjoint from an observed bit when every
layout wire it may read or write is disjoint from that observed bit. -/
theorem cleanupSumStage_bitDisjoint
    (observed : EncodedBit encoding)
    (hleft : ∀ i : Fin n, (layout.left.bit i).wire ≠ observed.wire)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire) :
    ∀ gate, gate ∈ cleanupSumStage layout ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  rw [cleanupSumStage, mem_concatStages] at hmem
  rcases hmem with ⟨stage, hstage, hgate⟩
  simp only [cleanupSumStageStages, List.mem_map] at hstage
  rcases hstage with ⟨i, _hi, rfl⟩
  exact cleanupSumGatesAt_bitDisjoint layout i observed hleft hright
    hcarryIn hwork gate hgate

/-- The cleanup-aware carry/sum gate list is disjoint from an observed bit when
every layout wire it may read or write is disjoint from that observed bit. -/
theorem cleanCarrySumGates_bitDisjoint
    (observed : EncodedBit encoding)
    (hleft : ∀ i : Fin n, (layout.left.bit i).wire ≠ observed.wire)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hcarryIn : layout.carryIn.wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire) :
    ∀ gate, gate ∈ cleanCarrySumGates layout ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  simp only [cleanCarrySumGates, List.mem_append] at hmem
  rcases hmem with hcarry | hsum
  · exact carryStage_bitDisjoint layout observed hleft hright hcarryIn hwork
      gate hcarry
  · exact cleanupSumStage_bitDisjoint layout observed hleft hright hcarryIn
      hwork gate hsum

/-- Base-gate program for the cleanup-aware carry/sum schedule object. -/
def cleanCarrySumProgram : BaseGateProgram encoding.width :=
  EncodedBit.GateSpec.programList (cleanCarrySumGates layout)

/-- Folded semantic action of the cleanup-aware carry/sum schedule object. -/
def cleanCarrySumStep : Carrier -> Carrier :=
  EncodedBit.GateSpec.stepList (cleanCarrySumGates layout)

/-- Folded semantic action of the cleanup-aware carry/sum schedule, exposed as
the forward carry fold followed by the cleanup-aware sum fold. -/
theorem cleanCarrySum_stepList_eq_indexStep (x : Carrier) :
    EncodedBit.GateSpec.stepList (cleanCarrySumGates layout) x =
      cleanupSumStageIndexStep layout (carryStageIndexStep layout x) := by
  rw [cleanCarrySumGates, EncodedBit.GateSpec.stepList_append]
  rw [carryStage_stepList_eq_indexStep, cleanupSumStage_stepList_eq_indexStep]

/-- The folded cleanup-aware carry/sum gate list preserves every left readout. -/
theorem cleanCarrySumGates_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList (cleanCarrySumGates layout) x) =
      (layout.left.bit i).get x := by
  rw [cleanCarrySumGates, EncodedBit.GateSpec.stepList_append]
  rw [cleanupSumStage_get_left, carryStage_get_left]

/-- The folded cleanup-aware carry/sum gate list preserves the data carry-in
readout. -/
theorem cleanCarrySumGates_get_dataCarry (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (cleanCarrySumGates layout) x) =
      layout.carryIn.get x := by
  rw [cleanCarrySumGates, EncodedBit.GateSpec.stepList_append]
  rw [cleanupSumStage_get_dataCarry, carryStage_get_dataCarry]

/-- The complete cleanup-aware carry/sum gate list preserves an observed
readout whose wire is distinct from every right/target wire and every
temporary carry-work target.  This is useful when the VBE adder is embedded
beside untouched auxiliary fields [VBE95, 9511018.tex:237-264,591-618]. -/
theorem cleanCarrySumGates_get_observed_of_right_work_ne
    (observed : EncodedBit encoding)
    (hright : ∀ i : Fin n, (layout.right.bit i).wire ≠ observed.wire)
    (hwork : ∀ j : Fin (n - 1),
      (layout.workCarry.bit j).wire ≠ observed.wire)
    (x : Carrier) :
    observed.get
        (EncodedBit.GateSpec.stepList (cleanCarrySumGates layout) x) =
      observed.get x := by
  rw [cleanCarrySumGates, EncodedBit.GateSpec.stepList_append]
  rw [cleanupSumStage_get_observed_of_right_work_ne layout observed
    hright hwork]
  exact carryStage_get_observed_of_work_ne layout observed hwork x

/-- The folded cleanup-aware carry/sum gate list writes each target bit as the
original target bit xored with the preserved left bit and the carry selected
after the forward carry pass. -/
theorem cleanCarrySumGates_get_right (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (cleanCarrySumGates layout) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get
          (EncodedBit.GateSpec.stepList (carryStage layout) x)) := by
  rw [cleanCarrySumGates, EncodedBit.GateSpec.stepList_append]
  rw [cleanupSumStage_get_right]
  rw [carryStage_get_right, carryStage_get_left]

/-- The folded cleanup-aware carry/sum gate list restores every temporary
carry-work readout to false, provided the input work register is clean. -/
theorem cleanCarrySumGates_get_workCarry_clean
    (j : Fin (n - 1)) (x : Carrier)
    (hclean : ∀ k : Fin (n - 1), (layout.workCarry.bit k).get x = false) :
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList (cleanCarrySumGates layout) x) =
      false := by
  rw [cleanCarrySumGates, EncodedBit.GateSpec.stepList_append]
  rw [cleanupSumStage_stepList_eq_indexStep]
  rw [carryStage_stepList_eq_indexStep]
  apply cleanupSumStageIndexStep_get_workCarry_clean_of_computed
  rw [carryStageIndexStep_get_left, carryStageIndexStep_get_right]
  exact carryStageIndexStep_get_workCarry_recurrence layout j x hclean

/-- The inverse gate list of the cleanup-aware carry/sum schedule also preserves
clean temporary carry-work.  Since the forward schedule is a finite permutation
that maps the clean-work subset into itself, its inverse maps that subset into
itself as well. -/
theorem cleanCarrySumGates_reverse_get_workCarry_clean
    (j : Fin (n - 1)) (x : Carrier)
    (hclean : ∀ k : Fin (n - 1), (layout.workCarry.bit k).get x = false) :
    (layout.workCarry.bit j).get
        (EncodedBit.GateSpec.stepList (cleanCarrySumGates layout).reverse x) =
      false := by
  let gates := cleanCarrySumGates layout
  let perm : Equiv.Perm Carrier := {
    toFun := EncodedBit.GateSpec.stepList gates
    invFun := EncodedBit.GateSpec.stepList gates.reverse
    left_inv := by
      intro y
      exact EncodedBit.GateSpec.stepList_reverse_stepList gates y
    right_inv := by
      intro y
      have h := EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse y
      simpa [gates] using h
  }
  let cleanSet : Set Carrier :=
    {y | ∀ k : Fin (n - 1), (layout.workCarry.bit k).get y = false}
  haveI : Finite Carrier :=
    Finite.of_injective encoding.encode encoding.encode_injective
  have hmap : Set.MapsTo perm cleanSet cleanSet := by
    intro y hy k
    exact cleanCarrySumGates_get_workCarry_clean layout k y hy
  have hsymm := Equiv.Perm.perm_symm_mapsTo_of_mapsTo perm hmap
  have hcleanReverse : perm.symm x ∈ cleanSet := hsymm hclean
  exact hcleanReverse j

/-- The cleanup-aware carry/sum schedule realizes its folded bit-lens action
with the same base-gate program object used for resources. -/
theorem cleanCarrySum_realizes :
    BaseGateProgram.Realizes encoding
      (cleanCarrySumProgram layout) (cleanCarrySumStep layout) :=
  EncodedBit.GateSpec.realizesList (cleanCarrySumGates layout)

/-- Same-Circuit witness for the cleanup-aware carry/sum schedule object. -/
def cleanCarrySumSameCircuit :
    BaseGateSameCircuitWitness Carrier (cleanCarrySumStep layout) where
  encoding := encoding
  program := cleanCarrySumProgram layout
  realizes := cleanCarrySum_realizes layout

/-- Folded carry/sum gate list for the carry-work layout.  This leaves the
temporary carry-work register dirty; a correct reverse-cleanup schedule cannot
be obtained by simply reversing the carry gates after the target bits have been
changed by `sumStage`.  The clean-work word-level invariant remains separate
[VBE95, 9511018.tex:244-264,596-603]. -/
def carryAndSumGates : List (EncodedBit.GateSpec encoding) :=
  carryStage layout ++ sumStage layout

/-- The folded dirty-work carry/sum gate list preserves every left readout. -/
theorem carryAndSumGates_get_left (i : Fin n) (x : Carrier) :
    (layout.left.bit i).get
        (EncodedBit.GateSpec.stepList (carryAndSumGates layout) x) =
      (layout.left.bit i).get x := by
  rw [carryAndSumGates, EncodedBit.GateSpec.stepList_append]
  rw [sumStage_get_left, carryStage_get_left]

/-- The folded dirty-work carry/sum gate list preserves the data carry-in
readout. -/
theorem carryAndSumGates_get_dataCarry (x : Carrier) :
    layout.carryIn.get
        (EncodedBit.GateSpec.stepList (carryAndSumGates layout) x) =
      layout.carryIn.get x := by
  rw [carryAndSumGates, EncodedBit.GateSpec.stepList_append]
  rw [sumStage_get_dataCarry, carryStage_get_dataCarry]

/-- The folded dirty-work carry/sum gate list writes each target bit as the
original target bit xored with the preserved left bit and the carry selected
after the forward carry pass. -/
theorem carryAndSumGates_get_right (i : Fin n) (x : Carrier) :
    (layout.right.bit i).get
        (EncodedBit.GateSpec.stepList (carryAndSumGates layout) x) =
      (((layout.right.bit i).get x ^^ (layout.left.bit i).get x) ^^
        (carryBeforeSum layout i).get
          (EncodedBit.GateSpec.stepList (carryStage layout) x)) := by
  rw [carryAndSumGates, EncodedBit.GateSpec.stepList_append]
  rw [sumStage_stepList_eq_indexStep]
  rw [sumStageIndexStep_get_right]
  rw [carryStage_get_right, carryStage_get_left]

/-- Base-gate program for the folded dirty-work carry/sum schedule object. -/
def program : BaseGateProgram encoding.width :=
  EncodedBit.GateSpec.programList (carryAndSumGates layout)

/-- Folded semantic action of the dirty-work carry/sum schedule object. -/
def step : Carrier -> Carrier :=
  EncodedBit.GateSpec.stepList (carryAndSumGates layout)

/-- The dirty-work carry/sum schedule realizes its folded bit-lens action with
the same base-gate program object used for resources. -/
theorem realizes :
    BaseGateProgram.Realizes encoding (program layout) (step layout) :=
  EncodedBit.GateSpec.realizesList (carryAndSumGates layout)

/-- Same-Circuit witness for the dirty-work carry/sum schedule object. -/
def sameCircuit : BaseGateSameCircuitWitness Carrier (step layout) where
  encoding := encoding
  program := program layout
  realizes := realizes layout

end CarryWorkLayout

namespace PowerOfTwo

/-- Canonical power-of-two residue encoding used by plain-adder word fields. -/
@[nolint defLemma]
def residueEncoding (n : Nat) : BinaryResidueEncoding (2 ^ n) n where
  modulus_pos := by
    exact pow_pos (by decide : (0 : Nat) < 2) n
  register_fits := le_rfl

/-- The canonical `ZMod (2^n)` word label as an `n`-bit basis label. -/
def wordLabelEquiv (n : Nat) : Word n ≃ Fin (2 ^ n) where
  toFun := (residueEncoding n).encode
  invFun := (residueEncoding n).decode
  left_inv := by
    intro z
    exact (residueEncoding n).decode_encode z
  right_inv := by
    intro x
    exact (residueEncoding n).encode_decode_of_valid x x.isLt

/-- Canonical binary label encoding for one plain-adder word. -/
def wordEncoding (n : Nat) : BinaryLabelEncoding (Word n) :=
  BinaryLabelEncoding.ofEquiv (wordLabelEquiv n)

/-- Bit lens for one canonical power-of-two word bit. -/
def wordBit (n : Nat) (bit : Fin n) : EncodedBit (wordEncoding n) :=
  BinaryLabelEncoding.ofEquivBit (wordLabelEquiv n)
    (WireAddress.littleEndianWire bit)

@[simp] theorem wordBit_get (n : Nat) (bit : Fin n) (x : Word n) :
    (wordBit n bit).get x =
      x.val.testBit bit.val := by
  change
    (wordLabelEquiv n x).val.testBit
        (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val =
      x.val.testBit bit.val
  rw [WireAddress.bitIndex_littleEndianWire]
  rfl

/-- Boolean carry sequence for natural-number addition, ordered from least
significant to most significant bit.  This is the pure arithmetic recurrence
mirrored by the VBE carry-work stage [VBE95, 9511018.tex:248-253,591-618]. -/
def natAddCarry (a b : Nat) : Nat -> Bool
  | 0 => false
  | i + 1 => Bool.carry (a.testBit i) (b.testBit i) (natAddCarry a b i)

theorem bool_carry_comm (a b c : Bool) :
    Bool.carry a b c = Bool.carry b a c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem natAddCarry_comm (a b i : Nat) :
    natAddCarry a b i = natAddCarry b a i := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      simp [natAddCarry, ih, bool_carry_comm]

/-- One-step numeric identity for adding two `Nat.bit` decompositions plus an
incoming carry bit. -/
theorem bit_add_bit (a b c : Bool) (ah bh : Nat) :
    Nat.bit a ah + Nat.bit b bh + c.toNat =
      Nat.bit ((a ^^ b) ^^ c) (ah + bh + (Bool.carry a b c).toNat) := by
  cases a <;> cases b <;> cases c <;>
    simp [Nat.bit, Bool.carry] <;> omega

/-- Shifting away the first `i` bits of `a + b` leaves the shifted addends plus
the carry propagated through the low `i` bits. -/
theorem shifted_add_decomp (a b i : Nat) :
    (a + b) >>> i = (a >>> i) + (b >>> i) + (natAddCarry a b i).toNat := by
  induction i with
  | zero =>
      simp [natAddCarry]
  | succ i ih =>
      rw [show i + 1 = i + 1 by rfl]
      rw [Nat.shiftRight_add]
      rw [ih]
      have hbit := bit_add_bit ((a >>> i).testBit 0) ((b >>> i).testBit 0)
        (natAddCarry a b i) ((a >>> i) >>> 1) ((b >>> i) >>> 1)
      have ha :
          Nat.bit ((a >>> i).testBit 0) ((a >>> i) >>> 1) = a >>> i :=
        Nat.bit_testBit_zero_shiftRight_one (a >>> i)
      have hb :
          Nat.bit ((b >>> i).testBit 0) ((b >>> i) >>> 1) = b >>> i :=
        Nat.bit_testBit_zero_shiftRight_one (b >>> i)
      rw [ha, hb] at hbit
      rw [hbit]
      rw [Nat.bit_shiftRight_one]
      simp [natAddCarry, Nat.shiftRight_add, Nat.add_assoc]

/-- Low-bit addition formula with an explicit incoming carry bit. -/
theorem testBit_zero_add_with_carry (a b : Nat) (c : Bool) :
    (a + b + c.toNat).testBit 0 = ((a.testBit 0 ^^ b.testBit 0) ^^ c) := by
  have ha : Nat.bit (a.testBit 0) (a >>> 1) = a :=
    Nat.bit_testBit_zero_shiftRight_one a
  have hb : Nat.bit (b.testBit 0) (b >>> 1) = b :=
    Nat.bit_testBit_zero_shiftRight_one b
  rw [ha.symm, hb.symm]
  rw [bit_add_bit (a.testBit 0) (b.testBit 0) c (a >>> 1) (b >>> 1)]
  cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0 <;> cases c <;>
    simp

/-- Each bit of `a + b` is the xor of the two input bits and the propagated
incoming carry at that bit. -/
theorem testBit_add_eq_xor3 (a b i : Nat) :
    (a + b).testBit i = ((a.testBit i ^^ b.testBit i) ^^ natAddCarry a b i) := by
  rw [show (a + b).testBit i = ((a + b) >>> i).testBit 0 by
    rw [Nat.testBit_shiftRight]
    rfl]
  rw [shifted_add_decomp a b i]
  rw [testBit_zero_add_with_carry]
  simp

/-- Two power-of-two words are equal when all in-range value bits agree. -/
theorem word_eq_of_testBit_eq {n : Nat} {a b : Word n}
    (h : forall i : Fin n, a.val.testBit i.val = b.val.testBit i.val) :
    a = b := by
  have hval : a.val = b.val := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < n
    case pos =>
      exact h { val := k, isLt := hk }
    case neg =>
      have hnk : n <= k := Nat.le_of_not_gt hk
      have hpow : 2 ^ n <= 2 ^ k :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hnk
      have ha : a.val.testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (ZMod.val_lt a) hpow)
      have hb : b.val.testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (ZMod.val_lt b) hpow)
      rw [ha, hb]
  have haCast : ((a.val : Nat) : Word n) = a := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hbCast : ((b.val : Nat) : Word n) = b := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  calc
    a = ((a.val : Nat) : Word n) := haCast.symm
    _ = ((b.val : Nat) : Word n) := by rw [hval]
    _ = b := hbCast

/-- Low `n` bits of a `ZMod (2^n)` addition are the low `n` bits of the
corresponding natural-number addition. -/
theorem word_add_val_testBit (n : Nat) (a b : Word n) (i : Fin n) :
    (a + b).val.testBit i.val = (a.val + b.val).testBit i.val := by
  rw [ZMod.val_add]
  rw [Nat.testBit_mod_two_pow]
  simp [i.isLt]

/-- Power-of-two word addition has the same in-range bit formula as natural
addition.  The carry is stated in `left,right` order to match the VBE carry
stage even though the target endpoint is `right + left` [VBE95,
9511018.tex:591-618]. -/
theorem word_add_val_testBit_eq_xor3
    (n : Nat) (left right : Word n) (i : Fin n) :
    (right + left).val.testBit i.val =
      ((right.val.testBit i.val ^^ left.val.testBit i.val) ^^
        natAddCarry left.val right.val i.val) := by
  rw [word_add_val_testBit]
  rw [testBit_add_eq_xor3]
  rw [natAddCarry_comm right.val left.val i.val]

/-- Product-tuple view of plain-adder data. -/
def dataTupleEquiv (n : Nat) : Data n ≃ Word n × (Word n × Bool) where
  toFun := fun x => (x.left, (x.right, x.carry))
  invFun := fun x => { left := x.1, right := x.2.1, carry := x.2.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rcases x with ⟨left, rest⟩
    rcases rest with ⟨right, carry⟩
    rfl

/-- Canonical product encoding for `PlainAdder.Data n`. -/
def dataEncoding (n : Nat) : BinaryLabelEncoding (Data n) :=
  (BinaryLabelEncoding.prod (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)).relabel
      (dataTupleEquiv n)

@[simp] theorem dataEncoding_width (n : Nat) :
    (dataEncoding n).width = n + (n + 1) := by
  rfl

/-- Canonical clean carry-work register used by the full plain-adder route.
The VBE network allocates `n - 1` temporary carry qubits and restores them to
zero after the reverse cleanup stage [VBE95, 9511018.tex:237-240,254-257]. -/
abbrev CarryWork (n : Nat) : Type :=
  Fin (2 ^ (n - 1))

/-- Canonical binary encoding for the `n - 1` carry-work register. -/
def carryWorkEncoding (n : Nat) : BinaryLabelEncoding (CarryWork n) :=
  BinaryLabelEncoding.finIdentity (n - 1)

/-- Distinguished all-zero carry-work label. -/
def cleanCarryWork (n : Nat) : CarryWork n :=
  0

/-- Canonical product encoding for plain-adder data plus carry work. -/
def dataWithCarryWorkEncoding (n : Nat) :
    BinaryLabelEncoding (Prod (Data n) (CarryWork n)) :=
  BinaryLabelEncoding.prod (dataEncoding n) (carryWorkEncoding n)

/-- Left/source word bit lens in the canonical plain-adder data layout. -/
def leftBit (n : Nat) (bit : Fin n) : EncodedBit (dataEncoding n) :=
  (BinaryLabelEncoding.prodLeftBit (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)
    (wordBit n bit)).relabel (dataTupleEquiv n)

/-- Right/target word bit lens in the canonical plain-adder data layout. -/
def rightBit (n : Nat) (bit : Fin n) : EncodedBit (dataEncoding n) :=
  (BinaryLabelEncoding.prodRightBit (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit (wordEncoding n) BinaryLabelEncoding.bool
      (wordBit n bit))).relabel (dataTupleEquiv n)

/-- Carry-flag bit lens in the canonical plain-adder data layout. -/
def carryBit (n : Nat) : EncodedBit (dataEncoding n) :=
  (BinaryLabelEncoding.prodRightBit (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit)).relabel (dataTupleEquiv n)

@[simp] theorem leftBit_get (n : Nat) (wire : Fin n) (x : Data n) :
    (leftBit n wire).get x = (wordBit n wire).get x.left :=
  rfl

@[simp] theorem rightBit_get (n : Nat) (wire : Fin n) (x : Data n) :
    (rightBit n wire).get x = (wordBit n wire).get x.right :=
  rfl

@[simp] theorem carryBit_get (n : Nat) (x : Data n) :
    (carryBit n).get x = x.carry :=
  rfl

theorem leftBit_get_testBit
    (n : Nat) (bit : Fin n) (x : Data n) :
    (leftBit n bit).get x =
      x.left.val.testBit bit.val := by
  simp

theorem rightBit_get_testBit
    (n : Nat) (bit : Fin n) (x : Data n) :
    (rightBit n bit).get x =
      x.right.val.testBit bit.val := by
  simp

/-- Left/source bit lens lifted to the canonical data-plus-carry-work layout. -/
def withCarryWorkLeftBit (n : Nat) (bit : Fin n) :
    EncodedBit (dataWithCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (dataEncoding n) (carryWorkEncoding n)
    (leftBit n bit)

/-- Right/target bit lens lifted to the canonical data-plus-carry-work layout. -/
def withCarryWorkRightBit (n : Nat) (bit : Fin n) :
    EncodedBit (dataWithCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (dataEncoding n) (carryWorkEncoding n)
    (rightBit n bit)

/-- Data carry-flag lens lifted to the canonical data-plus-carry-work layout. -/
def withCarryWorkCarryBit (n : Nat) :
    EncodedBit (dataWithCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (dataEncoding n) (carryWorkEncoding n)
    (carryBit n)

/-- Carry-work bit lens in the canonical data-plus-carry-work layout. -/
def carryWorkBit (n : Nat) (bit : Fin (n - 1)) :
    EncodedBit (dataWithCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodRightBit (dataEncoding n) (carryWorkEncoding n)
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit)

@[simp] theorem withCarryWorkLeftBit_get (n : Nat) (bit : Fin n)
    (x : Data n) (work : CarryWork n) :
    (withCarryWorkLeftBit n bit).get (x, work) =
      (leftBit n bit).get x :=
  rfl

@[simp] theorem withCarryWorkLeftBit_get_fst (n : Nat) (bit : Fin n)
    (x : Data n × CarryWork n) :
    (withCarryWorkLeftBit n bit).get x =
      (leftBit n bit).get x.1 :=
  rfl

@[simp] theorem withCarryWorkRightBit_get (n : Nat) (bit : Fin n)
    (x : Data n) (work : CarryWork n) :
    (withCarryWorkRightBit n bit).get (x, work) =
      (rightBit n bit).get x :=
  rfl

@[simp] theorem withCarryWorkRightBit_get_fst (n : Nat) (bit : Fin n)
    (x : Data n × CarryWork n) :
    (withCarryWorkRightBit n bit).get x =
      (rightBit n bit).get x.1 :=
  rfl

theorem withCarryWorkCarryBit_get (n : Nat)
    (x : Data n) (work : CarryWork n) :
    (withCarryWorkCarryBit n).get (x, work) = x.carry := by
  rfl

@[simp] theorem withCarryWorkCarryBit_get_fst (n : Nat)
    (x : Data n × CarryWork n) :
    (withCarryWorkCarryBit n).get x = x.1.carry := by
  rfl

@[simp] theorem finIdentityBit_get_zero (width : Nat) (bit : Fin width) :
    (BinaryLabelEncoding.finIdentityBit width bit).get
        (0 : Fin (2 ^ width)) = false := by
  simp [BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit]

/-- A raw identity-encoded register is zero if every addressed bit reads
`false`. -/
theorem finIdentity_eq_zero_of_get_false {width : Nat} (x : Fin (2 ^ width))
    (h : ∀ bit : Fin width,
      (BinaryLabelEncoding.finIdentityBit width bit).get x = false) :
    x = 0 := by
  apply Fin.ext
  change x.val = 0
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < width
  · have hb := h (WireAddress.littleEndianWire ⟨k, hk⟩)
    simpa [BinaryLabelEncoding.finIdentityBit,
      BinaryLabelEncoding.ofEquivBit] using hb
  · have hkw : width <= k := Nat.le_of_not_gt hk
    have hpow : 2 ^ width <= 2 ^ k :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hkw
    have hx : x.val.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt hpow)
    simp [hx]

@[simp] theorem carryWorkBit_get_clean (n : Nat) (bit : Fin (n - 1))
    (x : Data n) :
    (carryWorkBit n bit).get (x, cleanCarryWork n) = false := by
  change
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get
      (cleanCarryWork n) = false
  simp [cleanCarryWork]

/-- Lifted left/source word in the canonical data-plus-carry-work layout. -/
def withCarryWorkLeftWord (n : Nat) :
    EncodedBit.Word (dataWithCarryWorkEncoding n) n where
  bit := withCarryWorkLeftBit n

/-- Lifted right/target word in the canonical data-plus-carry-work layout. -/
def withCarryWorkRightWord (n : Nat) :
    EncodedBit.Word (dataWithCarryWorkEncoding n) n where
  bit := withCarryWorkRightBit n

/-- Temporary carry-work word in the canonical data-plus-carry-work layout. -/
def carryWorkWord (n : Nat) :
    EncodedBit.Word (dataWithCarryWorkEncoding n) (n - 1) where
  bit := carryWorkBit n

@[simp] theorem leftBit_wire_val (n : Nat) (bit : Fin n) :
    ((leftBit n bit).wire).val = n - 1 - bit.val := by
  rfl

@[simp] theorem rightBit_wire_val (n : Nat) (bit : Fin n) :
    ((rightBit n bit).wire).val = n + (n - 1 - bit.val) := by
  rfl

@[simp] theorem carryBit_wire_val (n : Nat) :
    ((carryBit n).wire).val = n + n := by
  rfl

@[simp] theorem carryWorkEncoding_width (n : Nat) :
    (carryWorkEncoding n).width = n - 1 := by
  rfl

@[simp] theorem dataWithCarryWorkEncoding_width (n : Nat) :
    (dataWithCarryWorkEncoding n).width =
      (dataEncoding n).width + (n - 1) := by
  rfl

@[simp] theorem withCarryWorkLeftBit_wire_val (n : Nat) (bit : Fin n) :
    ((withCarryWorkLeftBit n bit).wire).val = n - 1 - bit.val := by
  rfl

@[simp] theorem withCarryWorkRightBit_wire_val (n : Nat) (bit : Fin n) :
    ((withCarryWorkRightBit n bit).wire).val = n + (n - 1 - bit.val) := by
  rfl

@[simp] theorem withCarryWorkCarryBit_wire_val (n : Nat) :
    ((withCarryWorkCarryBit n).wire).val = n + n := by
  rfl

@[simp] theorem carryWorkBit_wire_val (n : Nat) (bit : Fin (n - 1)) :
    ((carryWorkBit n bit).wire).val = (dataEncoding n).width + bit.val := by
  rfl

/-- Concrete single-carry bit layout for the canonical `PlainAdder.Data n`
encoding.  This is a layout witness only; it does not state the folded schedule
equals `PlainAdder.Data.addIntoRight`. -/
def singleCarryLayout (n : Nat) :
    SingleCarryLayout (encoding := dataEncoding n) n where
  left := { bit := leftBit n }
  right := { bit := rightBit n }
  carry := carryBit n
  leftRight_ne := by
    intro i h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [leftBit_wire_val, rightBit_wire_val] at hv
    omega
  leftCarry_ne := by
    intro i h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [leftBit_wire_val, carryBit_wire_val] at hv
    omega
  rightCarry_ne := by
    intro i h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [rightBit_wire_val, carryBit_wire_val] at hv
    omega

/-- Concrete full carry-work layout for the canonical data-plus-carry-work
encoding.  This fixes the line allocation for the later carry-schedule
invariant; it does not claim that any folded gate list is already a word-level
plain adder. -/
def carryWorkLayout (n : Nat) :
    CarryWorkLayout (encoding := dataWithCarryWorkEncoding n) n where
  left := withCarryWorkLeftWord n
  right := withCarryWorkRightWord n
  carryIn := withCarryWorkCarryBit n
  workCarry := carryWorkWord n
  leftLeft_ne := by
    intro i j hij
    change (withCarryWorkLeftBit n i).wire ≠ (withCarryWorkLeftBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [withCarryWorkLeftBit_wire_val] at hv
    omega
  rightRight_ne := by
    intro i j hij
    change (withCarryWorkRightBit n i).wire ≠ (withCarryWorkRightBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [withCarryWorkRightBit_wire_val] at hv
    omega
  leftRight_ne := by
    intro i j
    change (withCarryWorkLeftBit n i).wire ≠
      (withCarryWorkRightBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkLeftBit_wire_val,
      withCarryWorkRightBit_wire_val] at hv
    omega
  leftCarryIn_ne := by
    intro i
    change (withCarryWorkLeftBit n i).wire ≠
      (withCarryWorkCarryBit n).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkLeftBit_wire_val,
      withCarryWorkCarryBit_wire_val] at hv
    omega
  rightCarryIn_ne := by
    intro i
    change (withCarryWorkRightBit n i).wire ≠
      (withCarryWorkCarryBit n).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkRightBit_wire_val,
      withCarryWorkCarryBit_wire_val] at hv
    omega
  leftWork_ne := by
    intro i j
    change (withCarryWorkLeftBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkLeftBit_wire_val, carryWorkBit_wire_val,
      dataEncoding_width] at hv
    omega
  rightWork_ne := by
    intro i j
    change (withCarryWorkRightBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkRightBit_wire_val, carryWorkBit_wire_val,
      dataEncoding_width] at hv
    omega
  carryInWork_ne := by
    intro j
    change (withCarryWorkCarryBit n).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    simp only [withCarryWorkCarryBit_wire_val, carryWorkBit_wire_val,
      dataEncoding_width] at hv
    omega
  workWork_ne := by
    intro i j hij
    change (carryWorkBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [carryWorkBit_wire_val] at hv
    omega

@[simp] theorem carryWorkLayout_carryInput_get_clean
    (n : Nat) (j : Fin (n - 1)) (x : Data n) :
    (CarryWorkLayout.carryInput (carryWorkLayout n) j).get
        (x, cleanCarryWork n) =
      if j.val = 0 then x.carry else false := by
  unfold CarryWorkLayout.carryInput
  by_cases h : j.val = 0
  · simp [h, carryWorkLayout]
  · simp [h, carryWorkLayout, carryWorkWord]

/-- The canonical clean-work local carry stage writes the expected full-adder
carry into its selected work bit.  This is the first concrete recurrence hook
for the later word-level carry invariant in the VBE carry-work schedule
[VBE95, 9511018.tex:237-264,596-618]. -/
theorem carryWorkLayout_carryOutGatesAt_get_workCarry_clean
    (n : Nat) (j : Fin (n - 1)) (x : Data n) :
    (carryWorkBit n j).get
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryOutGatesAt (carryWorkLayout n) j)
          (x, cleanCarryWork n)) =
      Bool.carry
        ((withCarryWorkLeftBit n (CarryWorkLayout.lowIndex j)).get
          (x, cleanCarryWork n))
        ((withCarryWorkRightBit n (CarryWorkLayout.lowIndex j)).get
          (x, cleanCarryWork n))
        (if j.val = 0 then x.carry else false) := by
  have h :=
    CarryWorkLayout.carryOutGatesAt_get_workCarry_clean
      (carryWorkLayout n) j (x, cleanCarryWork n)
      (carryWorkBit_get_clean n j x)
  rw [← carryWorkLayout_carryInput_get_clean n j x]
  simpa [carryWorkLayout, carryWorkWord, withCarryWorkLeftWord,
    withCarryWorkRightWord] using h

/-- Canonical clean-work recurrence for the full forward carry stage. -/
theorem carryWorkLayout_carryStageIndexStep_get_workCarry_recurrence
    (n : Nat) (j : Fin (n - 1)) (x : Data n) :
    (carryWorkBit n j).get
        (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
          (x, cleanCarryWork n)) =
      Bool.carry
        ((leftBit n (CarryWorkLayout.lowIndex j)).get x)
        ((rightBit n (CarryWorkLayout.lowIndex j)).get x)
        ((CarryWorkLayout.carryInput (carryWorkLayout n) j).get
          (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
            (x, cleanCarryWork n))) := by
  have h :=
    CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
      (carryWorkLayout n) j (x, cleanCarryWork n)
      (by
        intro k
        simp [carryWorkLayout, carryWorkWord])
  simpa [carryWorkLayout, carryWorkWord, withCarryWorkLeftWord,
    withCarryWorkRightWord] using h

/-- Canonical clean-work forward-carry recurrence in little-endian `testBit`
form. -/
theorem carryWorkLayout_carryStageIndexStep_get_workCarry_recurrence_testBit
    (n : Nat) (j : Fin (n - 1)) (x : Data n) :
    (carryWorkBit n j).get
        (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
          (x, cleanCarryWork n)) =
      Bool.carry
        (x.left.val.testBit j.val)
        (x.right.val.testBit j.val)
        ((CarryWorkLayout.carryInput (carryWorkLayout n) j).get
          (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
            (x, cleanCarryWork n))) := by
  simpa [CarryWorkLayout.lowIndex] using
    carryWorkLayout_carryStageIndexStep_get_workCarry_recurrence n j x

/-- Canonical clean-work forward-carry stage computes the propagated natural
addition carry in work bit `j`.  This closes the ordered carry recurrence for
the VBE-style forward pass, but does not assert that the dirty work has been
uncomputed [VBE95, 9511018.tex:237-264,596-618]. -/
theorem carryWorkLayout_carryStageIndexStep_get_workCarry_natAddCarry
    (n : Nat) (j : Fin (n - 1)) (x : Data n)
    (hcarry : x.CarryClean) :
    (carryWorkBit n j).get
        (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
          (x, cleanCarryWork n)) =
      natAddCarry x.left.val x.right.val (j.val + 1) := by
  have hcarryFalse : x.carry = false := hcarry
  let stage := CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
      (x, cleanCarryWork n)
  change (carryWorkBit n j).get stage =
    natAddCarry x.left.val x.right.val (j.val + 1)
  have hmain : forall m, forall j : Fin (n - 1), j.val = m ->
      (carryWorkBit n j).get stage =
        natAddCarry x.left.val x.right.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          carryWorkLayout_carryStageIndexStep_get_workCarry_recurrence_testBit
            n j x
        change (carryWorkBit n j).get stage =
          natAddCarry x.left.val x.right.val (j.val + 1)
        rw [hrec]
        unfold CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        case pos =>
          rw [dif_pos hzero]
          have hdata := CarryWorkLayout.carryStageIndexStep_get_dataCarry
            (carryWorkLayout n) (x, cleanCarryWork n)
          rw [hdata]
          simp [carryWorkLayout, hcarryFalse, natAddCarry, hzero]
        case neg =>
          rw [dif_neg hzero]
          let p := CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, CarryWorkLayout.previousWorkIndex]
            omega
          change
            Bool.carry (x.left.val.testBit j.val)
              (x.right.val.testBit j.val) ((carryWorkBit n p).get stage) =
            natAddCarry x.left.val x.right.val (j.val + 1)
          rw [hpRec, hpSucc]
          simp [natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before summing target bit `i` is exactly the propagated
natural addition carry at `i` for clean input carry/work. -/
theorem carryWorkLayout_carryBeforeSum_get_natAddCarry
    (n : Nat) (i : Fin n) (x : Data n) (hcarry : x.CarryClean) :
    (CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
        (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
          (x, cleanCarryWork n)) =
      natAddCarry x.left.val x.right.val i.val := by
  have hcarryFalse : x.carry = false := hcarry
  unfold CarryWorkLayout.carryBeforeSum
  by_cases hzero : i.val = 0
  case pos =>
    rw [dif_pos hzero]
    have hdata := CarryWorkLayout.carryStageIndexStep_get_dataCarry
      (carryWorkLayout n) (x, cleanCarryWork n)
    rw [hdata]
    simp [carryWorkLayout, hcarryFalse, natAddCarry, hzero]
  case neg =>
    rw [dif_neg hzero]
    have hjLt : i.val - 1 < n - 1 := by
      have hi := i.isLt
      omega
    let j : Fin (n - 1) := { val := i.val - 1, isLt := hjLt }
    have hwork :=
      carryWorkLayout_carryStageIndexStep_get_workCarry_natAddCarry
        n j x hcarry
    have hjSucc : j.val + 1 = i.val := by
      dsimp [j]
      omega
    change
      (carryWorkBit n j).get
          (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
            (x, cleanCarryWork n)) =
        natAddCarry x.left.val x.right.val i.val
    rw [hwork, hjSucc]

/-- Canonical clean-work target-bit formula for the folded dirty carry/sum
stage.  This is still a bit-level statement; the remaining endpoint proof must
assemble these bit equations into the `ZMod (2^n)` word equality. -/
theorem carryWorkLayout_carryAndSumGates_get_right
    (n : Nat) (i : Fin n) (x : Data n) :
    (rightBit n i).get
        (Prod.fst
          (EncodedBit.GateSpec.stepList
            (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
            (x, cleanCarryWork n))) =
      (((rightBit n i).get x ^^ (leftBit n i).get x) ^^
        (CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
          (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
            (x, cleanCarryWork n))) := by
  have h :=
    CarryWorkLayout.carryAndSumGates_get_right
      (carryWorkLayout n) i (x, cleanCarryWork n)
  rw [CarryWorkLayout.carryStage_stepList_eq_indexStep] at h
  simpa [carryWorkLayout, carryWorkWord, withCarryWorkLeftWord,
    withCarryWorkRightWord] using h

/-- Canonical clean-work target-bit formula in little-endian `testBit` form. -/
theorem carryWorkLayout_carryAndSumGates_get_right_testBit
    (n : Nat) (i : Fin n) (x : Data n) :
    (Prod.fst
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
          (x, cleanCarryWork n))).right.val.testBit i.val =
      ((x.right.val.testBit i.val ^^ x.left.val.testBit i.val) ^^
        (CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
          (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
            (x, cleanCarryWork n))) := by
  simpa using carryWorkLayout_carryAndSumGates_get_right n i x

/-- On clean carry/work inputs, the dirty forward carry plus sum stage gives
the correct target-word bit of `Data.addIntoRight`.  This theorem identifies
the right-word endpoint only; it deliberately does not claim carry-work cleanup
[VBE95, 9511018.tex:237-264,591-618]. -/
theorem carryWorkLayout_carryAndSumGates_get_right_addIntoRight_testBit
    (n : Nat) (i : Fin n) (x : Data n) (hcarry : x.CarryClean) :
    (Prod.fst
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
          (x, cleanCarryWork n))).right.val.testBit i.val =
      x.addIntoRight.right.val.testBit i.val := by
  rw [carryWorkLayout_carryAndSumGates_get_right_testBit]
  rw [carryWorkLayout_carryBeforeSum_get_natAddCarry n i x hcarry]
  simp [Data.addIntoRight]
  simpa [Bool.xor_assoc] using
    (word_add_val_testBit_eq_xor3 n x.left x.right i).symm

/-- Word-level right-target endpoint for the dirty forward carry plus sum
stage, obtained by assembling the per-bit formula.  Work cleanup remains a
separate obligation for the full VBE schedule [VBE95,
9511018.tex:237-264,591-618]. -/
theorem carryWorkLayout_carryAndSumGates_get_right_addIntoRight
    (n : Nat) (x : Data n) (hcarry : x.CarryClean) :
    (Prod.fst
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
          (x, cleanCarryWork n))).right =
      x.addIntoRight.right := by
  apply word_eq_of_testBit_eq
  intro i
  exact carryWorkLayout_carryAndSumGates_get_right_addIntoRight_testBit
    n i x hcarry

/-- The dirty forward carry plus sum stage preserves the left/source word. -/
theorem carryWorkLayout_carryAndSumGates_get_left_word
    (n : Nat) (x : Data n) :
    (Prod.fst
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
          (x, cleanCarryWork n))).left =
      x.left := by
  apply word_eq_of_testBit_eq
  intro i
  have h := CarryWorkLayout.carryAndSumGates_get_left
    (carryWorkLayout n) i (x, cleanCarryWork n)
  simpa [carryWorkLayout, carryWorkWord, withCarryWorkLeftWord] using h

/-- The dirty forward carry plus sum stage preserves the data carry flag. -/
theorem carryWorkLayout_carryAndSumGates_get_dataCarry
    (n : Nat) (x : Data n) :
    (Prod.fst
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
          (x, cleanCarryWork n))).carry =
      x.carry := by
  have h := CarryWorkLayout.carryAndSumGates_get_dataCarry
    (carryWorkLayout n) (x, cleanCarryWork n)
  simpa [carryWorkLayout] using h

/-- Data-register endpoint for the dirty forward carry plus sum stage.  The
right target has been updated as a plain adder and the source/carry data fields
are preserved; the temporary carry work may still be dirty [VBE95,
9511018.tex:237-264,591-618]. -/
theorem carryWorkLayout_carryAndSumGates_get_data_addIntoRight
    (n : Nat) (x : Data n) (hcarry : x.CarryClean) :
    Prod.fst
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
          (x, cleanCarryWork n)) =
      x.addIntoRight := by
  let y := Prod.fst
        (EncodedBit.GateSpec.stepList
          (CarryWorkLayout.carryAndSumGates (carryWorkLayout n))
          (x, cleanCarryWork n))
  have hleft : y.left = x.left :=
    carryWorkLayout_carryAndSumGates_get_left_word n x
  have hright : y.right = x.addIntoRight.right :=
    carryWorkLayout_carryAndSumGates_get_right_addIntoRight n x hcarry
  have hcar : y.carry = x.carry :=
    carryWorkLayout_carryAndSumGates_get_dataCarry n x
  change y = x.addIntoRight
  clear_value y
  cases y with
  | mk yl yr yc =>
      cases x with
      | mk xl xr xc =>
          simp [Data.addIntoRight] at hleft hright hcar
          simp [Data.addIntoRight, hleft, hright, hcar]

/-- Folded gate list for the canonical cleanup-aware carry-work schedule.  This
is the concrete object intended for the final clean-work plain-adder endpoint;
the right-word and work-clean invariants are proved separately [VBE95,
9511018.tex:237-264,596-618]. -/
def carryWorkCleanCarrySumGates (n : Nat) :
    List (EncodedBit.GateSpec (dataWithCarryWorkEncoding n)) :=
  CarryWorkLayout.cleanCarrySumGates (carryWorkLayout n)

/-- Base-gate program for the canonical cleanup-aware carry-work schedule. -/
def carryWorkCleanCarrySumProgram (n : Nat) :
    BaseGateProgram (dataWithCarryWorkEncoding n).width :=
  CarryWorkLayout.cleanCarrySumProgram (carryWorkLayout n)

/-- Folded semantic action of the canonical cleanup-aware carry-work schedule. -/
def carryWorkCleanCarrySumStep (n : Nat) :
    Data n × CarryWork n -> Data n × CarryWork n :=
  CarryWorkLayout.cleanCarrySumStep (carryWorkLayout n)

/-- The canonical cleanup-aware carry-work schedule realizes its folded
bit-lens action with the same base-gate program object used for resources. -/
theorem carryWorkCleanCarrySum_realizes (n : Nat) :
    BaseGateProgram.Realizes (dataWithCarryWorkEncoding n)
      (carryWorkCleanCarrySumProgram n) (carryWorkCleanCarrySumStep n) :=
  CarryWorkLayout.cleanCarrySum_realizes (carryWorkLayout n)

/-- Same-Circuit witness for the canonical cleanup-aware carry-work schedule. -/
def carryWorkCleanCarrySumSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness
      (Data n × CarryWork n) (carryWorkCleanCarrySumStep n) :=
  CarryWorkLayout.cleanCarrySumSameCircuit (carryWorkLayout n)

/-- The canonical cleanup-aware carry-work schedule preserves the left/source
word [VBE95, 9511018.tex:237-264,596-618]. -/
theorem carryWorkCleanCarrySumStep_get_left_word
    (n : Nat) (x : Data n) (work : CarryWork n) :
    (Prod.fst (carryWorkCleanCarrySumStep n (x, work))).left =
      x.left := by
  apply word_eq_of_testBit_eq
  intro i
  have h := CarryWorkLayout.cleanCarrySumGates_get_left
    (carryWorkLayout n) i (x, work)
  simpa [carryWorkCleanCarrySumStep, CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, carryWorkWord, withCarryWorkLeftWord] using h

/-- The canonical cleanup-aware carry-work schedule preserves the data carry
flag [VBE95, 9511018.tex:237-264,596-618]. -/
theorem carryWorkCleanCarrySumStep_get_dataCarry
    (n : Nat) (x : Data n) (work : CarryWork n) :
    (Prod.fst (carryWorkCleanCarrySumStep n (x, work))).carry =
      x.carry := by
  have h := CarryWorkLayout.cleanCarrySumGates_get_dataCarry
    (carryWorkLayout n) (x, work)
  simpa [carryWorkCleanCarrySumStep, CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout] using h

/-- Canonical cleanup-aware target-bit formula for the concrete carry-work
schedule [VBE95, 9511018.tex:237-264,596-618]. -/
theorem carryWorkCleanCarrySumStep_get_right
    (n : Nat) (i : Fin n) (x : Data n) :
    (rightBit n i).get
        (Prod.fst (carryWorkCleanCarrySumStep n
          (x, cleanCarryWork n))) =
      (((rightBit n i).get x ^^ (leftBit n i).get x) ^^
        (CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
          (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
            (x, cleanCarryWork n))) := by
  have h :=
    CarryWorkLayout.cleanCarrySumGates_get_right
      (carryWorkLayout n) i (x, cleanCarryWork n)
  rw [CarryWorkLayout.carryStage_stepList_eq_indexStep] at h
  simpa [carryWorkCleanCarrySumStep, CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, carryWorkWord, withCarryWorkLeftWord,
    withCarryWorkRightWord] using h

/-- Canonical cleanup-aware target-bit formula in little-endian `testBit`
form [VBE95, 9511018.tex:237-264,596-618]. -/
theorem carryWorkCleanCarrySumStep_get_right_testBit
    (n : Nat) (i : Fin n) (x : Data n) :
    (Prod.fst
        (carryWorkCleanCarrySumStep n
          (x, cleanCarryWork n))).right.val.testBit i.val =
      ((x.right.val.testBit i.val ^^ x.left.val.testBit i.val) ^^
        (CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
          (CarryWorkLayout.carryStageIndexStep (carryWorkLayout n)
            (x, cleanCarryWork n))) := by
  simpa using carryWorkCleanCarrySumStep_get_right n i x

/-- On clean carry/work inputs, the cleanup-aware carry/sum schedule gives the
correct target-word bit of `Data.addIntoRight`.  This theorem identifies the
right-word endpoint only; work cleanup remains a separate invariant [VBE95,
9511018.tex:237-264,591-618]. -/
theorem carryWorkCleanCarrySumStep_get_right_addIntoRight_testBit
    (n : Nat) (i : Fin n) (x : Data n) (hcarry : x.CarryClean) :
    (Prod.fst
        (carryWorkCleanCarrySumStep n
          (x, cleanCarryWork n))).right.val.testBit i.val =
      x.addIntoRight.right.val.testBit i.val := by
  rw [carryWorkCleanCarrySumStep_get_right_testBit]
  rw [carryWorkLayout_carryBeforeSum_get_natAddCarry n i x hcarry]
  simp [Data.addIntoRight]
  simpa [Bool.xor_assoc] using
    (word_add_val_testBit_eq_xor3 n x.left x.right i).symm

/-- Word-level right-target endpoint for the cleanup-aware carry/sum schedule.
Work cleanup remains a separate invariant for the final structured witness
[VBE95, 9511018.tex:237-264,591-618]. -/
theorem carryWorkCleanCarrySumStep_get_right_addIntoRight
    (n : Nat) (x : Data n) (hcarry : x.CarryClean) :
    (Prod.fst
        (carryWorkCleanCarrySumStep n
          (x, cleanCarryWork n))).right =
      x.addIntoRight.right := by
  apply word_eq_of_testBit_eq
  intro i
  exact carryWorkCleanCarrySumStep_get_right_addIntoRight_testBit
    n i x hcarry

/-- Data-register endpoint for the cleanup-aware carry/sum schedule.  The data
register has been updated as a plain adder and source/carry data fields are
preserved; the all-zero work cleanup is still proved separately [VBE95,
9511018.tex:237-264,591-618]. -/
theorem carryWorkCleanCarrySumStep_get_data_addIntoRight
    (n : Nat) (x : Data n) (hcarry : x.CarryClean) :
    Prod.fst
        (carryWorkCleanCarrySumStep n
          (x, cleanCarryWork n)) =
      x.addIntoRight := by
  let y := Prod.fst
        (carryWorkCleanCarrySumStep n
          (x, cleanCarryWork n))
  have hleft : y.left = x.left :=
    carryWorkCleanCarrySumStep_get_left_word n x (cleanCarryWork n)
  have hright : y.right = x.addIntoRight.right :=
    carryWorkCleanCarrySumStep_get_right_addIntoRight n x hcarry
  have hcar : y.carry = x.carry :=
    carryWorkCleanCarrySumStep_get_dataCarry n x (cleanCarryWork n)
  change y = x.addIntoRight
  clear_value y
  cases y with
  | mk yl yr yc =>
      cases x with
      | mk xl xr xc =>
          simp [Data.addIntoRight] at hleft hright hcar
          simp [Data.addIntoRight, hleft, hright, hcar]

/-- The canonical cleanup-aware carry/sum schedule clears each temporary carry
work bit when started from the clean work register [VBE95,
9511018.tex:237-264,591-618]. -/
theorem carryWorkCleanCarrySumStep_get_workCarry_clean
    (n : Nat) (j : Fin (n - 1)) (x : Data n) :
    (carryWorkBit n j).get
        (carryWorkCleanCarrySumStep n (x, cleanCarryWork n)) =
      false := by
  have h := CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
    (carryWorkLayout n) j (x, cleanCarryWork n)
    (by
      intro k
      simp [carryWorkLayout, carryWorkWord])
  simpa [carryWorkCleanCarrySumStep, CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, carryWorkWord] using h

/-- The canonical cleanup-aware carry/sum schedule restores the whole temporary
carry-work register to the all-zero label [VBE95,
9511018.tex:237-264,591-618]. -/
theorem carryWorkCleanCarrySumStep_get_work_clean
    (n : Nat) (x : Data n) :
    Prod.snd
        (carryWorkCleanCarrySumStep n (x, cleanCarryWork n)) =
      cleanCarryWork n := by
  apply finIdentity_eq_zero_of_get_false
  intro bit
  have h := carryWorkCleanCarrySumStep_get_workCarry_clean n bit x
  simpa [carryWorkBit, BinaryLabelEncoding.prodRightBit, cleanCarryWork] using h

/-- Full clean endpoint for the canonical cleanup-aware carry-work schedule:
on clean carry and clean work inputs, the data register is `addIntoRight` and
the work register is restored to zero [VBE95, 9511018.tex:237-264,591-618]. -/
theorem carryWorkCleanCarrySumStep_cleanEndpoint
    (n : Nat) (x : Data n) (hcarry : x.CarryClean) :
    carryWorkCleanCarrySumStep n (x, cleanCarryWork n) =
      (x.addIntoRight, cleanCarryWork n) := by
  exact Prod.ext
    (carryWorkCleanCarrySumStep_get_data_addIntoRight n x hcarry)
    (carryWorkCleanCarrySumStep_get_work_clean n x)

/-- Folded gate list for the canonical single-carry schedule shell. -/
def gates (n : Nat) : List (EncodedBit.GateSpec (dataEncoding n)) :=
  SingleCarryLayout.gates (singleCarryLayout n)

/-- Base-gate program for the canonical single-carry schedule shell. -/
def program (n : Nat) : BaseGateProgram (dataEncoding n).width :=
  SingleCarryLayout.program (singleCarryLayout n)

/-- Folded semantic action of the canonical single-carry schedule shell. -/
def step (n : Nat) : Data n -> Data n :=
  SingleCarryLayout.step (singleCarryLayout n)

/-- The canonical single-carry schedule shell realizes its folded bit-lens
action with the same base-gate program object. -/
theorem realizes (n : Nat) :
    BaseGateProgram.Realizes (dataEncoding n) (program n) (step n) :=
  SingleCarryLayout.realizes (singleCarryLayout n)

/-- Same-Circuit witness for the canonical single-carry schedule shell. -/
def sameCircuit (n : Nat) : BaseGateSameCircuitWitness (Data n) (step n) :=
  SingleCarryLayout.sameCircuit (singleCarryLayout n)

/-- Package any proved canonical data-plus-carry-work gate list as the clean
plain-adder witness expected by downstream modular-arithmetic code.  The proof
argument is exactly the missing word-level carry invariant: on clean work and
clean carry inputs, the folded gate-list action must be `Data.addIntoRight` and
must restore the all-zero carry-work label. -/
def structuredWithCarryWorkWitness (n : Nat)
    (gates : List (EncodedBit.GateSpec (dataWithCarryWorkEncoding n)))
    (hclean :
      forall x : Data n,
        x.CarryClean ->
        EncodedBit.GateSpec.stepList gates (x, cleanCarryWork n) =
          (Data.addIntoRight x, cleanCarryWork n)) :
    StructuredWithWorkWitness n (CarryWork n) where
  encoding := dataWithCarryWorkEncoding n
  cleanWork := cleanCarryWork n
  step := EncodedBit.GateSpec.stepList gates
  program := EncodedBit.GateSpec.programList gates
  realizes := EncodedBit.GateSpec.realizesList gates
  cleanEndpoint := hclean

/-- Structured clean-work plain-adder witness built from the canonical
cleanup-aware carry-work gate list.  Correctness and resources are tied to the
same folded `BaseGateProgram` object [VBE95, 9511018.tex:237-264,591-618]. -/
def carryWorkStructuredWitness (n : Nat) :
    StructuredWithWorkWitness n (CarryWork n) :=
  structuredWithCarryWorkWitness n (carryWorkCleanCarrySumGates n)
    (by
      intro x hcarry
      simpa [carryWorkCleanCarrySumStep, carryWorkCleanCarrySumGates,
        CarryWorkLayout.cleanCarrySumStep] using
          carryWorkCleanCarrySumStep_cleanEndpoint n x hcarry)

end PowerOfTwo

end

end Schedule
end PlainAdder
end QuantumAlg
