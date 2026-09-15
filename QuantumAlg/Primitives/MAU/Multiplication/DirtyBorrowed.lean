/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.DirtyBorrowed
import Mathlib.Tactic

/-!
# HRS-style dirty-borrowed modular multiplication boundary

Häner--Roetteler--Svore construct an in-place constant modular multiplier by
repeated, bit-selected modular additions, a register swap, and a reverse
multiply-accumulate using the inverse constant [HRS16,
`paper.tex:263-300`].  Their modular adder needs both the dirty-borrowed
constant-adder/carry primitive and a comparator/reduction network with one
clean flag [HRS16, `paper.tex:268-285`].

`MAU.Addition.DirtyBorrowed` supplies the former: an executable literal
X/CNOT/Toffoli circuit for fixed-width addition modulo a power of two, with a
strong arbitrary-joint-state restoration theorem.  It does *not* by itself
supply the comparator/reduction network required to change that modulus to
`N`.  This file therefore records the smallest honest circuit boundary for
that missing controlled modular-add stage and constructs the HRS
compute/swap/uncompute composition from any such certified stages.  No VBE
clean-work circuit is renamed or treated as an HRS implementation here.

The boundary deliberately requires one actual `UnitaryCircuit`, its permutation
semantics, and its native X/CNOT/Toffoli coordinates to agree.  Thus an
eventual literal comparator/reducer cannot attach independent accounting
metadata, and it must restore every dirty-borrowed basis label before this
module can expose the in-place multiplier realization.
-/

section

namespace QuantumAlg
namespace MAU.Multiplication.DirtyBorrowed

noncomputable section

open scoped BigOperators

/-! ## R.0 building block -/

/-- The concrete R.0 HRS dirty-carry program used by any later reducer.

It adds a constant modulo `2^(n+1)` and restores its `n` dirty wires.  The
extra comparator/reduction construction required for addition modulo `N` is
intentionally not hidden behind this definition. -/
abbrev r0PlainAdderProgram (n : Nat) (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit (Qubits (MAU.Addition.DirtyBorrowed.straightforwardEncoding n).width) :=
  MAU.Addition.DirtyBorrowed.straightforwardProgram n constant

/-- R.0's literal program has the exact strong dirty-state semantics already
proved in the addition module. -/
theorem r0PlainAdderProgram_realizes (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit.Realizes (MAU.Addition.DirtyBorrowed.straightforwardEncoding n)
      (r0PlainAdderProgram n constant)
      (fun state => (state.1 + constant, state.2)) :=
  MAU.Addition.DirtyBorrowed.straightforwardProgram_realizes n constant

/-! ## HRS logical carrier -/

/-- An HRS modular-add boundary has a source word, an accumulator word, one
clean comparison flag, and an arbitrary borrowed register.  The source word
is preserved by every selected addition, so it may be entangled with the
borrowed subsystem. -/
abbrev State (n : Nat) (Borrowed : Register) : Type :=
  (PlainAdder.Word n × PlainAdder.Word n) × (Bool × Borrowed.Index)

/-- The typed carrier of the HRS source, accumulator, clean comparator flag,
and arbitrary borrowed environment. -/
abbrev register (n : Nat) (Borrowed : Register) : Register where
  Index := State n Borrowed
  fintype := inferInstance
  decEq := inferInstance

/-- Source (multiplicand) word. -/
def source {n : Nat} {Borrowed : Register} (state : State n Borrowed) :
    PlainAdder.Word n :=
  state.1.1

/-- Accumulator word. -/
def target {n : Nat} {Borrowed : Register} (state : State n Borrowed) :
    PlainAdder.Word n :=
  state.1.2

/-- The one clean comparator/reduction flag. -/
def cleanFlag {n : Nat} {Borrowed : Register} (state : State n Borrowed) : Bool :=
  state.2.1

/-- The complete arbitrary dirty-borrowed label. -/
def borrowed {n : Nat} {Borrowed : Register} (state : State n Borrowed) :
    Borrowed.Index :=
  state.2.2

/-- Replace only the accumulator word. -/
def withTarget {n : Nat} {Borrowed : Register} (state : State n Borrowed)
    (newTarget : PlainAdder.Word n) : State n Borrowed :=
  ((source state, newTarget), (cleanFlag state, borrowed state))

/-- Replace only the clean comparison flag. -/
def withCleanFlag {n : Nat} {Borrowed : Register} (state : State n Borrowed)
    (newFlag : Bool) : State n Borrowed :=
  ((source state, target state), (newFlag, borrowed state))

@[simp] theorem source_withTarget {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newTarget : PlainAdder.Word n) :
    source (withTarget state newTarget) = source state :=
  rfl

@[simp] theorem target_withTarget {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newTarget : PlainAdder.Word n) :
    target (withTarget state newTarget) = newTarget :=
  rfl

@[simp] theorem cleanFlag_withTarget {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newTarget : PlainAdder.Word n) :
    cleanFlag (withTarget state newTarget) = cleanFlag state :=
  rfl

@[simp] theorem borrowed_withTarget {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newTarget : PlainAdder.Word n) :
    borrowed (withTarget state newTarget) = borrowed state :=
  rfl

@[simp] theorem source_withCleanFlag {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newFlag : Bool) :
    source (withCleanFlag state newFlag) = source state :=
  rfl

@[simp] theorem target_withCleanFlag {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newFlag : Bool) :
    target (withCleanFlag state newFlag) = target state :=
  rfl

@[simp] theorem cleanFlag_withCleanFlag {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newFlag : Bool) :
    cleanFlag (withCleanFlag state newFlag) = newFlag :=
  rfl

@[simp] theorem borrowed_withCleanFlag {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newFlag : Bool) :
    borrowed (withCleanFlag state newFlag) = borrowed state :=
  rfl

/-- Replacing the accumulator by its current value is the identity. -/
@[simp] theorem withTarget_target {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) :
    withTarget state (target state) = state := by
  rcases state with ⟨⟨sourceWord, targetWord⟩, ⟨flag, dirty⟩⟩
  rfl

/-- Consecutive accumulator replacements retain only the final value. -/
@[simp] theorem withTarget_withTarget {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (first second : PlainAdder.Word n) :
    withTarget (withTarget state first) second = withTarget state second :=
  rfl

/-- Replacing the clean flag by its current value is the identity. -/
@[simp] theorem withCleanFlag_cleanFlag {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) :
    withCleanFlag state (cleanFlag state) = state := by
  rcases state with ⟨⟨sourceWord, targetWord⟩, ⟨flag, dirty⟩⟩
  rfl

/-- Consecutive clean-flag replacements retain only the final value. -/
@[simp] theorem withCleanFlag_withCleanFlag {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (first second : Bool) :
    withCleanFlag (withCleanFlag state first) second =
      withCleanFlag state second :=
  rfl

/-- Accumulator and clean-flag replacement commute because they address
disjoint logical projections. -/
theorem withCleanFlag_withTarget {n : Nat} {Borrowed : Register}
    (state : State n Borrowed) (newTarget : PlainAdder.Word n)
    (newFlag : Bool) :
    withCleanFlag (withTarget state newTarget) newFlag =
      withTarget (withCleanFlag state newFlag) newTarget :=
  rfl

/-- Parameters required by the source's in-place multiplication construction.
`inverse` is the classical inverse of `constant` modulo the positive modulus;
the multiplication circuit itself must use it in its reverse accumulation
pass. -/
structure Parameters (n : Nat) where
  /-- Classical positive modulus represented in `n` bits. -/
  modulus : Nat
  modulus_pos : 0 < modulus
  modulus_lt_width : modulus < 2 ^ n
  /-- Forward multiplication constant. -/
  constant : PlainAdder.Word n
  constant_lt_modulus : constant.val < modulus
  /-- Classical inverse used by the reverse accumulation. -/
  inverse : PlainAdder.Word n
  inverse_lt_modulus : inverse.val < modulus
  inverse_mul_constant : (inverse.val * constant.val) % modulus = 1

variable {n : Nat} {Borrowed : Register}

namespace Parameters

/-- Canonically embed a residue below the modulus in the `n`-bit word. -/
def word (params : Parameters n) (value : Nat) : PlainAdder.Word n :=
  (value % params.modulus : PlainAdder.Word n)

@[simp] theorem word_val (params : Parameters n) (value : Nat) :
    (params.word value).val = value % params.modulus :=
  ZMod.val_natCast_of_lt
    ((Nat.mod_lt _ params.modulus_pos).trans params.modulus_lt_width)

/-- The selected constant for bit `i` in HRS's repeated-addition schedule. -/
def stageConstant (params : Parameters n) (bit : Fin n) : Nat :=
  (params.constant.val * 2 ^ bit.val) % params.modulus

/-- The inverse accumulation uses subtraction of the selected inverse
constant, implemented as addition by its additive inverse modulo `N`. -/
def signedStageConstant (params : Parameters n) (subtract : Bool)
    (bit : Fin n) : Nat :=
  if subtract then
    (params.modulus -
      ((params.inverse.val * 2 ^ bit.val) % params.modulus)) % params.modulus
  else
    params.stageConstant bit

/-- Every forward or inverse-pass stage constant is a canonical residue below
the positive modulus. -/
theorem signedStageConstant_lt_modulus (params : Parameters n)
    (subtract : Bool) (bit : Fin n) :
    params.signedStageConstant subtract bit < params.modulus := by
  cases subtract <;>
    simp only [signedStageConstant, stageConstant, Bool.false_eq_true,
      if_false, if_true] <;>
    exact Nat.mod_lt _ params.modulus_pos

/-- Addition modulo `N` on valid word labels, with invalid padding labels left
untouched.  A concrete circuit must provide a reversible extension agreeing
with this action on canonical labels. -/
def addReduced (params : Parameters n) (addend : Nat)
    (value : PlainAdder.Word n) : PlainAdder.Word n :=
  if value.val < params.modulus then
    params.word (value.val + addend)
  else
    value

@[simp] theorem addReduced_invalid (params : Parameters n) (addend : Nat)
    (value : PlainAdder.Word n) (hvalue : ¬ value.val < params.modulus) :
    params.addReduced addend value = value := by
  simp [addReduced, hvalue]

end Parameters

/-- Semantic target update of one HRS selected modular-add stage.  It makes
the required canonical behavior explicit but deliberately does not purport to
be a reversible extension on the padding subspace; that extension is carried
by `ControlledModularAdd.perm` below. -/
def stageTarget (params : Parameters n) (bit : Fin n) (subtract : Bool)
    (state : State n Borrowed) : PlainAdder.Word n :=
  if (source state).val.testBit bit.val then
    params.addReduced (params.signedStageConstant subtract bit) (target state)
  else
    target state

/-- Semantic update required of a controlled modular-add stage on the clean,
canonical HRS subspace. -/
def stageUpdate (params : Parameters n) (bit : Fin n) (subtract : Bool)
    (state : State n Borrowed) : State n Borrowed :=
  withTarget state (stageTarget params bit subtract state)

@[simp] theorem stageUpdate_source (params : Parameters n) (bit : Fin n)
    (subtract : Bool) (state : State n Borrowed) :
    source (stageUpdate params bit subtract state) = source state :=
  rfl

@[simp] theorem stageUpdate_cleanFlag (params : Parameters n) (bit : Fin n)
    (subtract : Bool) (state : State n Borrowed) :
    cleanFlag (stageUpdate params bit subtract state) = cleanFlag state :=
  rfl

@[simp] theorem stageUpdate_borrowed (params : Parameters n) (bit : Fin n)
    (subtract : Bool) (state : State n Borrowed) :
    borrowed (stageUpdate params bit subtract state) = borrowed state :=
  rfl

/-! ## Missing controlled modular-add circuit boundary -/

/-- A literal HRS controlled modular addition, once the comparator/reduction
network has been supplied.

The `perm` field is intentionally a total reversible extension over padding
labels.  `canonical_action` identifies the physically relevant clean-flag
subspace, while the source and borrowed preservation fields make the
dirty-borrowed guarantee strong enough for arbitrary joint states.  The clean
flag is a clean work bit, not an additional dirty-borrowed input: its
restoration is part of `canonical_action`.  The fields `toffoli_exact` and
`cnot_exact` are equations about the same stored circuit, not estimates.

This is an interface, not an unproved implementation: no inhabitant is
provided until the HRS comparator/reducer is compiled from R.0's dirty-carry
primitive and verified. -/
structure ControlledModularAdd (params : Parameters n) (Borrowed : Register)
    (bit : Fin n) (subtract : Bool) where
  /-- Reversible extension on every physical basis label. -/
  perm : Equiv.Perm (State n Borrowed)
  /-- On the canonical HRS subspace, the permutation is precisely the
bit-selected modular add/subtract operation. -/
  canonical_action : ∀ sourceWord targetWord borrowedWord,
    sourceWord.val < params.modulus →
    targetWord.val < params.modulus →
    perm ((sourceWord, targetWord), (false, borrowedWord)) =
      stageUpdate params bit subtract
        ((sourceWord, targetWord), (false, borrowedWord))
  /-- The selected source word is not overwritten, including on padding
labels. -/
  preserves_source : ∀ state, source (perm state) = source state
  /-- Every dirty-borrowed label is restored exactly, including when it is
part of a larger entangled environment. -/
  preserves_borrowed : ∀ state, borrowed (perm state) = borrowed state
  /-- Actual owned circuit. -/
  circuit : UnitaryCircuit (register n Borrowed)
  /-- Its matrix is exactly the declared reversible extension. -/
  matrix_eq : circuit.matrix = UnitaryOperator.ofPerm perm.symm
  /-- Exact native coordinates derived from that circuit. -/
  toffoli_count : Nat
  cnot_count : Nat
  toffoli_exact :
    ResourcePool.count (.gate (.builtin "toffoli")) circuit.eventCost =
      toffoli_count
  cnot_exact :
    ResourcePool.count (.gate (.builtin "cnot")) circuit.eventCost =
      cnot_count

namespace ControlledModularAdd

variable {n : Nat} {params : Parameters n} {Borrowed : Register}
variable {bit : Fin n} {subtract : Bool}

/-- Basis action of the actual controlled modular-add circuit. -/
theorem applyNormalized_ket
    (implementation : ControlledModularAdd params Borrowed bit subtract)
    (state : State n Borrowed) :
    implementation.circuit.applyNormalized
        (NormalizedVector.ket (R := register n Borrowed) state) =
      NormalizedVector.ket (R := register n Borrowed)
        (implementation.perm state) := by
  change implementation.circuit.matrix.apply _ = _
  rw [implementation.matrix_eq, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-- Amplitude-level action of the actual circuit on an arbitrary joint state.
This theorem is stronger than a clean-basis endpoint: it applies to arbitrary
superpositions and entanglement across all borrowed labels. -/
theorem applyVec_arbitrary_joint_state
    (implementation : ControlledModularAdd params Borrowed bit subtract)
    (state : HilbertVector (register n Borrowed))
    (output : State n Borrowed) :
    implementation.circuit.applyVec state output =
      state (implementation.perm.symm output) := by
  change implementation.circuit.matrix.applyVec state output = _
  rw [implementation.matrix_eq, UnitaryOperator.ofPerm_applyVec]

/-- The inverse permutation also leaves the entire borrowed label unchanged. -/
theorem preserves_borrowed_symm
    (implementation : ControlledModularAdd params Borrowed bit subtract)
    (state : State n Borrowed) :
    borrowed (implementation.perm.symm state) = borrowed state := by
  have h := implementation.preserves_borrowed (implementation.perm.symm state)
  simpa using h.symm

/-- Exact Toffoli coordinate of the owned stage circuit. -/
theorem toffoli_count_eq
    (implementation : ControlledModularAdd params Borrowed bit subtract) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        implementation.circuit.eventCost = implementation.toffoli_count :=
  implementation.toffoli_exact

/-- Exact CNOT coordinate of the owned stage circuit. -/
theorem cnot_count_eq
    (implementation : ControlledModularAdd params Borrowed bit subtract) :
    ResourcePool.count (.gate (.builtin "cnot"))
        implementation.circuit.eventCost = implementation.cnot_count :=
  implementation.cnot_exact

end ControlledModularAdd

/-! ## Actual compute/swap/uncompute assembly -/

/-- Certified physical swap of the two `n`-bit HRS arithmetic words.  A
literal implementation should expose the standard three-CNOT-per-bit
schedule; keeping it as a certificate here avoids pretending that the missing
modular-add reducer has already been compiled. -/
structure WordSwap (n : Nat) (Borrowed : Register) where
  perm : Equiv.Perm (State n Borrowed)
  swaps_words : ∀ sourceWord targetWord flag borrowedWord,
    perm ((sourceWord, targetWord), (flag, borrowedWord)) =
      ((targetWord, sourceWord), (flag, borrowedWord))
  circuit : UnitaryCircuit (register n Borrowed)
  matrix_eq : circuit.matrix = UnitaryOperator.ofPerm perm.symm
  toffoli_exact :
    ResourcePool.count (.gate (.builtin "toffoli")) circuit.eventCost = 0
  cnot_exact :
    ResourcePool.count (.gate (.builtin "cnot")) circuit.eventCost = 3 * n

/-! ## Literal physical word swap -/

/-- Zero-qubit environment for the literal HRS core word swap.  The actual
core contains only the two arithmetic words and the clean comparison flag.
Future dirty arithmetic must alias temporary roles onto those physical words;
adding a separate `n`-qubit tensor factor would incorrectly make the carrier
`3n+1` qubits wide. -/
abbrev LiteralBorrowed (_n : Nat) : Register := Qubits 0

/-! ## Dirty-work triple-controlled X -/

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Four-Toffoli realization of a triple-controlled X using one arbitrarily
initialized dirty work bit.  The first/third gates compute and erase `a ∧ b`
in the dirty bit; the second/fourth copies the difference through control `c`,
so the dirty initial value cancels exactly. -/
def dirtyTripleControlledXGates
    (controlA controlB controlC target work : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (_hac : controlA.wire ≠ controlC.wire)
    (_hat : controlA.wire ≠ target.wire)
    (haw : controlA.wire ≠ work.wire)
    (_hbc : controlB.wire ≠ controlC.wire)
    (_hbt : controlB.wire ≠ target.wire)
    (hbw : controlB.wire ≠ work.wire)
    (hct : controlC.wire ≠ target.wire)
    (hcw : controlC.wire ≠ work.wire)
    (htw : target.wire ≠ work.wire) :
    List (EncodedBit.GateSpec encoding) :=
  let compute := EncodedBit.GateSpec.toffoli
    controlA controlB work hab haw hbw
  let copy := EncodedBit.GateSpec.toffoli
    controlC work target hcw hct htw.symm
  [compute, copy, compute, copy]

/-- Folded action of the four-Toffoli dirty-work sequence. -/
def dirtyTripleControlledXStep
    (controlA controlB controlC target work : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (hac : controlA.wire ≠ controlC.wire)
    (hat : controlA.wire ≠ target.wire)
    (haw : controlA.wire ≠ work.wire)
    (hbc : controlB.wire ≠ controlC.wire)
    (hbt : controlB.wire ≠ target.wire)
    (hbw : controlB.wire ≠ work.wire)
    (hct : controlC.wire ≠ target.wire)
    (hcw : controlC.wire ≠ work.wire)
    (htw : target.wire ≠ work.wire) : Data → Data :=
  EncodedBit.GateSpec.stepList
    (dirtyTripleControlledXGates controlA controlB controlC target work
      hab hac hat haw hbc hbt hbw hct hcw htw)

/-- The arbitrary dirty value cancels: the sequence flips only the target,
and only when all three controls are true. -/
theorem dirtyTripleControlledXStep_eq
    (controlA controlB controlC target work : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (hac : controlA.wire ≠ controlC.wire)
    (hat : controlA.wire ≠ target.wire)
    (haw : controlA.wire ≠ work.wire)
    (hbc : controlB.wire ≠ controlC.wire)
    (hbt : controlB.wire ≠ target.wire)
    (hbw : controlB.wire ≠ work.wire)
    (hct : controlC.wire ≠ target.wire)
    (hcw : controlC.wire ≠ work.wire)
    (htw : target.wire ≠ work.wire)
    (state : Data) :
    dirtyTripleControlledXStep controlA controlB controlC target work
        hab hac hat haw hbc hbt hbw hct hcw htw state =
      if controlA.get state && controlB.get state && controlC.get state then
        target.flip state
      else
        state := by
  have hAWork (input : Data) :
      controlA.get (work.flip input) = controlA.get input :=
    EncodedBit.get_flip_of_wire_ne work controlA haw.symm input
  have hBWork (input : Data) :
      controlB.get (work.flip input) = controlB.get input :=
    EncodedBit.get_flip_of_wire_ne work controlB hbw.symm input
  have hCWork (input : Data) :
      controlC.get (work.flip input) = controlC.get input :=
    EncodedBit.get_flip_of_wire_ne work controlC hcw.symm input
  have hATarget (input : Data) :
      controlA.get (target.flip input) = controlA.get input :=
    EncodedBit.get_flip_of_wire_ne target controlA hat.symm input
  have hBTarget (input : Data) :
      controlB.get (target.flip input) = controlB.get input :=
    EncodedBit.get_flip_of_wire_ne target controlB hbt.symm input
  have hCTarget (input : Data) :
      controlC.get (target.flip input) = controlC.get input :=
    EncodedBit.get_flip_of_wire_ne target controlC hct.symm input
  have hWorkTarget (input : Data) :
      work.get (target.flip input) = work.get input :=
    EncodedBit.get_flip_of_wire_ne target work htw input
  unfold dirtyTripleControlledXStep dirtyTripleControlledXGates
  simp only [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step, id_eq]
  cases ha : controlA.get state <;>
    cases hb : controlB.get state <;>
    cases hc : controlC.get state <;>
    cases hw : work.get state <;>
    simp [EncodedBit.toffoliStep, ha, hb, hc, hw,
      hAWork, hBWork, hCWork, hATarget, hBTarget, hCTarget, hWorkTarget,
      EncodedBit.get_flip_self, EncodedBit.flip_flip,
      EncodedBit.flip_comm target work]

/-- Actual four-Toffoli dirty-work triple-control circuit. -/
def dirtyTripleControlledXProgram
    (controlA controlB controlC target work : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (hac : controlA.wire ≠ controlC.wire)
    (hat : controlA.wire ≠ target.wire)
    (haw : controlA.wire ≠ work.wire)
    (hbc : controlB.wire ≠ controlC.wire)
    (hbt : controlB.wire ≠ target.wire)
    (hbw : controlB.wire ≠ work.wire)
    (hct : controlC.wire ≠ target.wire)
    (hcw : controlC.wire ≠ work.wire)
    (htw : target.wire ≠ work.wire) :
    UnitaryCircuit (Qubits encoding.width) :=
  EncodedBit.GateSpec.programList
    (dirtyTripleControlledXGates controlA controlB controlC target work
      hab hac hat haw hbc hbt hbw hct hcw htw)

/-- The actual circuit realizes its exact arbitrary-dirty semantic action. -/
theorem dirtyTripleControlledXProgram_realizes
    (controlA controlB controlC target work : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (hac : controlA.wire ≠ controlC.wire)
    (hat : controlA.wire ≠ target.wire)
    (haw : controlA.wire ≠ work.wire)
    (hbc : controlB.wire ≠ controlC.wire)
    (hbt : controlB.wire ≠ target.wire)
    (hbw : controlB.wire ≠ work.wire)
    (hct : controlC.wire ≠ target.wire)
    (hcw : controlC.wire ≠ work.wire)
    (htw : target.wire ≠ work.wire) :
    UnitaryCircuit.Realizes encoding
      (dirtyTripleControlledXProgram controlA controlB controlC target work
        hab hac hat haw hbc hbt hbw hct hcw htw)
      (dirtyTripleControlledXStep controlA controlB controlC target work
        hab hac hat haw hbc hbt hbw hct hcw htw) :=
  EncodedBit.GateSpec.realizesList
    (dirtyTripleControlledXGates controlA controlB controlC target work
      hab hac hat haw hbc hbt hbw hct hcw htw)

/-- The same owned circuit contains exactly four Toffoli leaves. -/
theorem dirtyTripleControlledXProgram_toffoli_count_eq
    (controlA controlB controlC target work : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (hac : controlA.wire ≠ controlC.wire)
    (hat : controlA.wire ≠ target.wire)
    (haw : controlA.wire ≠ work.wire)
    (hbc : controlB.wire ≠ controlC.wire)
    (hbt : controlB.wire ≠ target.wire)
    (hbw : controlB.wire ≠ work.wire)
    (hct : controlC.wire ≠ target.wire)
    (hcw : controlC.wire ≠ work.wire)
    (htw : target.wire ≠ work.wire) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (dirtyTripleControlledXProgram controlA controlB controlC target work
          hab hac hat haw hbc hbt hbw hct hcw htw).eventCost = 4 := by
  rw [dirtyTripleControlledXProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  simp [dirtyTripleControlledXGates]

/-- Canonical little-endian bit-vector view of a fixed-width word. -/
def wordBitsEquiv (n : Nat) :
    PlainAdder.Word n ≃ (Fin n → Bool) where
  toFun word bit := word.val.testBit bit.val
  invFun bits := (Nat.ofBits bits : PlainAdder.Word n)
  left_inv word := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    rw [ZMod.val_natCast_of_lt
      (Nat.ofBits_lt_two_pow
        (fun index : Fin n => word.val.testBit index.val))]
    exact Nat.testBit_ofBits_lt
      (fun index : Fin n => word.val.testBit index.val) bit.val bit.isLt
  right_inv bits := by
    funext bit
    change ((Nat.ofBits bits : PlainAdder.Word n).val.testBit bit.val) = bits bit
    rw [ZMod.val_natCast_of_lt (Nat.ofBits_lt_two_pow bits)]
    exact Nat.testBit_ofBits_lt bits bit.val bit.isLt

/-- Reading the canonical bit-vector view is ordinary little-endian
`testBit`. -/
@[simp] theorem wordBitsEquiv_apply (n : Nat) (word : PlainAdder.Word n)
    (bit : Fin n) :
    wordBitsEquiv n word bit = word.val.testBit bit.val :=
  rfl

/-- Split an arbitrary selected source bit from all remaining source bits.
The residual word is ordered by `pivot.succAbove`, so no bit is duplicated or
discarded and the selected bit itself is unavailable as dirty carry work. -/
def wordRemoveEquiv (pivot : Fin n.succ) :
    PlainAdder.Word n.succ ≃ Bool × PlainAdder.Word n :=
  (wordBitsEquiv n.succ).trans
    ((Fin.insertNthEquiv (fun _ : Fin n.succ => Bool) pivot).symm.trans
      ((Equiv.refl Bool).prodCongr (wordBitsEquiv n).symm))

/-- The first split component is exactly the selected source bit. -/
@[simp] theorem wordRemoveEquiv_fst (pivot : Fin n.succ)
    (word : PlainAdder.Word n.succ) :
    (wordRemoveEquiv pivot word).1 = word.val.testBit pivot.val := by
  rfl

/-- Residual bit `j` is exactly source bit `pivot.succAbove j`. -/
@[simp] theorem wordRemoveEquiv_snd_testBit (pivot : Fin n.succ)
    (word : PlainAdder.Word n.succ) (bit : Fin n) :
    (wordRemoveEquiv pivot word).2.val.testBit bit.val =
      word.val.testBit (pivot.succAbove bit).val := by
  change
    ((wordBitsEquiv n).symm
      (Fin.removeNth pivot (wordBitsEquiv n.succ word))).val.testBit bit.val = _
  calc
    ((wordBitsEquiv n).symm
        (Fin.removeNth pivot (wordBitsEquiv n.succ word))).val.testBit bit.val =
        wordBitsEquiv n
          ((wordBitsEquiv n).symm
            (Fin.removeNth pivot (wordBitsEquiv n.succ word))) bit := rfl
    _ = Fin.removeNth pivot (wordBitsEquiv n.succ word) bit :=
      congrFun ((wordBitsEquiv n).apply_symm_apply _) bit
    _ = word.val.testBit (pivot.succAbove bit).val := rfl

/-- Reinsertion restores the selected bit at the pivot position. -/
@[simp] theorem wordRemoveEquiv_symm_testBit_pivot (pivot : Fin n.succ)
    (selector : Bool) (remainder : PlainAdder.Word n) :
    ((wordRemoveEquiv pivot).symm (selector, remainder)).val.testBit pivot.val =
      selector := by
  have h := wordRemoveEquiv_fst pivot
    ((wordRemoveEquiv pivot).symm (selector, remainder))
  simpa using h.symm

/-- Reinsertion restores every residual bit at its `succAbove` position. -/
@[simp] theorem wordRemoveEquiv_symm_testBit_succAbove
    (pivot : Fin n.succ) (selector : Bool)
    (remainder : PlainAdder.Word n) (bit : Fin n) :
    ((wordRemoveEquiv pivot).symm (selector, remainder)).val.testBit
        (pivot.succAbove bit).val = remainder.val.testBit bit.val := by
  have h := wordRemoveEquiv_snd_testBit pivot
    ((wordRemoveEquiv pivot).symm (selector, remainder)) bit
  simpa using h.symm

/-- Pack the clean comparison flag above the `n` low accumulator bits.  This
is the `(n+1)`-bit target word consumed by R.0's literal dirty-carry adder. -/
def flagTargetWordEquiv (n : Nat) :
    Bool × PlainAdder.Word n ≃ PlainAdder.Word n.succ :=
  ((Equiv.prodCongr finTwoEquiv.symm
      (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n)).trans
    (prodEquiv (m := 1) (n := n))).trans
    ((finCongr (congrArg (fun exponent : Nat => 2 ^ exponent) (by omega))).trans
      (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n.succ).symm)

/-- Numeric value of the packed flag/target word. -/
@[simp] theorem flagTargetWordEquiv_val (n : Nat) (flag : Bool)
    (targetWord : PlainAdder.Word n) :
    (flagTargetWordEquiv n (flag, targetWord)).val =
      (prodEquiv (m := 1) (n := n)
        (finTwoEquiv.symm flag,
          PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n targetWord)).val := by
  unfold flagTargetWordEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply]
  change ((PlainAdder.Schedule.PowerOfTwo.residueEncoding n.succ).decode
      (finCongr (congrArg (fun exponent : Nat => 2 ^ exponent) (by omega))
        (prodEquiv (m := 1) (n := n)
          (finTwoEquiv.symm flag,
            PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n targetWord)))).val = _
  rw [BinaryResidueEncoding.decode_val]
  rw [Nat.mod_eq_of_lt]
  · rfl
  · exact (finCongr
      (congrArg (fun exponent : Nat => 2 ^ exponent) (by omega))
      (prodEquiv (m := 1) (n := n)
        (finTwoEquiv.symm flag,
          PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n targetWord))).isLt

/-- Packing the clean flag above the accumulator leaves every low accumulator
bit at the same little-endian position. -/
theorem flagTargetWordEquiv_low_bit (n : Nat) (flag : Bool)
    (targetWord : PlainAdder.Word n) (bit : Fin n) :
    (flagTargetWordEquiv n (flag, targetWord)).val.testBit bit.val =
      targetWord.val.testBit bit.val := by
  rw [flagTargetWordEquiv_val]
  exact prodEquiv_testBit_right (m := 1) (n := n)
    (finTwoEquiv.symm flag)
    (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n targetWord) bit

/-- The final bit of the packed target is exactly the clean flag. -/
theorem flagTargetWordEquiv_high_bit (n : Nat) (flag : Bool)
    (targetWord : PlainAdder.Word n) :
    (flagTargetWordEquiv n (flag, targetWord)).val.testBit n = flag := by
  rw [flagTargetWordEquiv_val]
  have h := prodEquiv_testBit_left (m := 1) (n := n)
    (finTwoEquiv.symm flag)
    (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n targetWord) (0 : Fin 1)
  cases flag <;> simpa [finTwoEquiv] using h

/-- Erase only the unique zero-qubit environment next to the clean flag. -/
def flagLiteralBorrowedEquiv (n : Nat) :
    Bool × (LiteralBorrowed n).Index ≃ Bool where
  toFun := Prod.fst
  invFun := fun flag => (flag, 0)
  left_inv := fun state => Prod.ext rfl (Fin.eq_zero state.2).symm
  right_inv := fun _ => rfl

/-- Exact semantic identification used by the literal R.0 block.  The
accumulator and clean flag form its `(n+1)`-bit target, while the source word
itself is the `n`-bit dirty-carry register.  The zero-qubit environment is
erased only through the canonical unique-type equivalence. -/
def literalR0StateEquiv (n : Nat) :
    State n (LiteralBorrowed n) ≃
      (PlainAdder.Word n.succ × MAU.Addition.DirtyBorrowed.StraightforwardDirty n) :=
  (((((Equiv.refl (PlainAdder.Word n × PlainAdder.Word n)).prodCongr
      (flagLiteralBorrowedEquiv n)).trans
    (Equiv.prodAssoc (PlainAdder.Word n) (PlainAdder.Word n) Bool)).trans
    ((Equiv.refl (PlainAdder.Word n)).prodCongr
      (Equiv.prodComm (PlainAdder.Word n) Bool))).trans
    (Equiv.prodComm (PlainAdder.Word n) (Bool × PlainAdder.Word n))).trans
    (Equiv.prodCongr (flagTargetWordEquiv n)
      (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n))

/-- On the literal `2n+1` carrier, R.0 borrows the source word rather than a
third physical word. -/
@[simp] theorem literalR0StateEquiv_snd (n : Nat)
    (state : State n (LiteralBorrowed n)) :
    (literalR0StateEquiv n state).2 =
      PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n (source state) := by
  simp [literalR0StateEquiv, flagLiteralBorrowedEquiv, source]

/-- The other R.0 component is exactly the accumulator with the clean flag
packed above it. -/
@[simp] theorem literalR0StateEquiv_fst (n : Nat)
    (state : State n (LiteralBorrowed n)) :
    (literalR0StateEquiv n state).1 =
      flagTargetWordEquiv n (cleanFlag state, target state) := by
  simp [literalR0StateEquiv, flagLiteralBorrowedEquiv, cleanFlag, target]

/-- R.0's original binary layout, semantically relabelled onto the literal
HRS core without changing a wire or adding a tensor factor. -/
def literalR0Encoding (n : Nat) :
    BinaryLabelEncoding (State n (LiteralBorrowed n)) :=
  (MAU.Addition.DirtyBorrowed.straightforwardEncoding n).relabel
    (literalR0StateEquiv n)

/-- The literal R.0 carrier is exactly the HRS `2n+1` core. -/
@[simp] theorem literalR0Encoding_width (n : Nat) :
    (literalR0Encoding n).width = 2 * n + 1 := by
  exact MAU.Addition.DirtyBorrowed.straightforwardEncoding_width n

/-- Exact semantic-state to flat-basis layout of the literal HRS core. -/
def literalR0LabelEquiv (n : Nat) :
    State n (LiteralBorrowed n) ≃ Fin (2 ^ (literalR0Encoding n).width) :=
  (literalR0StateEquiv n).trans
    (MAU.Addition.DirtyBorrowed.straightforwardLabelEquiv n)

@[simp] theorem literalR0Encoding_encode (n : Nat)
    (state : State n (LiteralBorrowed n)) :
    (literalR0Encoding n).encode state = literalR0LabelEquiv n state :=
  rfl

/-- Register-typed direction of the complete literal HRS basis layout. -/
def literalR0IndexEquiv (n : Nat) :
    (Qubits (literalR0Encoding n).width).Index ≃
      (register n (LiteralBorrowed n)).Index :=
  (literalR0LabelEquiv n).symm

theorem literalR0IndexEquiv_encode (n : Nat)
    (state : State n (LiteralBorrowed n)) :
    literalR0IndexEquiv n ((literalR0Encoding n).encode state) = state := by
  change (literalR0LabelEquiv n).symm (literalR0LabelEquiv n state) = state
  exact Equiv.symm_apply_apply (literalR0LabelEquiv n) state

/-- Every literal encoded-bit gate list determines a total reversible
extension: execute the list forward and its self-inverse gates in reverse
order for the inverse. -/
def literalGateListPerm (n : Nat)
    (gates : List (EncodedBit.GateSpec (literalR0Encoding n))) :
    Equiv.Perm (State n (LiteralBorrowed n)) where
  toFun := EncodedBit.GateSpec.stepList gates
  invFun := EncodedBit.GateSpec.stepList gates.reverse
  left_inv := EncodedBit.GateSpec.stepList_reverse_stepList gates
  right_inv := by
    intro state
    simpa using
      (EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse state)

/-- Transport a compiled flat gate list onto the typed HRS register without
changing its physical schedule or resource trace. -/
def literalGateListCircuit (n : Nat)
    (gates : List (EncodedBit.GateSpec (literalR0Encoding n))) :
    UnitaryCircuit (register n (LiteralBorrowed n)) :=
  UnitaryCircuit.reindex (literalR0IndexEquiv n)
    (EncodedBit.GateSpec.programList gates)

/-- Basis action of the transported literal gate-list circuit. -/
theorem literalGateListCircuit_applyNormalized_ket (n : Nat)
    (gates : List (EncodedBit.GateSpec (literalR0Encoding n)))
    (state : State n (LiteralBorrowed n)) :
    (literalGateListCircuit n gates).applyNormalized
        (NormalizedVector.ket (R := register n (LiteralBorrowed n)) state) =
      NormalizedVector.ket
        (R := register n (LiteralBorrowed n))
        (literalGateListPerm n gates state) := by
  have hflat :=
    (EncodedBit.GateSpec.realizesList gates).apply_encoded_ket state
  have hreindexed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (literalR0IndexEquiv n)
    (EncodedBit.GateSpec.programList gates)
    ((literalR0Encoding n).encode state)
    ((literalR0Encoding n).encode
      (EncodedBit.GateSpec.stepList gates state)) hflat
  rw [literalR0IndexEquiv_encode, literalR0IndexEquiv_encode] at hreindexed
  exact hreindexed

/-- Operator equality for every transported literal gate list.  This derives
the strong total-permutation certificate from the same circuit that owns the
native event trace. -/
theorem literalGateListCircuit_matrix_eq (n : Nat)
    (gates : List (EncodedBit.GateSpec (literalR0Encoding n))) :
    (literalGateListCircuit n gates).matrix =
      UnitaryOperator.ofPerm (literalGateListPerm n gates).symm := by
  apply Subtype.ext
  apply Matrix.ext
  intro output input
  have hcircuit := literalGateListCircuit_applyNormalized_ket n gates input
  have hperm :
      (UnitaryOperator.ofPerm (literalGateListPerm n gates).symm).apply
          (NormalizedVector.ket
            (R := register n (LiteralBorrowed n)) input) =
        NormalizedVector.ket
          (R := register n (LiteralBorrowed n))
          (literalGateListPerm n gates input) := by
    rw [UnitaryOperator.ofPerm_apply_ket]
    rfl
  have heq := hcircuit.trans hperm.symm
  have hpoint := congrArg
    (fun state : NormalizedVector (register n (LiteralBorrowed n)) =>
      state output) heq
  simpa [UnitaryCircuit.applyNormalized, UnitaryOperator.apply,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using hpoint

/-- Semantic action of one literal R.0 addition after aliasing the source word
as dirty carry work. -/
def literalR0Step (n : Nat) (constant : PlainAdder.Word n.succ)
    (state : State n (LiteralBorrowed n)) : State n (LiteralBorrowed n) :=
  (literalR0StateEquiv n).symm
    ((literalR0StateEquiv n state).1 + constant,
      (literalR0StateEquiv n state).2)

/-- The aliased R.0 step restores the entire source word for every complete
basis label; the source is the dirty work and is never initialized. -/
@[simp] theorem literalR0Step_source (n : Nat)
    (constant : PlainAdder.Word n.succ)
    (state : State n (LiteralBorrowed n)) :
    source (literalR0Step n constant state) = source state := by
  apply (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n).injective
  rw [← literalR0StateEquiv_snd n]
  simp [literalR0Step]

/-- The actual X/CNOT/Toffoli R.0 circuit on the aliased HRS core. -/
abbrev literalR0Program (n : Nat) (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit (Qubits (literalR0Encoding n).width) :=
  MAU.Addition.DirtyBorrowed.straightforwardProgram n constant

/-- The wire-identical R.0 program realizes the aliased core transition. -/
theorem literalR0Program_realizes (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit.Realizes (literalR0Encoding n) (literalR0Program n constant)
      (literalR0Step n constant) := by
  constructor
  intro state
  have hstep :
      literalR0StateEquiv n (literalR0Step n constant state) =
        ((literalR0StateEquiv n state).1 + constant,
          (literalR0StateEquiv n state).2) := by
    simp [literalR0Step]
  change (MAU.Addition.DirtyBorrowed.straightforwardProgram n constant).applyNormalized
      (NormalizedVector.ket
        ((MAU.Addition.DirtyBorrowed.straightforwardEncoding n).encode
          (literalR0StateEquiv n state))) =
    NormalizedVector.ket
      ((MAU.Addition.DirtyBorrowed.straightforwardEncoding n).encode
        (literalR0StateEquiv n (literalR0Step n constant state)))
  rw [hstep]
  exact (MAU.Addition.DirtyBorrowed.straightforwardProgram_realizes n constant).apply_encoded_ket
    (literalR0StateEquiv n state)

/-- Exact Toffoli count of the aliased R.0 program. -/
theorem literalR0Program_toffoli_count_eq (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (literalR0Program n constant).eventCost = 2 * n * (n - 1) :=
  MAU.Addition.DirtyBorrowed.straightforwardProgram_toffoli_count_eq n constant

/-- Exact CNOT count of the same aliased R.0 program. -/
theorem literalR0Program_cnot_count_eq (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (literalR0Program n constant).eventCost =
      MAU.Addition.DirtyBorrowed.highCnotClosedForm constant n :=
  MAU.Addition.DirtyBorrowed.straightforwardProgram_cnot_count_eq n constant

/-- Exact X count of the same aliased R.0 program. -/
theorem literalR0Program_x_count_eq (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (literalR0Program n constant).eventCost =
      MAU.Addition.DirtyBorrowed.highXClosedForm constant n +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant 0 :=
  MAU.Addition.DirtyBorrowed.straightforwardProgram_x_count_eq n constant

/-- Exact `2n+1`-qubit binary layout for two HRS words and the clean
comparison flag.  It is the same physical wire order as the aliased R.0
adder: packed target/flag first, borrowed source word second. -/
abbrev literalSwapEncoding (n : Nat) :
    BinaryLabelEncoding (State n (LiteralBorrowed n)) :=
  literalR0Encoding n

/-- The concrete literal swap carrier has the actual HRS core width. -/
theorem literalSwapEncoding_width (n : Nat) :
    (literalSwapEncoding n).width = 2 * n + 1 := by
  exact literalR0Encoding_width n

/-- The source-word bit in the literal physical swap layout. -/
def literalSourceBit (n : Nat) (bit : Fin n) :
    EncodedBit (literalSwapEncoding n) :=
  (MAU.Addition.DirtyBorrowed.straightforwardDirtyBit n bit).relabel
    (literalR0StateEquiv n)

/-- The target-word bit in the literal physical swap layout. -/
def literalTargetBit (n : Nat) (bit : Fin n) :
    EncodedBit (literalSwapEncoding n) :=
  (MAU.Addition.DirtyBorrowed.straightforwardTargetBit n bit.castSucc).relabel
    (literalR0StateEquiv n)

/-- The untouched high target bit carrying the clean comparison flag. -/
def literalFlagBit (n : Nat) : EncodedBit (literalSwapEncoding n) :=
  (MAU.Addition.DirtyBorrowed.straightforwardTargetBit n (Fin.last n)).relabel
    (literalR0StateEquiv n)

/-- The two concrete HRS arithmetic words. -/
def literalSourceWord (n : Nat) :
    EncodedBit.Word (literalSwapEncoding n) n where
  bit := literalSourceBit n

/-- The second concrete HRS arithmetic word. -/
def literalTargetWord (n : Nat) :
    EncodedBit.Word (literalSwapEncoding n) n where
  bit := literalTargetBit n

/-- Readout of one source-word wire in the literal HRS layout. -/
@[simp] theorem literalSourceBit_get (n : Nat) (bit : Fin n)
    (state : State n (LiteralBorrowed n)) :
    (literalSourceBit n bit).get state =
      (source state).val.testBit bit.val := by
  change (MAU.Addition.DirtyBorrowed.straightforwardDirtyBit n bit).get
      (literalR0StateEquiv n state) = _
  rw [MAU.Addition.DirtyBorrowed.straightforwardDirtyBit_get,
    literalR0StateEquiv_snd]
  rfl

/-- Readout of one accumulator-word wire in the literal HRS layout. -/
@[simp] theorem literalTargetBit_get (n : Nat) (bit : Fin n)
    (state : State n (LiteralBorrowed n)) :
    (literalTargetBit n bit).get state =
      (target state).val.testBit bit.val := by
  change (MAU.Addition.DirtyBorrowed.straightforwardTargetBit n bit.castSucc).get
      (literalR0StateEquiv n state) = _
  rw [MAU.Addition.DirtyBorrowed.straightforwardTargetBit_get,
    literalR0StateEquiv_fst]
  exact flagTargetWordEquiv_low_bit n (cleanFlag state) (target state) bit

/-- Readout of the clean comparison flag in the shared R.0/swap layout. -/
@[simp] theorem literalFlagBit_get (n : Nat)
    (state : State n (LiteralBorrowed n)) :
    (literalFlagBit n).get state = cleanFlag state := by
  change (MAU.Addition.DirtyBorrowed.straightforwardTargetBit n (Fin.last n)).get
      (literalR0StateEquiv n state) = _
  rw [MAU.Addition.DirtyBorrowed.straightforwardTargetBit_get,
    literalR0StateEquiv_fst]
  exact flagTargetWordEquiv_high_bit n (cleanFlag state) (target state)

/-- Corresponding source and target wires are physically distinct. -/
theorem literalSourceTargetBit_wire_ne (n : Nat) (bit : Fin n) :
    (literalSourceBit n bit).wire ≠ (literalTargetBit n bit).wire := by
  exact (MAU.Addition.DirtyBorrowed.straightforwardTargetBit_wire_ne_dirtyBit
    n bit.castSucc bit).symm

/-- Distinct source-word indices occupy distinct physical wires. -/
theorem literalSourceBit_wire_ne (n : Nat) {left right : Fin n}
    (hne : left ≠ right) :
    (literalSourceBit n left).wire ≠ (literalSourceBit n right).wire := by
  exact MAU.Addition.DirtyBorrowed.straightforwardDirtyBit_wire_ne n hne

/-- Distinct target-word indices occupy distinct physical wires. -/
theorem literalTargetBit_wire_ne (n : Nat) {left right : Fin n}
    (hne : left ≠ right) :
    (literalTargetBit n left).wire ≠ (literalTargetBit n right).wire := by
  apply MAU.Addition.DirtyBorrowed.straightforwardTargetBit_wire_ne n
  intro heq
  apply hne
  apply Fin.ext
  simpa using congrArg Fin.val heq

/-- Any source-word wire is distinct from any target-word wire. -/
theorem literalSourceTargetBit_cross_wire_ne (n : Nat)
    (sourceBit targetBit : Fin n) :
    (literalSourceBit n sourceBit).wire ≠
      (literalTargetBit n targetBit).wire := by
  exact (MAU.Addition.DirtyBorrowed.straightforwardTargetBit_wire_ne_dirtyBit
    n targetBit.castSucc sourceBit).symm

/-- Every source-word wire is disjoint from the clean flag wire. -/
theorem literalSourceBit_wire_ne_flag (n : Nat) (bit : Fin n) :
    (literalSourceBit n bit).wire ≠ (literalFlagBit n).wire :=
  (MAU.Addition.DirtyBorrowed.straightforwardTargetBit_wire_ne_dirtyBit
    n (Fin.last n) bit).symm

/-- Every low target-word wire is disjoint from the clean flag wire. -/
theorem literalTargetBit_wire_ne_flag (n : Nat) (bit : Fin n) :
    (literalTargetBit n bit).wire ≠ (literalFlagBit n).wire := by
  apply MAU.Addition.DirtyBorrowed.straightforwardTargetBit_wire_ne n
  exact bit.castSucc_ne_last

/-! ## Selector-excluding dirty-carry carrier -/

/-- The selected source bit that controls one HRS modular-add stage. -/
def literalSelectedSourceBit {tail : Nat} (pivot : Fin tail.succ) :
    EncodedBit (literalR0Encoding tail.succ) :=
  literalSourceBit tail.succ pivot

/-- Source bit `pivot.succAbove bit`, used as dirty carry work while the
selected source bit itself remains exclusively a control. -/
def literalCarryDirtyBit {tail : Nat} (pivot : Fin tail.succ)
    (bit : Fin tail) : EncodedBit (literalR0Encoding tail.succ) :=
  literalSourceBit tail.succ (pivot.succAbove bit)

/-- The selector lens reads exactly the requested source-word bit. -/
@[simp] theorem literalSelectedSourceBit_get {tail : Nat}
    (pivot : Fin tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    (literalSelectedSourceBit pivot).get state =
      (source state).val.testBit pivot.val :=
  literalSourceBit_get tail.succ pivot state

/-- Every dirty-carry lens reads the corresponding non-selector source bit. -/
@[simp] theorem literalCarryDirtyBit_get {tail : Nat}
    (pivot : Fin tail.succ) (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    (literalCarryDirtyBit pivot bit).get state =
      (source state).val.testBit (pivot.succAbove bit).val :=
  literalSourceBit_get tail.succ (pivot.succAbove bit) state

/-- The physical dirty-carry lens agrees with the residual word produced by
the selector-removal equivalence. -/
theorem literalCarryDirtyBit_get_eq_removedWord {tail : Nat}
    (pivot : Fin tail.succ) (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    (literalCarryDirtyBit pivot bit).get state =
      (wordRemoveEquiv pivot (source state)).2.val.testBit bit.val := by
  rw [literalCarryDirtyBit_get, wordRemoveEquiv_snd_testBit]

/-- The selected control wire is excluded from every dirty-carry role. -/
theorem literalSelectedSourceBit_wire_ne_carryDirtyBit {tail : Nat}
    (pivot : Fin tail.succ) (bit : Fin tail) :
    (literalSelectedSourceBit pivot).wire ≠
      (literalCarryDirtyBit pivot bit).wire := by
  exact literalSourceBit_wire_ne tail.succ (Fin.ne_succAbove pivot bit)

/-- Reverse orientation of selector/dirty disjointness for gate predicates. -/
theorem literalCarryDirtyBit_wire_ne_selectedSourceBit {tail : Nat}
    (pivot : Fin tail.succ) (bit : Fin tail) :
    (literalCarryDirtyBit pivot bit).wire ≠
      (literalSelectedSourceBit pivot).wire :=
  (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot bit).symm

/-- Different residual indices occupy different physical source wires. -/
theorem literalCarryDirtyBit_wire_ne {tail : Nat}
    (pivot : Fin tail.succ) {left right : Fin tail} (hne : left ≠ right) :
    (literalCarryDirtyBit pivot left).wire ≠
      (literalCarryDirtyBit pivot right).wire := by
  exact literalSourceBit_wire_ne tail.succ
    (fun heq => hne (Fin.succAbove_right_injective heq))

/-- Every residual dirty-carry wire is disjoint from every accumulator wire. -/
theorem literalCarryDirtyBit_wire_ne_targetBit {tail : Nat}
    (pivot : Fin tail.succ) (dirty : Fin tail) (targetBit : Fin tail.succ) :
    (literalCarryDirtyBit pivot dirty).wire ≠
      (literalTargetBit tail.succ targetBit).wire :=
  literalSourceTargetBit_cross_wire_ne tail.succ
    (pivot.succAbove dirty) targetBit

/-- Every residual dirty-carry wire is disjoint from the clean flag. -/
theorem literalCarryDirtyBit_wire_ne_flag {tail : Nat}
    (pivot : Fin tail.succ) (bit : Fin tail) :
    (literalCarryDirtyBit pivot bit).wire ≠
      (literalFlagBit tail.succ).wire :=
  literalSourceBit_wire_ne_flag tail.succ (pivot.succAbove bit)

/-- The selector is disjoint from every accumulator bit. -/
theorem literalSelectedSourceBit_wire_ne_targetBit {tail : Nat}
    (pivot : Fin tail.succ) (targetBit : Fin tail.succ) :
    (literalSelectedSourceBit pivot).wire ≠
      (literalTargetBit tail.succ targetBit).wire :=
  literalSourceTargetBit_cross_wire_ne tail.succ pivot targetBit

/-- Reverse orientation of selector/accumulator disjointness. -/
theorem literalTargetBit_wire_ne_selectedSourceBit {tail : Nat}
    (pivot : Fin tail.succ) (targetBit : Fin tail.succ) :
    (literalTargetBit tail.succ targetBit).wire ≠
      (literalSelectedSourceBit pivot).wire :=
  (literalSelectedSourceBit_wire_ne_targetBit pivot targetBit).symm

/-- The selector is disjoint from the clean comparison flag. -/
theorem literalSelectedSourceBit_wire_ne_flag {tail : Nat}
    (pivot : Fin tail.succ) :
    (literalSelectedSourceBit pivot).wire ≠
      (literalFlagBit tail.succ).wire :=
  literalSourceBit_wire_ne_flag tail.succ pivot

/-- Flipping a residual source bit never changes the accumulator word. -/
@[simp] theorem literalCarryDirtyBit_flip_target {tail : Nat}
    (pivot : Fin tail.succ) (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    target ((literalCarryDirtyBit pivot bit).flip state) = target state := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro observed
  have hread := EncodedBit.get_flip_of_wire_ne
    (literalCarryDirtyBit pivot bit)
    (literalTargetBit tail.succ observed)
    (literalCarryDirtyBit_wire_ne_targetBit pivot bit observed) state
  simpa only [literalTargetBit_get] using hread

/-- Flipping one physical accumulator bit has exactly the ordinary word-bit
action on the accumulator projection. -/
@[simp] theorem literalTargetBit_flip_target (n : Nat) (bit : Fin n)
    (state : State n (LiteralBorrowed n)) :
    target ((literalTargetBit n bit).flip state) =
      (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).flip (target state) := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro observed
  rw [← literalTargetBit_get n observed]
  rw [← PlainAdder.Schedule.PowerOfTwo.wordBit_get n observed]
  by_cases heq : bit = observed
  · subst observed
    rw [EncodedBit.get_flip_self, EncodedBit.get_flip_self,
      literalTargetBit_get]
    simp only [PlainAdder.Schedule.PowerOfTwo.wordBit_get]
  · rw [EncodedBit.get_flip_of_wire_ne
        (literalTargetBit n bit) (literalTargetBit n observed)
        (literalTargetBit_wire_ne n heq),
      EncodedBit.get_flip_of_wire_ne
        (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)
        (PlainAdder.Schedule.PowerOfTwo.wordBit n observed)
        (MAU.Addition.DirtyBorrowed.straightforwardWordBit_wire_ne n heq),
      literalTargetBit_get]
    simp only [PlainAdder.Schedule.PowerOfTwo.wordBit_get]

/-- Flipping one literal accumulator wire is exactly replacement of the
accumulator by the corresponding fixed-width word-bit flip. -/
theorem literalTargetBit_flip_eq_withTarget (n : Nat) (bit : Fin n)
    (state : State n (LiteralBorrowed n)) :
    (literalTargetBit n bit).flip state =
      withTarget state
        ((PlainAdder.Schedule.PowerOfTwo.wordBit n bit).flip (target state)) := by
  apply Prod.ext
  · apply Prod.ext
    · apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
      intro observed
      have hread := EncodedBit.get_flip_of_wire_ne
        (literalTargetBit n bit) (literalSourceBit n observed)
        (literalSourceTargetBit_cross_wire_ne n observed bit).symm state
      simpa only [literalSourceBit_get, source, withTarget] using hread
    · simpa only [target, withTarget] using
        literalTargetBit_flip_target n bit state
  · apply Prod.ext
    · have hread := EncodedBit.get_flip_of_wire_ne
        (literalTargetBit n bit) (literalFlagBit n)
        (literalTargetBit_wire_ne_flag n bit) state
      simpa only [literalFlagBit_get, cleanFlag, withTarget] using hread
    · exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- Flipping the physical comparison-flag wire replaces only the logical
clean flag by its Boolean complement. -/
theorem literalFlagBit_flip_eq_withCleanFlag (n : Nat)
    (state : State n (LiteralBorrowed n)) :
    (literalFlagBit n).flip state =
      withCleanFlag state (!cleanFlag state) := by
  apply Prod.ext
  · apply Prod.ext
    · apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
      intro observed
      have hread := EncodedBit.get_flip_of_wire_ne
        (literalFlagBit n) (literalSourceBit n observed)
        (literalSourceBit_wire_ne_flag n observed).symm state
      simpa only [literalSourceBit_get, source, withCleanFlag] using hread
    · apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
      intro observed
      have hread := EncodedBit.get_flip_of_wire_ne
        (literalFlagBit n) (literalTargetBit n observed)
        (literalTargetBit_wire_ne_flag n observed).symm state
      simpa only [literalTargetBit_get, target, withCleanFlag] using hread
  · apply Prod.ext
    · have hread := EncodedBit.get_flip_self (literalFlagBit n) state
      simpa only [literalFlagBit_get, cleanFlag, withCleanFlag] using hread
    · exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- Recursive lower carry prefix on the selector-excluding physical carrier.
For `bit`, it uses residual source bits `0, ..., bit` as dirty work and only
accumulator bits at or below `bit`.  It intentionally stops before the top
accumulator bit; the selected terminal carry logic is a separate stage. -/
def selectedLowerCarryGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) (bit : Fin tail) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  match bit with
  | ⟨0, hzero⟩ =>
      if constant.val.testBit 0 then
        [EncodedBit.GateSpec.cnot
          (literalTargetBit tail.succ 0)
          (literalCarryDirtyBit pivot ⟨0, hzero⟩)
          (literalCarryDirtyBit_wire_ne_targetBit pivot ⟨0, hzero⟩ 0).symm]
      else
        []
  | ⟨index + 1, hindex⟩ =>
      let current : Fin tail := ⟨index + 1, hindex⟩
      let currentTarget : Fin tail.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self tail)⟩
      let previous : Fin tail := ⟨index, by omega⟩
      let previous_ne_current : previous ≠ current := by
        apply Fin.ne_of_val_ne
        dsimp [previous, current]
        omega
      let target := literalTargetBit tail.succ currentTarget
      let previousDirty := literalCarryDirtyBit pivot previous
      let currentDirty := literalCarryDirtyBit pivot current
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty target currentDirty
        (literalCarryDirtyBit_wire_ne_targetBit pivot previous currentTarget)
        (literalCarryDirtyBit_wire_ne pivot previous_ne_current)
        (literalCarryDirtyBit_wire_ne_targetBit pivot current currentTarget).symm
      (if constant.val.testBit current.val then
        [EncodedBit.GateSpec.cnot target currentDirty
            (literalCarryDirtyBit_wire_ne_targetBit
              pivot current currentTarget).symm,
          EncodedBit.GateSpec.x target]
       else
        []) ++
        [toffoli] ++
        selectedLowerCarryGates tail pivot constant ⟨index, by omega⟩ ++
        [toffoli] ++
        if constant.val.testBit current.val then
          [EncodedBit.GateSpec.x target]
        else
          []
termination_by bit.val
decreasing_by omega

/-- The selected lower carry prefix only borrows accumulator bits as controls;
every temporary target flip is undone before the prefix returns. -/
@[simp] theorem selectedLowerCarryGates_target (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    target (EncodedBit.GateSpec.stepList
      (selectedLowerCarryGates tail pivot constant bit) state) =
      target state := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · rw [show selectedLowerCarryGates tail pivot constant ⟨0, hbit⟩ =
            [EncodedBit.GateSpec.cnot
              (literalTargetBit tail.succ 0)
              (literalCarryDirtyBit pivot ⟨0, hbit⟩)
              (literalCarryDirtyBit_wire_ne_targetBit
                pivot ⟨0, hbit⟩ 0).symm] by
            simp [selectedLowerCarryGates, hc]]
        simp only [EncodedBit.GateSpec.stepList, id_eq,
          EncodedBit.GateSpec.step]
        unfold EncodedBit.cnotStep
        split
        · exact literalCarryDirtyBit_flip_target pivot ⟨0, hbit⟩ state
        · rfl
      · simp [selectedLowerCarryGates, hc,
          EncodedBit.GateSpec.stepList]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin tail := ⟨index + 1, hbit⟩
      let currentTarget : Fin tail.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self tail)⟩
      let previous : Fin tail := ⟨index, by omega⟩
      let targetBit := literalTargetBit tail.succ currentTarget
      let previousDirty := literalCarryDirtyBit pivot previous
      let currentDirty := literalCarryDirtyBit pivot current
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty targetBit currentDirty
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot previous currentTarget)
        (literalCarryDirtyBit_wire_ne pivot (by
          apply Fin.ne_of_val_ne
          dsimp [previous, current]
          omega))
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot current currentTarget).symm
      have toffoliTarget
          (input : State tail.succ (LiteralBorrowed tail.succ)) :
          target (toffoli.step input) = target input := by
        dsimp [toffoli]
        simp only [EncodedBit.GateSpec.step]
        unfold EncodedBit.toffoliStep
        split
        · exact literalCarryDirtyBit_flip_target pivot current input
        · rfl
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot targetBit currentDirty
          (literalCarryDirtyBit_wire_ne_targetBit
            pivot current currentTarget).symm
        let afterCnot := prefixCnot.step state
        let afterX := (EncodedBit.GateSpec.x targetBit).step afterCnot
        let afterFirstToffoli := toffoli.step afterX
        let afterCarry := EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant previous)
          afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hcnotTarget : target afterCnot = target state := by
          dsimp [afterCnot, prefixCnot]
          simp only [EncodedBit.GateSpec.step]
          unfold EncodedBit.cnotStep
          split
          · exact literalCarryDirtyBit_flip_target pivot current state
          · rfl
        have hxTarget : target afterX =
            (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ currentTarget).flip
              (target state) := by
          change target (targetBit.flip afterCnot) = _
          rw [literalTargetBit_flip_target, hcnotTarget]
        have hfirstTarget : target afterFirstToffoli = target afterX :=
          toffoliTarget afterX
        have hcarryTarget : target afterCarry = target afterFirstToffoli :=
          selectedLowerCarryGates_target tail pivot constant previous
            afterFirstToffoli
        have hsecondTarget : target afterSecondToffoli = target afterCarry :=
          toffoliTarget afterCarry
        rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x targetBit] ++ [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] ++ [EncodedBit.GateSpec.x targetBit] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change target (targetBit.flip afterSecondToffoli) = target state
        rw [literalTargetBit_flip_target, hsecondTarget, hcarryTarget,
          hfirstTarget, hxTarget]
        exact EncodedBit.flip_flip
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ currentTarget)
          (target state)
      · let afterFirstToffoli := toffoli.step state
        let afterCarry := EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant previous)
          afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hfirstTarget : target afterFirstToffoli = target state :=
          toffoliTarget state
        have hcarryTarget : target afterCarry = target afterFirstToffoli :=
          selectedLowerCarryGates_target tail pivot constant previous
            afterFirstToffoli
        have hsecondTarget : target afterSecondToffoli = target afterCarry :=
          toffoliTarget afterCarry
        rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change target afterSecondToffoli = target state
        rw [hsecondTarget, hcarryTarget, hfirstTarget]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- A selected carry prefix never writes a residual dirty bit above its own
output.  This isolates the unknown higher dirty value while a lower carry is
computed. -/
theorem selectedLowerCarryGates_higherDirty_get (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit observed : Fin tail) (hlt : bit.val < observed.val)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    (literalCarryDirtyBit pivot observed).get
        (EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant bit) state) =
      (literalCarryDirtyBit pivot observed).get state := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · rw [show selectedLowerCarryGates tail pivot constant ⟨0, hbit⟩ =
            [EncodedBit.GateSpec.cnot
              (literalTargetBit tail.succ 0)
              (literalCarryDirtyBit pivot ⟨0, hbit⟩)
              (literalCarryDirtyBit_wire_ne_targetBit
                pivot ⟨0, hbit⟩ 0).symm] by
            simp [selectedLowerCarryGates, hc]]
        simp only [EncodedBit.GateSpec.stepList, id_eq,
          EncodedBit.GateSpec.step]
        exact EncodedBit.cnotStep_get_of_target_ne
          (literalTargetBit tail.succ 0)
          (literalCarryDirtyBit pivot ⟨0, hbit⟩)
          (literalCarryDirtyBit pivot observed)
          (literalCarryDirtyBit_wire_ne pivot (by
            apply Fin.ne_of_val_ne
            omega)) state
      · simp [selectedLowerCarryGates, hc,
          EncodedBit.GateSpec.stepList]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin tail := ⟨index + 1, hbit⟩
      let currentTarget : Fin tail.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self tail)⟩
      let previous : Fin tail := ⟨index, by omega⟩
      let targetBit := literalTargetBit tail.succ currentTarget
      let previousDirty := literalCarryDirtyBit pivot previous
      let currentDirty := literalCarryDirtyBit pivot current
      let observedDirty := literalCarryDirtyBit pivot observed
      have hcurrentLt : current.val < observed.val := by
        simpa [current] using hlt
      have hpreviousLt : previous.val < observed.val := by
        exact lt_trans (by simp [previous, current]) hcurrentLt
      have hcurrentObserved : current ≠ observed := by
        apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt hcurrentLt
      have hcurrentDirtyObserved :
          currentDirty.wire ≠ observedDirty.wire :=
        literalCarryDirtyBit_wire_ne pivot hcurrentObserved
      have htargetObserved : targetBit.wire ≠ observedDirty.wire :=
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot observed currentTarget).symm
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty targetBit currentDirty
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot previous currentTarget)
        (literalCarryDirtyBit_wire_ne pivot (by
          apply Fin.ne_of_val_ne
          dsimp [previous, current]
          omega))
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot current currentTarget).symm
      have toffoliGet
          (input : State tail.succ (LiteralBorrowed tail.succ)) :
          observedDirty.get (toffoli.step input) = observedDirty.get input := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_of_target_ne
          previousDirty targetBit currentDirty observedDirty
          hcurrentDirtyObserved input
      have xGet
          (input : State tail.succ (LiteralBorrowed tail.succ)) :
          observedDirty.get
              ((EncodedBit.GateSpec.x targetBit).step input) =
            observedDirty.get input := by
        change observedDirty.get (targetBit.flip input) = observedDirty.get input
        exact EncodedBit.get_flip_of_wire_ne targetBit observedDirty
          htargetObserved input
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot targetBit currentDirty
          (literalCarryDirtyBit_wire_ne_targetBit
            pivot current currentTarget).symm
        let afterCnot := prefixCnot.step state
        let afterX := (EncodedBit.GateSpec.x targetBit).step afterCnot
        let afterFirstToffoli := toffoli.step afterX
        let afterCarry := EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant previous)
          afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hcnotGet : observedDirty.get afterCnot = observedDirty.get state := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_of_target_ne targetBit currentDirty
            observedDirty hcurrentDirtyObserved state
        have hxFirstGet : observedDirty.get afterX = observedDirty.get afterCnot :=
          xGet afterCnot
        have hfirstGet : observedDirty.get afterFirstToffoli =
            observedDirty.get afterX := toffoliGet afterX
        have hcarryGet : observedDirty.get afterCarry =
            observedDirty.get afterFirstToffoli :=
          selectedLowerCarryGates_higherDirty_get tail pivot constant
            previous observed hpreviousLt afterFirstToffoli
        have hsecondGet : observedDirty.get afterSecondToffoli =
            observedDirty.get afterCarry := toffoliGet afterCarry
        rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x targetBit] ++ [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] ++ [EncodedBit.GateSpec.x targetBit] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change observedDirty.get
            ((EncodedBit.GateSpec.x targetBit).step afterSecondToffoli) =
          observedDirty.get state
        rw [xGet, hsecondGet, hcarryGet, hfirstGet, hxFirstGet, hcnotGet]
      · let afterFirstToffoli := toffoli.step state
        let afterCarry := EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant previous)
          afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hfirstGet : observedDirty.get afterFirstToffoli =
            observedDirty.get state := toffoliGet state
        have hcarryGet : observedDirty.get afterCarry =
            observedDirty.get afterFirstToffoli :=
          selectedLowerCarryGates_higherDirty_get tail pivot constant
            previous observed hpreviousLt afterFirstToffoli
        have hsecondGet : observedDirty.get afterSecondToffoli =
            observedDirty.get afterCarry := toffoliGet afterCarry
        rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change observedDirty.get afterSecondToffoli = observedDirty.get state
        rw [hsecondGet, hcarryGet, hfirstGet]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- Classical carry entering accumulator bit `bit+1`, computed only from the
low accumulator bits and the supplied constant. -/
def selectedLowerCarryToggle (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ))
    (bit : Fin tail) : Bool :=
  Nat.BinaryArithmetic.natAddCarry
    (target state).val constant.val (bit.val + 1)

/-- The selected physical carry prefix toggles its current residual source bit
by exactly the classical low-word carry, independently of every dirty input
value. -/
theorem selectedLowerCarryGates_currentDirty_get (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    (literalCarryDirtyBit pivot bit).get
        (EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant bit) state) =
      ((literalCarryDirtyBit pivot bit).get state ^^
        selectedLowerCarryToggle tail constant state bit) := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · rw [show selectedLowerCarryGates tail pivot constant ⟨0, hbit⟩ =
            [EncodedBit.GateSpec.cnot
              (literalTargetBit tail.succ 0)
              (literalCarryDirtyBit pivot ⟨0, hbit⟩)
              (literalCarryDirtyBit_wire_ne_targetBit
                pivot ⟨0, hbit⟩ 0).symm] by
            simp [selectedLowerCarryGates, hc]]
        simp only [EncodedBit.GateSpec.stepList, id_eq,
          EncodedBit.GateSpec.step]
        rw [EncodedBit.cnotStep_get_target]
        simp [selectedLowerCarryToggle,
          Nat.BinaryArithmetic.natAddCarry, hc, Bool.carry]
      · simp [selectedLowerCarryGates, hc,
          EncodedBit.GateSpec.stepList, selectedLowerCarryToggle,
          Nat.BinaryArithmetic.natAddCarry, Bool.carry]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin tail := ⟨index + 1, hbit⟩
      let currentTarget : Fin tail.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self tail)⟩
      let previous : Fin tail := ⟨index, by omega⟩
      let targetBit := literalTargetBit tail.succ currentTarget
      let previousDirty := literalCarryDirtyBit pivot previous
      let currentDirty := literalCarryDirtyBit pivot current
      have hpreviousCurrent : previous ≠ current := by
        apply Fin.ne_of_val_ne
        dsimp [previous, current]
        omega
      have hpreviousCurrentWire :
          previousDirty.wire ≠ currentDirty.wire :=
        literalCarryDirtyBit_wire_ne pivot hpreviousCurrent
      have htargetCurrentWire : targetBit.wire ≠ currentDirty.wire :=
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot current currentTarget).symm
      have htargetPreviousWire : targetBit.wire ≠ previousDirty.wire :=
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot previous currentTarget).symm
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty targetBit currentDirty
        htargetPreviousWire.symm hpreviousCurrentWire htargetCurrentWire
      have toffoliCurrent
          (input : State tail.succ (LiteralBorrowed tail.succ)) :
          currentDirty.get (toffoli.step input) =
            (currentDirty.get input ^^
              (previousDirty.get input && targetBit.get input)) := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_target _ _ _ input
      have toffoliPrevious
          (input : State tail.succ (LiteralBorrowed tail.succ)) :
          previousDirty.get (toffoli.step input) =
            previousDirty.get input := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
          hpreviousCurrentWire.symm input
      have toffoliTargetGet
          (input : State tail.succ (LiteralBorrowed tail.succ)) :
          targetBit.get (toffoli.step input) = targetBit.get input := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
          htargetCurrentWire.symm input
      have toffoliTargetWord
          (input : State tail.succ (LiteralBorrowed tail.succ)) :
          target (toffoli.step input) = target input := by
        dsimp [toffoli]
        simp only [EncodedBit.GateSpec.step]
        unfold EncodedBit.toffoliStep
        split
        · exact literalCarryDirtyBit_flip_target pivot current input
        · rfl
      have hcarryRecurrence :
          selectedLowerCarryToggle tail constant state current =
            Bool.carry (targetBit.get state)
              (constant.val.testBit current.val)
              (selectedLowerCarryToggle tail constant state previous) := by
        simp [selectedLowerCarryToggle, targetBit, currentTarget, current,
          previous, Nat.BinaryArithmetic.natAddCarry]
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot targetBit currentDirty
          htargetCurrentWire
        let afterCnot := prefixCnot.step state
        let afterX := (EncodedBit.GateSpec.x targetBit).step afterCnot
        let afterFirstToffoli := toffoli.step afterX
        let afterCarry := EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant previous)
          afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hcnotCurrent : currentDirty.get afterCnot =
            (currentDirty.get state ^^ targetBit.get state) := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_target targetBit currentDirty state
        have hcnotPrevious : previousDirty.get afterCnot =
            previousDirty.get state := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_of_target_ne targetBit currentDirty
            previousDirty hpreviousCurrentWire.symm state
        have hcnotTargetGet : targetBit.get afterCnot = targetBit.get state := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_of_target_ne targetBit currentDirty
            targetBit htargetCurrentWire.symm state
        have hcnotTargetWord : target afterCnot = target state := by
          dsimp [afterCnot, prefixCnot]
          simp only [EncodedBit.GateSpec.step]
          unfold EncodedBit.cnotStep
          split
          · exact literalCarryDirtyBit_flip_target pivot current state
          · rfl
        have hxCurrent : currentDirty.get afterX =
            currentDirty.get afterCnot := by
          change currentDirty.get (targetBit.flip afterCnot) = _
          exact EncodedBit.get_flip_of_wire_ne targetBit currentDirty
            htargetCurrentWire afterCnot
        have hxPrevious : previousDirty.get afterX =
            previousDirty.get afterCnot := by
          change previousDirty.get (targetBit.flip afterCnot) = _
          exact EncodedBit.get_flip_of_wire_ne targetBit previousDirty
            htargetPreviousWire afterCnot
        have hxTargetGet : targetBit.get afterX = !targetBit.get afterCnot := by
          change targetBit.get (targetBit.flip afterCnot) = _
          exact EncodedBit.get_flip_self targetBit afterCnot
        have hfirstCurrent : currentDirty.get afterFirstToffoli =
            (currentDirty.get afterX ^^
              (previousDirty.get afterX && targetBit.get afterX)) :=
          toffoliCurrent afterX
        have hfirstPrevious : previousDirty.get afterFirstToffoli =
            previousDirty.get afterX := toffoliPrevious afterX
        have hfirstTargetGet : targetBit.get afterFirstToffoli =
            targetBit.get afterX := toffoliTargetGet afterX
        have hcarryCurrent : currentDirty.get afterCarry =
            currentDirty.get afterFirstToffoli :=
          selectedLowerCarryGates_higherDirty_get tail pivot constant
            previous current (by dsimp [previous, current]; omega)
            afterFirstToffoli
        have hcarryPrevious : previousDirty.get afterCarry =
            (previousDirty.get afterFirstToffoli ^^
              selectedLowerCarryToggle tail constant afterFirstToffoli
                previous) :=
          selectedLowerCarryGates_currentDirty_get tail pivot constant
            previous afterFirstToffoli
        have hcarryTargetGet : targetBit.get afterCarry =
            targetBit.get afterFirstToffoli := by
          dsimp [targetBit]
          simp only [literalTargetBit_get]
          rw [selectedLowerCarryGates_target]
        have hafterXTarget : target afterX =
            (PlainAdder.Schedule.PowerOfTwo.wordBit
              tail.succ currentTarget).flip (target state) := by
          change target (targetBit.flip afterCnot) = _
          rw [literalTargetBit_flip_target, hcnotTargetWord]
        have hafterFirstTarget : target afterFirstToffoli = target afterX :=
          toffoliTargetWord afterX
        have hlowerCarry :
            selectedLowerCarryToggle tail constant afterFirstToffoli previous =
              selectedLowerCarryToggle tail constant state previous := by
          unfold selectedLowerCarryToggle
          apply MAU.Addition.DirtyBorrowed.natAddCarry_congr_left_of_testBit_eq_lt
          intro low hlow
          rw [hafterFirstTarget, hafterXTarget]
          let lowBit : Fin tail.succ := ⟨low, by
            dsimp [previous] at hlow
            omega⟩
          have hne : currentTarget ≠ lowBit := by
            apply Fin.ne_of_val_ne
            have hlowCurrent : low < current.val := by
              dsimp [previous, current] at hlow ⊢
              omega
            dsimp [currentTarget, lowBit]
            exact (Nat.ne_of_lt hlowCurrent).symm
          simpa [PlainAdder.Schedule.PowerOfTwo.wordBit_get] using
            (EncodedBit.get_flip_of_wire_ne
              (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ currentTarget)
              (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ lowBit)
              (MAU.Addition.DirtyBorrowed.straightforwardWordBit_wire_ne
                tail.succ hne) (target state))
        have hsecondCurrent : currentDirty.get afterSecondToffoli =
            (currentDirty.get afterCarry ^^
              (previousDirty.get afterCarry && targetBit.get afterCarry)) :=
          toffoliCurrent afterCarry
        rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x targetBit] ++ [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] ++ [EncodedBit.GateSpec.x targetBit] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change currentDirty.get
            ((EncodedBit.GateSpec.x targetBit).step afterSecondToffoli) =
          (currentDirty.get state ^^
            selectedLowerCarryToggle tail constant state current)
        rw [show currentDirty.get
            ((EncodedBit.GateSpec.x targetBit).step afterSecondToffoli) =
              currentDirty.get afterSecondToffoli by
          change currentDirty.get (targetBit.flip afterSecondToffoli) = _
          exact EncodedBit.get_flip_of_wire_ne targetBit currentDirty
            htargetCurrentWire afterSecondToffoli]
        rw [hsecondCurrent, hcarryCurrent, hcarryPrevious, hcarryTargetGet,
          hfirstCurrent, hfirstPrevious, hfirstTargetGet, hxCurrent,
          hxPrevious, hxTargetGet, hcnotCurrent, hcnotPrevious,
          hcnotTargetGet, hlowerCarry]
        rw [hcarryRecurrence, hc]
        cases currentDirty.get state <;>
          cases previousDirty.get state <;>
          cases targetBit.get state <;>
          cases selectedLowerCarryToggle tail constant state previous <;> rfl
      · have hcFalse : constant.val.testBit current.val = false :=
          Bool.eq_false_of_not_eq_true hc
        let afterFirstToffoli := toffoli.step state
        let afterCarry := EncodedBit.GateSpec.stepList
          (selectedLowerCarryGates tail pivot constant previous)
          afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hfirstCurrent : currentDirty.get afterFirstToffoli =
            (currentDirty.get state ^^
              (previousDirty.get state && targetBit.get state)) :=
          toffoliCurrent state
        have hfirstPrevious : previousDirty.get afterFirstToffoli =
            previousDirty.get state := toffoliPrevious state
        have hfirstTargetGet : targetBit.get afterFirstToffoli =
            targetBit.get state := toffoliTargetGet state
        have hcarryCurrent : currentDirty.get afterCarry =
            currentDirty.get afterFirstToffoli :=
          selectedLowerCarryGates_higherDirty_get tail pivot constant
            previous current (by dsimp [previous, current]; omega)
            afterFirstToffoli
        have hcarryPrevious : previousDirty.get afterCarry =
            (previousDirty.get afterFirstToffoli ^^
              selectedLowerCarryToggle tail constant afterFirstToffoli
                previous) :=
          selectedLowerCarryGates_currentDirty_get tail pivot constant
            previous afterFirstToffoli
        have hcarryTargetGet : targetBit.get afterCarry =
            targetBit.get afterFirstToffoli := by
          dsimp [targetBit]
          simp only [literalTargetBit_get]
          rw [selectedLowerCarryGates_target]
        have hafterFirstTarget : target afterFirstToffoli = target state :=
          toffoliTargetWord state
        have hlowerCarry :
            selectedLowerCarryToggle tail constant afterFirstToffoli previous =
              selectedLowerCarryToggle tail constant state previous := by
          unfold selectedLowerCarryToggle
          rw [hafterFirstTarget]
        have hsecondCurrent : currentDirty.get afterSecondToffoli =
            (currentDirty.get afterCarry ^^
              (previousDirty.get afterCarry && targetBit.get afterCarry)) :=
          toffoliCurrent afterCarry
        rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change currentDirty.get afterSecondToffoli =
          (currentDirty.get state ^^
            selectedLowerCarryToggle tail constant state current)
        rw [hsecondCurrent, hcarryCurrent, hcarryPrevious, hcarryTargetGet,
          hfirstCurrent, hfirstPrevious, hfirstTargetGet, hlowerCarry]
        rw [hcarryRecurrence, hcFalse]
        cases currentDirty.get state <;>
          cases previousDirty.get state <;>
          cases targetBit.get state <;>
          cases selectedLowerCarryToggle tail constant state previous <;> rfl
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- Every gate in a selector-excluding carry prefix is disjoint from any
strictly higher accumulator bit.  This lets the prefix commute through the
controlled flip that writes its output bit. -/
theorem selectedLowerCarryGates_forall_bitDisjoint_target_of_lt (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) (observed : Fin tail.succ)
    (hlt : bit.val < observed.val) :
    (selectedLowerCarryGates tail pivot constant bit).Forall
      (EncodedBit.GateSpec.bitDisjoint
        (literalTargetBit tail.succ observed)) := by
  match bit with
  | ⟨0, hbit⟩ =>
      have hzeroObserved : (0 : Fin tail.succ) ≠ observed := by
        apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt hlt
      by_cases hc : constant.val.testBit 0
      · simp [selectedLowerCarryGates, hc,
          EncodedBit.GateSpec.bitDisjoint,
          literalTargetBit_wire_ne tail.succ hzeroObserved,
          literalCarryDirtyBit_wire_ne_targetBit pivot ⟨0, hbit⟩ observed]
      · simp [selectedLowerCarryGates, hc]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin tail := ⟨index + 1, hbit⟩
      let currentTarget : Fin tail.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self tail)⟩
      let previous : Fin tail := ⟨index, by omega⟩
      let targetBit := literalTargetBit tail.succ currentTarget
      let previousDirty := literalCarryDirtyBit pivot previous
      let currentDirty := literalCarryDirtyBit pivot current
      have hcurrentObserved : currentTarget ≠ observed := by
        apply Fin.ne_of_val_ne
        dsimp [currentTarget, current]
        exact Nat.ne_of_lt hlt
      have hpreviousObserved : previous.val < observed.val := by
        exact lt_trans (by simp [previous]) hlt
      have htargetObserved : targetBit.wire ≠
          (literalTargetBit tail.succ observed).wire :=
        literalTargetBit_wire_ne tail.succ hcurrentObserved
      have hpreviousDirtyObserved : previousDirty.wire ≠
          (literalTargetBit tail.succ observed).wire :=
        literalCarryDirtyBit_wire_ne_targetBit pivot previous observed
      have hcurrentDirtyObserved : currentDirty.wire ≠
          (literalTargetBit tail.succ observed).wire :=
        literalCarryDirtyBit_wire_ne_targetBit pivot current observed
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty targetBit currentDirty
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot previous currentTarget)
        (literalCarryDirtyBit_wire_ne pivot (by
          apply Fin.ne_of_val_ne
          dsimp [previous, current]
          omega))
        (literalCarryDirtyBit_wire_ne_targetBit
          pivot current currentTarget).symm
      have htoffoli : EncodedBit.GateSpec.bitDisjoint
          (literalTargetBit tail.succ observed) toffoli := by
        exact ⟨hpreviousDirtyObserved, htargetObserved,
          hcurrentDirtyObserved⟩
      have hrecursive :=
        selectedLowerCarryGates_forall_bitDisjoint_target_of_lt
          tail pivot constant previous observed hpreviousObserved
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot targetBit currentDirty
          (literalCarryDirtyBit_wire_ne_targetBit
            pivot current currentTarget).symm
        have hprefix : EncodedBit.GateSpec.bitDisjoint
            (literalTargetBit tail.succ observed) prefixCnot :=
          ⟨htargetObserved, hcurrentDirtyObserved⟩
        have hx : EncodedBit.GateSpec.bitDisjoint
            (literalTargetBit tail.succ observed)
            (EncodedBit.GateSpec.x targetBit) := htargetObserved
        rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x targetBit] ++ [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] ++ [EncodedBit.GateSpec.x targetBit] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp [hprefix, hx, htoffoli, hrecursive]
      · rw [show selectedLowerCarryGates tail pivot constant
            ⟨index + 1, hbit⟩ =
            [toffoli] ++
              selectedLowerCarryGates tail pivot constant previous ++
              [toffoli] by
          simp [selectedLowerCarryGates, current, currentTarget, previous,
            targetBit, previousDirty, currentDirty, toffoli, hc]]
        simp [htoffoli, hrecursive]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- The selected lower carry prefix has exactly the same strict primitive
event schedule as the corresponding already-verified R.0 carry prefix. -/
theorem selectedLowerCarryGates_eventTrace_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    (selectedLowerCarryGates tail pivot constant bit).map
        EncodedBit.GateSpec.event =
      (MAU.Addition.DirtyBorrowed.straightforwardCarryGates
        tail constant bit).map EncodedBit.GateSpec.event := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · simp [selectedLowerCarryGates,
          MAU.Addition.DirtyBorrowed.straightforwardCarryGates,
          EncodedBit.GateSpec.event, hc]
      · simp [selectedLowerCarryGates,
          MAU.Addition.DirtyBorrowed.straightforwardCarryGates,
          hc]
  | ⟨index + 1, hbit⟩ =>
      let previous : Fin tail := ⟨index, by omega⟩
      have ih := selectedLowerCarryGates_eventTrace_eq
        tail pivot constant previous
      by_cases hc : constant.val.testBit (index + 1)
      · simp [selectedLowerCarryGates,
          MAU.Addition.DirtyBorrowed.straightforwardCarryGates,
          EncodedBit.GateSpec.event, previous, hc, ih]
      · simp [selectedLowerCarryGates,
          MAU.Addition.DirtyBorrowed.straightforwardCarryGates,
          EncodedBit.GateSpec.event, previous, hc, ih]
termination_by bit.val
decreasing_by omega

/-- The carry prefix never reads or writes its excluded selector wire. -/
theorem selectedLowerCarryGates_forall_bitDisjoint_selector (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    (selectedLowerCarryGates tail pivot constant bit).Forall
      (EncodedBit.GateSpec.bitDisjoint
        (literalSelectedSourceBit pivot)) := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · simp [selectedLowerCarryGates, hc,
          EncodedBit.GateSpec.bitDisjoint,
          literalTargetBit_wire_ne_selectedSourceBit,
          literalCarryDirtyBit_wire_ne_selectedSourceBit]
      · simp [selectedLowerCarryGates, hc]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin tail := ⟨index + 1, hbit⟩
      let previous : Fin tail := ⟨index, by omega⟩
      have ih := selectedLowerCarryGates_forall_bitDisjoint_selector
        tail pivot constant previous
      by_cases hc : constant.val.testBit (index + 1)
      · simp [selectedLowerCarryGates, previous, hc, ih,
          EncodedBit.GateSpec.bitDisjoint,
          literalTargetBit_wire_ne_selectedSourceBit,
          literalCarryDirtyBit_wire_ne_selectedSourceBit]
      · simp [selectedLowerCarryGates, previous, hc, ih,
          EncodedBit.GateSpec.bitDisjoint,
          literalTargetBit_wire_ne_selectedSourceBit,
          literalCarryDirtyBit_wire_ne_selectedSourceBit]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- The lower carry prefix also leaves the clean comparison flag completely
untouched, reserving it for the terminal selected-copy layer. -/
theorem selectedLowerCarryGates_forall_bitDisjoint_flag (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    (selectedLowerCarryGates tail pivot constant bit).Forall
      (EncodedBit.GateSpec.bitDisjoint (literalFlagBit tail.succ)) := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · simp [selectedLowerCarryGates, hc,
          EncodedBit.GateSpec.bitDisjoint,
          literalTargetBit_wire_ne_flag,
          literalCarryDirtyBit_wire_ne_flag]
      · simp [selectedLowerCarryGates, hc]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin tail := ⟨index + 1, hbit⟩
      let previous : Fin tail := ⟨index, by omega⟩
      have ih := selectedLowerCarryGates_forall_bitDisjoint_flag
        tail pivot constant previous
      by_cases hc : constant.val.testBit (index + 1)
      · simp [selectedLowerCarryGates, previous, hc, ih,
          EncodedBit.GateSpec.bitDisjoint,
          literalTargetBit_wire_ne_flag,
          literalCarryDirtyBit_wire_ne_flag]
      · simp [selectedLowerCarryGates, previous, hc, ih,
          EncodedBit.GateSpec.bitDisjoint,
          literalTargetBit_wire_ne_flag,
          literalCarryDirtyBit_wire_ne_flag]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- A gate list disjoint from one observed bit preserves that bit's readout. -/
theorem stepList_get_of_forall_bitDisjoint
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding))
    (observed : EncodedBit encoding)
    (h : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint observed gate)
    (state : Data) :
    observed.get (EncodedBit.GateSpec.stepList gates state) =
      observed.get state := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
      simp only [EncodedBit.GateSpec.stepList]
      rw [ih (fun next hnext => h next (by simp [hnext]))]
      exact EncodedBit.GateSpec.step_get_of_bitDisjoint
        gate observed (h gate (by simp)) state

/-- Actual compiled lower carry-prefix circuit. -/
def selectedLowerCarryProgram (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) (bit : Fin tail) :
    UnitaryCircuit (Qubits (literalR0Encoding tail.succ).width) :=
  EncodedBit.GateSpec.programList
    (selectedLowerCarryGates tail pivot constant bit)

/-- The compiled prefix realizes its literal folded encoded-bit action. -/
theorem selectedLowerCarryProgram_realizes (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (selectedLowerCarryProgram tail pivot constant bit)
      (EncodedBit.GateSpec.stepList
        (selectedLowerCarryGates tail pivot constant bit)) :=
  EncodedBit.GateSpec.realizesList
    (selectedLowerCarryGates tail pivot constant bit)

/-- Exact Toffoli count of the actual selector-excluding carry prefix. -/
theorem selectedLowerCarryProgram_toffoli_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (selectedLowerCarryProgram tail pivot constant bit).eventCost =
      2 * bit.val := by
  rw [selectedLowerCarryProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  calc
    ((selectedLowerCarryGates tail pivot constant bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
        ((MAU.Addition.DirtyBorrowed.straightforwardCarryGates
          tail constant bit).map
            EncodedBit.GateSpec.toffoliMultiplicity).sum := by
      apply EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
      exact selectedLowerCarryGates_eventTrace_eq tail pivot constant bit
    _ = 2 * bit.val :=
      MAU.Addition.DirtyBorrowed.straightforwardCarryGates_toffoliMultiplicity_sum
        tail constant bit

/-- Exact CNOT count of the actual selector-excluding carry prefix. -/
theorem selectedLowerCarryProgram_cnot_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (selectedLowerCarryProgram tail pivot constant bit).eventCost =
      MAU.Addition.DirtyBorrowed.carryCnotClosedForm
        constant (bit.val + 1) := by
  rw [selectedLowerCarryProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  calc
    ((selectedLowerCarryGates tail pivot constant bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
        ((MAU.Addition.DirtyBorrowed.straightforwardCarryGates
          tail constant bit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum := by
      apply EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
      exact selectedLowerCarryGates_eventTrace_eq tail pivot constant bit
    _ = MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (bit.val + 1) :=
      MAU.Addition.DirtyBorrowed.straightforwardCarryGates_cnotMultiplicity_sum
        tail constant bit

/-- Exact X count of the actual selector-excluding carry prefix. -/
theorem selectedLowerCarryProgram_x_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "x"))
        (selectedLowerCarryProgram tail pivot constant bit).eventCost =
      MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val := by
  rw [selectedLowerCarryProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  calc
    ((selectedLowerCarryGates tail pivot constant bit).map
        EncodedBit.GateSpec.xMultiplicity).sum =
        ((MAU.Addition.DirtyBorrowed.straightforwardCarryGates
          tail constant bit).map
            EncodedBit.GateSpec.xMultiplicity).sum := by
      apply EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
      exact selectedLowerCarryGates_eventTrace_eq tail pivot constant bit
    _ = MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val :=
      MAU.Addition.DirtyBorrowed.straightforwardCarryGates_xMultiplicity_sum
        tail constant bit

/-! ## Source-controlled fixed-width addition -/

/-- One non-low output bit of a constant addition controlled by the selected
source bit.  Only the two dirty-copy gates and the known constant-bit flip are
controlled; the carry compute/uncompute network remains selector-disjoint. -/
def sourceControlledOutputBitGates (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  let carry := selectedLowerCarryGates tail pivot constant bit
  let selector := literalSelectedSourceBit pivot
  let targetBit := literalTargetBit tail.succ bit.succ
  let dirty := literalCarryDirtyBit pivot bit
  let copy := EncodedBit.GateSpec.toffoli selector dirty targetBit
    (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot bit)
    (literalSelectedSourceBit_wire_ne_targetBit pivot bit.succ)
    (literalCarryDirtyBit_wire_ne_targetBit pivot bit bit.succ)
  let constantCopy := EncodedBit.GateSpec.cnot selector targetBit
    (literalSelectedSourceBit_wire_ne_targetBit pivot bit.succ)
  let middle := [copy] ++ carry.reverse ++ [copy]
  carry ++ middle ++
    if constant.val.testBit bit.succ.val then
      [constantCopy]
    else
      []

/-- A source-controlled output block cancels the arbitrary dirty initial bit
and flips precisely by the selected sum bit contribution. -/
theorem sourceControlledOutputBitGates_step (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (sourceControlledOutputBitGates tail pivot constant bit) state =
      if (literalSelectedSourceBit pivot).get state &&
          (selectedLowerCarryToggle tail constant state bit ^^
            constant.val.testBit bit.succ.val) then
        (literalTargetBit tail.succ bit.succ).flip state
      else
        state := by
  let carry := selectedLowerCarryGates tail pivot constant bit
  let selector := literalSelectedSourceBit pivot
  let targetBit := literalTargetBit tail.succ bit.succ
  let dirty := literalCarryDirtyBit pivot bit
  let copy := EncodedBit.GateSpec.toffoli selector dirty targetBit
    (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot bit)
    (literalSelectedSourceBit_wire_ne_targetBit pivot bit.succ)
    (literalCarryDirtyBit_wire_ne_targetBit pivot bit bit.succ)
  let constantCopy := EncodedBit.GateSpec.cnot selector targetBit
    (literalSelectedSourceBit_wire_ne_targetBit pivot bit.succ)
  let middle := [copy] ++ carry.reverse ++ [copy]
  have hdisjoint : ∀ gate, gate ∈ carry →
      EncodedBit.GateSpec.bitDisjoint targetBit gate := by
    intro gate hgate
    exact List.forall_iff_forall_mem.mp
      (selectedLowerCarryGates_forall_bitDisjoint_target_of_lt
        tail pivot constant bit bit.succ (by simp)) gate hgate
  have huncompute :
      EncodedBit.GateSpec.stepList carry.reverse
          (EncodedBit.GateSpec.stepList carry state) = state :=
    EncodedBit.GateSpec.stepList_reverse_stepList carry state
  have huncomputeFlip :
      EncodedBit.GateSpec.stepList carry.reverse
          (targetBit.flip (EncodedBit.GateSpec.stepList carry state)) =
        targetBit.flip state := by
    rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint]
    · exact congrArg targetBit.flip
        (EncodedBit.GateSpec.stepList_reverse_stepList carry state)
    · intro gate hgate
      exact hdisjoint gate (List.mem_reverse.mp hgate)
  have hselectorAfter :
      selector.get (EncodedBit.GateSpec.stepList carry state) =
        selector.get state := by
    apply stepList_get_of_forall_bitDisjoint
    intro gate hgate
    exact List.forall_iff_forall_mem.mp
      (selectedLowerCarryGates_forall_bitDisjoint_selector
        tail pivot constant bit) gate hgate
  have hdirtyAfter :
      dirty.get (EncodedBit.GateSpec.stepList carry state) =
        (dirty.get state ^^
          selectedLowerCarryToggle tail constant state bit) := by
    exact selectedLowerCarryGates_currentDirty_get
      tail pivot constant bit state
  have hselectorTargetFlip
      (input : State tail.succ (LiteralBorrowed tail.succ)) :
      selector.get (targetBit.flip input) = selector.get input :=
    EncodedBit.get_flip_of_wire_ne targetBit selector
      (literalSelectedSourceBit_wire_ne_targetBit pivot bit.succ).symm input
  have hdirtyTargetFlip
      (input : State tail.succ (LiteralBorrowed tail.succ)) :
      dirty.get (targetBit.flip input) = dirty.get input :=
    EncodedBit.get_flip_of_wire_ne targetBit dirty
      (literalCarryDirtyBit_wire_ne_targetBit pivot bit bit.succ).symm input
  have hcopyStep (input : State tail.succ (LiteralBorrowed tail.succ)) :
      copy.step input =
        if selector.get input && dirty.get input then
          targetBit.flip input
        else
          input := by
    simp [copy, EncodedBit.GateSpec.step, EncodedBit.toffoliStep]
  have hcopy (input : State tail.succ (LiteralBorrowed tail.succ)) :
      EncodedBit.GateSpec.stepList [copy] input =
        if selector.get input && dirty.get input then
          targetBit.flip input
        else
          input := by
    simpa only [EncodedBit.GateSpec.stepList, id_eq] using hcopyStep input
  have hmiddle :
      EncodedBit.GateSpec.stepList middle
          (EncodedBit.GateSpec.stepList carry state) =
        if selector.get state &&
            selectedLowerCarryToggle tail constant state bit then
          targetBit.flip state
        else
          state := by
    unfold middle
    simp only [EncodedBit.GateSpec.stepList_append]
    rw [hcopy (EncodedBit.GateSpec.stepList carry state),
      hselectorAfter, hdirtyAfter]
    cases hselector : selector.get state <;>
      cases hinitial : dirty.get state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      simp [hselector, hinitial,
        huncompute, huncomputeFlip, hcopy,
        hselectorTargetFlip, hdirtyTargetFlip, EncodedBit.flip_flip]
  have hconstantCopy
      (input : State tail.succ (LiteralBorrowed tail.succ)) :
      EncodedBit.GateSpec.stepList [constantCopy] input =
        if selector.get input then targetBit.flip input else input := by
    simp [constantCopy, EncodedBit.GateSpec.stepList,
      EncodedBit.GateSpec.step, EncodedBit.cnotStep]
  unfold sourceControlledOutputBitGates
  change EncodedBit.GateSpec.stepList
      (carry ++ middle ++
        if constant.val.testBit bit.succ.val then
          [constantCopy]
        else []) state =
      if selector.get state &&
          (selectedLowerCarryToggle tail constant state bit ^^
            constant.val.testBit bit.succ.val) then
        targetBit.flip state
      else
        state
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle]
  rw [show bit.succ.val = bit.val + 1 by rfl]
  by_cases hconstant : constant.val.testBit (bit.val + 1)
  · rw [if_pos hconstant, hconstantCopy]
    cases hselector : selector.get state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      simp [hselector, hconstant,
        hselectorTargetFlip, EncodedBit.flip_flip]
  · rw [if_neg hconstant]
    cases hselector : selector.get state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      simp [hconstant, EncodedBit.GateSpec.stepList]

/-- Folded basis action of one source-controlled output-bit block. -/
def sourceControlledOutputBitStep (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    State tail.succ (LiteralBorrowed tail.succ) →
      State tail.succ (LiteralBorrowed tail.succ) :=
  EncodedBit.GateSpec.stepList
    (sourceControlledOutputBitGates tail pivot constant bit)

/-- Actual X/CNOT/Toffoli circuit for one controlled output bit. -/
def sourceControlledOutputBitProgram (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    UnitaryCircuit (Qubits (literalR0Encoding tail.succ).width) :=
  EncodedBit.GateSpec.programList
    (sourceControlledOutputBitGates tail pivot constant bit)

/-- The compiled output-bit circuit realizes its folded encoded-bit action. -/
theorem sourceControlledOutputBitProgram_realizes (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (sourceControlledOutputBitProgram tail pivot constant bit)
      (sourceControlledOutputBitStep tail pivot constant bit) :=
  EncodedBit.GateSpec.realizesList
    (sourceControlledOutputBitGates tail pivot constant bit)

/-- Exact Toffoli count of one source-controlled output-bit block. -/
theorem sourceControlledOutputBitProgram_toffoli_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (sourceControlledOutputBitProgram tail pivot constant bit).eventCost =
      4 * bit.val + 2 := by
  have hcarry :
      ((selectedLowerCarryGates tail pivot constant bit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * bit.val := by
    rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
    exact selectedLowerCarryProgram_toffoli_count_eq
      tail pivot constant bit
  rw [sourceControlledOutputBitProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  unfold sourceControlledOutputBitGates
  by_cases hc : constant.val.testBit (bit.val + 1) <;>
    simp [hc, hcarry] <;> omega

/-- Exact CNOT count of one source-controlled output-bit block. -/
theorem sourceControlledOutputBitProgram_cnot_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (sourceControlledOutputBitProgram tail pivot constant bit).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (bit.val + 1) +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant
          bit.succ.val := by
  have hcarry :
      ((selectedLowerCarryGates tail pivot constant bit).map
          EncodedBit.GateSpec.cnotMultiplicity).sum =
        MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (bit.val + 1) := by
    rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
    exact selectedLowerCarryProgram_cnot_count_eq
      tail pivot constant bit
  rw [sourceControlledOutputBitProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  unfold sourceControlledOutputBitGates
  by_cases hc : constant.val.testBit (bit.val + 1) <;>
    simp [hc, hcarry,
      MAU.Addition.DirtyBorrowed.constantBitMultiplicity] <;> omega

/-- Exact X count of one source-controlled output-bit block. -/
theorem sourceControlledOutputBitProgram_x_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "x"))
        (sourceControlledOutputBitProgram tail pivot constant bit).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val := by
  have hcarry :
      ((selectedLowerCarryGates tail pivot constant bit).map
          EncodedBit.GateSpec.xMultiplicity).sum =
        MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val := by
    rw [← EncodedBit.GateSpec.programList_x_count_eq_sum]
    exact selectedLowerCarryProgram_x_count_eq tail pivot constant bit
  rw [sourceControlledOutputBitProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  unfold sourceControlledOutputBitGates
  by_cases hc : constant.val.testBit (bit.val + 1) <;>
    simp [hc, hcarry] <;> omega

/-- Gate-list form of the exact Toffoli coordinate for one output bit. -/
theorem sourceControlledOutputBitGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ((sourceControlledOutputBitGates tail pivot constant bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      4 * bit.val + 2 := by
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact sourceControlledOutputBitProgram_toffoli_count_eq
    tail pivot constant bit

/-- Gate-list form of the exact CNOT coordinate for one output bit. -/
theorem sourceControlledOutputBitGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ((sourceControlledOutputBitGates tail pivot constant bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (bit.val + 1) +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant
          bit.succ.val := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact sourceControlledOutputBitProgram_cnot_count_eq
    tail pivot constant bit

/-- Gate-list form of the exact X coordinate for one output bit. -/
theorem sourceControlledOutputBitGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ((sourceControlledOutputBitGates tail pivot constant bit).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val := by
  rw [← EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact sourceControlledOutputBitProgram_x_count_eq tail pivot constant bit

/-- Recursive high-to-low controlled output sweep.  `count` processes target
bits `count, ..., 1`, so every carry reads only target bits that have not yet
been updated. -/
def sourceControlledHighGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    (count : Nat) → count ≤ tail →
      List (EncodedBit.GateSpec (literalR0Encoding tail.succ))
  | 0, _ => []
  | count + 1, hcount =>
      sourceControlledOutputBitGates tail pivot constant
          ⟨count, by omega⟩ ++
        sourceControlledHighGates tail pivot constant count (by omega)

/-- Final controlled least-significant constant bit. -/
def sourceControlledLowGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  if constant.val.testBit 0 then
    [EncodedBit.GateSpec.cnot
      (literalSelectedSourceBit pivot) (literalTargetBit tail.succ 0)
      (literalSelectedSourceBit_wire_ne_targetBit pivot 0)]
  else
    []

/-- Complete source-controlled fixed-width constant-adder gate schedule. -/
def sourceControlledAdderGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  sourceControlledHighGates tail pivot constant tail le_rfl ++
    sourceControlledLowGates tail pivot constant

/-- Closed CNOT coordinate of the non-low controlled output sweep. -/
def sourceControlledHighCnotClosedForm {width : Nat}
    (constant : PlainAdder.Word width) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (count + 1) +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity
          constant (count + 1) +
        sourceControlledHighCnotClosedForm constant count

/-- Closed X coordinate of the non-low controlled output sweep. -/
def sourceControlledHighXClosedForm {width : Nat}
    (constant : PlainAdder.Word width) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm constant count +
        sourceControlledHighXClosedForm constant count

/-- Exact Toffoli coordinate of a high-to-low controlled prefix. -/
theorem sourceControlledHighGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail) :
    ((sourceControlledHighGates tail pivot constant count hcount).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * count * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show sourceControlledHighGates tail pivot constant
            (count + 1) hcount =
          sourceControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            sourceControlledHighGates tail pivot constant count
              (by omega) by rfl]
      simp only [List.map_append, List.sum_append]
      rw [sourceControlledOutputBitGates_toffoliMultiplicity_sum,
        ih (by omega)]
      ring

/-- Exact CNOT coordinate of a high-to-low controlled prefix. -/
theorem sourceControlledHighGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail) :
    ((sourceControlledHighGates tail pivot constant count hcount).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      sourceControlledHighCnotClosedForm constant count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show sourceControlledHighGates tail pivot constant
            (count + 1) hcount =
          sourceControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            sourceControlledHighGates tail pivot constant count
              (by omega) by rfl]
      simp [sourceControlledHighCnotClosedForm,
        sourceControlledOutputBitGates_cnotMultiplicity_sum,
        ih (by omega)]

/-- Exact X coordinate of a high-to-low controlled prefix. -/
theorem sourceControlledHighGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail) :
    ((sourceControlledHighGates tail pivot constant count hcount).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      sourceControlledHighXClosedForm constant count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show sourceControlledHighGates tail pivot constant
            (count + 1) hcount =
          sourceControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            sourceControlledHighGates tail pivot constant count
              (by omega) by rfl]
      simp [sourceControlledHighXClosedForm,
        sourceControlledOutputBitGates_xMultiplicity_sum,
        ih (by omega)]

/-- Folded basis action of the complete source-controlled adder. -/
def sourceControlledAdderStep (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    State tail.succ (LiteralBorrowed tail.succ) →
      State tail.succ (LiteralBorrowed tail.succ) :=
  EncodedBit.GateSpec.stepList
    (sourceControlledAdderGates tail pivot constant)

/-- Actual X/CNOT/Toffoli source-controlled fixed-width adder. -/
def sourceControlledAdderProgram (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit (Qubits (literalR0Encoding tail.succ).width) :=
  EncodedBit.GateSpec.programList
    (sourceControlledAdderGates tail pivot constant)

/-- The compiled controlled adder realizes its folded encoded-bit action. -/
theorem sourceControlledAdderProgram_realizesFoldedStep (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (sourceControlledAdderProgram tail pivot constant)
      (sourceControlledAdderStep tail pivot constant) :=
  EncodedBit.GateSpec.realizesList
    (sourceControlledAdderGates tail pivot constant)

/-- Exact Toffoli count of the complete source-controlled adder. -/
theorem sourceControlledAdderProgram_toffoli_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (sourceControlledAdderProgram tail pivot constant).eventCost =
      2 * tail * tail := by
  rw [sourceControlledAdderProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  by_cases hc : constant.val.testBit 0 <;>
    simp [sourceControlledAdderGates, sourceControlledLowGates, hc,
      sourceControlledHighGates_toffoliMultiplicity_sum]

/-- Exact CNOT count of the complete source-controlled adder. -/
theorem sourceControlledAdderProgram_cnot_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (sourceControlledAdderProgram tail pivot constant).eventCost =
      sourceControlledHighCnotClosedForm constant tail +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant 0 := by
  rw [sourceControlledAdderProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  by_cases hc : constant.val.testBit 0 <;>
    simp [sourceControlledAdderGates, sourceControlledLowGates, hc,
      sourceControlledHighGates_cnotMultiplicity_sum,
      MAU.Addition.DirtyBorrowed.constantBitMultiplicity]

/-- Exact X count of the complete source-controlled adder. -/
theorem sourceControlledAdderProgram_x_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (sourceControlledAdderProgram tail pivot constant).eventCost =
      sourceControlledHighXClosedForm constant tail := by
  rw [sourceControlledAdderProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  by_cases hc : constant.val.testBit 0 <;>
    simp [sourceControlledAdderGates, sourceControlledLowGates, hc,
      sourceControlledHighGates_xMultiplicity_sum]

/-! ### Classical semantics of the controlled adder -/

/-- One non-low output block is exactly an accumulator-only replacement. -/
theorem sourceControlledOutputBitGates_step_eq_withTarget (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (sourceControlledOutputBitGates tail pivot constant bit) state =
      withTarget state
        (if (literalSelectedSourceBit pivot).get state &&
            (selectedLowerCarryToggle tail constant state bit ^^
              constant.val.testBit bit.succ.val) then
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ bit.succ).flip
            (target state)
        else
          target state) := by
  rw [sourceControlledOutputBitGates_step]
  by_cases htoggle :
      (literalSelectedSourceBit pivot).get state &&
        (selectedLowerCarryToggle tail constant state bit ^^
          constant.val.testBit bit.succ.val)
  · rw [if_pos htoggle, if_pos htoggle,
      literalTargetBit_flip_eq_withTarget]
  · rw [if_neg htoggle, if_neg htoggle, withTarget_target]

/-- One non-low block changes only its selected accumulator readout, by the
source-controlled xor of the propagated carry and compile-time constant bit. -/
theorem sourceControlledOutputBitGates_target_testBit (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ))
    (observed : Fin tail.succ) :
    (target (EncodedBit.GateSpec.stepList
        (sourceControlledOutputBitGates tail pivot constant bit) state)).val.testBit
          observed.val =
      if observed = bit.succ then
        ((target state).val.testBit observed.val ^^
          ((literalSelectedSourceBit pivot).get state &&
            (selectedLowerCarryToggle tail constant state bit ^^
              constant.val.testBit observed.val)))
      else
        (target state).val.testBit observed.val := by
  rw [← literalTargetBit_get tail.succ observed]
  rw [← literalTargetBit_get tail.succ observed state]
  rw [sourceControlledOutputBitGates_step]
  have hflip :
      ((PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ bit.succ).flip
          (target state)).val.testBit bit.succ.val =
        !(target state).val.testBit bit.succ.val := by
    simpa only [PlainAdder.Schedule.PowerOfTwo.wordBit_get] using
      (EncodedBit.get_flip_self
        (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ bit.succ)
        (target state))
  by_cases heq : observed = bit.succ
  · subst observed
    simp only [if_pos]
    cases hselector : (literalSelectedSourceBit pivot).get state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      cases hconstant : constant.val.testBit bit.succ.val <;>
      cases hinput : (target state).val.testBit bit.succ.val <;>
      simp_all
  · simp only [if_neg heq]
    split
    · exact EncodedBit.get_flip_of_wire_ne
        (literalTargetBit tail.succ bit.succ)
        (literalTargetBit tail.succ observed)
        (literalTargetBit_wire_ne tail.succ (Ne.symm heq)) state
    · rfl

/-- The final low-bit layer is also exactly an accumulator-only replacement. -/
theorem sourceControlledLowGates_step_eq_withTarget (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (sourceControlledLowGates tail pivot constant) state =
      withTarget state
        (if (literalSelectedSourceBit pivot).get state &&
            constant.val.testBit 0 then
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0).flip
            (target state)
        else
          target state) := by
  by_cases hconstant : constant.val.testBit 0
  · rw [show sourceControlledLowGates tail pivot constant =
        [EncodedBit.GateSpec.cnot
          (literalSelectedSourceBit pivot) (literalTargetBit tail.succ 0)
          (literalSelectedSourceBit_wire_ne_targetBit pivot 0)] by
        simp [sourceControlledLowGates, hconstant]]
    cases hselector : (literalSelectedSourceBit pivot).get state
    · simp only [EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, id_eq]
      rw [EncodedBit.cnotStep]
      simp only [hselector, hconstant, Bool.false_eq_true,
        Bool.false_and, if_false,
        withTarget_target]
    · simp only [EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, id_eq]
      rw [EncodedBit.cnotStep]
      simp only [hselector, hconstant, Bool.true_and, if_true,
        literalTargetBit_flip_eq_withTarget]
  · rw [show sourceControlledLowGates tail pivot constant = [] by
        simp [sourceControlledLowGates, hconstant]]
    have hconstantFalse : constant.val.testBit 0 = false :=
      Bool.eq_false_iff.mpr hconstant
    simp only [EncodedBit.GateSpec.stepList, id_eq, hconstantFalse,
      Bool.false_eq_true,
      Bool.and_false, if_false, withTarget_target]

/-- Exact accumulator readout after the final controlled low-bit layer. -/
theorem sourceControlledLowGates_target_testBit (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ))
    (observed : Fin tail.succ) :
    (target (EncodedBit.GateSpec.stepList
        (sourceControlledLowGates tail pivot constant) state)).val.testBit
          observed.val =
      if observed = 0 then
        ((target state).val.testBit observed.val ^^
          ((literalSelectedSourceBit pivot).get state &&
            constant.val.testBit 0))
      else
        (target state).val.testBit observed.val := by
  rw [sourceControlledLowGates_step_eq_withTarget]
  simp only [target_withTarget]
  by_cases htoggle :
      (literalSelectedSourceBit pivot).get state && constant.val.testBit 0
  · rw [if_pos htoggle]
    by_cases hzero : observed = 0
    · subst observed
      simp only [if_pos]
      have hflip := EncodedBit.get_flip_self
        (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0) (target state)
      simpa only [PlainAdder.Schedule.PowerOfTwo.wordBit_get, htoggle,
        Bool.xor_true] using hflip
    · rw [if_neg hzero]
      rw [← PlainAdder.Schedule.PowerOfTwo.wordBit_get tail.succ observed]
      simpa only [PlainAdder.Schedule.PowerOfTwo.wordBit_get] using
        (EncodedBit.get_flip_of_wire_ne
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0)
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ observed)
          (MAU.Addition.DirtyBorrowed.straightforwardWordBit_wire_ne
            tail.succ (Ne.symm hzero)) (target state))
  · rw [if_neg htoggle]
    have htoggleFalse :
        ((literalSelectedSourceBit pivot).get state &&
            constant.val.testBit 0) = false :=
      Bool.eq_false_of_not_eq_true htoggle
    by_cases hzero : observed = 0
    · rw [if_pos hzero, htoggleFalse]
      simp only [Bool.xor_false]
    · rw [if_neg hzero]

/-- A single non-low block preserves the selected source readout. -/
theorem sourceControlledOutputBitGates_selector_get (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    (literalSelectedSourceBit pivot).get
        (EncodedBit.GateSpec.stepList
          (sourceControlledOutputBitGates tail pivot constant bit) state) =
      (literalSelectedSourceBit pivot).get state := by
  rw [sourceControlledOutputBitGates_step_eq_withTarget]
  split <;> rfl

/-- The high-to-low prefix preserves the selected source readout. -/
theorem sourceControlledHighGates_selector_get (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    (literalSelectedSourceBit pivot).get
        (EncodedBit.GateSpec.stepList
          (sourceControlledHighGates tail pivot constant count hcount) state) =
      (literalSelectedSourceBit pivot).get state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [show sourceControlledHighGates tail pivot constant
            (count + 1) hcount =
          sourceControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            sourceControlledHighGates tail pivot constant count
              (by omega) by rfl]
      rw [EncodedBit.GateSpec.stepList_append, ih (by omega),
        sourceControlledOutputBitGates_selector_get]

/-- After a controlled high prefix, the selected non-low accumulator bits
agree with fixed-width addition exactly when the source selector is true. -/
theorem sourceControlledHighGates_target_testBit (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail)
    (state : State tail.succ (LiteralBorrowed tail.succ))
    (observed : Fin tail.succ) :
    (target (EncodedBit.GateSpec.stepList
        (sourceControlledHighGates tail pivot constant count hcount) state)).val.testBit
          observed.val =
      if (literalSelectedSourceBit pivot).get state then
        if 0 < observed.val ∧ observed.val ≤ count then
          (target state + constant).val.testBit observed.val
        else
          (target state).val.testBit observed.val
      else
        (target state).val.testBit observed.val := by
  induction count generalizing state with
  | zero =>
      rw [show sourceControlledHighGates tail pivot constant 0 hcount = [] by
        rfl]
      change (target state).val.testBit observed.val =
        if (literalSelectedSourceBit pivot).get state then
          if 0 < observed.val ∧ observed.val ≤ 0 then
            (target state + constant).val.testBit observed.val
          else
            (target state).val.testBit observed.val
        else
          (target state).val.testBit observed.val
      have houtside : ¬(0 < observed.val ∧ observed.val ≤ 0) := by omega
      by_cases hselector : (literalSelectedSourceBit pivot).get state
      · rw [if_pos hselector, if_neg houtside]
      · rw [if_neg hselector]
  | succ count ih =>
      let top : Fin tail := ⟨count, by omega⟩
      let afterTop := EncodedBit.GateSpec.stepList
        (sourceControlledOutputBitGates tail pivot constant top) state
      rw [show sourceControlledHighGates tail pivot constant
            (count + 1) hcount =
          sourceControlledOutputBitGates tail pivot constant top ++
            sourceControlledHighGates tail pivot constant count
              (by omega) by rfl]
      rw [EncodedBit.GateSpec.stepList_append]
      rw [ih (by omega) afterTop]
      have hselectorAfter :
          (literalSelectedSourceBit pivot).get afterTop =
            (literalSelectedSourceBit pivot).get state := by
        dsimp [afterTop]
        exact sourceControlledOutputBitGates_selector_get
          tail pivot constant top state
      rw [hselectorAfter]
      by_cases hselector : (literalSelectedSourceBit pivot).get state
      · rw [if_pos hselector, if_pos hselector]
        by_cases hinside : 0 < observed.val ∧ observed.val ≤ count
        · rw [if_pos hinside]
          have houter : 0 < observed.val ∧ observed.val ≤ count + 1 :=
            ⟨hinside.1, by omega⟩
          rw [if_pos houter]
          apply MAU.Addition.DirtyBorrowed.word_add_testBit_congr_left_of_testBit_eq_le
          intro inputBit hinputBit
          let selected : Fin tail.succ := ⟨inputBit, by omega⟩
          have hselected : selected ≠ top.succ := by
            apply Fin.ne_of_val_ne
            dsimp [selected, top]
            omega
          have hread := sourceControlledOutputBitGates_target_testBit
            tail pivot constant top state selected
          simpa [afterTop, if_neg hselected] using hread
        · rw [if_neg hinside]
          by_cases htop : observed.val = count + 1
          · have hselected : observed = top.succ := by
              apply Fin.ext
              simpa [top] using htop
            have houter : 0 < observed.val ∧ observed.val ≤ count + 1 := by
              omega
            rw [if_pos houter]
            have hread := sourceControlledOutputBitGates_target_testBit
              tail pivot constant top state observed
            rw [hread, if_pos hselected]
            have hselectorSource :
                (source state).val.testBit pivot.val = true := by
              simpa only [literalSelectedSourceBit_get] using hselector
            simpa [hselectorSource, selectedLowerCarryToggle, top, Fin.val_succ,
              htop, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm,
              Nat.BinaryArithmetic.natAddCarry_comm] using
                (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
                  tail.succ constant (target state) observed).symm
          · have houter :
                ¬(0 < observed.val ∧ observed.val ≤ count + 1) := by
              omega
            rw [if_neg houter]
            have hselected : observed ≠ top.succ := by
              apply Fin.ne_of_val_ne
              dsimp [top]
              omega
            have hread := sourceControlledOutputBitGates_target_testBit
              tail pivot constant top state observed
            simpa [afterTop, if_neg hselected] using hread
      · rw [if_neg hselector, if_neg hselector]
        have hread := sourceControlledOutputBitGates_target_testBit
          tail pivot constant top state observed
        have hselectorFalse :
            (literalSelectedSourceBit pivot).get state = false :=
          Bool.eq_false_iff.mpr hselector
        have hselectorSourceFalse :
            (source state).val.testBit pivot.val = false := by
          simpa only [literalSelectedSourceBit_get] using hselectorFalse
        simpa [afterTop, hselectorSourceFalse] using hread

/-- Every high prefix changes only the accumulator component. -/
theorem sourceControlledHighGates_step_eq_withTarget (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (sourceControlledHighGates tail pivot constant count hcount) state =
      withTarget state
        (target (EncodedBit.GateSpec.stepList
          (sourceControlledHighGates tail pivot constant count hcount) state)) := by
  induction count generalizing state with
  | zero =>
      rw [show sourceControlledHighGates tail pivot constant 0 hcount = [] by
        rfl]
      simp only [EncodedBit.GateSpec.stepList, id_eq, withTarget_target]
  | succ count ih =>
      let top : Fin tail := ⟨count, by omega⟩
      let afterTop := EncodedBit.GateSpec.stepList
        (sourceControlledOutputBitGates tail pivot constant top) state
      rw [show sourceControlledHighGates tail pivot constant
            (count + 1) hcount =
          sourceControlledOutputBitGates tail pivot constant top ++
            sourceControlledHighGates tail pivot constant count
              (by omega) by rfl]
      rw [EncodedBit.GateSpec.stepList_append]
      change EncodedBit.GateSpec.stepList
          (sourceControlledHighGates tail pivot constant count (by omega))
            afterTop =
        withTarget state
          (target (EncodedBit.GateSpec.stepList
            (sourceControlledHighGates tail pivot constant count (by omega))
              afterTop))
      rw [ih (by omega) afterTop]
      dsimp [afterTop]
      rw [sourceControlledOutputBitGates_step_eq_withTarget]
      simp only [withTarget_withTarget]

/-- The complete controlled-adder schedule changes only the accumulator. -/
theorem sourceControlledAdderStep_eq_withTargetCurrent (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    sourceControlledAdderStep tail pivot constant state =
      withTarget state
        (target (sourceControlledAdderStep tail pivot constant state)) := by
  unfold sourceControlledAdderStep sourceControlledAdderGates
  rw [EncodedBit.GateSpec.stepList_append]
  let afterHigh := EncodedBit.GateSpec.stepList
    (sourceControlledHighGates tail pivot constant tail le_rfl) state
  change EncodedBit.GateSpec.stepList
      (sourceControlledLowGates tail pivot constant) afterHigh =
    withTarget state
        (target (EncodedBit.GateSpec.stepList
          (sourceControlledLowGates tail pivot constant) afterHigh))
  rw [sourceControlledLowGates_step_eq_withTarget]
  let finalTarget :=
    if (literalSelectedSourceBit pivot).get afterHigh &&
        constant.val.testBit 0 then
      (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0).flip
        (target afterHigh)
    else
      target afterHigh
  change withTarget afterHigh finalTarget = withTarget state finalTarget
  dsimp [afterHigh]
  rw [sourceControlledHighGates_step_eq_withTarget]
  simp only [withTarget_withTarget]

/-- The complete physical schedule performs fixed-width addition iff the
selected source bit is true. -/
theorem sourceControlledAdderStep_target (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    target (sourceControlledAdderStep tail pivot constant state) =
      if (literalSelectedSourceBit pivot).get state then
        target state + constant
      else
        target state := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro observed
  unfold sourceControlledAdderStep sourceControlledAdderGates
  rw [EncodedBit.GateSpec.stepList_append]
  let afterHigh := EncodedBit.GateSpec.stepList
    (sourceControlledHighGates tail pivot constant tail le_rfl) state
  change (target (EncodedBit.GateSpec.stepList
      (sourceControlledLowGates tail pivot constant) afterHigh)).val.testBit
        observed.val = _
  rw [sourceControlledLowGates_target_testBit]
  have hselectorAfter :
      (literalSelectedSourceBit pivot).get afterHigh =
        (literalSelectedSourceBit pivot).get state := by
    dsimp [afterHigh]
    exact sourceControlledHighGates_selector_get
      tail pivot constant tail le_rfl state
  rw [hselectorAfter]
  by_cases hselector : (literalSelectedSourceBit pivot).get state
  · rw [if_pos hselector]
    have hselectorSource :
        (source state).val.testBit pivot.val = true := by
      simpa only [literalSelectedSourceBit_get] using hselector
    by_cases hzero : observed = 0
    · rw [if_pos hzero]
      subst observed
      have hhigh := sourceControlledHighGates_target_testBit
        tail pivot constant tail le_rfl state (0 : Fin tail.succ)
      rw [hhigh, if_pos hselector]
      rw [if_neg (by simp : ¬(0 < (0 : Fin tail.succ).val ∧
        (0 : Fin tail.succ).val ≤ tail))]
      simpa [hselectorSource, Nat.BinaryArithmetic.natAddCarry] using
        (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
          tail.succ constant (target state) 0).symm
    · rw [if_neg hzero]
      have hpositive : 0 < observed.val := by
        have hval : observed.val ≠ 0 := by
          intro h
          exact hzero (Fin.ext h)
        omega
      have hle : observed.val ≤ tail := by omega
      have hhigh := sourceControlledHighGates_target_testBit
        tail pivot constant tail le_rfl state observed
      rw [hhigh, if_pos hselector, if_pos ⟨hpositive, hle⟩]
  · rw [if_neg hselector]
    have hhigh := sourceControlledHighGates_target_testBit
      tail pivot constant tail le_rfl state observed
    rw [hhigh, if_neg hselector]
    have hselectorFalse :
        (literalSelectedSourceBit pivot).get state = false :=
      Bool.eq_false_of_not_eq_true hselector
    by_cases hzero : observed = 0
    · subst observed
      rw [if_pos rfl, hselectorFalse]
      simp only [Bool.false_and, Bool.xor_false]
    · rw [if_neg hzero]

/-- Classical controlled-add transition on the literal shared carrier. -/
def sourceControlledAdd (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    State tail.succ (LiteralBorrowed tail.succ) :=
  if (literalSelectedSourceBit pivot).get state then
    withTarget state (target state + constant)
  else
    state

/-- The folded gate action agrees exactly with classical controlled addition. -/
theorem sourceControlledAdderStep_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    sourceControlledAdderStep tail pivot constant state =
      sourceControlledAdd tail pivot constant state := by
  rw [sourceControlledAdderStep_eq_withTargetCurrent,
    sourceControlledAdderStep_target]
  unfold sourceControlledAdd
  by_cases hselector : (literalSelectedSourceBit pivot).get state
  · rw [if_pos hselector, if_pos hselector]
  · rw [if_neg hselector, if_neg hselector, withTarget_target]

/-- The actual circuit realizes classical source-controlled fixed-width
addition and restores every non-accumulator basis label. -/
theorem sourceControlledAdderProgram_realizes (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (sourceControlledAdderProgram tail pivot constant)
      (sourceControlledAdd tail pivot constant) :=
  UnitaryCircuit.Realizes.congrStep
    (sourceControlledAdderProgram_realizesFoldedStep tail pivot constant)
    (sourceControlledAdderStep_eq tail pivot constant)

/-! ## Clean-flag-controlled fixed-width addition -/

/-- One non-low output bit controlled by the clean comparison flag.  The
source word remains available as dirty carry work, with `pivot` excluded only
to reuse the already certified residual-word carrier. -/
def flagControlledOutputBitGates (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  let carry := selectedLowerCarryGates tail pivot constant bit
  let control := literalFlagBit tail.succ
  let targetBit := literalTargetBit tail.succ bit.succ
  let dirty := literalCarryDirtyBit pivot bit
  let copy := EncodedBit.GateSpec.toffoli control dirty targetBit
    (literalCarryDirtyBit_wire_ne_flag pivot bit).symm
    (literalTargetBit_wire_ne_flag tail.succ bit.succ).symm
    (literalCarryDirtyBit_wire_ne_targetBit pivot bit bit.succ)
  let constantCopy := EncodedBit.GateSpec.cnot control targetBit
    (literalTargetBit_wire_ne_flag tail.succ bit.succ).symm
  let middle := [copy] ++ carry.reverse ++ [copy]
  carry ++ middle ++
    if constant.val.testBit bit.succ.val then
      [constantCopy]
    else
      []

/-- The clean-flag-controlled output block cancels every dirty initial value
and flips exactly by the selected sum-bit contribution. -/
theorem flagControlledOutputBitGates_step (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (flagControlledOutputBitGates tail pivot constant bit) state =
      if (literalFlagBit tail.succ).get state &&
          (selectedLowerCarryToggle tail constant state bit ^^
            constant.val.testBit bit.succ.val) then
        (literalTargetBit tail.succ bit.succ).flip state
      else
        state := by
  let carry := selectedLowerCarryGates tail pivot constant bit
  let control := literalFlagBit tail.succ
  let targetBit := literalTargetBit tail.succ bit.succ
  let dirty := literalCarryDirtyBit pivot bit
  let copy := EncodedBit.GateSpec.toffoli control dirty targetBit
    (literalCarryDirtyBit_wire_ne_flag pivot bit).symm
    (literalTargetBit_wire_ne_flag tail.succ bit.succ).symm
    (literalCarryDirtyBit_wire_ne_targetBit pivot bit bit.succ)
  let constantCopy := EncodedBit.GateSpec.cnot control targetBit
    (literalTargetBit_wire_ne_flag tail.succ bit.succ).symm
  let middle := [copy] ++ carry.reverse ++ [copy]
  have hdisjoint : ∀ gate, gate ∈ carry →
      EncodedBit.GateSpec.bitDisjoint targetBit gate := by
    intro gate hgate
    exact List.forall_iff_forall_mem.mp
      (selectedLowerCarryGates_forall_bitDisjoint_target_of_lt
        tail pivot constant bit bit.succ (by simp)) gate hgate
  have huncompute :
      EncodedBit.GateSpec.stepList carry.reverse
          (EncodedBit.GateSpec.stepList carry state) = state :=
    EncodedBit.GateSpec.stepList_reverse_stepList carry state
  have huncomputeFlip :
      EncodedBit.GateSpec.stepList carry.reverse
          (targetBit.flip (EncodedBit.GateSpec.stepList carry state)) =
        targetBit.flip state := by
    rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint]
    · exact congrArg targetBit.flip
        (EncodedBit.GateSpec.stepList_reverse_stepList carry state)
    · intro gate hgate
      exact hdisjoint gate (List.mem_reverse.mp hgate)
  have hcontrolAfter :
      control.get (EncodedBit.GateSpec.stepList carry state) =
        control.get state := by
    apply stepList_get_of_forall_bitDisjoint
    intro gate hgate
    exact List.forall_iff_forall_mem.mp
      (selectedLowerCarryGates_forall_bitDisjoint_flag
        tail pivot constant bit) gate hgate
  have hdirtyAfter :
      dirty.get (EncodedBit.GateSpec.stepList carry state) =
        (dirty.get state ^^
          selectedLowerCarryToggle tail constant state bit) :=
    selectedLowerCarryGates_currentDirty_get
      tail pivot constant bit state
  have hcontrolTargetFlip
      (input : State tail.succ (LiteralBorrowed tail.succ)) :
      control.get (targetBit.flip input) = control.get input :=
    EncodedBit.get_flip_of_wire_ne targetBit control
      (literalTargetBit_wire_ne_flag tail.succ bit.succ) input
  have hdirtyTargetFlip
      (input : State tail.succ (LiteralBorrowed tail.succ)) :
      dirty.get (targetBit.flip input) = dirty.get input :=
    EncodedBit.get_flip_of_wire_ne targetBit dirty
      (literalCarryDirtyBit_wire_ne_targetBit pivot bit bit.succ).symm input
  have hcopyStep (input : State tail.succ (LiteralBorrowed tail.succ)) :
      copy.step input =
        if control.get input && dirty.get input then
          targetBit.flip input
        else
          input := by
    simp [copy, EncodedBit.GateSpec.step, EncodedBit.toffoliStep]
  have hcopy (input : State tail.succ (LiteralBorrowed tail.succ)) :
      EncodedBit.GateSpec.stepList [copy] input =
        if control.get input && dirty.get input then
          targetBit.flip input
        else
          input := by
    simpa only [EncodedBit.GateSpec.stepList, id_eq] using hcopyStep input
  have hmiddle :
      EncodedBit.GateSpec.stepList middle
          (EncodedBit.GateSpec.stepList carry state) =
        if control.get state &&
            selectedLowerCarryToggle tail constant state bit then
          targetBit.flip state
        else
          state := by
    unfold middle
    simp only [EncodedBit.GateSpec.stepList_append]
    rw [hcopy (EncodedBit.GateSpec.stepList carry state),
      hcontrolAfter, hdirtyAfter]
    cases hcontrol : control.get state <;>
      cases hinitial : dirty.get state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      simp [hcontrol, hinitial, huncompute, huncomputeFlip, hcopy,
        hcontrolTargetFlip, hdirtyTargetFlip, EncodedBit.flip_flip]
  have hconstantCopy
      (input : State tail.succ (LiteralBorrowed tail.succ)) :
      EncodedBit.GateSpec.stepList [constantCopy] input =
        if control.get input then targetBit.flip input else input := by
    simp [constantCopy, EncodedBit.GateSpec.stepList,
      EncodedBit.GateSpec.step, EncodedBit.cnotStep]
  unfold flagControlledOutputBitGates
  change EncodedBit.GateSpec.stepList
      (carry ++ middle ++
        if constant.val.testBit bit.succ.val then
          [constantCopy]
        else []) state =
      if control.get state &&
          (selectedLowerCarryToggle tail constant state bit ^^
            constant.val.testBit bit.succ.val) then
        targetBit.flip state
      else
        state
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [hmiddle]
  rw [show bit.succ.val = bit.val + 1 by rfl]
  by_cases hconstant : constant.val.testBit (bit.val + 1)
  · rw [if_pos hconstant, hconstantCopy]
    cases hcontrol : control.get state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      simp [hcontrol, hconstant,
        hcontrolTargetFlip, EncodedBit.flip_flip]
  · rw [if_neg hconstant]
    cases hcontrol : control.get state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      simp [hconstant, EncodedBit.GateSpec.stepList]

/-- Actual circuit for one clean-flag-controlled output bit. -/
def flagControlledOutputBitProgram (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    UnitaryCircuit (Qubits (literalR0Encoding tail.succ).width) :=
  EncodedBit.GateSpec.programList
    (flagControlledOutputBitGates tail pivot constant bit)

/-- The flag-controlled output circuit realizes its literal folded action. -/
theorem flagControlledOutputBitProgram_realizes (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (flagControlledOutputBitProgram tail pivot constant bit)
      (EncodedBit.GateSpec.stepList
        (flagControlledOutputBitGates tail pivot constant bit)) :=
  EncodedBit.GateSpec.realizesList
    (flagControlledOutputBitGates tail pivot constant bit)

/-- Exact Toffoli count of one flag-controlled output bit. -/
theorem flagControlledOutputBitProgram_toffoli_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (flagControlledOutputBitProgram tail pivot constant bit).eventCost =
      4 * bit.val + 2 := by
  have hcarry :
      ((selectedLowerCarryGates tail pivot constant bit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * bit.val := by
    rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
    exact selectedLowerCarryProgram_toffoli_count_eq
      tail pivot constant bit
  rw [flagControlledOutputBitProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  unfold flagControlledOutputBitGates
  by_cases hc : constant.val.testBit (bit.val + 1) <;>
    simp [hc, hcarry] <;> omega

/-- Exact CNOT count of one flag-controlled output bit. -/
theorem flagControlledOutputBitProgram_cnot_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (flagControlledOutputBitProgram tail pivot constant bit).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (bit.val + 1) +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant
          bit.succ.val := by
  have hcarry :
      ((selectedLowerCarryGates tail pivot constant bit).map
          EncodedBit.GateSpec.cnotMultiplicity).sum =
        MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (bit.val + 1) := by
    rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
    exact selectedLowerCarryProgram_cnot_count_eq
      tail pivot constant bit
  rw [flagControlledOutputBitProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  unfold flagControlledOutputBitGates
  by_cases hc : constant.val.testBit (bit.val + 1) <;>
    simp [hc, hcarry,
      MAU.Addition.DirtyBorrowed.constantBitMultiplicity] <;> omega

/-- Exact X count of one flag-controlled output bit. -/
theorem flagControlledOutputBitProgram_x_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ResourcePool.count (.gate (.builtin "x"))
        (flagControlledOutputBitProgram tail pivot constant bit).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val := by
  have hcarry :
      ((selectedLowerCarryGates tail pivot constant bit).map
          EncodedBit.GateSpec.xMultiplicity).sum =
        MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val := by
    rw [← EncodedBit.GateSpec.programList_x_count_eq_sum]
    exact selectedLowerCarryProgram_x_count_eq tail pivot constant bit
  rw [flagControlledOutputBitProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  unfold flagControlledOutputBitGates
  by_cases hc : constant.val.testBit (bit.val + 1) <;>
    simp [hc, hcarry] <;> omega

/-- Gate-list Toffoli coordinate of one flag-controlled output bit. -/
theorem flagControlledOutputBitGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ((flagControlledOutputBitGates tail pivot constant bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      4 * bit.val + 2 := by
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact flagControlledOutputBitProgram_toffoli_count_eq
    tail pivot constant bit

/-- Gate-list CNOT coordinate of one flag-controlled output bit. -/
theorem flagControlledOutputBitGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ((flagControlledOutputBitGates tail pivot constant bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (bit.val + 1) +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant
          bit.succ.val := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact flagControlledOutputBitProgram_cnot_count_eq
    tail pivot constant bit

/-- Gate-list X coordinate of one flag-controlled output bit. -/
theorem flagControlledOutputBitGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail) :
    ((flagControlledOutputBitGates tail pivot constant bit).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm constant bit.val := by
  rw [← EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact flagControlledOutputBitProgram_x_count_eq tail pivot constant bit

/-- Recursive high-to-low clean-flag-controlled output sweep. -/
def flagControlledHighGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    (count : Nat) → count ≤ tail →
      List (EncodedBit.GateSpec (literalR0Encoding tail.succ))
  | 0, _ => []
  | count + 1, hcount =>
      flagControlledOutputBitGates tail pivot constant
          ⟨count, by omega⟩ ++
        flagControlledHighGates tail pivot constant count (by omega)

/-- Final clean-flag-controlled least-significant constant bit. -/
def flagControlledLowGates (tail : Nat) (constant : PlainAdder.Word tail.succ) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  if constant.val.testBit 0 then
    [EncodedBit.GateSpec.cnot
      (literalFlagBit tail.succ) (literalTargetBit tail.succ 0)
      (literalTargetBit_wire_ne_flag tail.succ 0).symm]
  else
    []

/-- Complete clean-flag-controlled fixed-width constant-adder schedule. -/
def flagControlledAdderGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  flagControlledHighGates tail pivot constant tail le_rfl ++
    flagControlledLowGates tail constant

/-- Exact Toffoli coordinate of a flag-controlled high prefix. -/
theorem flagControlledHighGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail) :
    ((flagControlledHighGates tail pivot constant count hcount).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * count * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show flagControlledHighGates tail pivot constant
            (count + 1) hcount =
          flagControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            flagControlledHighGates tail pivot constant count
              (by omega) by rfl]
      simp only [List.map_append, List.sum_append]
      rw [flagControlledOutputBitGates_toffoliMultiplicity_sum,
        ih (by omega)]
      ring

/-- Exact CNOT coordinate of a flag-controlled high prefix. -/
theorem flagControlledHighGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail) :
    ((flagControlledHighGates tail pivot constant count hcount).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      sourceControlledHighCnotClosedForm constant count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show flagControlledHighGates tail pivot constant
            (count + 1) hcount =
          flagControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            flagControlledHighGates tail pivot constant count
              (by omega) by rfl]
      simp [sourceControlledHighCnotClosedForm,
        flagControlledOutputBitGates_cnotMultiplicity_sum,
        ih (by omega)]

/-- Exact X coordinate of a flag-controlled high prefix. -/
theorem flagControlledHighGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail) :
    ((flagControlledHighGates tail pivot constant count hcount).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      sourceControlledHighXClosedForm constant count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show flagControlledHighGates tail pivot constant
            (count + 1) hcount =
          flagControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            flagControlledHighGates tail pivot constant count
              (by omega) by rfl]
      simp [sourceControlledHighXClosedForm,
        flagControlledOutputBitGates_xMultiplicity_sum,
        ih (by omega)]

/-- Folded basis action of the complete clean-flag-controlled adder. -/
def flagControlledAdderStep (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    State tail.succ (LiteralBorrowed tail.succ) →
      State tail.succ (LiteralBorrowed tail.succ) :=
  EncodedBit.GateSpec.stepList
    (flagControlledAdderGates tail pivot constant)

/-- Actual clean-flag-controlled X/CNOT/Toffoli constant adder. -/
def flagControlledAdderProgram (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit (Qubits (literalR0Encoding tail.succ).width) :=
  EncodedBit.GateSpec.programList
    (flagControlledAdderGates tail pivot constant)

/-- The compiled flag-controlled adder realizes its folded action. -/
theorem flagControlledAdderProgram_realizesFoldedStep (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (flagControlledAdderProgram tail pivot constant)
      (flagControlledAdderStep tail pivot constant) :=
  EncodedBit.GateSpec.realizesList
    (flagControlledAdderGates tail pivot constant)

/-- Exact Toffoli count of the complete flag-controlled adder. -/
theorem flagControlledAdderProgram_toffoli_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (flagControlledAdderProgram tail pivot constant).eventCost =
      2 * tail * tail := by
  rw [flagControlledAdderProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  by_cases hc : constant.val.testBit 0 <;>
    simp [flagControlledAdderGates, flagControlledLowGates, hc,
      flagControlledHighGates_toffoliMultiplicity_sum]

/-- Exact CNOT count of the complete flag-controlled adder. -/
theorem flagControlledAdderProgram_cnot_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (flagControlledAdderProgram tail pivot constant).eventCost =
      sourceControlledHighCnotClosedForm constant tail +
        MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant 0 := by
  rw [flagControlledAdderProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  by_cases hc : constant.val.testBit 0 <;>
    simp [flagControlledAdderGates, flagControlledLowGates, hc,
      flagControlledHighGates_cnotMultiplicity_sum,
      MAU.Addition.DirtyBorrowed.constantBitMultiplicity]

/-- Exact X count of the complete flag-controlled adder. -/
theorem flagControlledAdderProgram_x_count_eq (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (flagControlledAdderProgram tail pivot constant).eventCost =
      sourceControlledHighXClosedForm constant tail := by
  rw [flagControlledAdderProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  by_cases hc : constant.val.testBit 0 <;>
    simp [flagControlledAdderGates, flagControlledLowGates, hc,
      flagControlledHighGates_xMultiplicity_sum]

/-! ### Classical semantics of the flag-controlled adder -/

/-- One flag-controlled output block is accumulator-only replacement. -/
theorem flagControlledOutputBitGates_step_eq_withTarget (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (flagControlledOutputBitGates tail pivot constant bit) state =
      withTarget state
        (if cleanFlag state &&
            (selectedLowerCarryToggle tail constant state bit ^^
              constant.val.testBit bit.succ.val) then
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ bit.succ).flip
            (target state)
        else
          target state) := by
  rw [flagControlledOutputBitGates_step]
  simp only [literalFlagBit_get]
  by_cases htoggle : cleanFlag state &&
      (selectedLowerCarryToggle tail constant state bit ^^
        constant.val.testBit bit.succ.val)
  · rw [if_pos htoggle, if_pos htoggle,
      literalTargetBit_flip_eq_withTarget]
  · rw [if_neg htoggle, if_neg htoggle, withTarget_target]

/-- Exact accumulator readout of one flag-controlled non-low block. -/
theorem flagControlledOutputBitGates_target_testBit (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ))
    (observed : Fin tail.succ) :
    (target (EncodedBit.GateSpec.stepList
        (flagControlledOutputBitGates tail pivot constant bit) state)).val.testBit
          observed.val =
      if observed = bit.succ then
        ((target state).val.testBit observed.val ^^
          (cleanFlag state &&
            (selectedLowerCarryToggle tail constant state bit ^^
              constant.val.testBit observed.val)))
      else
        (target state).val.testBit observed.val := by
  rw [← literalTargetBit_get tail.succ observed]
  rw [← literalTargetBit_get tail.succ observed state]
  rw [flagControlledOutputBitGates_step]
  simp only [literalFlagBit_get]
  have hflip :
      ((PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ bit.succ).flip
          (target state)).val.testBit bit.succ.val =
        !(target state).val.testBit bit.succ.val := by
    simpa only [PlainAdder.Schedule.PowerOfTwo.wordBit_get] using
      (EncodedBit.get_flip_self
        (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ bit.succ)
        (target state))
  by_cases heq : observed = bit.succ
  · subst observed
    simp only [if_pos]
    cases hcontrol : cleanFlag state <;>
      cases hcarry : selectedLowerCarryToggle tail constant state bit <;>
      cases hconstant : constant.val.testBit bit.succ.val <;>
      cases hinput : (target state).val.testBit bit.succ.val <;>
      simp_all
  · simp only [if_neg heq]
    split
    · exact EncodedBit.get_flip_of_wire_ne
        (literalTargetBit tail.succ bit.succ)
        (literalTargetBit tail.succ observed)
        (literalTargetBit_wire_ne tail.succ (Ne.symm heq)) state
    · rfl

/-- A flag-controlled output block preserves its own clean control. -/
@[simp] theorem flagControlledOutputBitGates_cleanFlag (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (bit : Fin tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    cleanFlag (EncodedBit.GateSpec.stepList
        (flagControlledOutputBitGates tail pivot constant bit) state) =
      cleanFlag state := by
  rw [flagControlledOutputBitGates_step_eq_withTarget]
  exact cleanFlag_withTarget _ _

/-- The final flag-controlled low-bit layer is accumulator-only replacement. -/
theorem flagControlledLowGates_step_eq_withTarget (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (flagControlledLowGates tail constant) state =
      withTarget state
        (if cleanFlag state && constant.val.testBit 0 then
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0).flip
            (target state)
        else
          target state) := by
  by_cases hconstant : constant.val.testBit 0
  · rw [show flagControlledLowGates tail constant =
        [EncodedBit.GateSpec.cnot
          (literalFlagBit tail.succ) (literalTargetBit tail.succ 0)
          (literalTargetBit_wire_ne_flag tail.succ 0).symm] by
        simp [flagControlledLowGates, hconstant]]
    cases hcontrol : cleanFlag state
    · simp only [EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, id_eq]
      rw [EncodedBit.cnotStep]
      simp only [literalFlagBit_get, hcontrol, hconstant,
        Bool.false_eq_true, Bool.false_and, if_false, withTarget_target]
    · simp only [EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, id_eq]
      rw [EncodedBit.cnotStep]
      simp only [literalFlagBit_get, hcontrol, hconstant,
        Bool.true_and, if_true, literalTargetBit_flip_eq_withTarget]
  · rw [show flagControlledLowGates tail constant = [] by
        simp [flagControlledLowGates, hconstant]]
    have hconstantFalse : constant.val.testBit 0 = false :=
      Bool.eq_false_of_not_eq_true hconstant
    simp only [EncodedBit.GateSpec.stepList, id_eq, hconstantFalse,
      Bool.false_eq_true, Bool.and_false, if_false, withTarget_target]

/-- Exact accumulator readout after the flag-controlled low-bit layer. -/
theorem flagControlledLowGates_target_testBit (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ))
    (observed : Fin tail.succ) :
    (target (EncodedBit.GateSpec.stepList
        (flagControlledLowGates tail constant) state)).val.testBit observed.val =
      if observed = 0 then
        ((target state).val.testBit observed.val ^^
          (cleanFlag state && constant.val.testBit 0))
      else
        (target state).val.testBit observed.val := by
  rw [flagControlledLowGates_step_eq_withTarget]
  simp only [target_withTarget]
  by_cases htoggle : cleanFlag state && constant.val.testBit 0
  · rw [if_pos htoggle]
    by_cases hzero : observed = 0
    · subst observed
      simp only [if_pos]
      have hflip := EncodedBit.get_flip_self
        (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0) (target state)
      simpa only [PlainAdder.Schedule.PowerOfTwo.wordBit_get, htoggle,
        Bool.xor_true] using hflip
    · rw [if_neg hzero]
      rw [← PlainAdder.Schedule.PowerOfTwo.wordBit_get tail.succ observed]
      simpa only [PlainAdder.Schedule.PowerOfTwo.wordBit_get] using
        (EncodedBit.get_flip_of_wire_ne
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0)
          (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ observed)
          (MAU.Addition.DirtyBorrowed.straightforwardWordBit_wire_ne
            tail.succ (Ne.symm hzero)) (target state))
  · rw [if_neg htoggle]
    have htoggleFalse :
        (cleanFlag state && constant.val.testBit 0) = false :=
      Bool.eq_false_of_not_eq_true htoggle
    by_cases hzero : observed = 0
    · rw [if_pos hzero, htoggleFalse]
      simp only [Bool.xor_false]
    · rw [if_neg hzero]

/-- The high flag-controlled sweep preserves the clean control. -/
@[simp] theorem flagControlledHighGates_cleanFlag (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    cleanFlag (EncodedBit.GateSpec.stepList
        (flagControlledHighGates tail pivot constant count hcount) state) =
      cleanFlag state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [show flagControlledHighGates tail pivot constant
            (count + 1) hcount =
          flagControlledOutputBitGates tail pivot constant
              ⟨count, by omega⟩ ++
            flagControlledHighGates tail pivot constant count
              (by omega) by rfl]
      rw [EncodedBit.GateSpec.stepList_append, ih (by omega),
        flagControlledOutputBitGates_cleanFlag]

/-- After a flag-controlled high prefix, selected non-low accumulator bits
agree with fixed-width addition exactly when the clean flag is true. -/
theorem flagControlledHighGates_target_testBit (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail)
    (state : State tail.succ (LiteralBorrowed tail.succ))
    (observed : Fin tail.succ) :
    (target (EncodedBit.GateSpec.stepList
        (flagControlledHighGates tail pivot constant count hcount) state)).val.testBit
          observed.val =
      if cleanFlag state then
        if 0 < observed.val ∧ observed.val ≤ count then
          (target state + constant).val.testBit observed.val
        else
          (target state).val.testBit observed.val
      else
        (target state).val.testBit observed.val := by
  induction count generalizing state with
  | zero =>
      rw [show flagControlledHighGates tail pivot constant 0 hcount = [] by
        rfl]
      change (target state).val.testBit observed.val =
        if cleanFlag state then
          if 0 < observed.val ∧ observed.val ≤ 0 then
            (target state + constant).val.testBit observed.val
          else
            (target state).val.testBit observed.val
        else
          (target state).val.testBit observed.val
      have houtside : ¬(0 < observed.val ∧ observed.val ≤ 0) := by omega
      by_cases hcontrol : cleanFlag state
      · rw [if_pos hcontrol, if_neg houtside]
      · rw [if_neg hcontrol]
  | succ count ih =>
      let top : Fin tail := ⟨count, by omega⟩
      let afterTop := EncodedBit.GateSpec.stepList
        (flagControlledOutputBitGates tail pivot constant top) state
      rw [show flagControlledHighGates tail pivot constant
            (count + 1) hcount =
          flagControlledOutputBitGates tail pivot constant top ++
            flagControlledHighGates tail pivot constant count
              (by omega) by rfl]
      rw [EncodedBit.GateSpec.stepList_append]
      rw [ih (by omega) afterTop]
      have hcontrolAfter : cleanFlag afterTop = cleanFlag state := by
        dsimp [afterTop]
        exact flagControlledOutputBitGates_cleanFlag
          tail pivot constant top state
      rw [hcontrolAfter]
      by_cases hcontrol : cleanFlag state
      · rw [if_pos hcontrol, if_pos hcontrol]
        by_cases hinside : 0 < observed.val ∧ observed.val ≤ count
        · rw [if_pos hinside]
          have houter : 0 < observed.val ∧ observed.val ≤ count + 1 :=
            ⟨hinside.1, by omega⟩
          rw [if_pos houter]
          apply MAU.Addition.DirtyBorrowed.word_add_testBit_congr_left_of_testBit_eq_le
          intro inputBit hinputBit
          let selected : Fin tail.succ := ⟨inputBit, by omega⟩
          have hselected : selected ≠ top.succ := by
            apply Fin.ne_of_val_ne
            dsimp [selected, top]
            omega
          have hread := flagControlledOutputBitGates_target_testBit
            tail pivot constant top state selected
          simpa [afterTop, if_neg hselected] using hread
        · rw [if_neg hinside]
          by_cases htop : observed.val = count + 1
          · have hselected : observed = top.succ := by
              apply Fin.ext
              simpa [top] using htop
            have houter : 0 < observed.val ∧ observed.val ≤ count + 1 := by
              omega
            rw [if_pos houter]
            have hread := flagControlledOutputBitGates_target_testBit
              tail pivot constant top state observed
            rw [hread, if_pos hselected]
            simpa [hcontrol, selectedLowerCarryToggle, top, Fin.val_succ,
              htop, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm,
              Nat.BinaryArithmetic.natAddCarry_comm] using
                (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
                  tail.succ constant (target state) observed).symm
          · have houter :
                ¬(0 < observed.val ∧ observed.val ≤ count + 1) := by
              omega
            rw [if_neg houter]
            have hselected : observed ≠ top.succ := by
              apply Fin.ne_of_val_ne
              dsimp [top]
              omega
            have hread := flagControlledOutputBitGates_target_testBit
              tail pivot constant top state observed
            simpa [afterTop, if_neg hselected] using hread
      · rw [if_neg hcontrol, if_neg hcontrol]
        have hread := flagControlledOutputBitGates_target_testBit
          tail pivot constant top state observed
        have hcontrolFalse : cleanFlag state = false :=
          Bool.eq_false_of_not_eq_true hcontrol
        simpa [afterTop, hcontrolFalse] using hread

/-- Every flag-controlled high prefix changes only the accumulator. -/
theorem flagControlledHighGates_step_eq_withTarget (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (count : Nat) (hcount : count ≤ tail)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    EncodedBit.GateSpec.stepList
        (flagControlledHighGates tail pivot constant count hcount) state =
      withTarget state
        (target (EncodedBit.GateSpec.stepList
          (flagControlledHighGates tail pivot constant count hcount) state)) := by
  induction count generalizing state with
  | zero =>
      rw [show flagControlledHighGates tail pivot constant 0 hcount = [] by
        rfl]
      simp only [EncodedBit.GateSpec.stepList, id_eq, withTarget_target]
  | succ count ih =>
      let top : Fin tail := ⟨count, by omega⟩
      let afterTop := EncodedBit.GateSpec.stepList
        (flagControlledOutputBitGates tail pivot constant top) state
      rw [show flagControlledHighGates tail pivot constant
            (count + 1) hcount =
          flagControlledOutputBitGates tail pivot constant top ++
            flagControlledHighGates tail pivot constant count
              (by omega) by rfl]
      rw [EncodedBit.GateSpec.stepList_append]
      change EncodedBit.GateSpec.stepList
          (flagControlledHighGates tail pivot constant count (by omega))
            afterTop =
        withTarget state
          (target (EncodedBit.GateSpec.stepList
            (flagControlledHighGates tail pivot constant count (by omega))
              afterTop))
      rw [ih (by omega) afterTop]
      dsimp [afterTop]
      rw [flagControlledOutputBitGates_step_eq_withTarget]
      simp only [withTarget_withTarget]

/-- The complete flag-controlled schedule changes only the accumulator. -/
theorem flagControlledAdderStep_eq_withTargetCurrent (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    flagControlledAdderStep tail pivot constant state =
      withTarget state
        (target (flagControlledAdderStep tail pivot constant state)) := by
  unfold flagControlledAdderStep flagControlledAdderGates
  rw [EncodedBit.GateSpec.stepList_append]
  let afterHigh := EncodedBit.GateSpec.stepList
    (flagControlledHighGates tail pivot constant tail le_rfl) state
  change EncodedBit.GateSpec.stepList
      (flagControlledLowGates tail constant) afterHigh =
    withTarget state
      (target (EncodedBit.GateSpec.stepList
        (flagControlledLowGates tail constant) afterHigh))
  rw [flagControlledLowGates_step_eq_withTarget]
  let finalTarget :=
    if cleanFlag afterHigh && constant.val.testBit 0 then
      (PlainAdder.Schedule.PowerOfTwo.wordBit tail.succ 0).flip
        (target afterHigh)
    else
      target afterHigh
  change withTarget afterHigh finalTarget = withTarget state finalTarget
  dsimp [afterHigh]
  rw [flagControlledHighGates_step_eq_withTarget]
  simp only [withTarget_withTarget]

/-- The complete physical schedule adds the constant iff the clean flag is
true, while leaving that flag itself unchanged. -/
theorem flagControlledAdderStep_target (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    target (flagControlledAdderStep tail pivot constant state) =
      if cleanFlag state then target state + constant else target state := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro observed
  unfold flagControlledAdderStep flagControlledAdderGates
  rw [EncodedBit.GateSpec.stepList_append]
  let afterHigh := EncodedBit.GateSpec.stepList
    (flagControlledHighGates tail pivot constant tail le_rfl) state
  change (target (EncodedBit.GateSpec.stepList
      (flagControlledLowGates tail constant) afterHigh)).val.testBit
        observed.val = _
  rw [flagControlledLowGates_target_testBit]
  have hcontrolAfter : cleanFlag afterHigh = cleanFlag state := by
    dsimp [afterHigh]
    exact flagControlledHighGates_cleanFlag
      tail pivot constant tail le_rfl state
  rw [hcontrolAfter]
  by_cases hcontrol : cleanFlag state
  · rw [if_pos hcontrol]
    by_cases hzero : observed = 0
    · rw [if_pos hzero]
      subst observed
      have hhigh := flagControlledHighGates_target_testBit
        tail pivot constant tail le_rfl state (0 : Fin tail.succ)
      rw [hhigh, if_pos hcontrol]
      rw [if_neg (by simp : ¬(0 < (0 : Fin tail.succ).val ∧
        (0 : Fin tail.succ).val ≤ tail))]
      simpa [hcontrol, Nat.BinaryArithmetic.natAddCarry] using
        (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
          tail.succ constant (target state) 0).symm
    · rw [if_neg hzero]
      have hpositive : 0 < observed.val := by
        have hval : observed.val ≠ 0 := by
          intro h
          exact hzero (Fin.ext h)
        omega
      have hle : observed.val ≤ tail := by omega
      have hhigh := flagControlledHighGates_target_testBit
        tail pivot constant tail le_rfl state observed
      rw [hhigh, if_pos hcontrol, if_pos ⟨hpositive, hle⟩]
  · rw [if_neg hcontrol]
    have hhigh := flagControlledHighGates_target_testBit
      tail pivot constant tail le_rfl state observed
    rw [hhigh, if_neg hcontrol]
    have hcontrolFalse : cleanFlag state = false :=
      Bool.eq_false_of_not_eq_true hcontrol
    by_cases hzero : observed = 0
    · subst observed
      rw [if_pos rfl, hcontrolFalse]
      simp only [Bool.false_and, Bool.xor_false]
    · rw [if_neg hzero]

/-- Classical clean-flag-controlled addition on the literal carrier. -/
def flagControlledAdd (tail : Nat) (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    State tail.succ (LiteralBorrowed tail.succ) :=
  if cleanFlag state then
    withTarget state (target state + constant)
  else
    state

/-- The folded flag-controlled gate action has the advertised semantics. -/
theorem flagControlledAdderStep_eq (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    flagControlledAdderStep tail pivot constant state =
      flagControlledAdd tail constant state := by
  rw [flagControlledAdderStep_eq_withTargetCurrent,
    flagControlledAdderStep_target]
  unfold flagControlledAdd
  by_cases hcontrol : cleanFlag state
  · rw [if_pos hcontrol, if_pos hcontrol]
  · rw [if_neg hcontrol, if_neg hcontrol, withTarget_target]

/-- The actual flag-controlled circuit realizes its classical transition. -/
theorem flagControlledAdderProgram_realizes (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (flagControlledAdderProgram tail pivot constant)
      (flagControlledAdd tail constant) :=
  UnitaryCircuit.Realizes.congrStep
    (flagControlledAdderProgram_realizesFoldedStep tail pivot constant)
    (flagControlledAdderStep_eq tail pivot constant)

/-! ## Selected terminal carry for widths at least three -/

/-- Highest accumulator bit in an HRS word of width `interior+3`. -/
def selectedTerminalTopBit (interior : Nat)
    (_pivot : Fin (interior + 2).succ) :
    EncodedBit (literalR0Encoding (interior + 2).succ) :=
  literalTargetBit (interior + 2).succ (Fin.last (interior + 2))

/-- Dirty bit holding the carry entering the highest accumulator bit. -/
def selectedTerminalCarryBit (interior : Nat)
    (pivot : Fin (interior + 2).succ) :
    EncodedBit (literalR0Encoding (interior + 2).succ) :=
  literalCarryDirtyBit pivot (Fin.last (interior + 1))

/-- A distinct residual source bit used as arbitrary dirty work by the
four-Toffoli triple-control realization. -/
def selectedTerminalWorkBit (interior : Nat)
    (pivot : Fin (interior + 2).succ) :
    EncodedBit (literalR0Encoding (interior + 2).succ) :=
  literalCarryDirtyBit pivot 0

/-- The carry-holding residual bit and dirty work bit are distinct for every
word width `interior+3`. -/
theorem selectedTerminalCarryBit_wire_ne_workBit (interior : Nat)
    (pivot : Fin (interior + 2).succ) :
    (selectedTerminalCarryBit interior pivot).wire ≠
      (selectedTerminalWorkBit interior pivot).wire := by
  apply literalCarryDirtyBit_wire_ne pivot
  apply Fin.ne_of_val_ne
  simp

/-- Four-Toffoli selected `top ∧ carry` copy into the clean flag, using a
fully arbitrary dirty work bit. -/
def selectedTerminalAndGates (interior : Nat)
    (pivot : Fin (interior + 2).succ) :
    List (EncodedBit.GateSpec (literalR0Encoding (interior + 2).succ)) :=
  let selector := literalSelectedSourceBit pivot
  let top := selectedTerminalTopBit interior pivot
  let carry := selectedTerminalCarryBit interior pivot
  let flag := literalFlagBit (interior + 2).succ
  let work := selectedTerminalWorkBit interior pivot
  dirtyTripleControlledXGates selector top carry flag work
    (literalSelectedSourceBit_wire_ne_targetBit pivot (Fin.last (interior + 2)))
    (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot (Fin.last (interior + 1)))
    (literalSelectedSourceBit_wire_ne_flag pivot)
    (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot 0)
    ((literalCarryDirtyBit_wire_ne_targetBit pivot
      (Fin.last (interior + 1)) (Fin.last (interior + 2))).symm)
    (literalTargetBit_wire_ne_flag (interior + 2).succ
      (Fin.last (interior + 2)))
    ((literalCarryDirtyBit_wire_ne_targetBit pivot 0
      (Fin.last (interior + 2))).symm)
    (literalCarryDirtyBit_wire_ne_flag pivot (Fin.last (interior + 1)))
    (selectedTerminalCarryBit_wire_ne_workBit interior pivot)
    ((literalCarryDirtyBit_wire_ne_flag pivot 0).symm)

/-- Terminal selected carry-out gate list.  If the highest constant bit is
zero, carry-out is `top ∧ carry`.  If it is one, the two leading Toffolis
add `selector ∧ top` and `selector ∧ carry`, so together with the dirty
triple-control term the flag receives `selector ∧ (top ∨ carry)`. -/
def selectedTerminalCarryGates (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    List (EncodedBit.GateSpec (literalR0Encoding (interior + 2).succ)) :=
  let selector := literalSelectedSourceBit pivot
  let top := selectedTerminalTopBit interior pivot
  let carry := selectedTerminalCarryBit interior pivot
  let flag := literalFlagBit (interior + 2).succ
  if constant.val.testBit (interior + 2) then
    [ EncodedBit.GateSpec.toffoli selector top flag
        (literalSelectedSourceBit_wire_ne_targetBit pivot
          (Fin.last (interior + 2)))
        (literalSelectedSourceBit_wire_ne_flag pivot)
        (literalTargetBit_wire_ne_flag (interior + 2).succ
          (Fin.last (interior + 2)))
    , EncodedBit.GateSpec.toffoli selector carry flag
        (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot
          (Fin.last (interior + 1)))
        (literalSelectedSourceBit_wire_ne_flag pivot)
        (literalCarryDirtyBit_wire_ne_flag pivot
          (Fin.last (interior + 1))) ] ++
      selectedTerminalAndGates interior pivot
  else
    selectedTerminalAndGates interior pivot

private theorem selectedTerminalCarryGates_toffoliMultiplicity_sum
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedTerminalCarryGates interior pivot constant).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        if constant.val.testBit (interior + 2) then 6 else 4 := by
  by_cases hc : constant.val.testBit (interior + 2)
  · simp only [selectedTerminalCarryGates, hc, if_true]
    change 6 = 6
    rfl
  · simp only [selectedTerminalCarryGates, hc]
    change 4 = 4
    rfl

private theorem selectedTerminalCarryGates_cnotMultiplicity_sum
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedTerminalCarryGates interior pivot constant).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  by_cases hc : constant.val.testBit (interior + 2)
  · simp only [selectedTerminalCarryGates, hc, if_true]
    change 0 = 0
    rfl
  · simp only [selectedTerminalCarryGates, hc]
    change 0 = 0
    rfl

private theorem selectedTerminalCarryGates_xMultiplicity_sum
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedTerminalCarryGates interior pivot constant).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  by_cases hc : constant.val.testBit (interior + 2)
  · simp only [selectedTerminalCarryGates, hc, if_true]
    change 0 = 0
    rfl
  · simp only [selectedTerminalCarryGates, hc]
    change 0 = 0
    rfl

/-- The four-Toffoli terminal AND block has its advertised arbitrary-dirty
semantics on the concrete HRS bits. -/
theorem selectedTerminalAndGates_step (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    EncodedBit.GateSpec.stepList
        (selectedTerminalAndGates interior pivot) state =
      if (literalSelectedSourceBit pivot).get state &&
          (selectedTerminalTopBit interior pivot).get state &&
          (selectedTerminalCarryBit interior pivot).get state then
        (literalFlagBit (interior + 2).succ).flip state
      else
        state := by
  simpa [selectedTerminalAndGates, dirtyTripleControlledXStep] using
    (dirtyTripleControlledXStep_eq
      (literalSelectedSourceBit pivot)
      (selectedTerminalTopBit interior pivot)
      (selectedTerminalCarryBit interior pivot)
      (literalFlagBit (interior + 2).succ)
      (selectedTerminalWorkBit interior pivot)
      (literalSelectedSourceBit_wire_ne_targetBit pivot
        (Fin.last (interior + 2)))
      (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot
        (Fin.last (interior + 1)))
      (literalSelectedSourceBit_wire_ne_flag pivot)
      (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot 0)
      ((literalCarryDirtyBit_wire_ne_targetBit pivot
        (Fin.last (interior + 1)) (Fin.last (interior + 2))).symm)
      (literalTargetBit_wire_ne_flag (interior + 2).succ
        (Fin.last (interior + 2)))
      ((literalCarryDirtyBit_wire_ne_targetBit pivot 0
        (Fin.last (interior + 2))).symm)
      (literalCarryDirtyBit_wire_ne_flag pivot (Fin.last (interior + 1)))
      (selectedTerminalCarryBit_wire_ne_workBit interior pivot)
      ((literalCarryDirtyBit_wire_ne_flag pivot 0).symm)
      state)

/-- Boolean toggle copied to the clean flag by the terminal selected-carry
block. -/
def selectedTerminalCarryToggle (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) : Bool :=
  (literalSelectedSourceBit pivot).get state &&
    Bool.carry
      ((selectedTerminalTopBit interior pivot).get state)
      (constant.val.testBit (interior + 2))
      ((selectedTerminalCarryBit interior pivot).get state)

/-- Both highest-constant branches implement the same selected carry-out
formula.  The arbitrary dirty work bit is restored by the four-Toffoli block. -/
theorem selectedTerminalCarryGates_step (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    EncodedBit.GateSpec.stepList
        (selectedTerminalCarryGates interior pivot constant) state =
      if selectedTerminalCarryToggle interior pivot constant state then
        (literalFlagBit (interior + 2).succ).flip state
      else
        state := by
  let selector := literalSelectedSourceBit pivot
  let top := selectedTerminalTopBit interior pivot
  let carry := selectedTerminalCarryBit interior pivot
  let flag := literalFlagBit (interior + 2).succ
  have hselectorFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      selector.get (flag.flip input) = selector.get input :=
    EncodedBit.get_flip_of_wire_ne flag selector
      (literalSelectedSourceBit_wire_ne_flag pivot).symm input
  have htopFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      top.get (flag.flip input) = top.get input :=
    EncodedBit.get_flip_of_wire_ne flag top
      (literalTargetBit_wire_ne_flag (interior + 2).succ
        (Fin.last (interior + 2))).symm input
  have hcarryFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      carry.get (flag.flip input) = carry.get input :=
    EncodedBit.get_flip_of_wire_ne flag carry
      (literalCarryDirtyBit_wire_ne_flag pivot
        (Fin.last (interior + 1))).symm input
  have hprefix :
      EncodedBit.GateSpec.stepList
          [ EncodedBit.GateSpec.toffoli selector top flag
              (literalSelectedSourceBit_wire_ne_targetBit pivot
                (Fin.last (interior + 2)))
              (literalSelectedSourceBit_wire_ne_flag pivot)
              (literalTargetBit_wire_ne_flag (interior + 2).succ
                (Fin.last (interior + 2)))
          , EncodedBit.GateSpec.toffoli selector carry flag
              (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot
                (Fin.last (interior + 1)))
              (literalSelectedSourceBit_wire_ne_flag pivot)
              (literalCarryDirtyBit_wire_ne_flag pivot
                (Fin.last (interior + 1))) ] state =
        if selector.get state && (top.get state ^^ carry.get state) then
          flag.flip state
        else
          state := by
    simp only [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step, id_eq]
    cases hselector : selector.get state <;>
      cases htop : top.get state <;>
      cases hcarry : carry.get state <;>
      simp [EncodedBit.toffoliStep, hselector, htop, hcarry,
        hselectorFlag, hcarryFlag, EncodedBit.flip_flip]
  have hterminal (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      EncodedBit.GateSpec.stepList
          (selectedTerminalAndGates interior pivot) input =
        if selector.get input && top.get input && carry.get input then
          flag.flip input
        else
          input :=
    selectedTerminalAndGates_step interior pivot input
  have htoggle : selectedTerminalCarryToggle interior pivot constant state =
      (selector.get state &&
        Bool.carry (top.get state)
          (constant.val.testBit (interior + 2)) (carry.get state)) :=
    rfl
  by_cases hconstant : constant.val.testBit (interior + 2)
  · rw [show selectedTerminalCarryGates interior pivot constant =
        [ EncodedBit.GateSpec.toffoli selector top flag
            (literalSelectedSourceBit_wire_ne_targetBit pivot
              (Fin.last (interior + 2)))
            (literalSelectedSourceBit_wire_ne_flag pivot)
            (literalTargetBit_wire_ne_flag (interior + 2).succ
              (Fin.last (interior + 2)))
        , EncodedBit.GateSpec.toffoli selector carry flag
            (literalSelectedSourceBit_wire_ne_carryDirtyBit pivot
              (Fin.last (interior + 1)))
            (literalSelectedSourceBit_wire_ne_flag pivot)
            (literalCarryDirtyBit_wire_ne_flag pivot
              (Fin.last (interior + 1))) ] ++
          selectedTerminalAndGates interior pivot by
        simp [selectedTerminalCarryGates, selector, top, carry, flag,
          hconstant]]
    rw [EncodedBit.GateSpec.stepList_append]
    rw [hterminal]
    rw [hprefix]
    rw [htoggle, hconstant]
    cases hselector : selector.get state <;>
      cases htop : top.get state <;>
      cases hcarry : carry.get state <;>
      simp [flag, hselector, htop, hcarry,
        hselectorFlag, htopFlag, hcarryFlag,
        Bool.carry]
  · rw [show selectedTerminalCarryGates interior pivot constant =
        selectedTerminalAndGates interior pivot by
        simp [selectedTerminalCarryGates, hconstant]]
    rw [hterminal]
    rw [htoggle]
    rw [show constant.val.testBit (interior + 2) = false from
      Bool.eq_false_of_not_eq_true hconstant]
    simp [flag, Bool.carry, Bool.and_assoc]

/-- Actual compiled selected terminal carry circuit. -/
def selectedTerminalCarryProgram (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    UnitaryCircuit (Qubits (literalR0Encoding (interior + 2).succ).width) :=
  EncodedBit.GateSpec.programList
    (selectedTerminalCarryGates interior pivot constant)

/-- The compiled terminal list realizes its folded base-gate action. -/
theorem selectedTerminalCarryProgram_realizes (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    UnitaryCircuit.Realizes (literalR0Encoding (interior + 2).succ)
      (selectedTerminalCarryProgram interior pivot constant)
      (EncodedBit.GateSpec.stepList
        (selectedTerminalCarryGates interior pivot constant)) :=
  EncodedBit.GateSpec.realizesList
    (selectedTerminalCarryGates interior pivot constant)

/-- The selected terminal block uses four Toffolis when the highest constant
bit is zero and six when it is one. -/
theorem selectedTerminalCarryProgram_toffoli_count_eq (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (selectedTerminalCarryProgram interior pivot constant).eventCost =
      if constant.val.testBit (interior + 2) then 6 else 4 := by
  rw [selectedTerminalCarryProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact selectedTerminalCarryGates_toffoliMultiplicity_sum
    interior pivot constant

/-- No CNOT coordinate is hidden in the terminal selected carry block. -/
theorem selectedTerminalCarryProgram_cnot_count_eq_zero (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (selectedTerminalCarryProgram interior pivot constant).eventCost = 0 := by
  rw [selectedTerminalCarryProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact selectedTerminalCarryGates_cnotMultiplicity_sum
    interior pivot constant

/-- No X coordinate is hidden in the terminal selected carry block. -/
theorem selectedTerminalCarryProgram_x_count_eq_zero (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (selectedTerminalCarryProgram interior pivot constant).eventCost = 0 := by
  rw [selectedTerminalCarryProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact selectedTerminalCarryGates_xMultiplicity_sum
    interior pivot constant

/-! ## Reversible selected carry extraction for widths at least three -/

/-- The lower carry prefix used immediately before the terminal selected-copy
block.  Its last residual dirty bit holds the carry entering the highest
accumulator bit. -/
def selectedCarryIntoFlagLowerGates (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    List (EncodedBit.GateSpec (literalR0Encoding (interior + 2).succ)) :=
  selectedLowerCarryGates (interior + 2) pivot constant
    (Fin.last (interior + 1))

/-- Highest-constant correction required after dirty-value cancellation.  When
the highest constant bit is one, this contributes the missing
`selector ∧ top` term. -/
def selectedCarryIntoFlagCorrectionGates (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    List (EncodedBit.GateSpec (literalR0Encoding (interior + 2).succ)) :=
  if constant.val.testBit (interior + 2) then
    [EncodedBit.GateSpec.toffoli
      (literalSelectedSourceBit pivot)
      (selectedTerminalTopBit interior pivot)
      (literalFlagBit (interior + 2).succ)
      (literalSelectedSourceBit_wire_ne_targetBit pivot
        (Fin.last (interior + 2)))
      (literalSelectedSourceBit_wire_ne_flag pivot)
      (literalTargetBit_wire_ne_flag (interior + 2).succ
        (Fin.last (interior + 2)))]
  else
    []

private theorem selectedCarryIntoFlagCorrectionGates_toffoliMultiplicity_sum
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedCarryIntoFlagCorrectionGates interior pivot constant).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        if constant.val.testBit (interior + 2) then 1 else 0 := by
  by_cases hc : constant.val.testBit (interior + 2)
  · simp only [selectedCarryIntoFlagCorrectionGates, hc, if_true]
    change 1 = 1
    rfl
  · simp only [selectedCarryIntoFlagCorrectionGates, hc,
      Bool.false_eq_true, if_false, List.map_nil, List.sum_nil]

private theorem selectedCarryIntoFlagCorrectionGates_cnotMultiplicity_sum
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedCarryIntoFlagCorrectionGates interior pivot constant).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  by_cases hc : constant.val.testBit (interior + 2)
  · simp only [selectedCarryIntoFlagCorrectionGates, hc, if_true]
    change 0 = 0
    rfl
  · simp only [selectedCarryIntoFlagCorrectionGates, hc,
      Bool.false_eq_true, if_false, List.map_nil, List.sum_nil]

private theorem selectedCarryIntoFlagCorrectionGates_xMultiplicity_sum
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedCarryIntoFlagCorrectionGates interior pivot constant).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  by_cases hc : constant.val.testBit (interior + 2)
  · simp only [selectedCarryIntoFlagCorrectionGates, hc, if_true]
    change 0 = 0
    rfl
  · simp only [selectedCarryIntoFlagCorrectionGates, hc,
      Bool.false_eq_true, if_false, List.map_nil, List.sum_nil]

/-- Boolean action of the highest-constant correction. -/
def selectedCarryIntoFlagCorrectionToggle (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) : Bool :=
  constant.val.testBit (interior + 2) &&
    (literalSelectedSourceBit pivot).get state &&
    (selectedTerminalTopBit interior pivot).get state

/-- The correction list has exactly its advertised selected top-bit action. -/
theorem selectedCarryIntoFlagCorrectionGates_step (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    EncodedBit.GateSpec.stepList
        (selectedCarryIntoFlagCorrectionGates interior pivot constant) state =
      if selectedCarryIntoFlagCorrectionToggle interior pivot constant state then
        (literalFlagBit (interior + 2).succ).flip state
      else
        state := by
  by_cases hc : constant.val.testBit (interior + 2)
  · simp [selectedCarryIntoFlagCorrectionGates,
      selectedCarryIntoFlagCorrectionToggle, hc,
      EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
      EncodedBit.toffoliStep]
  · simp [selectedCarryIntoFlagCorrectionGates,
      selectedCarryIntoFlagCorrectionToggle, hc,
      EncodedBit.GateSpec.stepList]

/-- The dirty-carry cancellation identity used by the physical construction. -/
theorem selectedCarryDirtyCancellation (selector top constantTop dirty carry : Bool) :
    ((selector && Bool.carry top constantTop (dirty ^^ carry)) ^^
      (selector && Bool.carry top constantTop dirty) ^^
      (constantTop && selector && top)) =
    (selector && Bool.carry top constantTop carry) := by
  cases selector <;> cases top <;> cases constantTop <;>
    cases dirty <;> cases carry <;> rfl

/-- Desired dirty-independent selected carry copied to the clean flag. -/
def selectedCarryIntoFlagToggle (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) : Bool :=
  (literalSelectedSourceBit pivot).get state &&
    Bool.carry
      ((selectedTerminalTopBit interior pivot).get state)
      (constant.val.testBit (interior + 2))
      (selectedLowerCarryToggle (interior + 2) constant state
        (Fin.last (interior + 1)))

/-- The compiled selected carry predicate is exactly a source-bit-selected
overflow comparison on the complete accumulator word. -/
theorem selectedCarryIntoFlagToggle_eq_overflow (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    selectedCarryIntoFlagToggle interior pivot constant state =
      ((source state).val.testBit pivot.val &&
        decide (2 ^ (interior + 2).succ ≤
          (target state).val + constant.val)) := by
  rw [show selectedCarryIntoFlagToggle interior pivot constant state =
      ((source state).val.testBit pivot.val &&
        Nat.BinaryArithmetic.natAddCarry
          (target state).val constant.val (interior + 2).succ) by
    simp [selectedCarryIntoFlagToggle, selectedLowerCarryToggle,
      selectedTerminalTopBit, Nat.BinaryArithmetic.natAddCarry]]
  rw [Nat.BinaryArithmetic.natAddCarry_eq_decide_two_pow_le
    (ZMod.val_lt (target state)) (ZMod.val_lt constant)]

/-- Fixed-width constant whose addition overflows exactly at `threshold`.
The positivity side condition below rules out the degenerate value `2^n`,
whose cast into the word would be zero. -/
def overflowComparisonConstant (n threshold : Nat) : PlainAdder.Word n :=
  ((2 ^ n - threshold : Nat) : PlainAdder.Word n)

@[simp] theorem overflowComparisonConstant_val {n threshold : Nat}
    (hthreshold : 0 < threshold) :
    (overflowComparisonConstant n threshold).val = 2 ^ n - threshold := by
  unfold overflowComparisonConstant
  apply ZMod.val_natCast_of_lt
  have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
  omega

/-- Instantiating the selected carry extractor with the two's-complement of a
positive threshold gives a literal selected `threshold ≤ target` comparator. -/
theorem selectedCarryIntoFlagToggle_comparison (interior threshold : Nat)
    (pivot : Fin (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ))
    (hthresholdPos : 0 < threshold)
    (hthresholdWidth : threshold < 2 ^ (interior + 2).succ) :
    selectedCarryIntoFlagToggle interior pivot
        (overflowComparisonConstant (interior + 2).succ threshold) state =
      ((source state).val.testBit pivot.val &&
        decide (threshold ≤ (target state).val)) := by
  rw [selectedCarryIntoFlagToggle_eq_overflow,
    overflowComparisonConstant_val hthresholdPos]
  have htargetWidth := ZMod.val_lt (target state)
  by_cases hcomparison : threshold ≤ (target state).val
  · have hoverflow : 2 ^ (interior + 2).succ ≤
        (target state).val + (2 ^ (interior + 2).succ - threshold) := by
      omega
    simp [hcomparison, hoverflow]
  · have hnoOverflow : ¬2 ^ (interior + 2).succ ≤
        (target state).val + (2 ^ (interior + 2).succ - threshold) := by
      omega
    simp [hcomparison, hnoOverflow]

/-- Compute the lower carry, copy once, uncompute, copy the original dirty
value a second time, then add the highest-constant correction.  The two copies
cancel every dependence on the arbitrary source bit borrowed for carry work. -/
def selectedCarryIntoFlagGates (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    List (EncodedBit.GateSpec (literalR0Encoding (interior + 2).succ)) :=
  let lower := selectedCarryIntoFlagLowerGates interior pivot constant
  let terminal := selectedTerminalCarryGates interior pivot constant
  lower ++ terminal ++ lower.reverse ++ terminal ++
    selectedCarryIntoFlagCorrectionGates interior pivot constant

/-- The lower carry prefix is completely disjoint from the clean output flag. -/
theorem selectedCarryIntoFlagLowerGates_forall_bitDisjoint_flag
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    (selectedCarryIntoFlagLowerGates interior pivot constant).Forall
      (EncodedBit.GateSpec.bitDisjoint
        (literalFlagBit (interior + 2).succ)) := by
  exact selectedLowerCarryGates_forall_bitDisjoint_flag
    (interior + 2) pivot constant (Fin.last (interior + 1))

/-- The complete dirty compute-copy-uncompute-copy block restores every
borrowed wire and toggles only the clean flag by the selected arithmetic carry,
with no dependence on any dirty initial value. -/
theorem selectedCarryIntoFlagGates_step (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    EncodedBit.GateSpec.stepList
        (selectedCarryIntoFlagGates interior pivot constant) state =
      if selectedCarryIntoFlagToggle interior pivot constant state then
        (literalFlagBit (interior + 2).succ).flip state
      else
        state := by
  let lower := selectedCarryIntoFlagLowerGates interior pivot constant
  let terminal := selectedTerminalCarryGates interior pivot constant
  let correction :=
    selectedCarryIntoFlagCorrectionGates interior pivot constant
  let selector := literalSelectedSourceBit pivot
  let top := selectedTerminalTopBit interior pivot
  let carry := selectedTerminalCarryBit interior pivot
  let flag := literalFlagBit (interior + 2).succ
  have hdisjoint :
      ∀ gate, gate ∈ lower → EncodedBit.GateSpec.bitDisjoint flag gate := by
    intro gate hgate
    exact List.forall_iff_forall_mem.mp
      (selectedCarryIntoFlagLowerGates_forall_bitDisjoint_flag
        interior pivot constant) gate hgate
  have huncompute :
      EncodedBit.GateSpec.stepList lower.reverse
          (EncodedBit.GateSpec.stepList lower state) = state :=
    EncodedBit.GateSpec.stepList_reverse_stepList lower state
  have huncomputeFlip :
      EncodedBit.GateSpec.stepList lower.reverse
          (flag.flip (EncodedBit.GateSpec.stepList lower state)) =
        flag.flip state := by
    rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint]
    · exact congrArg flag.flip
        (EncodedBit.GateSpec.stepList_reverse_stepList lower state)
    · intro gate hgate
      exact hdisjoint gate (List.mem_reverse.mp hgate)
  have hselectorLower :
      selector.get (EncodedBit.GateSpec.stepList lower state) =
        selector.get state := by
    apply stepList_get_of_forall_bitDisjoint
    intro gate hgate
    exact List.forall_iff_forall_mem.mp
      (selectedLowerCarryGates_forall_bitDisjoint_selector
        (interior + 2) pivot constant (Fin.last (interior + 1))) gate hgate
  have htopLower : top.get (EncodedBit.GateSpec.stepList lower state) =
      top.get state := by
    dsimp [top, lower, selectedCarryIntoFlagLowerGates,
      selectedTerminalTopBit]
    simp only [literalTargetBit_get]
    rw [selectedLowerCarryGates_target]
  have hcarryLower : carry.get (EncodedBit.GateSpec.stepList lower state) =
      (carry.get state ^^
        selectedLowerCarryToggle (interior + 2) constant state
          (Fin.last (interior + 1))) := by
    simpa [carry, lower, selectedCarryIntoFlagLowerGates,
      selectedTerminalCarryBit] using
      (selectedLowerCarryGates_currentDirty_get
        (interior + 2) pivot constant (Fin.last (interior + 1)) state)
  have hselectorFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      selector.get (flag.flip input) = selector.get input :=
    EncodedBit.get_flip_of_wire_ne flag selector
      (literalSelectedSourceBit_wire_ne_flag pivot).symm input
  have htopFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      top.get (flag.flip input) = top.get input :=
    EncodedBit.get_flip_of_wire_ne flag top
      (literalTargetBit_wire_ne_flag (interior + 2).succ
        (Fin.last (interior + 2))).symm input
  have hcarryFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      carry.get (flag.flip input) = carry.get input :=
    EncodedBit.get_flip_of_wire_ne flag carry
      (literalCarryDirtyBit_wire_ne_flag pivot
        (Fin.last (interior + 1))).symm input
  have hterminal (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      EncodedBit.GateSpec.stepList terminal input =
        if selectedTerminalCarryToggle interior pivot constant input then
          flag.flip input
        else
          input :=
    selectedTerminalCarryGates_step interior pivot constant input
  have hterminalFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      selectedTerminalCarryToggle interior pivot constant (flag.flip input) =
        selectedTerminalCarryToggle interior pivot constant input := by
    unfold selectedTerminalCarryToggle
    rw [hselectorFlag, htopFlag, hcarryFlag]
  have hcorrection (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      EncodedBit.GateSpec.stepList correction input =
        if selectedCarryIntoFlagCorrectionToggle
            interior pivot constant input then
          flag.flip input
        else
          input :=
    selectedCarryIntoFlagCorrectionGates_step
      interior pivot constant input
  have hcorrectionFlag (input : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
      selectedCarryIntoFlagCorrectionToggle interior pivot constant
          (flag.flip input) =
        selectedCarryIntoFlagCorrectionToggle interior pivot constant input := by
    unfold selectedCarryIntoFlagCorrectionToggle
    rw [hselectorFlag, htopFlag]
  have hterminalLower :
      selectedTerminalCarryToggle interior pivot constant
          (EncodedBit.GateSpec.stepList lower state) =
        (selector.get state &&
          Bool.carry (top.get state)
            (constant.val.testBit (interior + 2))
            (carry.get state ^^
              selectedLowerCarryToggle (interior + 2) constant state
                (Fin.last (interior + 1)))) := by
    unfold selectedTerminalCarryToggle
    rw [hselectorLower, htopLower, hcarryLower]
  have hterminalState :
      selectedTerminalCarryToggle interior pivot constant state =
        (selector.get state &&
          Bool.carry (top.get state)
            (constant.val.testBit (interior + 2)) (carry.get state)) :=
    rfl
  have hcorrectionState :
      selectedCarryIntoFlagCorrectionToggle interior pivot constant state =
        (constant.val.testBit (interior + 2) &&
          selector.get state && top.get state) :=
    rfl
  have hdesired : selectedCarryIntoFlagToggle interior pivot constant state =
      (selector.get state &&
        Bool.carry (top.get state)
          (constant.val.testBit (interior + 2))
          (selectedLowerCarryToggle (interior + 2) constant state
            (Fin.last (interior + 1)))) :=
    rfl
  unfold selectedCarryIntoFlagGates
  change EncodedBit.GateSpec.stepList
      (lower ++ terminal ++ lower.reverse ++ terminal ++ correction) state = _
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [hterminal (EncodedBit.GateSpec.stepList lower state), hterminalLower]
  cases hselector : selector.get state <;>
    cases htop : top.get state <;>
    cases hconstant : constant.val.testBit (interior + 2) <;>
    cases hdirty : carry.get state <;>
    cases hlower : selectedLowerCarryToggle (interior + 2) constant state
      (Fin.last (interior + 1)) <;>
    simp [hselector, htop, hconstant, hdirty, hlower,
      huncompute, huncomputeFlip, hterminal, hterminalFlag,
      hterminalState, hcorrection, hcorrectionFlag, hcorrectionState,
      hdesired, flag, Bool.carry, EncodedBit.flip_flip]

/-- Folded basis action of the complete selected carry extractor. -/
def selectedCarryIntoFlagStep (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    State (interior + 2).succ (LiteralBorrowed (interior + 2).succ) →
      State (interior + 2).succ (LiteralBorrowed (interior + 2).succ) :=
  EncodedBit.GateSpec.stepList
    (selectedCarryIntoFlagGates interior pivot constant)

/-- The selected comparator changes only the clean flag, toggling it by its
literal selected-carry predicate. -/
theorem selectedCarryIntoFlagStep_eq_withCleanFlag (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    selectedCarryIntoFlagStep interior pivot constant state =
      withCleanFlag state
        (cleanFlag state ^^
          selectedCarryIntoFlagToggle interior pivot constant state) := by
  unfold selectedCarryIntoFlagStep
  rw [selectedCarryIntoFlagGates_step]
  cases htoggle : selectedCarryIntoFlagToggle interior pivot constant state <;>
    simp [literalFlagBit_flip_eq_withCleanFlag]

/-- Exact state transition of the compiled positive-threshold comparator. -/
theorem selectedCarryIntoFlagStep_comparison (interior threshold : Nat)
    (pivot : Fin (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ))
    (hthresholdPos : 0 < threshold)
    (hthresholdWidth : threshold < 2 ^ (interior + 2).succ) :
    selectedCarryIntoFlagStep interior pivot
        (overflowComparisonConstant (interior + 2).succ threshold) state =
      withCleanFlag state
        (cleanFlag state ^^
          ((source state).val.testBit pivot.val &&
            decide (threshold ≤ (target state).val))) := by
  rw [selectedCarryIntoFlagStep_eq_withCleanFlag,
    selectedCarryIntoFlagToggle_comparison interior threshold pivot state
      hthresholdPos hthresholdWidth]

/-- Actual X/CNOT/Toffoli circuit for the reversible selected carry extractor. -/
def selectedCarryIntoFlagProgram (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    UnitaryCircuit (Qubits (literalR0Encoding (interior + 2).succ).width) :=
  EncodedBit.GateSpec.programList
    (selectedCarryIntoFlagGates interior pivot constant)

/-- The compiled circuit realizes the same folded basis action used by the
restoration theorem. -/
theorem selectedCarryIntoFlagProgram_realizes (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    UnitaryCircuit.Realizes (literalR0Encoding (interior + 2).succ)
      (selectedCarryIntoFlagProgram interior pivot constant)
      (selectedCarryIntoFlagStep interior pivot constant) :=
  EncodedBit.GateSpec.realizesList
    (selectedCarryIntoFlagGates interior pivot constant)

/-- Exact Toffoli coordinate of the complete compute-copy-uncompute block. -/
theorem selectedCarryIntoFlagProgram_toffoli_count_eq (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (selectedCarryIntoFlagProgram interior pivot constant).eventCost =
      4 * (interior + 1) +
        if constant.val.testBit (interior + 2) then 13 else 8 := by
  let lower := selectedCarryIntoFlagLowerGates interior pivot constant
  let terminal := selectedTerminalCarryGates interior pivot constant
  let correction :=
    selectedCarryIntoFlagCorrectionGates interior pivot constant
  have hlower :
      (lower.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
        2 * (Fin.last (interior + 1)).val := by
    dsimp [lower, selectedCarryIntoFlagLowerGates]
    calc
      ((selectedLowerCarryGates (interior + 2) pivot constant
          (Fin.last (interior + 1))).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum =
          ((MAU.Addition.DirtyBorrowed.straightforwardCarryGates
            (interior + 2) constant (Fin.last (interior + 1))).map
            EncodedBit.GateSpec.toffoliMultiplicity).sum := by
        apply EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        exact selectedLowerCarryGates_eventTrace_eq
          (interior + 2) pivot constant (Fin.last (interior + 1))
      _ = 2 * (Fin.last (interior + 1)).val :=
        MAU.Addition.DirtyBorrowed.straightforwardCarryGates_toffoliMultiplicity_sum
            (interior + 2) constant (Fin.last (interior + 1))
  have hterminal :
      (terminal.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
        if constant.val.testBit (interior + 2) then 6 else 4 := by
    exact selectedTerminalCarryGates_toffoliMultiplicity_sum
      interior pivot constant
  have hcorrection :
      (correction.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
        if constant.val.testBit (interior + 2) then 1 else 0 := by
    exact selectedCarryIntoFlagCorrectionGates_toffoliMultiplicity_sum
      interior pivot constant
  rw [selectedCarryIntoFlagProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  change ((lower ++ terminal ++ lower.reverse ++ terminal ++ correction).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _
  simp only [List.map_append, List.sum_append, List.map_reverse,
    List.sum_reverse]
  rw [hlower, hterminal, hcorrection]
  by_cases hc : constant.val.testBit (interior + 2) <;>
    simp [hc] <;> omega

/-- Exact CNOT coordinate of the complete compute-copy-uncompute block. -/
theorem selectedCarryIntoFlagProgram_cnot_count_eq (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (selectedCarryIntoFlagProgram interior pivot constant).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
        constant (interior + 2) := by
  let lower := selectedCarryIntoFlagLowerGates interior pivot constant
  let terminal := selectedTerminalCarryGates interior pivot constant
  let correction :=
    selectedCarryIntoFlagCorrectionGates interior pivot constant
  have hlower :
      (lower.map EncodedBit.GateSpec.cnotMultiplicity).sum =
        MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (interior + 2) := by
    dsimp [lower, selectedCarryIntoFlagLowerGates]
    calc
      ((selectedLowerCarryGates (interior + 2) pivot constant
          (Fin.last (interior + 1))).map
          EncodedBit.GateSpec.cnotMultiplicity).sum =
          ((MAU.Addition.DirtyBorrowed.straightforwardCarryGates
            (interior + 2) constant (Fin.last (interior + 1))).map
            EncodedBit.GateSpec.cnotMultiplicity).sum := by
        apply EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        exact selectedLowerCarryGates_eventTrace_eq
          (interior + 2) pivot constant (Fin.last (interior + 1))
      _ = MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          constant (interior + 2) := by
        convert MAU.Addition.DirtyBorrowed.straightforwardCarryGates_cnotMultiplicity_sum
            (interior + 2) constant (Fin.last (interior + 1)) using 1
        all_goals simp
  have hterminal :
      (terminal.map EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
    exact selectedTerminalCarryGates_cnotMultiplicity_sum
      interior pivot constant
  have hcorrection :
      (correction.map EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
    exact selectedCarryIntoFlagCorrectionGates_cnotMultiplicity_sum
      interior pivot constant
  rw [selectedCarryIntoFlagProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  change ((lower ++ terminal ++ lower.reverse ++ terminal ++ correction).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _
  simp only [List.map_append, List.sum_append, List.map_reverse,
    List.sum_reverse]
  rw [hlower, hterminal, hcorrection]
  simp
  omega

/-- Exact X coordinate of the complete compute-copy-uncompute block. -/
theorem selectedCarryIntoFlagProgram_x_count_eq (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (selectedCarryIntoFlagProgram interior pivot constant).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm
        constant (interior + 1) := by
  let lower := selectedCarryIntoFlagLowerGates interior pivot constant
  let terminal := selectedTerminalCarryGates interior pivot constant
  let correction :=
    selectedCarryIntoFlagCorrectionGates interior pivot constant
  have hlower :
      (lower.map EncodedBit.GateSpec.xMultiplicity).sum =
        MAU.Addition.DirtyBorrowed.carryXClosedForm
          constant (interior + 1) := by
    dsimp [lower, selectedCarryIntoFlagLowerGates]
    calc
      ((selectedLowerCarryGates (interior + 2) pivot constant
          (Fin.last (interior + 1))).map
          EncodedBit.GateSpec.xMultiplicity).sum =
          ((MAU.Addition.DirtyBorrowed.straightforwardCarryGates
            (interior + 2) constant (Fin.last (interior + 1))).map
            EncodedBit.GateSpec.xMultiplicity).sum := by
        apply EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
        exact selectedLowerCarryGates_eventTrace_eq
          (interior + 2) pivot constant (Fin.last (interior + 1))
      _ = MAU.Addition.DirtyBorrowed.carryXClosedForm
          constant (interior + 1) := by
        simpa using MAU.Addition.DirtyBorrowed.straightforwardCarryGates_xMultiplicity_sum
            (interior + 2) constant (Fin.last (interior + 1))
  have hterminal :
      (terminal.map EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
    exact selectedTerminalCarryGates_xMultiplicity_sum
      interior pivot constant
  have hcorrection :
      (correction.map EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
    exact selectedCarryIntoFlagCorrectionGates_xMultiplicity_sum
      interior pivot constant
  rw [selectedCarryIntoFlagProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  change ((lower ++ terminal ++ lower.reverse ++ terminal ++ correction).map
    EncodedBit.GateSpec.xMultiplicity).sum = _
  simp only [List.map_append, List.sum_append, List.map_reverse,
    List.sum_reverse]
  rw [hlower, hterminal, hcorrection]
  simp
  omega

/-! ## Literal HRS controlled modular-add schedule -/

/-- The one physical CNOT from the selected source bit to the clean comparison
flag used in the final HRS flag-uncomputation identity. -/
def selectedSourceFlagCnotGates (interior : Nat)
    (pivot : Fin (interior + 2).succ) :
    List (EncodedBit.GateSpec
      (literalR0Encoding (interior + 2).succ)) :=
  [EncodedBit.GateSpec.cnot
    (literalSelectedSourceBit pivot)
    (literalFlagBit (interior + 2).succ)
    (literalSelectedSourceBit_wire_ne_flag pivot)]

/-- Exact logical action of the selected source-to-flag CNOT. -/
theorem selectedSourceFlagCnotGates_step (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    EncodedBit.GateSpec.stepList
        (selectedSourceFlagCnotGates interior pivot) state =
      withCleanFlag state
        (cleanFlag state ^^ (literalSelectedSourceBit pivot).get state) := by
  unfold selectedSourceFlagCnotGates
  simp only [EncodedBit.GateSpec.stepList, id_eq,
    EncodedBit.GateSpec.step, EncodedBit.cnotStep]
  by_cases hselector : (literalSelectedSourceBit pivot).get state
  · rw [if_pos hselector, literalFlagBit_flip_eq_withCleanFlag]
    rw [hselector]
    simp
  · rw [if_neg hselector]
    have hselectorFalse :
        (literalSelectedSourceBit pivot).get state = false :=
      Bool.eq_false_of_not_eq_true hselector
    rw [hselectorFalse]
    simp

/-- Compare, add, and conditionally correct the accumulator.  The clean flag
records whether the canonical sum crossed `modulus`. -/
def literalControlledModularAddCoreGates (interior : Nat)
    (pivot : Fin (interior + 2).succ) (modulus addend : Nat) :
    List (EncodedBit.GateSpec
      (literalR0Encoding (interior + 2).succ)) :=
  selectedCarryIntoFlagGates interior pivot
      (overflowComparisonConstant (interior + 2).succ (modulus - addend)) ++
    sourceControlledAdderGates (interior + 2) pivot
      (addend : PlainAdder.Word (interior + 2).succ) ++
    flagControlledAdderGates (interior + 2) pivot
      (overflowComparisonConstant (interior + 2).succ modulus)

/-- Final HRS clean-flag erasure.  The zero-addend case omits the degenerate
zero-threshold comparison; its core flag is already unchanged. -/
def literalControlledModularAddClearGates (interior : Nat)
    (pivot : Fin (interior + 2).succ) (addend : Nat) :
    List (EncodedBit.GateSpec
      (literalR0Encoding (interior + 2).succ)) :=
  if addend = 0 then
    []
  else
    selectedSourceFlagCnotGates interior pivot ++
      selectedCarryIntoFlagGates interior pivot
        (overflowComparisonConstant (interior + 2).succ addend)

/-- Literal gate schedule for selected addition modulo `modulus` by `addend`.
The intended canonical preconditions are `0 < modulus`, `addend < modulus`,
and `target < modulus`; the gate list itself remains a total reversible
extension over every physical label.

The schedule is HRS's compare/add/correct/compare pattern: compare against
`modulus-addend`, add `addend`, conditionally add `2^width-modulus`, then clear
the comparison flag using the selected source CNOT and comparison against
`addend`. -/
def literalControlledModularAddGates (interior : Nat)
    (pivot : Fin (interior + 2).succ) (modulus addend : Nat) :
    List (EncodedBit.GateSpec
      (literalR0Encoding (interior + 2).succ)) :=
  literalControlledModularAddCoreGates interior pivot modulus addend ++
    literalControlledModularAddClearGates interior pivot addend

/-- Folded total basis action of the literal HRS modular-add schedule. -/
def literalControlledModularAddStep (interior : Nat)
    (pivot : Fin (interior + 2).succ) (modulus addend : Nat) :
    State (interior + 2).succ (LiteralBorrowed (interior + 2).succ) →
      State (interior + 2).succ (LiteralBorrowed (interior + 2).succ) :=
  EncodedBit.GateSpec.stepList
    (literalControlledModularAddGates interior pivot modulus addend)

/-- Total reversible extension implemented by the same literal gate list. -/
def literalControlledModularAddPerm (interior : Nat)
    (pivot : Fin (interior + 2).succ) (modulus addend : Nat) :
    Equiv.Perm
      (State (interior + 2).succ
        (LiteralBorrowed (interior + 2).succ)) :=
  literalGateListPerm (interior + 2).succ
    (literalControlledModularAddGates interior pivot modulus addend)

/-- Actual typed HRS circuit owning the modular-add gate schedule and its
resource trace. -/
def literalControlledModularAddCircuit (interior : Nat)
    (pivot : Fin (interior + 2).succ) (modulus addend : Nat) :
    UnitaryCircuit
      (register (interior + 2).succ
        (LiteralBorrowed (interior + 2).succ)) :=
  literalGateListCircuit (interior + 2).succ
    (literalControlledModularAddGates interior pivot modulus addend)

/-- Exact operator certificate of the literal modular-add circuit on every
physical basis label. -/
theorem literalControlledModularAddCircuit_matrix_eq (interior : Nat)
    (pivot : Fin (interior + 2).succ) (modulus addend : Nat) :
    (literalControlledModularAddCircuit interior pivot modulus addend).matrix =
      UnitaryOperator.ofPerm
        (literalControlledModularAddPerm interior pivot modulus addend).symm :=
  literalGateListCircuit_matrix_eq (interior + 2).succ
    (literalControlledModularAddGates interior pivot modulus addend)

/-- The HRS overflow threshold is equivalent to the reduced sum lying below
the addend.  This is the arithmetic identity used by the final comparison to
erase the clean flag. -/
theorem addMod_lt_addend_iff_threshold (modulus addend value : Nat)
    (_hmodulusPos : 0 < modulus) (haddend : addend < modulus)
    (hvalue : value < modulus) :
    (value + addend) % modulus < addend ↔
      modulus - addend ≤ value := by
  by_cases hsum : value + addend < modulus
  · rw [Nat.mod_eq_of_lt hsum]
    omega
  · have hmodulusLe : modulus ≤ value + addend := by omega
    rw [Nat.mod_eq_sub_mod hmodulusLe]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Adding the HRS correction `2^width-modulus` exactly reduces a canonical
sum modulo `modulus`; when the comparison flag is false, no correction is
needed. -/
theorem fixedWidthConditionalCorrection_eq_mod (width modulus addend : Nat)
    (value : PlainAdder.Word width)
    (_hmodulusPos : 0 < modulus) (hmodulusWidth : modulus < 2 ^ width)
    (haddend : addend < modulus) (hvalue : value.val < modulus) :
    (if modulus - addend ≤ value.val then
        value + (addend : PlainAdder.Word width) +
          overflowComparisonConstant width modulus
      else
        value + (addend : PlainAdder.Word width)) =
      ((value.val + addend) % modulus : PlainAdder.Word width) := by
  have haddendWidth : addend < 2 ^ width :=
    haddend.trans hmodulusWidth
  have hmodulusLeWidth : modulus ≤ 2 ^ width :=
    hmodulusWidth.le
  by_cases hoverflow : modulus - addend ≤ value.val
  · rw [if_pos hoverflow]
    have hmodulusLeSum : modulus ≤ value.val + addend := by omega
    have hsumLtTwice : value.val + addend < modulus + modulus := by omega
    have hmod :
        (value.val + addend) % modulus =
          value.val + addend - modulus := by
      rw [Nat.mod_eq_sub_mod hmodulusLeSum]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    unfold overflowComparisonConstant
    nth_rewrite 1 [← ZMod.natCast_zmod_val value]
    rw [Nat.cast_sub hmodulusLeWidth, Nat.cast_sub hmodulusLeSum]
    simp only [Nat.cast_add]
    rw [ZMod.natCast_self]
    ring
  · rw [if_neg hoverflow]
    have hsumLtModulus : value.val + addend < modulus := by omega
    have hsumLtWidth : value.val + addend < 2 ^ width :=
      hsumLtModulus.trans hmodulusWidth
    apply ZMod.val_injective
    rw [ZMod.val_add, ZMod.val_natCast_of_lt haddendWidth,
      Nat.mod_eq_of_lt hsumLtWidth,
      Nat.mod_eq_of_lt hsumLtModulus,
      ZMod.val_natCast_of_lt hsumLtWidth]

/-- Canonical action of the compare/add/correct core.  The accumulator is
already reduced modulo `modulus`; the clean flag records the same overflow
predicate that the final HRS comparison will erase. -/
theorem literalControlledModularAddCoreGates_step_canonical
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ))
    (hmodulusPos : 0 < modulus)
    (hmodulusWidth : modulus < 2 ^ (interior + 2).succ)
    (haddend : addend < modulus)
    (htarget : (target state).val < modulus)
    (hflag : cleanFlag state = false) :
    EncodedBit.GateSpec.stepList
        (literalControlledModularAddCoreGates
          interior pivot modulus addend) state =
      if (literalSelectedSourceBit pivot).get state then
        withCleanFlag
          (withTarget state
            (((target state).val + addend) % modulus :
              PlainAdder.Word (interior + 2).succ))
          (decide (modulus - addend ≤ (target state).val))
      else
        state := by
  have hthresholdPos : 0 < modulus - addend := by omega
  have hthresholdWidth :
      modulus - addend < 2 ^ (interior + 2).succ := by omega
  unfold literalControlledModularAddCoreGates
  simp only [EncodedBit.GateSpec.stepList_append]
  change flagControlledAdderStep (interior + 2) pivot
      (overflowComparisonConstant (interior + 2).succ modulus)
      (sourceControlledAdderStep (interior + 2) pivot
        (addend : PlainAdder.Word (interior + 2).succ)
        (selectedCarryIntoFlagStep interior pivot
          (overflowComparisonConstant (interior + 2).succ
            (modulus - addend)) state)) = _
  rw [selectedCarryIntoFlagStep_comparison interior (modulus - addend)
      pivot state hthresholdPos hthresholdWidth,
    sourceControlledAdderStep_eq, flagControlledAdderStep_eq]
  by_cases hselector : (literalSelectedSourceBit pivot).get state
  · rw [if_pos hselector]
    have hselectorSource :
        (source state).val.testBit pivot.val = true := by
      simpa only [literalSelectedSourceBit_get] using hselector
    simp only [sourceControlledAdd, flagControlledAdd,
      source_withCleanFlag, target_withCleanFlag,
      target_withTarget, cleanFlag_withCleanFlag, cleanFlag_withTarget,
      literalSelectedSourceBit_get, hselectorSource, if_true,
      hflag, Bool.false_xor, Bool.true_and]
    have hcorrect := fixedWidthConditionalCorrection_eq_mod
      (interior + 2).succ modulus addend (target state)
      hmodulusPos hmodulusWidth haddend htarget
    by_cases hoverflow : modulus - addend ≤ (target state).val
    · rw [if_pos hoverflow] at hcorrect
      have hstate := congrArg
        (fun word => withTarget (withCleanFlag state true) word) hcorrect
      simpa [hoverflow, withCleanFlag_withTarget] using hstate
    · rw [if_neg hoverflow] at hcorrect
      have hstate := congrArg
        (fun word => withTarget (withCleanFlag state false) word) hcorrect
      simpa [hoverflow, withCleanFlag_withTarget] using hstate
  · rw [if_neg hselector]
    have hselectorFalse :
        (literalSelectedSourceBit pivot).get state = false :=
      Bool.eq_false_of_not_eq_true hselector
    have hselectorSource :
        (source state).val.testBit pivot.val = false := by
      simpa only [literalSelectedSourceBit_get] using hselectorFalse
    simp only [sourceControlledAdd, flagControlledAdd,
      source_withCleanFlag, target_withCleanFlag, cleanFlag_withCleanFlag,
      literalSelectedSourceBit_get, hselectorSource, Bool.false_eq_true,
      if_false,
      hflag, Bool.false_xor, Bool.false_and]
    simpa only [hflag] using (withCleanFlag_cleanFlag state)

/-- On a selected canonical input, the final source CNOT and comparison erase
the overflow flag left by the core without changing the reduced accumulator. -/
theorem literalControlledModularAddClearGates_step_canonical
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ))
    (hmodulusPos : 0 < modulus)
    (hmodulusWidth : modulus < 2 ^ (interior + 2).succ)
    (haddend : addend < modulus)
    (htarget : (target state).val < modulus)
    (hflag : cleanFlag state = false)
    (hselector : (literalSelectedSourceBit pivot).get state = true) :
    EncodedBit.GateSpec.stepList
        (literalControlledModularAddClearGates interior pivot addend)
        (withCleanFlag
          (withTarget state
            (((target state).val + addend) % modulus :
              PlainAdder.Word (interior + 2).succ))
          (decide (modulus - addend ≤ (target state).val))) =
      withTarget state
        (((target state).val + addend) % modulus :
          PlainAdder.Word (interior + 2).succ) := by
  let reduced : PlainAdder.Word (interior + 2).succ :=
    (((target state).val + addend) % modulus :
      PlainAdder.Word (interior + 2).succ)
  have hreducedWidth :
      ((target state).val + addend) % modulus <
        2 ^ (interior + 2).succ :=
    (Nat.mod_lt _ hmodulusPos).trans hmodulusWidth
  have hreducedVal :
      reduced.val = ((target state).val + addend) % modulus := by
    exact ZMod.val_natCast_of_lt hreducedWidth
  have hselectorSource :
      (source state).val.testBit pivot.val = true := by
    simpa only [literalSelectedSourceBit_get] using hselector
  by_cases haddendZero : addend = 0
  · subst addend
    have hoverflowFalse :
        ¬modulus - 0 ≤ (target state).val := by
      simpa using htarget
    rw [show literalControlledModularAddClearGates interior pivot 0 = [] by
      simp [literalControlledModularAddClearGates]]
    change withCleanFlag (withTarget state reduced)
        (decide (modulus - 0 ≤ (target state).val)) =
      withTarget state reduced
    have hdecide :
        decide (modulus - 0 ≤ (target state).val) = false := by
      exact decide_eq_false_iff_not.mpr hoverflowFalse
    rw [hdecide]
    simpa only [cleanFlag_withTarget, hflag] using
      (withCleanFlag_cleanFlag (withTarget state reduced))
  · have haddendPos : 0 < addend := Nat.pos_of_ne_zero haddendZero
    have haddendWidth : addend < 2 ^ (interior + 2).succ :=
      haddend.trans hmodulusWidth
    have hflagClear :
        ((decide (modulus - addend ≤ (target state).val) ^^ true) ^^
          decide (addend ≤ reduced.val)) = false := by
      have hrelation := addMod_lt_addend_iff_threshold
        modulus addend (target state).val hmodulusPos haddend htarget
      by_cases hoverflow : modulus - addend ≤ (target state).val
      · have hreducedLt : reduced.val < addend := by
          rw [hreducedVal]
          exact hrelation.mpr hoverflow
        have hnotLe : ¬addend ≤ reduced.val := by omega
        simp [hoverflow, hnotLe]
      · have hnotReducedLt : ¬reduced.val < addend := by
          intro hreducedLt
          apply hoverflow
          apply hrelation.mp
          simpa only [hreducedVal] using hreducedLt
        have haddendLe : addend ≤ reduced.val := by omega
        simp [hoverflow, haddendLe]
    unfold literalControlledModularAddClearGates
    rw [if_neg haddendZero, EncodedBit.GateSpec.stepList_append]
    change selectedCarryIntoFlagStep interior pivot
        (overflowComparisonConstant (interior + 2).succ addend)
        (EncodedBit.GateSpec.stepList
          (selectedSourceFlagCnotGates interior pivot)
          (withCleanFlag (withTarget state reduced)
            (decide (modulus - addend ≤ (target state).val)))) = _
    rw [selectedSourceFlagCnotGates_step]
    rw [selectedCarryIntoFlagStep_comparison interior addend pivot _
      haddendPos haddendWidth]
    simp only [source_withCleanFlag, source_withTarget,
      target_withCleanFlag, target_withTarget, cleanFlag_withCleanFlag,
      literalSelectedSourceBit_get, hselectorSource, Bool.true_and,
      withCleanFlag_withCleanFlag]
    rw [hflagClear]
    simpa only [cleanFlag_withTarget, hflag] using
      (withCleanFlag_cleanFlag (withTarget state reduced))

/-- The flag-clear suffix is the identity whenever the selected source bit is
false, on every physical basis label and for every numerical addend. -/
theorem literalControlledModularAddClearGates_step_unselected
    (interior : Nat) (pivot : Fin (interior + 2).succ) (addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ))
    (hselector : (literalSelectedSourceBit pivot).get state = false) :
    EncodedBit.GateSpec.stepList
        (literalControlledModularAddClearGates interior pivot addend) state =
      state := by
  by_cases haddendZero : addend = 0
  · subst addend
    simp [literalControlledModularAddClearGates,
      EncodedBit.GateSpec.stepList]
  · unfold literalControlledModularAddClearGates
    rw [if_neg haddendZero, EncodedBit.GateSpec.stepList_append]
    rw [selectedSourceFlagCnotGates_step]
    have hafterCnot :
        withCleanFlag state
            (cleanFlag state ^^ (literalSelectedSourceBit pivot).get state) =
          state := by
      rw [hselector]
      simpa only [Bool.xor_false] using (withCleanFlag_cleanFlag state)
    rw [hafterCnot]
    change selectedCarryIntoFlagStep interior pivot
        (overflowComparisonConstant (interior + 2).succ addend) state = state
    rw [selectedCarryIntoFlagStep_eq_withCleanFlag,
      selectedCarryIntoFlagToggle_eq_overflow]
    have hselectorSource :
        (source state).val.testBit pivot.val = false := by
      simpa only [literalSelectedSourceBit_get] using hselector
    rw [hselectorSource]
    simpa only [Bool.false_and, Bool.xor_false] using
      (withCleanFlag_cleanFlag state)

/-- Complete canonical semantics of the literal HRS controlled modular-add
gate list, including exact restoration of the clean flag and every other
non-accumulator label. -/
theorem literalControlledModularAddStep_canonical
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ))
    (hmodulusPos : 0 < modulus)
    (hmodulusWidth : modulus < 2 ^ (interior + 2).succ)
    (haddend : addend < modulus)
    (htarget : (target state).val < modulus)
    (hflag : cleanFlag state = false) :
    literalControlledModularAddStep interior pivot modulus addend state =
      if (literalSelectedSourceBit pivot).get state then
        withTarget state
          (((target state).val + addend) % modulus :
            PlainAdder.Word (interior + 2).succ)
      else
        state := by
  unfold literalControlledModularAddStep literalControlledModularAddGates
  rw [EncodedBit.GateSpec.stepList_append]
  rw [literalControlledModularAddCoreGates_step_canonical
    interior pivot modulus addend state hmodulusPos hmodulusWidth
      haddend htarget hflag]
  by_cases hselector : (literalSelectedSourceBit pivot).get state
  · simp only [hselector, if_true]
    exact literalControlledModularAddClearGates_step_canonical
      interior pivot modulus addend state hmodulusPos hmodulusWidth
        haddend htarget hflag hselector
  · have hselectorFalse :
        (literalSelectedSourceBit pivot).get state = false :=
      Bool.eq_false_of_not_eq_true hselector
    simp only [hselectorFalse, Bool.false_eq_true, if_false]
    exact literalControlledModularAddClearGates_step_unselected
      interior pivot addend state hselectorFalse

/-- The compare/add/correct core never overwrites the source word, including
on padding labels and for an arbitrary initial clean-flag label. -/
theorem literalControlledModularAddCoreGates_source
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    source (EncodedBit.GateSpec.stepList
      (literalControlledModularAddCoreGates
        interior pivot modulus addend) state) = source state := by
  unfold literalControlledModularAddCoreGates
  simp only [EncodedBit.GateSpec.stepList_append]
  change source (flagControlledAdderStep (interior + 2) pivot
      (overflowComparisonConstant (interior + 2).succ modulus)
      (sourceControlledAdderStep (interior + 2) pivot
        (addend : PlainAdder.Word (interior + 2).succ)
        (selectedCarryIntoFlagStep interior pivot
          (overflowComparisonConstant (interior + 2).succ
            (modulus - addend)) state))) = _
  rw [flagControlledAdderStep_eq, sourceControlledAdderStep_eq,
    selectedCarryIntoFlagStep_eq_withCleanFlag]
  simp only [flagControlledAdd, sourceControlledAdd]
  split_ifs <;> rfl

/-- The compare/add/correct core restores every source label used as dirty
carry work; the zero-qubit literal environment is therefore also unchanged. -/
theorem literalControlledModularAddCoreGates_borrowed
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    borrowed (EncodedBit.GateSpec.stepList
      (literalControlledModularAddCoreGates
        interior pivot modulus addend) state) = borrowed state := by
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The final flag-clear suffix never overwrites the source word. -/
theorem literalControlledModularAddClearGates_source
    (interior : Nat) (pivot : Fin (interior + 2).succ) (addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    source (EncodedBit.GateSpec.stepList
      (literalControlledModularAddClearGates interior pivot addend) state) =
      source state := by
  by_cases haddendZero : addend = 0
  · subst addend
    simp [literalControlledModularAddClearGates,
      EncodedBit.GateSpec.stepList]
  · unfold literalControlledModularAddClearGates
    rw [if_neg haddendZero, EncodedBit.GateSpec.stepList_append]
    change source (selectedCarryIntoFlagStep interior pivot
      (overflowComparisonConstant (interior + 2).succ addend)
      (EncodedBit.GateSpec.stepList
        (selectedSourceFlagCnotGates interior pivot) state)) = _
    rw [selectedCarryIntoFlagStep_eq_withCleanFlag,
      selectedSourceFlagCnotGates_step]
    rfl

/-- The final flag-clear suffix leaves the literal borrowed environment
unchanged on every physical label. -/
theorem literalControlledModularAddClearGates_borrowed
    (interior : Nat) (pivot : Fin (interior + 2).succ) (addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    borrowed (EncodedBit.GateSpec.stepList
      (literalControlledModularAddClearGates interior pivot addend) state) =
      borrowed state := by
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The complete literal modular-add permutation preserves the source word on
the entire basis, not only on the canonical modular subspace. -/
theorem literalControlledModularAddStep_source
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    source (literalControlledModularAddStep
      interior pivot modulus addend state) = source state := by
  unfold literalControlledModularAddStep literalControlledModularAddGates
  rw [EncodedBit.GateSpec.stepList_append,
    literalControlledModularAddClearGates_source,
    literalControlledModularAddCoreGates_source]

/-- The complete literal modular-add permutation restores the full borrowed
label on every physical basis state. -/
theorem literalControlledModularAddStep_borrowed
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    borrowed (literalControlledModularAddStep
      interior pivot modulus addend state) = borrowed state := by
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-! ### Exact native coordinates of the literal modular adder -/

/-- Closed Toffoli coordinate of one selected comparator block. -/
def selectedCarryToffoliClosedForm (interior : Nat)
    (constant : PlainAdder.Word (interior + 2).succ) : Nat :=
  4 * (interior + 1) +
    if constant.val.testBit (interior + 2) then 13 else 8

/-- Closed CNOT coordinate of one selected comparator block. -/
def selectedCarryCnotClosedForm (interior : Nat)
    (constant : PlainAdder.Word (interior + 2).succ) : Nat :=
  2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
    constant (interior + 2)

/-- Closed CNOT coordinate shared by the source-controlled and
clean-flag-controlled fixed-width adders. -/
def controlledAdderCnotClosedForm {width : Nat}
    (constant : PlainAdder.Word width) (tail : Nat) : Nat :=
  sourceControlledHighCnotClosedForm constant tail +
    MAU.Addition.DirtyBorrowed.constantBitMultiplicity constant 0

/-- Exact closed Toffoli count of the complete selected modular-add list. -/
def literalControlledModularAddToffoliCount (interior modulus addend : Nat) :
    Nat :=
  selectedCarryToffoliClosedForm interior
      (overflowComparisonConstant (interior + 2).succ (modulus - addend)) +
    4 * (interior + 2) * (interior + 2) +
    if addend = 0 then
      0
    else
      selectedCarryToffoliClosedForm interior
        (overflowComparisonConstant (interior + 2).succ addend)

/-- Exact closed CNOT count of the complete selected modular-add list. -/
def literalControlledModularAddCnotCount (interior modulus addend : Nat) : Nat :=
  selectedCarryCnotClosedForm interior
      (overflowComparisonConstant (interior + 2).succ (modulus - addend)) +
    controlledAdderCnotClosedForm
      (addend : PlainAdder.Word (interior + 2).succ) (interior + 2) +
    controlledAdderCnotClosedForm
      (overflowComparisonConstant (interior + 2).succ modulus)
      (interior + 2) +
    if addend = 0 then
      0
    else
      1 + selectedCarryCnotClosedForm interior
        (overflowComparisonConstant (interior + 2).succ addend)

/-- Exact closed X count of the complete selected modular-add list. -/
def literalControlledModularAddXCount (interior modulus addend : Nat) : Nat :=
  2 * MAU.Addition.DirtyBorrowed.carryXClosedForm
      (overflowComparisonConstant (interior + 2).succ (modulus - addend))
      (interior + 1) +
    sourceControlledHighXClosedForm
      (addend : PlainAdder.Word (interior + 2).succ) (interior + 2) +
    sourceControlledHighXClosedForm
      (overflowComparisonConstant (interior + 2).succ modulus)
      (interior + 2) +
    if addend = 0 then
      0
    else
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm
        (overflowComparisonConstant (interior + 2).succ addend)
        (interior + 1)

/-- Gate-list form of the exact selected-comparator Toffoli coordinate. -/
theorem selectedCarryIntoFlagGates_toffoliMultiplicity_sum (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedCarryIntoFlagGates interior pivot constant).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      selectedCarryToffoliClosedForm interior constant := by
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact selectedCarryIntoFlagProgram_toffoli_count_eq
    interior pivot constant

/-- Gate-list form of the exact selected-comparator CNOT coordinate. -/
theorem selectedCarryIntoFlagGates_cnotMultiplicity_sum (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedCarryIntoFlagGates interior pivot constant).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      selectedCarryCnotClosedForm interior constant := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact selectedCarryIntoFlagProgram_cnot_count_eq
    interior pivot constant

/-- Gate-list form of the exact selected-comparator X coordinate. -/
theorem selectedCarryIntoFlagGates_xMultiplicity_sum (interior : Nat)
    (pivot : Fin (interior + 2).succ)
    (constant : PlainAdder.Word (interior + 2).succ) :
    ((selectedCarryIntoFlagGates interior pivot constant).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm
        constant (interior + 1) := by
  rw [← EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact selectedCarryIntoFlagProgram_x_count_eq interior pivot constant

/-- Gate-list form of the exact source-controlled-adder Toffoli coordinate. -/
theorem sourceControlledAdderGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((sourceControlledAdderGates tail pivot constant).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * tail * tail := by
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact sourceControlledAdderProgram_toffoli_count_eq tail pivot constant

/-- Gate-list form of the exact source-controlled-adder CNOT coordinate. -/
theorem sourceControlledAdderGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((sourceControlledAdderGates tail pivot constant).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      controlledAdderCnotClosedForm constant tail := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact sourceControlledAdderProgram_cnot_count_eq tail pivot constant

/-- Gate-list form of the exact source-controlled-adder X coordinate. -/
theorem sourceControlledAdderGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((sourceControlledAdderGates tail pivot constant).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      sourceControlledHighXClosedForm constant tail := by
  rw [← EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact sourceControlledAdderProgram_x_count_eq tail pivot constant

/-- Gate-list form of the exact flag-controlled-adder Toffoli coordinate. -/
theorem flagControlledAdderGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((flagControlledAdderGates tail pivot constant).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * tail * tail := by
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact flagControlledAdderProgram_toffoli_count_eq tail pivot constant

/-- Gate-list form of the exact flag-controlled-adder CNOT coordinate. -/
theorem flagControlledAdderGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((flagControlledAdderGates tail pivot constant).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      controlledAdderCnotClosedForm constant tail := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact flagControlledAdderProgram_cnot_count_eq tail pivot constant

/-- Gate-list form of the exact flag-controlled-adder X coordinate. -/
theorem flagControlledAdderGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((flagControlledAdderGates tail pivot constant).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      sourceControlledHighXClosedForm constant tail := by
  rw [← EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact flagControlledAdderProgram_x_count_eq tail pivot constant

/-- The typed literal modular-add circuit has exactly its closed Toffoli
coordinate, derived from the same compiled gate list. -/
theorem literalControlledModularAddCircuit_toffoli_count_eq
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (literalControlledModularAddCircuit
          interior pivot modulus addend).eventCost =
      literalControlledModularAddToffoliCount interior modulus addend := by
  change ResourcePool.count (.gate (.builtin "toffoli"))
      (EncodedBit.GateSpec.programList
        (literalControlledModularAddGates
          interior pivot modulus addend)).eventCost = _
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  unfold literalControlledModularAddGates
    literalControlledModularAddCoreGates
    literalControlledModularAddClearGates
    literalControlledModularAddToffoliCount
  simp only [List.map_append, List.sum_append]
  rw [selectedCarryIntoFlagGates_toffoliMultiplicity_sum,
    sourceControlledAdderGates_toffoliMultiplicity_sum,
    flagControlledAdderGates_toffoliMultiplicity_sum]
  by_cases haddendZero : addend = 0
  · simp [haddendZero]
    ring
  · rw [if_neg haddendZero]
    simp only [List.map_append, List.sum_append]
    rw [selectedCarryIntoFlagGates_toffoliMultiplicity_sum]
    simp [selectedSourceFlagCnotGates, haddendZero]
    ring

/-- The typed literal modular-add circuit has exactly its closed CNOT
coordinate, including the sole nonzero-addend source-to-flag CNOT. -/
theorem literalControlledModularAddCircuit_cnot_count_eq
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (literalControlledModularAddCircuit
          interior pivot modulus addend).eventCost =
      literalControlledModularAddCnotCount interior modulus addend := by
  change ResourcePool.count (.gate (.builtin "cnot"))
      (EncodedBit.GateSpec.programList
        (literalControlledModularAddGates
          interior pivot modulus addend)).eventCost = _
  rw [EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  unfold literalControlledModularAddGates
    literalControlledModularAddCoreGates
    literalControlledModularAddClearGates
    literalControlledModularAddCnotCount
  simp only [List.map_append, List.sum_append]
  rw [selectedCarryIntoFlagGates_cnotMultiplicity_sum,
    sourceControlledAdderGates_cnotMultiplicity_sum,
    flagControlledAdderGates_cnotMultiplicity_sum]
  by_cases haddendZero : addend = 0
  · simp [haddendZero]
  · rw [if_neg haddendZero]
    simp only [List.map_append, List.sum_append]
    rw [selectedCarryIntoFlagGates_cnotMultiplicity_sum]
    simp [selectedSourceFlagCnotGates]
    omega

/-- The typed literal modular-add circuit has exactly its closed X
coordinate, including both optional flag-clear branches. -/
theorem literalControlledModularAddCircuit_x_count_eq
    (interior : Nat) (pivot : Fin (interior + 2).succ)
    (modulus addend : Nat) :
    ResourcePool.count (.gate (.builtin "x"))
        (literalControlledModularAddCircuit
          interior pivot modulus addend).eventCost =
      literalControlledModularAddXCount interior modulus addend := by
  change ResourcePool.count (.gate (.builtin "x"))
      (EncodedBit.GateSpec.programList
        (literalControlledModularAddGates
          interior pivot modulus addend)).eventCost = _
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum]
  unfold literalControlledModularAddGates
    literalControlledModularAddCoreGates
    literalControlledModularAddClearGates
    literalControlledModularAddXCount
  simp only [List.map_append, List.sum_append]
  rw [selectedCarryIntoFlagGates_xMultiplicity_sum,
    sourceControlledAdderGates_xMultiplicity_sum,
    flagControlledAdderGates_xMultiplicity_sum]
  by_cases haddendZero : addend = 0
  · simp [haddendZero]
  · rw [if_neg haddendZero]
    simp only [List.map_append, List.sum_append]
    rw [selectedCarryIntoFlagGates_xMultiplicity_sum]
    simp [selectedSourceFlagCnotGates, haddendZero]

/-- Concrete HRS controlled modular-add certificate for every width of the
form `interior+3`.  Its circuit, total permutation, canonical semantics, and
exact resource coordinates all come from one compiled gate list. -/
def literalControlledModularAdd
    (interior : Nat)
    (params : Parameters (interior + 2).succ)
    (bit : Fin (interior + 2).succ) (subtract : Bool) :
    ControlledModularAdd params
      (LiteralBorrowed (interior + 2).succ) bit subtract where
  perm := literalControlledModularAddPerm interior bit params.modulus
    (params.signedStageConstant subtract bit)
  canonical_action := by
    intro sourceWord targetWord borrowedWord _hsource htarget
    let state : State (interior + 2).succ
        (LiteralBorrowed (interior + 2).succ) :=
      ((sourceWord, targetWord), (false, borrowedWord))
    change literalControlledModularAddStep interior bit params.modulus
        (params.signedStageConstant subtract bit) state =
      stageUpdate params bit subtract state
    rw [literalControlledModularAddStep_canonical interior bit
      params.modulus (params.signedStageConstant subtract bit) state
      params.modulus_pos params.modulus_lt_width
      (params.signedStageConstant_lt_modulus subtract bit) htarget rfl]
    dsimp [stageUpdate, stageTarget, Parameters.addReduced, Parameters.word,
      state, source, target]
    rw [literalSelectedSourceBit_get]
    simp only [source]
    by_cases hselected : sourceWord.val.testBit bit.val
    · simp [hselected, htarget]
    · simpa only [Nat.succ_eq_add_one, hselected, Bool.false_eq_true,
        if_false, state, target] using
        (withTarget_target state).symm
  preserves_source := by
    intro state
    change source (literalControlledModularAddStep interior bit params.modulus
      (params.signedStageConstant subtract bit) state) = source state
    exact literalControlledModularAddStep_source interior bit params.modulus
      (params.signedStageConstant subtract bit) state
  preserves_borrowed := by
    intro state
    change borrowed (literalControlledModularAddStep interior bit params.modulus
      (params.signedStageConstant subtract bit) state) = borrowed state
    exact literalControlledModularAddStep_borrowed interior bit params.modulus
      (params.signedStageConstant subtract bit) state
  circuit := literalControlledModularAddCircuit interior bit params.modulus
    (params.signedStageConstant subtract bit)
  matrix_eq := literalControlledModularAddCircuit_matrix_eq interior bit
    params.modulus (params.signedStageConstant subtract bit)
  toffoli_count := literalControlledModularAddToffoliCount interior
    params.modulus (params.signedStageConstant subtract bit)
  cnot_count := literalControlledModularAddCnotCount interior
    params.modulus (params.signedStageConstant subtract bit)
  toffoli_exact := literalControlledModularAddCircuit_toffoli_count_eq
    interior bit params.modulus (params.signedStageConstant subtract bit)
  cnot_exact := literalControlledModularAddCircuit_cnot_count_eq
    interior bit params.modulus (params.signedStageConstant subtract bit)

/-! ## Literal unselected carry extraction -/

/-- Embed an `n`-bit constant below the clean high flag. -/
abbrev unselectedCarryConstant (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    PlainAdder.Word tail.succ.succ :=
  MAU.Addition.VBECircuit.widenWord tail.succ constant

/-- The full-width dirty-carry output block, relabelled onto the literal HRS
carrier.  It computes the carry out of the `tail+1` low accumulator bits into
the clean flag and restores the source word used as dirty work.  There is no
source-bit selector in this block, so it is deliberately not called a
comparator or controlled modular addition. -/
def unselectedCarryIntoFlagGates (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    List (EncodedBit.GateSpec (literalR0Encoding tail.succ)) :=
  (MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates tail.succ
      (unselectedCarryConstant tail constant) (Fin.last tail)).map
    (EncodedBit.GateSpec.relabel (literalR0StateEquiv tail.succ))

/-- Folded basis action of the literal carry-to-flag gate list. -/
def unselectedCarryIntoFlagStep (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    State tail.succ (LiteralBorrowed tail.succ) →
      State tail.succ (LiteralBorrowed tail.succ) :=
  EncodedBit.GateSpec.stepList
    (unselectedCarryIntoFlagGates tail constant)

/-- Actual X/CNOT/Toffoli circuit for the unselected carry extractor. -/
def unselectedCarryIntoFlagProgram (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit (Qubits (literalR0Encoding tail.succ).width) :=
  EncodedBit.GateSpec.programList
    (unselectedCarryIntoFlagGates tail constant)

/-- Relabelling only conjugates the source dirty-carry step by the literal HRS
state equivalence. -/
theorem literalR0StateEquiv_unselectedCarryIntoFlagStep (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    literalR0StateEquiv tail.succ
        (unselectedCarryIntoFlagStep tail constant state) =
      EncodedBit.GateSpec.stepList
        (MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates tail.succ
          (unselectedCarryConstant tail constant) (Fin.last tail))
        (literalR0StateEquiv tail.succ state) := by
  unfold unselectedCarryIntoFlagStep unselectedCarryIntoFlagGates
    literalR0Encoding
  rw [EncodedBit.GateSpec.stepList_relabel]
  exact Equiv.apply_symm_apply (literalR0StateEquiv tail.succ) _

/-- The Boolean carry extracted from the complete low accumulator word. -/
def unselectedCarryToggle (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) : Bool :=
  Nat.BinaryArithmetic.natAddCarry
    (target state).val constant.val tail.succ

/-- The aliased R.0 carry predicate observes exactly the low accumulator and
the supplied low constant, not the input value of the clean high flag. -/
theorem straightforwardCarryToggle_literalR0StateEquiv (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    MAU.Addition.DirtyBorrowed.straightforwardCarryToggle tail.succ
        (unselectedCarryConstant tail constant)
        (literalR0StateEquiv tail.succ state).1 (Fin.last tail) =
      unselectedCarryToggle tail constant state := by
  unfold MAU.Addition.DirtyBorrowed.straightforwardCarryToggle
    unselectedCarryToggle
  rw [MAU.Addition.VBECircuit.widenWord_val]
  apply MAU.Addition.DirtyBorrowed.natAddCarry_congr_left_of_testBit_eq_lt
  intro bit hbit
  rw [literalR0StateEquiv_fst]
  exact flagTargetWordEquiv_low_bit tail.succ (cleanFlag state)
    (target state) ⟨bit, hbit⟩

/-- The unselected carry extractor restores the complete source word that it
borrows as dirty carry work. -/
@[simp] theorem unselectedCarryIntoFlagStep_source (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    source (unselectedCarryIntoFlagStep tail constant state) = source state := by
  apply (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv tail.succ).injective
  rw [← literalR0StateEquiv_snd tail.succ]
  rw [literalR0StateEquiv_unselectedCarryIntoFlagStep]
  exact MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates_snd
    tail.succ (unselectedCarryConstant tail constant) (Fin.last tail)
    (literalR0StateEquiv tail.succ state)

/-- Only the high clean flag changes; every low accumulator bit, and hence the
entire accumulator word, is restored. -/
@[simp] theorem unselectedCarryIntoFlagStep_target (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    target (unselectedCarryIntoFlagStep tail constant state) = target state := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro observed
  have hread :=
    MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates_fst_testBit
      tail.succ (unselectedCarryConstant tail constant) (Fin.last tail)
      (literalR0StateEquiv tail.succ state) observed.castSucc
  have hne : observed.castSucc ≠ (Fin.last tail).succ := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]
    omega
  rw [if_neg hne] at hread
  rw [← flagTargetWordEquiv_low_bit tail.succ
    (cleanFlag (unselectedCarryIntoFlagStep tail constant state))
    (target (unselectedCarryIntoFlagStep tail constant state)) observed]
  rw [← flagTargetWordEquiv_low_bit tail.succ
    (cleanFlag state) (target state) observed]
  rw [← literalR0StateEquiv_fst tail.succ
    (unselectedCarryIntoFlagStep tail constant state)]
  rw [← literalR0StateEquiv_fst tail.succ state]
  rw [literalR0StateEquiv_unselectedCarryIntoFlagStep]
  exact hread

/-- The clean flag is toggled exactly by the carry out of low-word addition.
The widened constant's dedicated high bit is definitionally clean. -/
@[simp] theorem unselectedCarryIntoFlagStep_cleanFlag (tail : Nat)
    (constant : PlainAdder.Word tail.succ)
    (state : State tail.succ (LiteralBorrowed tail.succ)) :
    cleanFlag (unselectedCarryIntoFlagStep tail constant state) =
      (cleanFlag state ^^ unselectedCarryToggle tail constant state) := by
  let observed : Fin tail.succ.succ := Fin.last tail.succ
  have hselected : observed = (Fin.last tail).succ := by
    apply Fin.ext
    rfl
  have hread :=
    MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates_fst_testBit
      tail.succ (unselectedCarryConstant tail constant) (Fin.last tail)
      (literalR0StateEquiv tail.succ state) observed
  rw [if_pos hselected] at hread
  have hconstantValueHigh : constant.val.testBit tail.succ = false :=
    Nat.testBit_lt_two_pow (ZMod.val_lt constant)
  rw [← flagTargetWordEquiv_high_bit tail.succ
    (cleanFlag (unselectedCarryIntoFlagStep tail constant state))
    (target (unselectedCarryIntoFlagStep tail constant state))]
  rw [← flagTargetWordEquiv_high_bit tail.succ
    (cleanFlag state) (target state)]
  rw [← literalR0StateEquiv_fst tail.succ
    (unselectedCarryIntoFlagStep tail constant state)]
  rw [← literalR0StateEquiv_fst tail.succ state]
  rw [literalR0StateEquiv_unselectedCarryIntoFlagStep]
  rw [straightforwardCarryToggle_literalR0StateEquiv] at hread
  simpa [observed, hconstantValueHigh] using hread

/-- The concrete compiled list realizes its own carry-to-flag folded step. -/
theorem unselectedCarryIntoFlagProgram_realizes (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit.Realizes (literalR0Encoding tail.succ)
      (unselectedCarryIntoFlagProgram tail constant)
      (unselectedCarryIntoFlagStep tail constant) :=
  EncodedBit.GateSpec.realizesList
    (unselectedCarryIntoFlagGates tail constant)

/-- Exact Toffoli coordinate of the literal full-width carry extractor. -/
theorem unselectedCarryIntoFlagProgram_toffoli_count_eq (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (unselectedCarryIntoFlagProgram tail constant).eventCost = 4 * tail := by
  rw [unselectedCarryIntoFlagProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  calc
    ((unselectedCarryIntoFlagGates tail constant).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
        ((MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates tail.succ
          (unselectedCarryConstant tail constant) (Fin.last tail)).map
            EncodedBit.GateSpec.toffoliMultiplicity).sum := by
      apply EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
      exact EncodedBit.GateSpec.map_event_relabel
        (literalR0StateEquiv tail.succ) _
    _ = 4 * tail := by
      simpa using
        (MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates_toffoliMultiplicity_sum
            tail.succ
            (unselectedCarryConstant tail constant) (Fin.last tail))

/-- Exact CNOT coordinate of the same carry extractor. -/
theorem unselectedCarryIntoFlagProgram_cnot_count_eq (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (unselectedCarryIntoFlagProgram tail constant).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          (unselectedCarryConstant tail constant) tail.succ + 2 := by
  rw [unselectedCarryIntoFlagProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  calc
    ((unselectedCarryIntoFlagGates tail constant).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
        ((MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates tail.succ
          (unselectedCarryConstant tail constant) (Fin.last tail)).map
            EncodedBit.GateSpec.cnotMultiplicity).sum := by
      apply EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
      exact EncodedBit.GateSpec.map_event_relabel
        (literalR0StateEquiv tail.succ) _
    _ = 2 * MAU.Addition.DirtyBorrowed.carryCnotClosedForm
          (unselectedCarryConstant tail constant) tail.succ + 2 := by
      simpa using
        (MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates_cnotMultiplicity_sum
            tail.succ
            (unselectedCarryConstant tail constant) (Fin.last tail))

/-- Exact X coordinate of the same carry extractor. -/
theorem unselectedCarryIntoFlagProgram_x_count_eq (tail : Nat)
    (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (unselectedCarryIntoFlagProgram tail constant).eventCost =
      2 * MAU.Addition.DirtyBorrowed.carryXClosedForm
          (unselectedCarryConstant tail constant) tail := by
  rw [unselectedCarryIntoFlagProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  calc
    ((unselectedCarryIntoFlagGates tail constant).map
        EncodedBit.GateSpec.xMultiplicity).sum =
        ((MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates tail.succ
          (unselectedCarryConstant tail constant) (Fin.last tail)).map
            EncodedBit.GateSpec.xMultiplicity).sum := by
      apply EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
      exact EncodedBit.GateSpec.map_event_relabel
        (literalR0StateEquiv tail.succ) _
    _ = 2 * MAU.Addition.DirtyBorrowed.carryXClosedForm
          (unselectedCarryConstant tail constant) tail := by
      rw [MAU.Addition.DirtyBorrowed.straightforwardOutputBitGates_xMultiplicity_sum]
      have hconstantValueHigh : constant.val.testBit tail.succ = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt constant)
      simp [MAU.Addition.DirtyBorrowed.constantBitMultiplicity,
        hconstantValueHigh]

/-- Literal three-CNOT-per-bit gate list for the HRS word swap. -/
def literalSwapGates (n : Nat) :
    List (EncodedBit.GateSpec (literalSwapEncoding n)) :=
  EncodedBit.Word.swapGates (literalSourceWord n) (literalTargetWord n)
    (literalSourceTargetBit_wire_ne n)

/-- The standard three-CNOT-per-bit physical HRS word swap. -/
def literalSwapProgram (n : Nat) :
    UnitaryCircuit (Qubits (literalSwapEncoding n).width) :=
  EncodedBit.GateSpec.programList (literalSwapGates n)

/-- The folded semantic action of the actual literal word-swap circuit. -/
def literalSwapStep (n : Nat) :
    State n (LiteralBorrowed n) → State n (LiteralBorrowed n) :=
  EncodedBit.GateSpec.stepList (literalSwapGates n)

/-- The folded standard three-CNOT word swap exchanges exactly the two
arithmetic words and leaves the clean flag and every dirty-borrowed label
unchanged. -/
theorem literalSwapStep_swaps (n : Nat) (state : State n (LiteralBorrowed n)) :
    literalSwapStep n state =
      ((target state, source state), (cleanFlag state, borrowed state)) := by
  have hleft :
      (fun bit => (literalSourceBit n bit).get (literalSwapStep n state)) =
        fun bit => (literalTargetBit n bit).get state := by
    simpa only [literalSwapStep, literalSwapGates,
      literalSourceWord, literalTargetWord, EncodedBit.Word.swapStep] using
      (EncodedBit.Word.swapStep_get_left_word
        (literalSourceWord n) (literalTargetWord n)
        (literalSourceTargetBit_wire_ne n)
        (fun left right hne => literalSourceBit_wire_ne n hne)
        (fun left right hne => literalTargetBit_wire_ne n hne)
        (literalSourceTargetBit_cross_wire_ne n) state)
  have hright :
      (fun bit => (literalTargetBit n bit).get (literalSwapStep n state)) =
        fun bit => (literalSourceBit n bit).get state := by
    simpa only [literalSwapStep, literalSwapGates,
      literalSourceWord, literalTargetWord, EncodedBit.Word.swapStep] using
      (EncodedBit.Word.swapStep_get_right_word
        (literalSourceWord n) (literalTargetWord n)
        (literalSourceTargetBit_wire_ne n)
        (fun left right hne => literalSourceBit_wire_ne n hne)
        (fun left right hne => literalTargetBit_wire_ne n hne)
        (literalSourceTargetBit_cross_wire_ne n) state)
  have hsource : source (literalSwapStep n state) = target state := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    calc
      (source (literalSwapStep n state)).val.testBit bit.val =
          (literalSourceBit n bit).get (literalSwapStep n state) :=
        (literalSourceBit_get n bit (literalSwapStep n state)).symm
      _ = (literalTargetBit n bit).get state := congrFun hleft bit
      _ = (target state).val.testBit bit.val := literalTargetBit_get n bit state
  have htarget : target (literalSwapStep n state) = source state := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    calc
      (target (literalSwapStep n state)).val.testBit bit.val =
          (literalTargetBit n bit).get (literalSwapStep n state) :=
        (literalTargetBit_get n bit (literalSwapStep n state)).symm
      _ = (literalSourceBit n bit).get state := congrFun hright bit
      _ = (source state).val.testBit bit.val := literalSourceBit_get n bit state
  have hflagRead :
      (literalFlagBit n).get (literalSwapStep n state) =
        (literalFlagBit n).get state := by
    simpa only [literalSwapStep, literalSwapGates,
      EncodedBit.Word.swapStep] using
      (EncodedBit.Word.swapStep_get_observed_of_swap_ne
        (literalSourceWord n) (literalTargetWord n)
        (literalSourceTargetBit_wire_ne n) (literalFlagBit n)
        (literalSourceBit_wire_ne_flag n)
        (literalTargetBit_wire_ne_flag n) state)
  have hflag : cleanFlag (literalSwapStep n state) = cleanFlag state := by
    simpa using hflagRead
  have hborrowed : borrowed (literalSwapStep n state) = borrowed state := by
    rw [Fin.eq_zero (borrowed (literalSwapStep n state)),
      Fin.eq_zero (borrowed state)]
  have hframe : (literalSwapStep n state).2 = state.2 :=
    Prod.ext hflag hborrowed
  apply Prod.ext
  · exact Prod.ext hsource htarget
  · exact hframe

/-- The concrete circuit realizes precisely its own folded base-gate action. -/
theorem literalSwapProgram_realizes (n : Nat) :
    UnitaryCircuit.Realizes (literalSwapEncoding n) (literalSwapProgram n)
      (literalSwapStep n) :=
  EncodedBit.Word.swap_realizes (literalSourceWord n) (literalTargetWord n)
    (literalSourceTargetBit_wire_ne n)

/-- Basis-state endpoint of the actual three-CNOT word-swap circuit in the
HRS carrier, including exact preservation of the borrowed label. -/
theorem literalSwapProgram_realizes_standard (n : Nat) :
    UnitaryCircuit.Realizes (literalSwapEncoding n) (literalSwapProgram n)
      (fun state =>
        ((target state, source state), (cleanFlag state, borrowed state))) :=
  UnitaryCircuit.Realizes.congrStep (literalSwapProgram_realizes n)
    (literalSwapStep_swaps n)

/-- Exact native CNOT coordinate of the standard physical word swap. -/
theorem literalSwapProgram_cnot_count_eq (n : Nat) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (literalSwapProgram n).eventCost = 3 * n := by
  simpa only [literalSwapProgram, literalSwapGates,
    EncodedBit.Word.swapCircuit, EncodedBit.Word.swapProgram] using
    (EncodedBit.Word.swapCircuit_cnot_eventCount
      (literalSourceWord n) (literalTargetWord n)
      (literalSourceTargetBit_wire_ne n))

/-- The standard physical word swap contains no Toffoli leaves. -/
theorem literalSwapProgram_toffoli_count_eq (n : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (literalSwapProgram n).eventCost = 0 := by
  have hwire : ∀ bit : Fin n,
      ((literalSourceWord n).bit bit).wire ≠
        ((literalTargetWord n).bit bit).wire := by
    intro bit
    exact literalSourceTargetBit_wire_ne n bit
  have hcount :
      ResourcePool.count (.gate (.builtin "toffoli"))
          (EncodedBit.Word.swapProgram (literalSourceWord n)
            (literalTargetWord n) hwire).eventCost = 0 := by
    rw [EncodedBit.Word.swapProgram,
      EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
    exact EncodedBit.Word.swapGates_toffoliMultiplicity_sum
      (literalSourceWord n) (literalTargetWord n) hwire
  simpa only [literalSwapProgram, literalSwapGates,
    EncodedBit.Word.swapProgram] using hcount

/-- Total permutation of the literal word-swap gate list. -/
def literalWordSwapPerm (n : Nat) :
    Equiv.Perm (State n (LiteralBorrowed n)) :=
  literalGateListPerm n (literalSwapGates n)

/-- Typed version of the same literal word-swap circuit. -/
def literalWordSwapCircuit (n : Nat) :
    UnitaryCircuit (register n (LiteralBorrowed n)) :=
  literalGateListCircuit n (literalSwapGates n)

/-- Exact operator certificate for the typed literal word swap. -/
theorem literalWordSwapCircuit_matrix_eq (n : Nat) :
    (literalWordSwapCircuit n).matrix =
      UnitaryOperator.ofPerm (literalWordSwapPerm n).symm :=
  literalGateListCircuit_matrix_eq n (literalSwapGates n)

/-- Concrete three-CNOT-per-bit `WordSwap` certificate on the literal HRS
carrier. -/
def literalWordSwap (n : Nat) : WordSwap n (LiteralBorrowed n) where
  perm := literalWordSwapPerm n
  swaps_words := by
    intro sourceWord targetWord flag borrowedWord
    change literalSwapStep n
        ((sourceWord, targetWord), (flag, borrowedWord)) = _
    exact literalSwapStep_swaps n
      ((sourceWord, targetWord), (flag, borrowedWord))
  circuit := literalWordSwapCircuit n
  matrix_eq := literalWordSwapCircuit_matrix_eq n
  toffoli_exact := by
    change ResourcePool.count (.gate (.builtin "toffoli"))
      (literalSwapProgram n).eventCost = 0
    exact literalSwapProgram_toffoli_count_eq n
  cnot_exact := by
    change ResourcePool.count (.gate (.builtin "cnot"))
      (literalSwapProgram n).eventCost = 3 * n
    exact literalSwapProgram_cnot_count_eq n

namespace WordSwap

variable {n : Nat} {Borrowed : Register}

/-- Basis action of a certified physical word swap. -/
theorem applyNormalized_ket (swap : WordSwap n Borrowed)
    (state : State n Borrowed) :
    swap.circuit.applyNormalized
        (NormalizedVector.ket (R := register n Borrowed) state) =
      NormalizedVector.ket (R := register n Borrowed) (swap.perm state) := by
  change swap.circuit.matrix.apply _ = _
  rw [swap.matrix_eq, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-- A certified word swap leaves every borrowed label unchanged. -/
theorem preserves_borrowed (swap : WordSwap n Borrowed)
    (state : State n Borrowed) :
    borrowed (swap.perm state) = borrowed state := by
  rcases state with ⟨⟨sourceWord, targetWord⟩, ⟨flag, borrowedWord⟩⟩
  rw [swap.swaps_words]
  rfl

end WordSwap

/-! ## Certified pass composition -/

/-- Compose certified stage permutations in list execution order. -/
def selectedPerm {params : Parameters n} {Borrowed : Register}
    {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract) :
    List (Fin n) → Equiv.Perm (State n Borrowed)
  | [] => Equiv.refl _
  | bit :: bits =>
      (implementation bit).perm.trans (selectedPerm implementation bits)

/-- Natural contribution selected by one source bit in either accumulation
pass. -/
def selectedContribution (params : Parameters n) (subtract : Bool)
    (sourceWord : PlainAdder.Word n) (bit : Fin n) : Nat :=
  if sourceWord.val.testBit bit.val then
    params.signedStageConstant subtract bit
  else
    0

/-- Pure accumulator fold corresponding to an ordered selected-add pass. -/
def selectedTarget (params : Parameters n) (subtract : Bool)
    (sourceWord : PlainAdder.Word n) :
    List (Fin n) → PlainAdder.Word n → PlainAdder.Word n
  | [], targetWord => targetWord
  | bit :: bits, targetWord =>
      selectedTarget params subtract sourceWord bits
        (if sourceWord.val.testBit bit.val then
          params.addReduced (params.signedStageConstant subtract bit)
            targetWord
        else
          targetWord)

/-- A selected target step preserves canonicality below the modulus. -/
theorem selectedTarget_lt_modulus (params : Parameters n) (subtract : Bool)
    (sourceWord : PlainAdder.Word n) :
    ∀ (bits : List (Fin n)) (targetWord : PlainAdder.Word n),
      targetWord.val < params.modulus →
      (selectedTarget params subtract sourceWord bits targetWord).val <
        params.modulus
  | [], _, htarget => htarget
  | bit :: bits, targetWord, htarget => by
      apply selectedTarget_lt_modulus params subtract sourceWord bits
      by_cases hselected : sourceWord.val.testBit bit.val
      · simp only [hselected, if_true, Parameters.addReduced, htarget]
        rw [Parameters.word_val]
        exact Nat.mod_lt _ params.modulus_pos
      · simpa [hselected] using htarget

/-- On the clean canonical subspace, a certified selected-stage pass changes
only the accumulator according to `selectedTarget`. -/
theorem selectedPerm_canonical_action
    {params : Parameters n} {Borrowed : Register} {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract) :
    ∀ (bits : List (Fin n)) (sourceWord targetWord : PlainAdder.Word n)
      (borrowedWord : Borrowed.Index),
      sourceWord.val < params.modulus →
      targetWord.val < params.modulus →
      selectedPerm implementation bits
          ((sourceWord, targetWord), (false, borrowedWord)) =
        ((sourceWord,
            selectedTarget params subtract sourceWord bits targetWord),
          (false, borrowedWord))
  | [], _, _, _, _, _ => rfl
  | bit :: bits, sourceWord, targetWord, borrowedWord,
      hsource, htarget => by
      change selectedPerm implementation bits
          ((implementation bit).perm
            ((sourceWord, targetWord), (false, borrowedWord))) = _
      rw [(implementation bit).canonical_action sourceWord targetWord
        borrowedWord hsource htarget]
      change selectedPerm implementation bits
          ((sourceWord,
              if sourceWord.val.testBit bit.val then
                params.addReduced
                  (params.signedStageConstant subtract bit) targetWord
              else
                targetWord),
            (false, borrowedWord)) = _
      apply selectedPerm_canonical_action implementation bits sourceWord _
        borrowedWord hsource
      by_cases hselected : sourceWord.val.testBit bit.val
      · simp only [hselected, if_true, Parameters.addReduced, htarget]
        rw [Parameters.word_val]
        exact Nat.mod_lt _ params.modulus_pos
      · simpa [hselected] using htarget

/-- Splitting a selected-target schedule preserves execution order. -/
theorem selectedTarget_append (params : Parameters n) (subtract : Bool)
    (sourceWord targetWord : PlainAdder.Word n)
    (first second : List (Fin n)) :
    selectedTarget params subtract sourceWord (first ++ second) targetWord =
      selectedTarget params subtract sourceWord second
        (selectedTarget params subtract sourceWord first targetWord) := by
  induction first generalizing targetWord with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.cons_append, selectedTarget]
      exact ih _

/-- Numeric value after a selected pass is the initial canonical accumulator
plus the sum of its actually selected modular constants, reduced once. -/
theorem selectedTarget_val_eq_sum (params : Parameters n) (subtract : Bool)
    (sourceWord : PlainAdder.Word n) :
    ∀ (bits : List (Fin n)) (targetWord : PlainAdder.Word n),
      targetWord.val < params.modulus →
      (selectedTarget params subtract sourceWord bits targetWord).val =
        (targetWord.val +
          (bits.map
            (selectedContribution params subtract sourceWord)).sum) %
          params.modulus
  | [], targetWord, htarget => by
      simp [selectedTarget, htarget, Nat.mod_eq_of_lt]
  | bit :: bits, targetWord, htarget => by
      let nextTarget : PlainAdder.Word n :=
        if sourceWord.val.testBit bit.val then
          params.addReduced (params.signedStageConstant subtract bit)
            targetWord
        else
          targetWord
      have hnext : nextTarget.val < params.modulus := by
        unfold nextTarget
        by_cases hselected : sourceWord.val.testBit bit.val
        · simp only [hselected, if_true, Parameters.addReduced, htarget]
          rw [Parameters.word_val]
          exact Nat.mod_lt _ params.modulus_pos
        · simpa [hselected] using htarget
      have hnextVal :
          nextTarget.val =
            (targetWord.val +
              selectedContribution params subtract sourceWord bit) %
              params.modulus := by
        unfold nextTarget selectedContribution
        by_cases hselected : sourceWord.val.testBit bit.val
        · simp only [hselected, if_true, Parameters.addReduced, htarget]
          rw [Parameters.word_val]
        · simp [hselected, Nat.mod_eq_of_lt htarget]
      change (selectedTarget params subtract sourceWord bits nextTarget).val = _
      rw [selectedTarget_val_eq_sum params subtract sourceWord bits nextTarget
        hnext, hnextVal]
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Ordinary bit-selected binary contribution for a coefficient modulo an
arbitrary positive modulus. -/
def binaryContribution (modulus coefficient sourceValue : Nat)
    {width : Nat} (bit : Fin width) : Nat :=
  if sourceValue.testBit bit.val then
    (coefficient * 2 ^ bit.val) % modulus
  else
    0

/-- A valid position extends the canonical finite-range prefix by exactly
that position. -/
theorem finRange_take_succ {width : Nat} (bit : Fin width) :
    (List.finRange width).take (bit.val + 1) =
      (List.finRange width).take bit.val ++ [bit] := by
  have hbit : bit.val < (List.finRange width).length := by
    simpa only [List.length_finRange] using bit.isLt
  have hat : (List.finRange width)[bit.val]'hbit = bit := by
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  simpa only [hat] using
    (List.take_concat_get' (List.finRange width) bit.val hbit).symm

/-- Cast form of the binary-prefix identity for the sum of selected modular
contributions.  Casting into `ZMod modulus` removes each stage's local
reduction without losing the exact final residue. -/
theorem binaryContribution_sum_cast_take {modulus width : Nat}
    [NeZero modulus] (coefficient sourceValue : Nat) :
    ∀ rounds : Nat, rounds ≤ width →
      ((((List.finRange width).take rounds).map
          (binaryContribution modulus coefficient sourceValue)).sum : Nat) =
        ((coefficient * (sourceValue % 2 ^ rounds) : Nat) : ZMod modulus)
  | 0, _ => by
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.cast_zero,
        pow_zero, Nat.mod_one, Nat.mul_zero]
  | rounds + 1, hrounds => by
      let bit : Fin width := ⟨rounds, Nat.lt_of_succ_le hrounds⟩
      have hprefix := finRange_take_succ bit
      have hinduction := binaryContribution_sum_cast_take
        (modulus := modulus) (width := width) coefficient sourceValue rounds
        (Nat.le_trans (Nat.le_succ rounds) hrounds)
      have hdecomp :
          sourceValue % 2 ^ (rounds + 1) =
            sourceValue % 2 ^ rounds +
              (sourceValue.testBit rounds).toNat * 2 ^ rounds := by
        rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]
      calc
        ((((List.finRange width).take (rounds + 1)).map
              (binaryContribution modulus coefficient sourceValue)).sum : Nat) =
            (((((List.finRange width).take rounds).map
                (binaryContribution modulus coefficient sourceValue)).sum +
              binaryContribution modulus coefficient sourceValue bit : Nat) :
                ZMod modulus) := by
                rw [show (List.finRange width).take (rounds + 1) =
                    (List.finRange width).take rounds ++ [bit] by
                  simpa only [bit, Nat.succ_eq_add_one] using hprefix]
                simp
        _ = ((((List.finRange width).take rounds).map
                (binaryContribution modulus coefficient sourceValue)).sum : Nat) +
              (binaryContribution modulus coefficient sourceValue bit : Nat) := by
                push_cast
                rfl
        _ = ((coefficient * (sourceValue % 2 ^ rounds) : Nat) :
              ZMod modulus) +
              (binaryContribution modulus coefficient sourceValue bit : Nat) := by
                rw [hinduction]
        _ = ((coefficient * (sourceValue % 2 ^ (rounds + 1)) : Nat) :
              ZMod modulus) := by
                cases hselected : sourceValue.testBit rounds
                · simp only [binaryContribution, bit, hselected,
                    Bool.false_eq_true, if_false, Bool.toNat_false, zero_mul,
                    add_zero] at ⊢ hdecomp
                  rw [hdecomp]
                  simp
                · simp only [binaryContribution, bit, hselected, if_true,
                    Bool.toNat_true, one_mul] at ⊢ hdecomp
                  rw [hdecomp]
                  rw [ZMod.natCast_mod]
                  push_cast
                  ring

/-- Full-width specialization of the selected binary-contribution sum. -/
theorem binaryContribution_sum_cast (modulus width coefficient sourceValue : Nat)
    [NeZero modulus] (hsource : sourceValue < 2 ^ width) :
    (((List.finRange width).map
        (binaryContribution modulus coefficient sourceValue)).sum : Nat) =
      ((coefficient * sourceValue : Nat) : ZMod modulus) := by
  have h := binaryContribution_sum_cast_take
    (modulus := modulus) (width := width) coefficient sourceValue width le_rfl
  have htake :
      (List.finRange width).take width = List.finRange width := by
    simp
  rw [htake, Nat.mod_eq_of_lt hsource] at h
  exact h

/-- A forward HRS stage selects exactly the ordinary binary contribution of
the multiplication constant. -/
theorem selectedContribution_false_eq_binary (params : Parameters n)
    (sourceWord : PlainAdder.Word n) (bit : Fin n) :
    selectedContribution params false sourceWord bit =
      binaryContribution params.modulus params.constant.val sourceWord.val bit := by
  simp [selectedContribution, binaryContribution,
    Parameters.signedStageConstant, Parameters.stageConstant]

/-- A reverse HRS stage contributes the additive inverse, modulo `N`, of the
ordinary binary contribution of the registered inverse constant. -/
theorem selectedContribution_true_cast_eq_neg (params : Parameters n)
    (sourceWord : PlainAdder.Word n) (bit : Fin n) :
    letI : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
    ((selectedContribution params true sourceWord bit : Nat) :
        ZMod params.modulus) =
      -((binaryContribution params.modulus params.inverse.val
          sourceWord.val bit : Nat) : ZMod params.modulus) := by
  let _ : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
  by_cases hselected : sourceWord.val.testBit bit.val
  · simp only [selectedContribution, binaryContribution, hselected, if_true,
      Parameters.signedStageConstant]
    have hremainder :
        (params.inverse.val * 2 ^ bit.val) % params.modulus ≤
          params.modulus :=
      Nat.le_of_lt (Nat.mod_lt _ params.modulus_pos)
    rw [ZMod.natCast_mod, Nat.cast_sub hremainder, ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  · simp [selectedContribution, binaryContribution, hselected]

/-- The complete reverse-pass contribution sum is the additive inverse of
the inverse constant times the source word.  Reversing the bit schedule does
not change this additive sum. -/
theorem selectedContribution_true_sum_cast (params : Parameters n)
    (sourceWord : PlainAdder.Word n) :
    letI : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
    ((((List.finRange n).reverse.map
        (selectedContribution params true sourceWord)).sum : Nat) :
        ZMod params.modulus) =
      -((params.inverse.val * sourceWord.val : Nat) : ZMod params.modulus) := by
  let _ : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
  have hpointwise :
      ∀ bits : List (Fin n),
        (((bits.map
            (selectedContribution params true sourceWord)).sum : Nat) :
            ZMod params.modulus) =
          -(((bits.map
              (binaryContribution params.modulus params.inverse.val
                sourceWord.val)).sum : Nat) : ZMod params.modulus) := by
    intro bits
    induction bits with
    | nil => simp
    | cons bit bits ih =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        rw [selectedContribution_true_cast_eq_neg, ih]
        ring
  rw [List.map_reverse, List.sum_reverse]
  rw [hpointwise]
  rw [binaryContribution_sum_cast params.modulus n params.inverse.val
    sourceWord.val (ZMod.val_lt sourceWord)]

/-- The complete forward-pass contribution sum is the multiplication
constant times the source word modulo `N`. -/
theorem selectedContribution_false_sum_cast (params : Parameters n)
    (sourceWord : PlainAdder.Word n) :
    letI : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
    (((List.finRange n).map
        (selectedContribution params false sourceWord)).sum : Nat) =
      ((params.constant.val * sourceWord.val : Nat) :
        ZMod params.modulus) := by
  let _ : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
  have hmap :
      (List.finRange n).map
          (selectedContribution params false sourceWord) =
        (List.finRange n).map
          (binaryContribution params.modulus params.constant.val
            sourceWord.val) := by
    apply List.map_congr_left
    intro bit _
    exact selectedContribution_false_eq_binary params sourceWord bit
  rw [hmap]
  exact binaryContribution_sum_cast params.modulus n params.constant.val
    sourceWord.val (ZMod.val_lt sourceWord)

/-- The complete forward selected-add pass, starting from zero, produces the
modular product of the fixed constant and the source word. -/
theorem selectedTarget_forward_zero (params : Parameters n)
    (sourceWord : PlainAdder.Word n) :
    selectedTarget params false sourceWord
        (List.ofFn fun bit : Fin n => bit) (params.word 0) =
      params.word (params.constant.val * sourceWord.val) := by
  let _ : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
  have hbits :
      List.ofFn (fun bit : Fin n => bit) = List.finRange n := by
    exact List.ofFn_id n
  rw [hbits]
  apply ZMod.val_injective
  rw [selectedTarget_val_eq_sum params false sourceWord
    (List.finRange n) (params.word 0) (by
      rw [Parameters.word_val]
      exact Nat.mod_lt _ params.modulus_pos)]
  rw [Parameters.word_val, Parameters.word_val]
  have hsumCast := selectedContribution_false_sum_cast params sourceWord
  have hsumMod :=
    (ZMod.natCast_eq_natCast_iff'
      ((List.finRange n).map
        (selectedContribution params false sourceWord) |>.sum)
      (params.constant.val * sourceWord.val) params.modulus).mp hsumCast
  simpa using hsumMod

/-- The reverse selected-add pass subtracts the inverse multiple of the
post-swap source.  When that source is the forward product, the original
source word in the target is cleared exactly. -/
theorem selectedTarget_inverse_cancels_product (params : Parameters n)
    (sourceWord : PlainAdder.Word n)
    (hsource : sourceWord.val < params.modulus) :
    selectedTarget params true
        (params.word (params.constant.val * sourceWord.val))
        (List.ofFn fun bit : Fin n => bit).reverse sourceWord =
      params.word 0 := by
  let _ : NeZero params.modulus := ⟨Nat.ne_of_gt params.modulus_pos⟩
  have hbits :
      List.ofFn (fun bit : Fin n => bit) = List.finRange n := by
    exact List.ofFn_id n
  rw [hbits]
  let productWord : PlainAdder.Word n :=
    params.word (params.constant.val * sourceWord.val)
  let inverseSum : Nat :=
    ((List.finRange n).reverse.map
      (selectedContribution params true productWord)).sum
  have honeLt : 1 < params.modulus := by
    have hlt := Nat.mod_lt
      (params.inverse.val * params.constant.val) params.modulus_pos
    rw [params.inverse_mul_constant] at hlt
    exact hlt
  have hinverseConstantCast :
      ((params.inverse.val * params.constant.val : Nat) :
          ZMod params.modulus) = 1 := by
    have hcast :
        ((params.inverse.val * params.constant.val : Nat) :
            ZMod params.modulus) = ((1 : Nat) : ZMod params.modulus) :=
      (ZMod.natCast_eq_natCast_iff'
        (params.inverse.val * params.constant.val) 1 params.modulus).mpr (by
          simpa [Nat.mod_eq_of_lt honeLt] using
            params.inverse_mul_constant)
    simpa using hcast
  have hproductCast :
      ((productWord.val : Nat) : ZMod params.modulus) =
        ((params.constant.val * sourceWord.val : Nat) :
          ZMod params.modulus) := by
    dsimp [productWord]
    rw [Parameters.word_val, ZMod.natCast_mod]
  have hcancelCast :
      ((params.inverse.val * productWord.val : Nat) :
          ZMod params.modulus) =
        (sourceWord.val : ZMod params.modulus) := by
    push_cast
    rw [hproductCast]
    push_cast
    calc
      (params.inverse.val : ZMod params.modulus) *
          ((params.constant.val : ZMod params.modulus) *
            (sourceWord.val : ZMod params.modulus)) =
          (((params.inverse.val * params.constant.val : Nat) :
              ZMod params.modulus) *
            (sourceWord.val : ZMod params.modulus)) := by
              push_cast
              ring
      _ = sourceWord.val := by
        rw [hinverseConstantCast]
        simp
  have hinverseSumCast :
      ((inverseSum : Nat) : ZMod params.modulus) =
        -((params.inverse.val * productWord.val : Nat) :
          ZMod params.modulus) := by
    simpa only [inverseSum] using
      selectedContribution_true_sum_cast params productWord
  have htotalCast :
      ((sourceWord.val + inverseSum : Nat) : ZMod params.modulus) = 0 := by
    push_cast
    rw [hinverseSumCast, hcancelCast]
    ring
  have htotalMod :=
    (ZMod.natCast_eq_natCast_iff'
      (sourceWord.val + inverseSum) 0 params.modulus).mp (by
        simpa using htotalCast)
  apply ZMod.val_injective
  rw [selectedTarget_val_eq_sum params true productWord
    (List.finRange n).reverse sourceWord hsource]
  rw [Parameters.word_val]
  simpa only [inverseSum, Nat.zero_mod] using htotalMod

/-- Compose the actual certified stage circuits in the same bit order. -/
def selectedProgram {params : Parameters n} (Borrowed : Register)
    {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract) :
    List (Fin n) → UnitaryCircuit (register n Borrowed)
  | [] => UnitaryCircuit.identity (register n Borrowed) [] (by simp)
  | bit :: bits =>
      UnitaryCircuit.seq (implementation bit).circuit
        (selectedProgram Borrowed implementation bits)

/-- The selected circuit fold acts by the selected permutation fold on every
basis label, including padding labels. -/
theorem selectedProgram_applyNormalized_ket
    {params : Parameters n} {Borrowed : Register} {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract) :
    ∀ (bits : List (Fin n)) (state : State n Borrowed),
      (selectedProgram Borrowed implementation bits).applyNormalized
          (NormalizedVector.ket (R := register n Borrowed) state) =
        NormalizedVector.ket (R := register n Borrowed)
          (selectedPerm implementation bits state)
  | [], state => by
      simp [selectedProgram, selectedPerm]
  | bit :: bits, state => by
      rw [selectedProgram, UnitaryCircuit.applyNormalized_seq,
        (implementation bit).applyNormalized_ket,
        selectedProgram_applyNormalized_ket implementation bits]
      rfl

/-- Operator equality for an arbitrary certified selected-stage pass. -/
theorem selectedProgram_matrix_eq
    {params : Parameters n} {Borrowed : Register} {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract)
    (bits : List (Fin n)) :
    (selectedProgram Borrowed implementation bits).matrix =
      UnitaryOperator.ofPerm (selectedPerm implementation bits).symm := by
  apply Subtype.ext
  apply Matrix.ext
  intro output input
  have hcircuit :=
    selectedProgram_applyNormalized_ket implementation bits input
  have hperm :
      (UnitaryOperator.ofPerm
          (selectedPerm implementation bits).symm).apply
          (NormalizedVector.ket (R := register n Borrowed) input) =
        NormalizedVector.ket (R := register n Borrowed)
          (selectedPerm implementation bits input) := by
    rw [UnitaryOperator.ofPerm_apply_ket]
    rfl
  have heq := hcircuit.trans hperm.symm
  have hpoint := congrArg
    (fun state : NormalizedVector (register n Borrowed) => state output) heq
  simpa [UnitaryCircuit.applyNormalized, UnitaryOperator.apply,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using hpoint

/-- Every selected-stage pass restores the complete borrowed label. -/
theorem selectedPerm_preserves_borrowed
    {params : Parameters n} {Borrowed : Register} {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract) :
    ∀ (bits : List (Fin n)) (state : State n Borrowed),
      borrowed (selectedPerm implementation bits state) = borrowed state
  | [], _ => rfl
  | bit :: bits, state => by
      change borrowed
          (selectedPerm implementation bits
            ((implementation bit).perm state)) = borrowed state
      rw [selectedPerm_preserves_borrowed implementation bits,
        (implementation bit).preserves_borrowed]

/-- Exact Toffoli coordinate of a selected-stage pass, expressed as the sum
of the exact coordinates stored by its actual member circuits. -/
def selectedToffoliCount {params : Parameters n} {Borrowed : Register}
    {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract)
    (bits : List (Fin n)) : Nat :=
  (bits.map fun bit => (implementation bit).toffoli_count).sum

/-- Exact CNOT coordinate of a selected-stage pass. -/
def selectedCnotCount {params : Parameters n} {Borrowed : Register}
    {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract)
    (bits : List (Fin n)) : Nat :=
  (bits.map fun bit => (implementation bit).cnot_count).sum

/-- The folded actual circuit has exactly the summed Toffoli coordinate. -/
theorem selectedProgram_toffoli_count_eq
    {params : Parameters n} {Borrowed : Register} {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract) :
    ∀ bits : List (Fin n),
      ResourcePool.count (.gate (.builtin "toffoli"))
          (selectedProgram Borrowed implementation bits).eventCost =
        selectedToffoliCount implementation bits
  | [] => by simp [selectedProgram, selectedToffoliCount]
  | bit :: bits => by
      rw [selectedProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        (implementation bit).toffoli_exact,
        selectedProgram_toffoli_count_eq implementation bits]
      rfl

/-- The folded actual circuit has exactly the summed CNOT coordinate. -/
theorem selectedProgram_cnot_count_eq
    {params : Parameters n} {Borrowed : Register} {subtract : Bool}
    (implementation : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit subtract) :
    ∀ bits : List (Fin n),
      ResourcePool.count (.gate (.builtin "cnot"))
          (selectedProgram Borrowed implementation bits).eventCost =
        selectedCnotCount implementation bits
  | [] => by simp [selectedProgram, selectedCnotCount]
  | bit :: bits => by
      rw [selectedProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        (implementation bit).cnot_exact,
        selectedProgram_cnot_count_eq implementation bits]
      rfl

/-- Ordered forward selected-add programs, one for each little-endian source
bit.  Each element is an actual circuit supplied by a future literal HRS
controlled modular-adder implementation. -/
def forwardPrograms (params : Parameters n) (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false) :
    List (UnitaryCircuit (register n Borrowed)) :=
  List.ofFn fun bit => (forward bit).circuit

/-- Forward repeated-addition program in HRS bit order. -/
def forwardProgram (params : Parameters n) (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false) :
    UnitaryCircuit (register n Borrowed) :=
  selectedProgram Borrowed forward (List.ofFn fun bit : Fin n => bit)

/-- Reverse selected-addition programs.  The list is reversed so the adjoint
uncompute runs the high bit first, precisely undoing the forward low-to-high
accumulation after the physical word swap. -/
def inversePrograms (params : Parameters n) (Borrowed : Register)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true) :
    List (UnitaryCircuit (register n Borrowed)) :=
  (List.ofFn fun bit => (inverse bit).circuit).reverse

/-- Reverse repeated-addition program in the HRS compute/swap/uncompute
construction. -/
def inverseProgram (params : Parameters n) (Borrowed : Register)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true) :
    UnitaryCircuit (register n Borrowed) :=
  selectedProgram Borrowed inverse
    (List.ofFn fun bit : Fin n => bit).reverse

/-- Total permutation of the forward low-to-high accumulation pass. -/
def forwardPerm (params : Parameters n) (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false) :
    Equiv.Perm (State n Borrowed) :=
  selectedPerm forward (List.ofFn fun bit : Fin n => bit)

/-- Total permutation of the reverse high-to-low inverse accumulation pass. -/
def inversePerm (params : Parameters n) (Borrowed : Register)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true) :
    Equiv.Perm (State n Borrowed) :=
  selectedPerm inverse (List.ofFn fun bit : Fin n => bit).reverse

/-- Total permutation of the HRS compute/swap/uncompute assembly. -/
def inPlacePerm (params : Parameters n) (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false)
    (swap : WordSwap n Borrowed)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true) :
    Equiv.Perm (State n Borrowed) :=
  (forwardPerm params Borrowed forward).trans
    (swap.perm.trans (inversePerm params Borrowed inverse))

/-- The complete HRS program is an actual `UnitaryCircuit.seq` composition of the
forward selected-adds, the physical word swap, and inverse selected-adds.
Its resource trace is consequently owned by one circuit tree. -/
def program (params : Parameters n) (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false)
    (swap : WordSwap n Borrowed)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true) :
    UnitaryCircuit (register n Borrowed) :=
  UnitaryCircuit.seq (forwardProgram params Borrowed forward)
    (UnitaryCircuit.seq swap.circuit (inverseProgram params Borrowed inverse))

/-- The assembled program acts by its composed certified permutation on every
basis label. -/
theorem program_applyNormalized_ket (params : Parameters n)
    (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false)
    (swap : WordSwap n Borrowed)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true)
    (state : State n Borrowed) :
    (program params Borrowed forward swap inverse).applyNormalized
        (NormalizedVector.ket (R := register n Borrowed) state) =
      NormalizedVector.ket (R := register n Borrowed)
        (inPlacePerm params Borrowed forward swap inverse state) := by
  rw [program, UnitaryCircuit.applyNormalized_seq,
    forwardProgram, selectedProgram_applyNormalized_ket,
    UnitaryCircuit.applyNormalized_seq, swap.applyNormalized_ket,
    inverseProgram, selectedProgram_applyNormalized_ket]
  rfl

/-- Exact operator equality of the assembled circuit and its composed total
permutation. -/
theorem program_matrix_eq (params : Parameters n) (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false)
    (swap : WordSwap n Borrowed)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true) :
    (program params Borrowed forward swap inverse).matrix =
      UnitaryOperator.ofPerm
        (inPlacePerm params Borrowed forward swap inverse).symm := by
  apply Subtype.ext
  apply Matrix.ext
  intro output input
  have hcircuit :=
    program_applyNormalized_ket params Borrowed forward swap inverse input
  have hperm :
      (UnitaryOperator.ofPerm
          (inPlacePerm params Borrowed forward swap inverse).symm).apply
          (NormalizedVector.ket (R := register n Borrowed) input) =
        NormalizedVector.ket (R := register n Borrowed)
          (inPlacePerm params Borrowed forward swap inverse input) := by
    rw [UnitaryOperator.ofPerm_apply_ket]
    rfl
  have heq := hcircuit.trans hperm.symm
  have hpoint := congrArg
    (fun state : NormalizedVector (register n Borrowed) => state output) heq
  simpa [UnitaryCircuit.applyNormalized, UnitaryOperator.apply,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using hpoint

/-- The total assembled permutation restores every borrowed label on the
entire carrier. -/
theorem inPlacePerm_preserves_borrowed (params : Parameters n)
    (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false)
    (swap : WordSwap n Borrowed)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true)
    (state : State n Borrowed) :
    borrowed (inPlacePerm params Borrowed forward swap inverse state) =
      borrowed state := by
  change borrowed
      (inversePerm params Borrowed inverse
        (swap.perm (forwardPerm params Borrowed forward state))) = _
  rw [inversePerm, selectedPerm_preserves_borrowed,
    swap.preserves_borrowed, forwardPerm,
    selectedPerm_preserves_borrowed]

/-- Clean HRS endpoint of the certified compute/swap/uncompute permutation.
The forward pass writes `constant * source`, the physical word swap moves that
product into place, and the inverse pass clears the former source word. -/
theorem inPlacePerm_clean_endpoint (params : Parameters n)
    (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false)
    (swap : WordSwap n Borrowed)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true)
    (sourceWord : PlainAdder.Word n) (borrowedWord : Borrowed.Index)
    (hsource : sourceWord.val < params.modulus) :
    inPlacePerm params Borrowed forward swap inverse
        ((sourceWord, params.word 0), (false, borrowedWord)) =
      ((params.word (params.constant.val * sourceWord.val), params.word 0),
        (false, borrowedWord)) := by
  have hzero : (params.word 0).val < params.modulus := by
    rw [Parameters.word_val]
    exact Nat.mod_lt _ params.modulus_pos
  have hproduct :
      (params.word (params.constant.val * sourceWord.val)).val <
        params.modulus := by
    rw [Parameters.word_val]
    exact Nat.mod_lt _ params.modulus_pos
  change inversePerm params Borrowed inverse
      (swap.perm
        (forwardPerm params Borrowed forward
          ((sourceWord, params.word 0), (false, borrowedWord)))) = _
  rw [forwardPerm,
    selectedPerm_canonical_action forward _ sourceWord (params.word 0)
      borrowedWord hsource hzero,
    selectedTarget_forward_zero params sourceWord,
    swap.swaps_words,
    inversePerm,
    selectedPerm_canonical_action inverse _
      (params.word (params.constant.val * sourceWord.val)) sourceWord
      borrowedWord hproduct hsource,
    selectedTarget_inverse_cancels_product params sourceWord hsource]

/-- Exact closed-form assembly of native gate coordinates once the two
accumulation passes have been counted from their literal circuits. -/
def toffoliCount (forwardToffoli inverseToffoli : Nat) : Nat :=
  forwardToffoli + inverseToffoli

/-- The middle word swap contributes exactly three CNOTs per word bit. -/
def cnotCount (n forwardCNOT inverseCNOT : Nat) : Nat :=
  forwardCNOT + 3 * n + inverseCNOT

/-- HRS's core in-place layout consists of two `n`-bit words and one clean
comparison flag [HRS16, `paper.tex:273-279`].  A nontrivial `Borrowed`
argument in the abstract certificates is additional physical space; only the
zero-qubit literal core below realizes this count. -/
def coreQubitCount (n : Nat) : Nat :=
  2 * n + 1

@[simp] theorem coreQubitCount_eq (n : Nat) :
    coreQubitCount n = 2 * n + 1 :=
  rfl

/-- The actual literal word-swap encoding, rather than an independent
metadata numeral, realizes the advertised HRS core width. -/
theorem literalSwapEncoding_width_eq_coreQubitCount (n : Nat) :
    (literalSwapEncoding n).width = coreQubitCount n := by
  rw [literalSwapEncoding_width, coreQubitCount_eq]

/-- A completed HRS assembly certificate.  Its equality fields bind the
clean endpoint and exact native coordinates to one actual composed circuit. -/
structure InPlaceRealization (params : Parameters n) (Borrowed : Register)
    (forward : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit false)
    (swap : WordSwap n Borrowed)
    (inverse : ∀ bit : Fin n,
      ControlledModularAdd params Borrowed bit true) where
  /-- Total reversible extension implemented by the assembled circuit. -/
  perm : Equiv.Perm (State n Borrowed)
  matrix_eq :
    (program params Borrowed forward swap inverse).matrix =
      UnitaryOperator.ofPerm perm.symm
  /-- The completed compute/swap/uncompute permutation preserves every
borrowed label, including labels outside the clean computational-basis
endpoint. -/
  preserves_borrowed : ∀ state, borrowed (perm state) = borrowed state
  /-- Clean endpoint required by HRS compute/swap/uncompute. -/
  clean_endpoint : ∀ sourceWord borrowedWord,
    sourceWord.val < params.modulus →
    perm ((sourceWord, params.word 0), (false, borrowedWord)) =
      ((params.word (params.constant.val * sourceWord.val), params.word 0),
        (false, borrowedWord))
  /-- Exact totals for the two literal accumulation passes. -/
  forward_toffoli : Nat
  inverse_toffoli : Nat
  forward_cnot : Nat
  inverse_cnot : Nat
  forward_toffoli_exact :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (forwardProgram params Borrowed forward).eventCost = forward_toffoli
  inverse_toffoli_exact :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (inverseProgram params Borrowed inverse).eventCost = inverse_toffoli
  forward_cnot_exact :
    ResourcePool.count (.gate (.builtin "cnot"))
        (forwardProgram params Borrowed forward).eventCost = forward_cnot
  inverse_cnot_exact :
    ResourcePool.count (.gate (.builtin "cnot"))
        (inverseProgram params Borrowed inverse).eventCost = inverse_cnot

namespace InPlaceRealization

variable {n : Nat} {params : Parameters n} {Borrowed : Register}
variable {forward : ∀ bit : Fin n,
  ControlledModularAdd params Borrowed bit false}
variable {swap : WordSwap n Borrowed}
variable {inverse : ∀ bit : Fin n,
  ControlledModularAdd params Borrowed bit true}

/-- The total assembled program has the exact closed-form Toffoli count from
its two certified selected-addition passes. -/
theorem toffoli_count_eq
    (realization : InPlaceRealization params Borrowed forward swap inverse) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (program params Borrowed forward swap inverse).eventCost =
      toffoliCount realization.forward_toffoli realization.inverse_toffoli := by
  change ResourcePool.count (.gate (.builtin "toffoli"))
      ((forwardProgram params Borrowed forward).eventCost +
        (swap.circuit.eventCost +
          (inverseProgram params Borrowed inverse).eventCost)) = _
  rw [ResourcePool.count_add, ResourcePool.count_add,
    realization.forward_toffoli_exact, swap.toffoli_exact,
    realization.inverse_toffoli_exact]
  simp [toffoliCount]

/-- The total assembled program has the exact closed-form CNOT count from its
two certified selected-addition passes plus the literal word swap. -/
theorem cnot_count_eq
    (realization : InPlaceRealization params Borrowed forward swap inverse) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (program params Borrowed forward swap inverse).eventCost =
      cnotCount n realization.forward_cnot realization.inverse_cnot := by
  change ResourcePool.count (.gate (.builtin "cnot"))
      ((forwardProgram params Borrowed forward).eventCost +
        (swap.circuit.eventCost +
          (inverseProgram params Borrowed inverse).eventCost)) = _
  rw [ResourcePool.count_add, ResourcePool.count_add,
    realization.forward_cnot_exact, swap.cnot_exact,
    realization.inverse_cnot_exact]
  simp [cnotCount, Nat.add_assoc]

/-- The inverse total permutation also preserves every borrowed label. -/
theorem preserves_borrowed_symm
    (realization : InPlaceRealization params Borrowed forward swap inverse)
    (state : State n Borrowed) :
    borrowed (realization.perm.symm state) = borrowed state := by
  have h := realization.preserves_borrowed (realization.perm.symm state)
  simpa using h.symm

/-- Arbitrary-joint-state amplitude law for a completed HRS assembly.  The
clean endpoint above is only a corollary; the matrix equality controls every
borrowed/environment label. -/
theorem applyVec_arbitrary_joint_state
    (realization : InPlaceRealization params Borrowed forward swap inverse)
    (state : HilbertVector (register n Borrowed))
    (output : State n Borrowed) :
    (program params Borrowed forward swap inverse).applyVec state output =
      state (realization.perm.symm output) := by
  change (program params Borrowed forward swap inverse).matrix.applyVec
      state output = _
  rw [realization.matrix_eq, UnitaryOperator.ofPerm_applyVec]

end InPlaceRealization

/-! ## Complete literal HRS multiplier -/

/-- Literal forward modular-add stage on the HRS `2n+1` carrier. -/
def literalForwardAdd (interior : Nat)
    (params : Parameters (interior + 2).succ)
    (bit : Fin (interior + 2).succ) :
    ControlledModularAdd params (LiteralBorrowed (interior + 2).succ)
      bit false :=
  literalControlledModularAdd interior params bit false

/-- Literal inverse modular-subtract stage on the same carrier. -/
def literalInverseAdd (interior : Nat)
    (params : Parameters (interior + 2).succ)
    (bit : Fin (interior + 2).succ) :
    ControlledModularAdd params (LiteralBorrowed (interior + 2).succ)
      bit true :=
  literalControlledModularAdd interior params bit true

/-- Exact forward-pass Toffoli closed form: the finite little-endian sum of
the literal per-stage formulas. -/
def literalForwardToffoliCount (interior : Nat)
    (params : Parameters (interior + 2).succ) : Nat :=
  selectedToffoliCount (literalForwardAdd interior params)
    (List.ofFn fun bit : Fin (interior + 2).succ => bit)

/-- Exact reverse-pass Toffoli closed form. -/
def literalInverseToffoliCount (interior : Nat)
    (params : Parameters (interior + 2).succ) : Nat :=
  selectedToffoliCount (literalInverseAdd interior params)
    (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse

/-- Exact forward-pass CNOT closed form. -/
def literalForwardCnotCount (interior : Nat)
    (params : Parameters (interior + 2).succ) : Nat :=
  selectedCnotCount (literalForwardAdd interior params)
    (List.ofFn fun bit : Fin (interior + 2).succ => bit)

/-- Exact reverse-pass CNOT closed form. -/
def literalInverseCnotCount (interior : Nat)
    (params : Parameters (interior + 2).succ) : Nat :=
  selectedCnotCount (literalInverseAdd interior params)
    (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse

/-- The actual literal HRS compute/swap/uncompute circuit. -/
def literalInPlaceProgram (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    UnitaryCircuit
      (register (interior + 2).succ
        (LiteralBorrowed (interior + 2).succ)) :=
  program params (LiteralBorrowed (interior + 2).succ)
    (literalForwardAdd interior params)
    (literalWordSwap (interior + 2).succ)
    (literalInverseAdd interior params)

/-- Total basis permutation of the literal HRS circuit. -/
def literalInPlacePerm (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    Equiv.Perm
      (State (interior + 2).succ
        (LiteralBorrowed (interior + 2).succ)) :=
  inPlacePerm params (LiteralBorrowed (interior + 2).succ)
    (literalForwardAdd interior params)
    (literalWordSwap (interior + 2).succ)
    (literalInverseAdd interior params)

/-- Complete no-sorry realization certificate for the literal HRS in-place
constant modular multiplier. -/
def literalInPlaceRealization (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    InPlaceRealization params (LiteralBorrowed (interior + 2).succ)
      (literalForwardAdd interior params)
      (literalWordSwap (interior + 2).succ)
      (literalInverseAdd interior params) where
  perm := literalInPlacePerm interior params
  matrix_eq := program_matrix_eq params
    (LiteralBorrowed (interior + 2).succ)
    (literalForwardAdd interior params)
    (literalWordSwap (interior + 2).succ)
    (literalInverseAdd interior params)
  preserves_borrowed := inPlacePerm_preserves_borrowed params
    (LiteralBorrowed (interior + 2).succ)
    (literalForwardAdd interior params)
    (literalWordSwap (interior + 2).succ)
    (literalInverseAdd interior params)
  clean_endpoint := inPlacePerm_clean_endpoint params
    (LiteralBorrowed (interior + 2).succ)
    (literalForwardAdd interior params)
    (literalWordSwap (interior + 2).succ)
    (literalInverseAdd interior params)
  forward_toffoli := literalForwardToffoliCount interior params
  inverse_toffoli := literalInverseToffoliCount interior params
  forward_cnot := literalForwardCnotCount interior params
  inverse_cnot := literalInverseCnotCount interior params
  forward_toffoli_exact := by
    simpa [forwardProgram, literalForwardToffoliCount] using
      selectedProgram_toffoli_count_eq
        (literalForwardAdd interior params)
        (List.ofFn fun bit : Fin (interior + 2).succ => bit)
  inverse_toffoli_exact := by
    simpa [inverseProgram, literalInverseToffoliCount] using
      selectedProgram_toffoli_count_eq
        (literalInverseAdd interior params)
        (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse
  forward_cnot_exact := by
    simpa [forwardProgram, literalForwardCnotCount] using
      selectedProgram_cnot_count_eq
        (literalForwardAdd interior params)
        (List.ofFn fun bit : Fin (interior + 2).succ => bit)
  inverse_cnot_exact := by
    simpa [inverseProgram, literalInverseCnotCount] using
      selectedProgram_cnot_count_eq
        (literalInverseAdd interior params)
        (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse

/-- Exact total-permutation operator certificate of the actual literal
multiplier circuit. -/
theorem literalInPlaceProgram_matrix_eq (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    (literalInPlaceProgram interior params).matrix =
      UnitaryOperator.ofPerm (literalInPlacePerm interior params).symm :=
  (literalInPlaceRealization interior params).matrix_eq

/-- Computational-basis correctness of the actual literal circuit: multiply
the source in place by the fixed unit modulo `N`, clear the second word, and
restore the clean flag and zero-qubit environment. -/
theorem literalInPlaceProgram_applyNormalized_clean_ket (interior : Nat)
    (params : Parameters (interior + 2).succ)
    (sourceWord : PlainAdder.Word (interior + 2).succ)
    (borrowedWord : (LiteralBorrowed (interior + 2).succ).Index)
    (hsource : sourceWord.val < params.modulus) :
    (literalInPlaceProgram interior params).applyNormalized
        (NormalizedVector.ket
          (R := register (interior + 2).succ
            (LiteralBorrowed (interior + 2).succ))
          ((sourceWord, params.word 0), (false, borrowedWord))) =
      NormalizedVector.ket
        (R := register (interior + 2).succ
          (LiteralBorrowed (interior + 2).succ))
        ((params.word (params.constant.val * sourceWord.val), params.word 0),
          (false, borrowedWord)) := by
  rw [literalInPlaceProgram, program_applyNormalized_ket]
  rw [inPlacePerm_clean_endpoint params
    (LiteralBorrowed (interior + 2).succ)
    (literalForwardAdd interior params)
    (literalWordSwap (interior + 2).succ)
    (literalInverseAdd interior params) sourceWord borrowedWord hsource]

/-- Exact Toffoli equality projected from the complete literal circuit. -/
theorem literalInPlaceProgram_toffoli_count_eq (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (literalInPlaceProgram interior params).eventCost =
      toffoliCount (literalForwardToffoliCount interior params)
        (literalInverseToffoliCount interior params) := by
  simpa only [literalInPlaceProgram, literalInPlaceRealization] using
    InPlaceRealization.toffoli_count_eq
      (literalInPlaceRealization interior params)

/-- Exact CNOT equality, including the physical three-CNOT-per-bit swap. -/
theorem literalInPlaceProgram_cnot_count_eq (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (literalInPlaceProgram interior params).eventCost =
      cnotCount (interior + 2).succ
        (literalForwardCnotCount interior params)
        (literalInverseCnotCount interior params) := by
  simpa only [literalInPlaceProgram, literalInPlaceRealization] using
    InPlaceRealization.cnot_count_eq
      (literalInPlaceRealization interior params)

/-- Literal program width is the exact HRS core count `2n+1`; the source word
is reused as dirty carry work rather than allocating a third word. -/
theorem literalInPlaceProgram_qubit_count_eq (interior : Nat) :
    (literalR0Encoding (interior + 2).succ).width =
      coreQubitCount (interior + 2).succ :=
  literalSwapEncoding_width_eq_coreQubitCount (interior + 2).succ

/-! ### Flat gate-list interface for exponent control -/

/-- Concatenate the literal modular-add schedules selected by one HRS pass.
This is the gate-list counterpart of `selectedProgram`; it is exposed so a
later exponentiation layer can mechanically add an exponent-bit control to
the actual X/CNOT/Toffoli schedule. -/
def literalSelectedGates (interior : Nat)
    (params : Parameters (interior + 2).succ) (subtract : Bool) :
    List (Fin (interior + 2).succ) →
      List (EncodedBit.GateSpec
        (literalR0Encoding (interior + 2).succ))
  | [] => []
  | bit :: bits =>
      literalControlledModularAddGates interior bit params.modulus
          (params.signedStageConstant subtract bit) ++
        literalSelectedGates interior params subtract bits

/-- Folding the flat selected-pass gate list gives the same total basis
action as the certified selected permutation. -/
theorem literalSelectedGates_stepList (interior : Nat)
    (params : Parameters (interior + 2).succ) (subtract : Bool) :
    ∀ (bits : List (Fin (interior + 2).succ))
      (state : State (interior + 2).succ
        (LiteralBorrowed (interior + 2).succ)),
      EncodedBit.GateSpec.stepList
          (literalSelectedGates interior params subtract bits) state =
        selectedPerm
          (fun bit => literalControlledModularAdd interior params bit subtract)
          bits state
  | [], _state => rfl
  | bit :: bits, state => by
      rw [literalSelectedGates, EncodedBit.GateSpec.stepList_append]
      rw [literalSelectedGates_stepList interior params subtract bits]
      rfl

/-- The flat selected-pass list has exactly the strict event pool of the
existing typed selected-program composition. -/
theorem literalSelectedGates_eventCost_eq (interior : Nat)
    (params : Parameters (interior + 2).succ) (subtract : Bool) :
    ∀ bits : List (Fin (interior + 2).succ),
      (EncodedBit.GateSpec.programList
          (literalSelectedGates interior params subtract bits)).eventCost =
        (selectedProgram (LiteralBorrowed (interior + 2).succ)
          (fun bit => literalControlledModularAdd interior params bit subtract)
          bits).eventCost
  | [] => rfl
  | bit :: bits => by
      rw [literalSelectedGates, selectedProgram, UnitaryCircuit.seq_eventCost,
        EncodedBit.GateSpec.programList_eventCost,
        List.map_append, ResourcePool.ofList_append,
        ← EncodedBit.GateSpec.programList_eventCost
          (literalControlledModularAddGates interior bit params.modulus
            (params.signedStageConstant subtract bit)),
        ← EncodedBit.GateSpec.programList_eventCost
          (literalSelectedGates interior params subtract bits),
        literalSelectedGates_eventCost_eq interior params subtract bits]
      change
        (literalControlledModularAddCircuit interior bit params.modulus
              (params.signedStageConstant subtract bit)).eventCost + _ = _
      rfl

/-- One literal GateSpec list for the complete HRS
compute/swap/inverse-uncompute multiplier. -/
def literalInPlaceGates (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    List (EncodedBit.GateSpec
      (literalR0Encoding (interior + 2).succ)) :=
  literalSelectedGates interior params false
      (List.ofFn fun bit : Fin (interior + 2).succ => bit) ++
    literalSwapGates (interior + 2).succ ++
    literalSelectedGates interior params true
      (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse

/-- The exposed flat list implements the same complete total permutation as
the typed HRS circuit on every basis label. -/
theorem literalInPlaceGates_stepList (interior : Nat)
    (params : Parameters (interior + 2).succ)
    (state : State (interior + 2).succ
      (LiteralBorrowed (interior + 2).succ)) :
    EncodedBit.GateSpec.stepList
        (literalInPlaceGates interior params) state =
      literalInPlacePerm interior params state := by
  unfold literalInPlaceGates literalInPlacePerm inPlacePerm
    forwardPerm inversePerm
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    literalSelectedGates_stepList,
    literalSelectedGates_stepList]
  rfl

/-- Flattening the literal multiplier does not change its strict event pool;
the list and the typed circuit are two views of the same physical schedule. -/
theorem literalInPlaceGates_eventCost_eq (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    (EncodedBit.GateSpec.programList
        (literalInPlaceGates interior params)).eventCost =
      (literalInPlaceProgram interior params).eventCost := by
  unfold literalInPlaceGates literalInPlaceProgram program forwardProgram
    inverseProgram
  rw [EncodedBit.GateSpec.programList_eventCost,
    List.map_append, List.map_append,
    ResourcePool.ofList_append, ResourcePool.ofList_append,
    ← EncodedBit.GateSpec.programList_eventCost
      (literalSelectedGates interior params false
        (List.ofFn fun bit : Fin (interior + 2).succ => bit)),
    ← EncodedBit.GateSpec.programList_eventCost
      (literalSwapGates (interior + 2).succ),
    ← EncodedBit.GateSpec.programList_eventCost
      (literalSelectedGates interior params true
        (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse),
    literalSelectedGates_eventCost_eq,
    literalSelectedGates_eventCost_eq]
  change _ + (literalSwapProgram (interior + 2).succ).eventCost + _ = _
  rw [UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost]
  simp only [literalWordSwap, literalWordSwapCircuit, literalGateListCircuit,
    UnitaryCircuit.reindex_eventCost]
  exact add_assoc _ _ _

end

end MAU.Multiplication.DirtyBorrowed
end QuantumAlg

end
