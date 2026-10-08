/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor

/-!
# Encoded-word xor by a classical constant

This module turns the set bits of a fixed basis label into concrete X, CNOT,
or Toffoli gate lists.  It is the shared constant load/unload surface for
arithmetic circuits; programs, semantic steps, and direct realization proofs
are all built from the same filtered gate lists.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit
namespace Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- Indices of the set bits of a fixed-width classical constant. -/
def constantOneIndices (constant : Fin (2 ^ width)) : List (Fin width) :=
  (List.ofFn fun bit : Fin width => bit).filter
    (fun bit => constant.val.testBit bit.val)

/-- A fixed-width constant has at most one selected position per target bit. -/
theorem constantOneIndices_length_le (constant : Fin (2 ^ width)) :
    (constantOneIndices constant).length ≤ width := by
  simpa [constantOneIndices] using
    List.length_filter_le
      (l := List.ofFn fun bit : Fin width => bit)
      (p := fun bit => constant.val.testBit bit.val)

theorem constantOneIndices_nodup (constant : Fin (2 ^ width)) :
    (constantOneIndices constant).Nodup := by
  exact (List.nodup_ofFn_ofInjective (fun _ _ h => h)).filter _

@[simp] theorem mem_constantOneIndices (constant : Fin (2 ^ width))
    (bit : Fin width) :
    bit ∈ constantOneIndices constant ↔
      constant.val.testBit bit.val = true := by
  simp [constantOneIndices]

/-- A word whose every semantic source bit is the same encoded control bit. -/
def constantBitWord (bit : EncodedBit encoding) : Word encoding width where
  bit := fun _ => bit

/-! ## Uncontrolled constant xor -/

/-- X gates on exactly the set-bit positions of a classical constant. -/
def xorConstantGates (target : Word encoding width)
    (constant : Fin (2 ^ width)) : List (GateSpec encoding) :=
  (constantOneIndices constant).map fun bit => GateSpec.x (target.bit bit)

/-- Exact leaf count of a constant xor: one X gate per set bit. -/
theorem xorConstantGates_length (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    (xorConstantGates target constant).length =
      (constantOneIndices constant).length := by
  simp [xorConstantGates]

/-- The X coordinate of a constant xor equals its set-bit count. -/
theorem xorConstantGates_xMultiplicity_sum (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    ((xorConstantGates target constant).map GateSpec.xMultiplicity).sum =
      (constantOneIndices constant).length := by
  unfold xorConstantGates
  generalize constantOneIndices constant = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.map_map] at ih ⊢
      simp [ih, Nat.add_comm]

/-- A constant xor has no CNOT leaves. -/
theorem xorConstantGates_cnotMultiplicity_sum (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    ((xorConstantGates target constant).map GateSpec.cnotMultiplicity).sum =
      0 := by
  unfold xorConstantGates
  generalize constantOneIndices constant = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.map_map] at ih ⊢
      simp [ih]

/-- A constant xor has no Toffoli leaves. -/
theorem xorConstantGates_toffoliMultiplicity_sum
    (target : Word encoding width) (constant : Fin (2 ^ width)) :
    ((xorConstantGates target constant).map GateSpec.toffoliMultiplicity).sum =
      0 := by
  unfold xorConstantGates
  generalize constantOneIndices constant = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.map_map] at ih ⊢
      simp [ih]

/-- Base-gate program that xors a classical constant into an encoded word. -/
def xorConstantProgram (target : Word encoding width)
    (constant : Fin (2 ^ width)) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (xorConstantGates target constant)

/-- Semantic action of constant xor. -/
def xorConstantStep (target : Word encoding width)
    (constant : Fin (2 ^ width)) : Data → Data :=
  GateSpec.stepList (xorConstantGates target constant)

/-- Fold semantics for X gates over an explicit index list. -/
def xorConstantIndicesStep (target : Word encoding width)
    (indices : List (Fin width)) : Data → Data :=
  fun x => indices.foldl (fun y bit => (target.bit bit).flip y) x

theorem xorConstantStep_eq_indicesStep (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    xorConstantStep target constant =
      xorConstantIndicesStep target (constantOneIndices constant) := by
  funext x
  rw [xorConstantStep, xorConstantGates, xorConstantIndicesStep,
    GateSpec.stepList_eq_foldl]
  generalize constantOneIndices constant = indices
  induction indices generalizing x with
  | nil => rfl
  | cons bit rest ih =>
      simpa [GateSpec.step] using ih ((target.bit bit).flip x)

/-- A gate list commutes with an explicit sequence of word-bit flips when
every gate is disjoint from every bit of that word. -/
theorem stepList_xorConstantIndicesStep_comm
    (gates : List (GateSpec encoding)) (target : Word encoding width)
    (indices : List (Fin width))
    (hdisjoint : ∀ bit gate, gate ∈ gates →
      GateSpec.bitDisjoint (target.bit bit) gate) (x : Data) :
    GateSpec.stepList gates (xorConstantIndicesStep target indices x) =
      xorConstantIndicesStep target indices (GateSpec.stepList gates x) := by
  induction indices generalizing x with
  | nil => rfl
  | cons bit rest ih =>
      unfold xorConstantIndicesStep at *
      simp only [List.foldl_cons]
      rw [ih]
      rw [GateSpec.stepList_flip_comm_of_bitDisjoint gates (target.bit bit)
        (hdisjoint bit)]

/-- A gate list commutes with xor-loading a classical word when it is
disjoint from every target position. -/
theorem stepList_xorConstantStep_comm
    (gates : List (GateSpec encoding)) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hdisjoint : ∀ bit gate, gate ∈ gates →
      GateSpec.bitDisjoint (target.bit bit) gate) (x : Data) :
    GateSpec.stepList gates (xorConstantStep target constant x) =
      xorConstantStep target constant (GateSpec.stepList gates x) := by
  rw [xorConstantStep_eq_indicesStep]
  rw [stepList_xorConstantIndicesStep_comm gates target
    (constantOneIndices constant) hdisjoint x]

theorem xorConstantIndicesStep_get_target
    (target : Word encoding width) (indices : List (Fin width))
    (hnodup : indices.Nodup) (bit : Fin width)
    (htargetTarget :
      ∀ other, other ≠ bit →
        (target.bit other).wire ≠ (target.bit bit).wire)
    (x : Data) :
    (target.bit bit).get (xorConstantIndicesStep target indices x) =
      ((target.bit bit).get x ^^ decide (bit ∈ indices)) := by
  induction indices generalizing x with
  | nil =>
      simp [xorConstantIndicesStep]
  | cons head rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hheadNotMem : head ∉ rest := hnodup.notMem
      unfold xorConstantIndicesStep at *
      change
        (target.bit bit).get
            (rest.foldl (fun y next => (target.bit next).flip y)
              ((target.bit head).flip x)) =
          ((target.bit bit).get x ^^ decide (bit ∈ head :: rest))
      by_cases hhead : head = bit
      · subst head
        rw [ih hrestNodup ((target.bit bit).flip x)]
        rw [EncodedBit.get_flip_self]
        simp [hheadNotMem]
      · rw [ih hrestNodup ((target.bit head).flip x)]
        have hget :
            (target.bit bit).get ((target.bit head).flip x) =
              (target.bit bit).get x := by
          rw [EncodedBit.get_flip_of_wire_ne (target.bit head)
            (target.bit bit) (htargetTarget head hhead)]
        rw [hget]
        have hbitHead : bit ≠ head := Ne.symm hhead
        by_cases hmem : bit ∈ rest <;> simp [hbitHead, hmem]

/-- Each target bit is toggled by the corresponding bit of the constant. -/
theorem xorConstantStep_get_target (target : Word encoding width)
    (constant : Fin (2 ^ width)) (bit : Fin width)
    (htargetTarget :
      ∀ other, other ≠ bit →
        (target.bit other).wire ≠ (target.bit bit).wire)
    (x : Data) :
    (target.bit bit).get (xorConstantStep target constant x) =
      ((target.bit bit).get x ^^ constant.val.testBit bit.val) := by
  rw [xorConstantStep_eq_indicesStep]
  have h := xorConstantIndicesStep_get_target target
    (constantOneIndices constant) (constantOneIndices_nodup constant)
    bit htargetTarget x
  by_cases hmem : bit ∈ constantOneIndices constant
  · have hbit := (mem_constantOneIndices constant bit).mp hmem
    simpa [hmem, hbit] using h
  · have hbit : constant.val.testBit bit.val = false := by
      cases hb : constant.val.testBit bit.val with
      | false => rfl
      | true => exact False.elim (hmem ((mem_constantOneIndices constant bit).mpr hb))
    simpa [hmem, hbit] using h

/-- Constant xor preserves every readout outside the target word. -/
theorem xorConstantStep_get_observed_of_target_ne
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (observed : EncodedBit encoding)
    (htargetObserved :
      ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (x : Data) :
    observed.get (xorConstantStep target constant x) = observed.get x := by
  unfold xorConstantStep
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [xorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  change ∀ y, observed.get ((target.bit bit).flip y) = observed.get y
  exact fun y =>
    EncodedBit.get_flip_of_wire_ne (target.bit bit) observed
      (htargetObserved bit) y

theorem xorConstant_realizes (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes encoding
      (xorConstantProgram physical oracles target constant) (xorConstantStep target constant) :=
  GateSpec.realizesList physical oracles (xorConstantGates target constant)

/-- Direct realization proof for uncontrolled constant xor. -/
theorem xorConstantWitness (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes encoding (xorConstantProgram physical oracles target constant)
      (xorConstantStep target constant) :=
  xorConstant_realizes physical oracles target constant

/-! ### Uncontrolled unload -/

/-- Reverse X-gate list for unloading a previously xored constant. -/
def xorConstantUnloadGates (target : Word encoding width)
    (constant : Fin (2 ^ width)) : List (GateSpec encoding) :=
  (xorConstantGates target constant).reverse

/-- Base-gate program for unloading an uncontrolled constant. -/
def xorConstantUnloadProgram (target : Word encoding width)
    (constant : Fin (2 ^ width)) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (xorConstantUnloadGates target constant)

/-- Folded reverse-list semantics for unloading an uncontrolled constant. -/
def xorConstantUnloadStep (target : Word encoding width)
    (constant : Fin (2 ^ width)) : Data → Data :=
  GateSpec.stepList (xorConstantUnloadGates target constant)

theorem xorConstantUnload_realizes (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes encoding
      (xorConstantUnloadProgram physical oracles target constant)
      (xorConstantUnloadStep target constant) :=
  GateSpec.realizesList physical oracles (xorConstantUnloadGates target constant)

/-- Direct realization proof for reverse-list uncontrolled unloading. -/
theorem xorConstantUnloadWitness (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes encoding (xorConstantUnloadProgram physical oracles target constant)
      (xorConstantUnloadStep target constant) :=
  xorConstantUnload_realizes physical oracles target constant

/-- Uncontrolled unload preserves every readout outside the target word. -/
theorem xorConstantUnloadStep_get_observed_of_target_ne
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (observed : EncodedBit encoding)
    (htargetObserved :
      ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (x : Data) :
    observed.get (xorConstantUnloadStep target constant x) = observed.get x := by
  unfold xorConstantUnloadStep
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hforward : gate ∈ xorConstantGates target constant := by
    exact List.mem_reverse.mp (by
      simpa [xorConstantUnloadGates] using hgate)
  rw [xorConstantGates] at hforward
  rcases List.mem_map.mp hforward with ⟨bit, _hbit, rfl⟩
  change ∀ y, observed.get ((target.bit bit).flip y) = observed.get y
  exact fun y =>
    EncodedBit.get_flip_of_wire_ne (target.bit bit) observed
      (htargetObserved bit) y

/-- Reverse-list unload toggles each target bit by the same constant bit. -/
theorem xorConstantUnloadStep_get_target
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (bit : Fin width)
    (htargetTarget :
      ∀ other, other ≠ bit →
        (target.bit other).wire ≠ (target.bit bit).wire)
    (x : Data) :
    (target.bit bit).get (xorConstantUnloadStep target constant x) =
      ((target.bit bit).get x ^^ constant.val.testBit bit.val) := by
  have hforward := xorConstantStep_get_target target constant bit
    htargetTarget (xorConstantUnloadStep target constant x)
  have hinverse :
      xorConstantStep target constant
          (xorConstantUnloadStep target constant x) = x := by
    simpa [xorConstantUnloadStep, xorConstantUnloadGates,
      xorConstantStep] using
      GateSpec.stepList_reverse_stepList
        (xorConstantGates target constant).reverse x
  rw [hinverse] at hforward
  cases hbefore :
      (target.bit bit).get (xorConstantUnloadStep target constant x) <;>
    cases hconstant : constant.val.testBit bit.val <;>
    simp_all

/-- Unloading after loading restores the entire encoded value. -/
theorem xorConstantUnloadStep_after_xorConstantStep
    (target : Word encoding width) (constant : Fin (2 ^ width)) (x : Data) :
    xorConstantUnloadStep target constant
        (xorConstantStep target constant x) = x := by
  simpa [xorConstantUnloadStep, xorConstantUnloadGates, xorConstantStep] using
    GateSpec.stepList_reverse_stepList (xorConstantGates target constant) x

/-- Loading after unloading also restores the entire encoded value. -/
theorem xorConstantStep_after_xorConstantUnloadStep
    (target : Word encoding width) (constant : Fin (2 ^ width)) (x : Data) :
    xorConstantStep target constant
        (xorConstantUnloadStep target constant x) = x := by
  simpa [xorConstantUnloadStep, xorConstantUnloadGates, xorConstantStep] using
    GateSpec.stepList_reverse_stepList
      (xorConstantGates target constant).reverse x

/-! ## Singly controlled constant xor -/

/-- CNOT gates that xor a constant into a target word when `control` is set. -/
def controlledXorConstantGates (control : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    List (GateSpec encoding) :=
  (constantOneIndices constant).map fun bit =>
    GateSpec.cnot control (target.bit bit) (hcontrolTarget bit)

/-- Base-gate program for singly controlled constant xor. -/
def controlledXorConstantProgram (control : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (controlledXorConstantGates control target constant hcontrolTarget)

/-- A controlled constant xor contains at most one CNOT per target bit. -/
theorem controlledXorConstantGates_length_le_width
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    (controlledXorConstantGates control target constant
      hcontrolTarget).length ≤ width := by
  simpa [controlledXorConstantGates] using
    constantOneIndices_length_le constant

/-- Exact leaf count of a singly controlled constant xor. -/
theorem controlledXorConstantGates_length
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    (controlledXorConstantGates control target constant
      hcontrolTarget).length = (constantOneIndices constant).length := by
  simp [controlledXorConstantGates]

/-- A singly controlled constant xor contains no physical X leaves. -/
theorem controlledXorConstantGates_xMultiplicity_sum
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    ((controlledXorConstantGates control target constant hcontrolTarget).map
      GateSpec.xMultiplicity).sum = 0 := by
  simp [controlledXorConstantGates, Function.comp_def]

/-- The CNOT coordinate of a singly controlled constant xor is the number of
set bits in the constant. -/
theorem controlledXorConstantGates_cnotMultiplicity_sum
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    ((controlledXorConstantGates control target constant hcontrolTarget).map
      GateSpec.cnotMultiplicity).sum =
      (constantOneIndices constant).length := by
  simp [controlledXorConstantGates, Function.comp_def]

/-- A singly controlled constant xor contains no Toffoli leaves. -/
theorem controlledXorConstantGates_toffoliMultiplicity_sum
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    ((controlledXorConstantGates control target constant hcontrolTarget).map
      GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [controlledXorConstantGates, Function.comp_def]

/-- Folded semantics of the singly controlled constant-xor gate list. -/
def controlledXorConstantStep (control : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    Data → Data :=
  GateSpec.stepList
    (controlledXorConstantGates control target constant hcontrolTarget)

theorem controlledXorConstantStep_eq_indicesStep
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    controlledXorConstantStep control target constant hcontrolTarget =
      xorIntoIndicesStep (constantBitWord control) target
        (constantOneIndices constant) := by
  funext x
  rw [controlledXorConstantStep, controlledXorConstantGates,
    xorIntoIndicesStep, GateSpec.stepList_eq_foldl]
  generalize constantOneIndices constant = indices
  induction indices generalizing x with
  | nil => rfl
  | cons bit rest ih =>
      simpa [GateSpec.step, constantBitWord] using
        ih (cnotStep control (target.bit bit) x)

/-- Each target bit is toggled by control and the matching constant bit. -/
theorem controlledXorConstantStep_get_target
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (bit : Fin width)
    (htargetTarget :
      ∀ other, other ≠ bit →
        (target.bit other).wire ≠ (target.bit bit).wire)
    (x : Data) :
    (target.bit bit).get
        (controlledXorConstantStep control target constant hcontrolTarget x) =
      ((target.bit bit).get x ^^ (control.get x &&
        constant.val.testBit bit.val)) := by
  rw [controlledXorConstantStep_eq_indicesStep]
  have h := xorIntoIndicesStep_get_target
    (constantBitWord control) target (constantOneIndices constant)
    (constantOneIndices_nodup constant) bit htargetTarget
    (fun other => Ne.symm (hcontrolTarget other)) x
  by_cases hmem : bit ∈ constantOneIndices constant
  · have hbit := (mem_constantOneIndices constant bit).mp hmem
    simpa [constantBitWord, hmem, hbit, Bool.and_self] using h
  · have hbit : constant.val.testBit bit.val = false := by
      cases hb : constant.val.testBit bit.val with
      | false => rfl
      | true => exact False.elim (hmem ((mem_constantOneIndices constant bit).mpr hb))
    simpa [constantBitWord, hmem, hbit] using h

/-- Singly controlled constant xor preserves readouts outside the target word. -/
theorem controlledXorConstantStep_get_observed_of_target_ne
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (observed : EncodedBit encoding)
    (htargetObserved :
      ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledXorConstantStep control target constant hcontrolTarget x) =
      observed.get x := by
  unfold controlledXorConstantStep
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [controlledXorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  change ∀ y, observed.get ((target.bit bit).flip y) = observed.get y
  exact fun y =>
    EncodedBit.get_flip_of_wire_ne (target.bit bit) observed
      (htargetObserved bit) y

/-- A false control makes a singly controlled constant xor a no-op. -/
theorem controlledXorConstantStep_eq_self_of_control_false
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (x : Data) (hcontrol : control.get x = false) :
    controlledXorConstantStep control target constant hcontrolTarget x = x := by
  rw [controlledXorConstantStep_eq_indicesStep]
  unfold xorIntoIndicesStep
  generalize constantOneIndices constant = indices
  induction indices generalizing x with
  | nil => rfl
  | cons bit rest ih =>
      change rest.foldl
          (fun y i => cnotStep control (target.bit i) y)
          (cnotStep control (target.bit bit) x) = x
      have hhead : cnotStep control (target.bit bit) x = x := by
        simp [cnotStep, hcontrol]
      rw [hhead]
      exact ih x hcontrol

theorem controlledXorConstant_realizes
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledXorConstantProgram physical oracles control target constant hcontrolTarget)
      (controlledXorConstantStep control target constant hcontrolTarget) :=
  GateSpec.realizesList physical oracles
    (controlledXorConstantGates control target constant hcontrolTarget)

/-- Direct realization proof for singly controlled constant xor. -/
theorem controlledXorConstantWitness
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledXorConstantProgram physical oracles control target constant hcontrolTarget)
      (controlledXorConstantStep control target constant hcontrolTarget) :=
  controlledXorConstant_realizes physical oracles control target constant hcontrolTarget

/-! ### Singly controlled unload -/

/-- Reverse CNOT list for unloading a singly controlled constant. -/
def controlledXorConstantUnloadGates (control : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    List (GateSpec encoding) :=
  (controlledXorConstantGates control target constant hcontrolTarget).reverse

/-- Base-gate program for unloading a singly controlled constant. -/
def controlledXorConstantUnloadProgram (control : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (controlledXorConstantUnloadGates control target constant hcontrolTarget)

/-- Folded reverse-list semantics for singly controlled unloading. -/
def controlledXorConstantUnloadStep (control : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    Data → Data :=
  GateSpec.stepList
    (controlledXorConstantUnloadGates control target constant hcontrolTarget)

theorem controlledXorConstantUnload_realizes
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledXorConstantUnloadProgram physical oracles control target constant hcontrolTarget)
      (controlledXorConstantUnloadStep control target constant hcontrolTarget) :=
  GateSpec.realizesList physical oracles
    (controlledXorConstantUnloadGates control target constant hcontrolTarget)

/-- Direct realization proof for reverse-list singly controlled unloading. -/
theorem controlledXorConstantUnloadWitness
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledXorConstantUnloadProgram physical oracles control target constant
        hcontrolTarget)
      (controlledXorConstantUnloadStep control target constant
        hcontrolTarget) :=
  controlledXorConstantUnload_realizes physical oracles control target constant hcontrolTarget

/-- Singly controlled unload preserves readouts outside the target word. -/
theorem controlledXorConstantUnloadStep_get_observed_of_target_ne
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (observed : EncodedBit encoding)
    (htargetObserved :
      ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledXorConstantUnloadStep control target constant
          hcontrolTarget x) = observed.get x := by
  unfold controlledXorConstantUnloadStep
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hforward :
      gate ∈ controlledXorConstantGates control target constant
        hcontrolTarget := by
    exact List.mem_reverse.mp (by
      simpa [controlledXorConstantUnloadGates] using hgate)
  rw [controlledXorConstantGates] at hforward
  rcases List.mem_map.mp hforward with ⟨bit, _hbit, rfl⟩
  change ∀ y, observed.get ((target.bit bit).flip y) = observed.get y
  exact fun y =>
    EncodedBit.get_flip_of_wire_ne (target.bit bit) observed
      (htargetObserved bit) y

/-- Reverse-list controlled unload has the same target-bit xor formula. -/
theorem controlledXorConstantUnloadStep_get_target
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (bit : Fin width)
    (htargetTarget :
      ∀ other, other ≠ bit →
        (target.bit other).wire ≠ (target.bit bit).wire)
    (x : Data) :
    (target.bit bit).get
        (controlledXorConstantUnloadStep control target constant
          hcontrolTarget x) =
      ((target.bit bit).get x ^^ (control.get x &&
        constant.val.testBit bit.val)) := by
  have hcontrol := controlledXorConstantUnloadStep_get_observed_of_target_ne
    control target constant hcontrolTarget control
    (fun other => Ne.symm (hcontrolTarget other)) x
  have hforward := controlledXorConstantStep_get_target control target constant
    hcontrolTarget bit htargetTarget
    (controlledXorConstantUnloadStep control target constant hcontrolTarget x)
  have hinverse :
      controlledXorConstantStep control target constant hcontrolTarget
          (controlledXorConstantUnloadStep control target constant
            hcontrolTarget x) = x := by
    simpa [controlledXorConstantUnloadStep,
      controlledXorConstantUnloadGates, controlledXorConstantStep] using
      GateSpec.stepList_reverse_stepList
        (controlledXorConstantGates control target constant
          hcontrolTarget).reverse x
  rw [hinverse, hcontrol] at hforward
  cases hbefore :
      (target.bit bit).get
        (controlledXorConstantUnloadStep control target constant
          hcontrolTarget x) <;>
    cases hcontrolValue : control.get x <;>
    cases hconstant : constant.val.testBit bit.val <;>
    simp_all

/-- Controlled unloading after controlled loading restores the encoded value. -/
theorem controlledXorConstantUnloadStep_after_controlledXorConstantStep
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) (x : Data) :
    controlledXorConstantUnloadStep control target constant hcontrolTarget
        (controlledXorConstantStep control target constant hcontrolTarget x) =
      x := by
  simpa [controlledXorConstantUnloadStep, controlledXorConstantUnloadGates,
    controlledXorConstantStep] using
    GateSpec.stepList_reverse_stepList
      (controlledXorConstantGates control target constant hcontrolTarget) x

/-- Controlled loading after controlled unloading restores the encoded value. -/
theorem controlledXorConstantStep_after_controlledXorConstantUnloadStep
    (control : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire) (x : Data) :
    controlledXorConstantStep control target constant hcontrolTarget
        (controlledXorConstantUnloadStep control target constant
          hcontrolTarget x) = x := by
  simpa [controlledXorConstantUnloadStep, controlledXorConstantUnloadGates,
    controlledXorConstantStep] using
    GateSpec.stepList_reverse_stepList
      (controlledXorConstantGates control target constant
        hcontrolTarget).reverse x

/-! ## Constant-schedule singly controlled constant xor -/

/-- Three CNOTs for one classical constant bit.  When the constant bit is set,
the real control acts once and the known-false `zeroControl` acts twice.  When
the constant bit is clear, the real control acts twice and `zeroControl` acts
once.  Thus every classical bit emits the same gate-unit sequence; on states
where `zeroControl` is false the semantic effect is the requested controlled
xor. -/
def constantScheduleBitGates (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (bit : Fin width) : List (GateSpec encoding) :=
  if constant.val.testBit bit.val then
    [ GateSpec.cnot control (target.bit bit) (hcontrolTarget bit),
      GateSpec.cnot zeroControl (target.bit bit) (hzeroTarget bit),
      GateSpec.cnot zeroControl (target.bit bit) (hzeroTarget bit) ]
  else
    [ GateSpec.cnot control (target.bit bit) (hcontrolTarget bit),
      GateSpec.cnot control (target.bit bit) (hcontrolTarget bit),
      GateSpec.cnot zeroControl (target.bit bit) (hzeroTarget bit) ]

/-- Fixed three-CNOT block for every bit of a classical constant. -/
def constantScheduleGates (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun bit : Fin width => bit).flatMap fun bit =>
    constantScheduleBitGates control zeroControl target constant
      hcontrolTarget hzeroTarget bit

/-- Base-gate program for the fixed-schedule controlled constant xor. -/
def constantScheduleProgram (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (constantScheduleGates control zeroControl target constant
      hcontrolTarget hzeroTarget)

/-- Folded semantic action of the fixed-schedule gate list. -/
def constantScheduleStep (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    Data → Data :=
  GateSpec.stepList
    (constantScheduleGates control zeroControl target constant
      hcontrolTarget hzeroTarget)

/-- The fixed-schedule program realizes its folded semantic action. -/
theorem constantSchedule_realizes (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (constantScheduleProgram physical oracles control zeroControl target constant
        hcontrolTarget hzeroTarget)
      (constantScheduleStep control zeroControl target constant
        hcontrolTarget hzeroTarget) :=
  GateSpec.realizesList physical oracles
    (constantScheduleGates control zeroControl target constant
      hcontrolTarget hzeroTarget)

/-- Direct realization proof for the fixed-schedule controlled constant xor. -/
theorem constantScheduleWitness (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (constantScheduleProgram physical oracles control zeroControl target constant
        hcontrolTarget hzeroTarget)
      (constantScheduleStep control zeroControl target constant
        hcontrolTarget hzeroTarget) :=
  constantSchedule_realizes physical oracles control zeroControl target constant
    hcontrolTarget hzeroTarget

/-- Each fixed-schedule bit block has exactly three gates. -/
@[simp] theorem constantScheduleBitGates_length
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (bit : Fin width) :
    (constantScheduleBitGates control zeroControl target constant
      hcontrolTarget hzeroTarget bit).length = 3 := by
  by_cases hbit : constant.val.testBit bit.val <;>
    simp [constantScheduleBitGates, hbit]

/-- The complete schedule always contains three CNOTs per target bit,
independently of the constant's Hamming weight. -/
theorem constantScheduleGates_length
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    (constantScheduleGates control zeroControl target constant
      hcontrolTarget hzeroTarget).length = 3 * width := by
  simp [constantScheduleGates, List.length_flatMap, Function.comp_def,
    Nat.mul_comm]

/-- One fixed-schedule bit block has a strict event trace independent of the
selected classical constant bit. -/
private theorem constantScheduleBitGates_events_eq
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (left right : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (bit : Fin width) :
    (constantScheduleBitGates control zeroControl target left
        hcontrolTarget hzeroTarget bit).map (GateSpec.event oracles) =
      (constantScheduleBitGates control zeroControl target right
        hcontrolTarget hzeroTarget bit).map (GateSpec.event oracles) := by
  unfold constantScheduleBitGates
  split <;> split <;> rfl

/-- The complete fixed schedule has an ordered strict event trace independent
of its compiled classical constant. -/
theorem constantScheduleGates_events_eq
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (left right : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    (constantScheduleGates control zeroControl target left
        hcontrolTarget hzeroTarget).map (GateSpec.event oracles) =
      (constantScheduleGates control zeroControl target right
        hcontrolTarget hzeroTarget).map (GateSpec.event oracles) := by
  unfold constantScheduleGates
  generalize List.ofFn (fun bit : Fin width => bit) = bits
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.flatMap_cons, List.map_append]
      rw [constantScheduleBitGates_events_eq oracles
        control zeroControl target left right hcontrolTarget hzeroTarget bit,
        ih]

/-- The fixed schedule emits exactly three targeted primitive events per bit. -/
theorem constantScheduleProgram_primitiveEventCount
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    GateSpec.primitiveEventCount
      (constantScheduleProgram physical oracles control zeroControl target constant
        hcontrolTarget hzeroTarget) = 3 * width := by
  rw [constantScheduleProgram, GateSpec.primitiveEventCount_programList,
    constantScheduleGates_length]

private def isCnotGate : GateSpec encoding → Prop
  | .cnot _ _ _ => True
  | _ => False

private theorem constantScheduleGates_isCnot
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    ∀ gate,
      gate ∈ constantScheduleGates control zeroControl target constant
        hcontrolTarget hzeroTarget →
      isCnotGate gate := by
  intro gate hgate
  simp only [constantScheduleGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨bit, _hbit, hgate⟩
  simp only [constantScheduleBitGates] at hgate
  split at hgate <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate <;>
    rcases hgate with hgate | hgate | hgate <;> subst gate <;>
    trivial

private theorem cnotMultiplicity_sum_eq_length
    (gates : List (GateSpec encoding))
    (hall : ∀ gate, gate ∈ gates → isCnotGate gate) :
    (gates.map GateSpec.cnotMultiplicity).sum = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      have hgate := hall gate (by simp)
      have hrest : ∀ next, next ∈ rest → isCnotGate next :=
        fun next hnext => hall next (by simp [hnext])
      cases gate with
      | x target => simp [isCnotGate] at hgate
      | cnot control target hct =>
          simp [ih hrest, Nat.add_comm]
      | toffoli controlA controlB target hab ha hb =>
          simp [isCnotGate] at hgate

/-- The fixed schedule's complete primitive envelope is its CNOT coordinate:
three CNOTs are emitted for every target bit. -/
theorem constantScheduleProgram_cnot_eventCount
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (constantScheduleProgram physical oracles control zeroControl target constant
          hcontrolTarget hzeroTarget).eventCost =
      3 * width := by
  rw [constantScheduleProgram, GateSpec.programList_cnot_count_eq_sum]
  rw [cnotMultiplicity_sum_eq_length _
    (constantScheduleGates_isCnot control zeroControl target constant
      hcontrolTarget hzeroTarget)]
  exact constantScheduleGates_length control zeroControl target constant
    hcontrolTarget hzeroTarget

/-- Fixed-schedule strict event cost is independent of the classical constant,
directly from its equal strict event schedule. -/
theorem constantScheduleProgram_eventCost_eq
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (left right : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    (constantScheduleProgram physical oracles control zeroControl target left
        hcontrolTarget hzeroTarget).eventCost =
      (constantScheduleProgram physical oracles control zeroControl target right
        hcontrolTarget hzeroTarget).eventCost := by
  unfold constantScheduleProgram
  apply GateSpec.programList_eventCost_eq_of_events_eq
  exact constantScheduleGates_events_eq oracles
    control zeroControl target left right hcontrolTarget hzeroTarget

/-- Fixed-schedule strict event depth is independent of the classical constant,
directly from its equal strict event schedule. -/
theorem constantScheduleProgram_eventDepth_eq
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (left right : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    (constantScheduleProgram physical oracles control zeroControl target left
        hcontrolTarget hzeroTarget).eventDepth =
      (constantScheduleProgram physical oracles control zeroControl target right
        hcontrolTarget hzeroTarget).eventDepth := by
  unfold constantScheduleProgram
  apply GateSpec.programList_eventDepth_eq_of_events_eq
  exact constantScheduleGates_events_eq oracles
    control zeroControl target left right hcontrolTarget hzeroTarget

/-- Reverse-list unload for the fixed schedule. -/
def constantScheduleUnloadProgram
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (constantScheduleGates control zeroControl target constant
      hcontrolTarget hzeroTarget).reverse

/-- The reverse fixed schedule emits the same targeted primitive events. -/
theorem constantScheduleUnloadProgram_primitiveEventCount
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    GateSpec.primitiveEventCount
      (constantScheduleUnloadProgram physical oracles control zeroControl target constant
        hcontrolTarget hzeroTarget) = 3 * width := by
  rw [constantScheduleUnloadProgram, GateSpec.primitiveEventCount_programList,
    List.length_reverse, constantScheduleGates_length]

/-- Folded reverse-list action for the fixed schedule. -/
def constantScheduleUnloadStep
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    Data → Data :=
  GateSpec.stepList
    (constantScheduleGates control zeroControl target constant
      hcontrolTarget hzeroTarget).reverse

/-- The reverse fixed schedule realizes its folded action. -/
theorem constantScheduleUnload_realizes
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (constantScheduleUnloadProgram physical oracles control zeroControl target constant
        hcontrolTarget hzeroTarget)
      (constantScheduleUnloadStep control zeroControl target constant
        hcontrolTarget hzeroTarget) :=
  GateSpec.realizesList physical oracles _

private theorem reverse_constantScheduleGates_isCnot
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    ∀ gate,
      gate ∈ (constantScheduleGates control zeroControl target constant
        hcontrolTarget hzeroTarget).reverse →
      isCnotGate gate := by
  intro gate hgate
  exact constantScheduleGates_isCnot control zeroControl target constant
    hcontrolTarget hzeroTarget gate (by simpa using hgate)

/-- Reverse fixed-schedule strict event cost is independent of the classical
constant. -/
theorem constantScheduleUnloadProgram_eventCost_eq
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (left right : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    (constantScheduleUnloadProgram physical oracles control zeroControl target left
        hcontrolTarget hzeroTarget).eventCost =
      (constantScheduleUnloadProgram physical oracles control zeroControl target right
        hcontrolTarget hzeroTarget).eventCost := by
  unfold constantScheduleUnloadProgram
  apply GateSpec.programList_eventCost_eq_of_events_eq
  simpa only [List.map_reverse] using
    congrArg List.reverse
      (constantScheduleGates_events_eq oracles
        control zeroControl target left right hcontrolTarget hzeroTarget)

/-- Reverse fixed-schedule strict event depth is independent of the classical
constant. -/
theorem constantScheduleUnloadProgram_eventDepth_eq
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (left right : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    (constantScheduleUnloadProgram physical oracles control zeroControl target left
        hcontrolTarget hzeroTarget).eventDepth =
      (constantScheduleUnloadProgram physical oracles control zeroControl target right
        hcontrolTarget hzeroTarget).eventDepth := by
  unfold constantScheduleUnloadProgram
  apply GateSpec.programList_eventDepth_eq_of_events_eq
  simpa only [List.map_reverse] using
    congrArg List.reverse
      (constantScheduleGates_events_eq oracles
        control zeroControl target left right hcontrolTarget hzeroTarget)

/-- Recursive view of the fixed-schedule bit blocks over an explicit index
list. -/
def constantScheduleIndicesStep (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire) :
    List (Fin width) → Data → Data
  | [], x => x
  | bit :: rest, x =>
      constantScheduleIndicesStep control zeroControl target constant
        hcontrolTarget hzeroTarget rest
        (GateSpec.stepList
          (constantScheduleBitGates control zeroControl target constant
            hcontrolTarget hzeroTarget bit) x)

/-- Flattening the block list agrees with the recursive semantic view. -/
theorem stepList_flatMap_constantScheduleBitGates
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (indices : List (Fin width)) (x : Data) :
    GateSpec.stepList
        (indices.flatMap fun bit =>
          constantScheduleBitGates control zeroControl target constant
            hcontrolTarget hzeroTarget bit) x =
      constantScheduleIndicesStep control zeroControl target constant
        hcontrolTarget hzeroTarget indices x := by
  induction indices generalizing x with
  | nil => rfl
  | cons bit rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append]
      exact ih _

/-- One fixed-schedule block preserves the known-zero control readout. -/
theorem constantScheduleBitStep_get_zeroControl
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (bit : Fin width) (x : Data) :
    zeroControl.get
        (GateSpec.stepList
          (constantScheduleBitGates control zeroControl target constant
            hcontrolTarget hzeroTarget bit) x) =
      zeroControl.get x := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [constantScheduleBitGates] at hgate
  split at hgate <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate <;>
    rcases hgate with hgate | hgate | hgate <;> subst gate <;>
    exact fun y => EncodedBit.get_flip_of_wire_ne
      (target.bit bit) zeroControl (Ne.symm (hzeroTarget bit)) y

/-- On the clean subspace, one three-CNOT block is either the requested CNOT
or the identity according to the corresponding classical constant bit. -/
theorem constantScheduleBitStep_of_zeroControl_false
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (bit : Fin width) (x : Data) (hzero : zeroControl.get x = false) :
    GateSpec.stepList
        (constantScheduleBitGates control zeroControl target constant
          hcontrolTarget hzeroTarget bit) x =
      if constant.val.testBit bit.val then
        cnotStep control (target.bit bit) x
      else x := by
  by_cases hbit : constant.val.testBit bit.val
  · simp only [constantScheduleBitGates]
    rw [if_pos hbit]
    simp only [GateSpec.stepList, GateSpec.step, id_eq]
    rw [EncodedBit.cnotStep_cnotStep zeroControl (target.bit bit)
      (hzeroTarget bit)]
    simp [hbit]
  · simp only [constantScheduleBitGates]
    rw [if_neg hbit]
    simp only [GateSpec.stepList, GateSpec.step, id_eq]
    rw [EncodedBit.cnotStep_cnotStep control (target.bit bit)
      (hcontrolTarget bit)]
    simp only [EncodedBit.cnotStep, hzero, Bool.false_eq_true, if_false]
    simp [hbit]

/-- On the clean subspace, the recursive fixed schedule is the ordinary fold
over exactly the set bits of the constant. -/
theorem constantScheduleIndicesStep_eq_filteredFold_of_zeroControl_false
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (indices : List (Fin width)) (x : Data)
    (hzero : zeroControl.get x = false) :
    constantScheduleIndicesStep control zeroControl target constant
        hcontrolTarget hzeroTarget indices x =
      (indices.filter fun bit => constant.val.testBit bit.val).foldl
        (fun y bit => cnotStep control (target.bit bit) y) x := by
  induction indices generalizing x with
  | nil => rfl
  | cons bit rest ih =>
      rw [constantScheduleIndicesStep]
      rw [constantScheduleBitStep_of_zeroControl_false control zeroControl
        target constant hcontrolTarget hzeroTarget bit x hzero]
      by_cases hbit : constant.val.testBit bit.val
      · simp only [hbit, List.filter_cons_of_pos]
        apply ih
        exact cnotStep_get_of_target_ne control (target.bit bit) zeroControl
          (Ne.symm (hzeroTarget bit)) x |>.trans hzero
      · simp only [hbit]
        simpa [hbit] using ih x hzero

/-- When the designated null control is false, the fixed schedule has exactly
the same semantic action as the Hamming-weight-optimized controlled xor. -/
theorem constantScheduleStep_eq_controlledXorConstantStep_of_zeroControl_false
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (x : Data) (hzero : zeroControl.get x = false) :
    constantScheduleStep control zeroControl target constant
        hcontrolTarget hzeroTarget x =
      controlledXorConstantStep control target constant hcontrolTarget x := by
  rw [constantScheduleStep, constantScheduleGates,
    stepList_flatMap_constantScheduleBitGates]
  rw [constantScheduleIndicesStep_eq_filteredFold_of_zeroControl_false
    control zeroControl target constant hcontrolTarget hzeroTarget _ x hzero]
  rw [controlledXorConstantStep_eq_indicesStep]
  rfl

/-- Reversing the fixed gate list gives an exact unload for every state, not
only on the clean subspace. -/
theorem stepList_reverse_constantScheduleGates
    (control zeroControl : EncodedBit encoding)
    (target : Word encoding width) (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hzeroTarget : ∀ bit, zeroControl.wire ≠ (target.bit bit).wire)
    (x : Data) :
    GateSpec.stepList
        (constantScheduleGates control zeroControl target constant
          hcontrolTarget hzeroTarget).reverse
        (constantScheduleStep control zeroControl target constant
          hcontrolTarget hzeroTarget x) = x := by
  simpa [constantScheduleStep] using
    GateSpec.stepList_reverse_stepList
      (constantScheduleGates control zeroControl target constant
        hcontrolTarget hzeroTarget) x

/-! ## Doubly controlled constant xor -/

/-- Toffoli gates that xor a constant when both controls are set. -/
def doubleControlledXorConstantGates
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    List (GateSpec encoding) :=
  (constantOneIndices constant).map fun bit =>
    GateSpec.toffoli controlA controlB (target.bit bit) hcontrols
      (hcontrolATarget bit) (hcontrolBTarget bit)

/-- Base-gate program for doubly controlled constant xor. -/
def doubleControlledXorConstantProgram
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (doubleControlledXorConstantGates controlA controlB target constant
      hcontrols hcontrolATarget hcontrolBTarget)

/-- Folded semantics of the doubly controlled constant-xor gate list. -/
def doubleControlledXorConstantStep
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    Data → Data :=
  GateSpec.stepList
    (doubleControlledXorConstantGates controlA controlB target constant
      hcontrols hcontrolATarget hcontrolBTarget)

theorem doubleControlledXorConstantStep_eq_indicesStep
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    doubleControlledXorConstantStep controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget =
      controlledXorIntoIndicesStep controlA (constantBitWord controlB) target
        (constantOneIndices constant) := by
  funext x
  rw [doubleControlledXorConstantStep, doubleControlledXorConstantGates,
    controlledXorIntoIndicesStep, GateSpec.stepList_eq_foldl]
  generalize constantOneIndices constant = indices
  induction indices generalizing x with
  | nil => rfl
  | cons bit rest ih =>
      simpa [GateSpec.step, constantBitWord] using
        ih (toffoliStep controlA controlB (target.bit bit) x)

/-- Each target bit is toggled by both controls and the matching constant bit. -/
theorem doubleControlledXorConstantStep_get_target
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire)
    (bit : Fin width)
    (htargetTarget :
      ∀ other, other ≠ bit →
        (target.bit other).wire ≠ (target.bit bit).wire)
    (x : Data) :
    (target.bit bit).get
        (doubleControlledXorConstantStep controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget x) =
      ((target.bit bit).get x ^^
        (controlA.get x && controlB.get x &&
          constant.val.testBit bit.val)) := by
  rw [doubleControlledXorConstantStep_eq_indicesStep]
  have h := controlledXorIntoIndicesStep_get_target
    controlA (constantBitWord controlB) target (constantOneIndices constant)
    (constantOneIndices_nodup constant) bit htargetTarget
    (fun other => Ne.symm (hcontrolATarget other))
    (fun other => Ne.symm (hcontrolBTarget other)) x
  by_cases hmem : bit ∈ constantOneIndices constant
  · have hbit := (mem_constantOneIndices constant bit).mp hmem
    simpa [constantBitWord, hmem, hbit] using h
  · have hbit : constant.val.testBit bit.val = false := by
      cases hb : constant.val.testBit bit.val with
      | false => rfl
      | true => exact False.elim (hmem ((mem_constantOneIndices constant bit).mpr hb))
    simpa [constantBitWord, hmem, hbit] using h

/-- Doubly controlled constant xor preserves readouts outside the target word. -/
theorem doubleControlledXorConstantStep_get_observed_of_target_ne
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire)
    (observed : EncodedBit encoding)
    (htargetObserved :
      ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (doubleControlledXorConstantStep controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget x) = observed.get x := by
  unfold doubleControlledXorConstantStep
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [doubleControlledXorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  change ∀ y, observed.get ((target.bit bit).flip y) = observed.get y
  exact fun y =>
    EncodedBit.get_flip_of_wire_ne (target.bit bit) observed
      (htargetObserved bit) y

theorem doubleControlledXorConstant_realizes
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (doubleControlledXorConstantProgram physical oracles controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget)
      (doubleControlledXorConstantStep controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget) :=
  GateSpec.realizesList physical oracles
    (doubleControlledXorConstantGates controlA controlB target constant
      hcontrols hcontrolATarget hcontrolBTarget)

/-- Direct realization proof for doubly controlled constant xor. -/
theorem doubleControlledXorConstantWitness
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (doubleControlledXorConstantProgram physical oracles controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget)
      (doubleControlledXorConstantStep controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget) :=
  doubleControlledXorConstant_realizes physical oracles controlA controlB target constant
    hcontrols hcontrolATarget hcontrolBTarget

/-! ### Doubly controlled unload -/

/-- Reverse Toffoli list for unloading a doubly controlled constant. -/
def doubleControlledXorConstantUnloadGates
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    List (GateSpec encoding) :=
  (doubleControlledXorConstantGates controlA controlB target constant
    hcontrols hcontrolATarget hcontrolBTarget).reverse

/-- Base-gate program for unloading a doubly controlled constant. -/
def doubleControlledXorConstantUnloadProgram
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (doubleControlledXorConstantUnloadGates controlA controlB target constant
      hcontrols hcontrolATarget hcontrolBTarget)

/-- Folded reverse-list semantics for doubly controlled unloading. -/
def doubleControlledXorConstantUnloadStep
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    Data → Data :=
  GateSpec.stepList
    (doubleControlledXorConstantUnloadGates controlA controlB target constant
      hcontrols hcontrolATarget hcontrolBTarget)

theorem doubleControlledXorConstantUnload_realizes
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (doubleControlledXorConstantUnloadProgram physical oracles controlA controlB target
        constant hcontrols hcontrolATarget hcontrolBTarget)
      (doubleControlledXorConstantUnloadStep controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget) :=
  GateSpec.realizesList physical oracles
    (doubleControlledXorConstantUnloadGates controlA controlB target constant
      hcontrols hcontrolATarget hcontrolBTarget)

/-- Direct realization proof for reverse-list doubly controlled unloading. -/
theorem doubleControlledXorConstantUnloadWitness
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire) :
    UnitaryCircuit.Realizes encoding
      (doubleControlledXorConstantUnloadProgram physical oracles controlA controlB target
        constant hcontrols hcontrolATarget hcontrolBTarget)
      (doubleControlledXorConstantUnloadStep controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget) :=
  doubleControlledXorConstantUnload_realizes physical oracles controlA controlB target constant
    hcontrols hcontrolATarget hcontrolBTarget

/-- Doubly controlled unload preserves readouts outside the target word. -/
theorem doubleControlledXorConstantUnloadStep_get_observed_of_target_ne
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire)
    (observed : EncodedBit encoding)
    (htargetObserved :
      ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (doubleControlledXorConstantUnloadStep controlA controlB target
          constant hcontrols hcontrolATarget hcontrolBTarget x) =
      observed.get x := by
  unfold doubleControlledXorConstantUnloadStep
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hforward :
      gate ∈ doubleControlledXorConstantGates controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget := by
    exact List.mem_reverse.mp (by
      simpa [doubleControlledXorConstantUnloadGates] using hgate)
  rw [doubleControlledXorConstantGates] at hforward
  rcases List.mem_map.mp hforward with ⟨bit, _hbit, rfl⟩
  change ∀ y, observed.get ((target.bit bit).flip y) = observed.get y
  exact fun y =>
    EncodedBit.get_flip_of_wire_ne (target.bit bit) observed
      (htargetObserved bit) y

/-- Reverse-list doubly controlled unload has the same target-bit formula. -/
theorem doubleControlledXorConstantUnloadStep_get_target
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire)
    (bit : Fin width)
    (htargetTarget :
      ∀ other, other ≠ bit →
        (target.bit other).wire ≠ (target.bit bit).wire)
    (x : Data) :
    (target.bit bit).get
        (doubleControlledXorConstantUnloadStep controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget x) =
      ((target.bit bit).get x ^^
        (controlA.get x && controlB.get x &&
          constant.val.testBit bit.val)) := by
  have hcontrolA :=
    doubleControlledXorConstantUnloadStep_get_observed_of_target_ne
      controlA controlB target constant hcontrols hcontrolATarget
      hcontrolBTarget controlA (fun other => Ne.symm (hcontrolATarget other)) x
  have hcontrolB :=
    doubleControlledXorConstantUnloadStep_get_observed_of_target_ne
      controlA controlB target constant hcontrols hcontrolATarget
      hcontrolBTarget controlB (fun other => Ne.symm (hcontrolBTarget other)) x
  have hforward := doubleControlledXorConstantStep_get_target controlA controlB
    target constant hcontrols hcontrolATarget hcontrolBTarget bit
    htargetTarget
    (doubleControlledXorConstantUnloadStep controlA controlB target constant
      hcontrols hcontrolATarget hcontrolBTarget x)
  have hinverse :
      doubleControlledXorConstantStep controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget
          (doubleControlledXorConstantUnloadStep controlA controlB target
            constant hcontrols hcontrolATarget hcontrolBTarget x) = x := by
    simpa [doubleControlledXorConstantUnloadStep,
      doubleControlledXorConstantUnloadGates,
      doubleControlledXorConstantStep] using
      GateSpec.stepList_reverse_stepList
        (doubleControlledXorConstantGates controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget).reverse x
  rw [hinverse, hcontrolA, hcontrolB] at hforward
  cases hbefore :
      (target.bit bit).get
        (doubleControlledXorConstantUnloadStep controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget x) <;>
    cases hcontrolAValue : controlA.get x <;>
    cases hcontrolBValue : controlB.get x <;>
    cases hconstant : constant.val.testBit bit.val <;>
    simp_all

/-- Doubly controlled unloading after loading restores the encoded value. -/
theorem doubleControlledXorConstantUnloadStep_after_doubleControlledXorConstantStep
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire)
    (x : Data) :
    doubleControlledXorConstantUnloadStep controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget
        (doubleControlledXorConstantStep controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget x) = x := by
  simpa [doubleControlledXorConstantUnloadStep,
    doubleControlledXorConstantUnloadGates,
    doubleControlledXorConstantStep] using
    GateSpec.stepList_reverse_stepList
      (doubleControlledXorConstantGates controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget) x

/-- Doubly controlled loading after unloading restores the encoded value. -/
theorem doubleControlledXorConstantStep_after_doubleControlledXorConstantUnloadStep
    (controlA controlB : EncodedBit encoding) (target : Word encoding width)
    (constant : Fin (2 ^ width)) (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit, controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit, controlB.wire ≠ (target.bit bit).wire)
    (x : Data) :
    doubleControlledXorConstantStep controlA controlB target constant hcontrols
        hcontrolATarget hcontrolBTarget
        (doubleControlledXorConstantUnloadStep controlA controlB target constant
          hcontrols hcontrolATarget hcontrolBTarget x) = x := by
  simpa [doubleControlledXorConstantUnloadStep,
    doubleControlledXorConstantUnloadGates,
    doubleControlledXorConstantStep] using
    GateSpec.stepList_reverse_stepList
      (doubleControlledXorConstantGates controlA controlB target constant
        hcontrols hcontrolATarget hcontrolBTarget).reverse x

end Word
end EncodedBit

end

end QuantumAlg

end
