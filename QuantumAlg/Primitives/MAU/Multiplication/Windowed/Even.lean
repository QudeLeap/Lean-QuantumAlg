/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Windowed

/-!
# Even-width exact windowed modular multiply-accumulate

This module scans an even-width multiplier two bits at a time.  Each pair
drives the one-add QROM lookup from `Windowed.FullLayout`, so every window
performs exactly one VBE modular addition and then uncomputes its lookup word.
The arithmetic recurrence groups the ordinary little-endian binary expansion
into radix-four digits [Gid19, main.tex:392-426].
-/

section

namespace QuantumAlg
namespace MAU.Multiplication.Windowed.Even

noncomputable section

/-- The even multiplier width represented by `half` two-bit windows. -/
def width (half : Nat) : Nat := 2 * half

/-- Low source bit of one little-endian two-bit window. -/
def lowBit (half : Nat) (window : Fin half) : Fin (width half) :=
  ⟨2 * window.val, by
    unfold width
    omega⟩

/-- High source bit of one little-endian two-bit window. -/
def highBit (half : Nat) (window : Fin half) : Fin (width half) :=
  ⟨2 * window.val + 1, by
    unfold width
    omega⟩

theorem lowBit_highBit_ne (half : Nat) (window : Fin half) :
    lowBit half window ≠ highBit half window := by
  intro h
  have hv := congrArg Fin.val h
  simp [lowBit, highBit] at hv

/-- Natural radix-four digit selected by window `index`. -/
def selectedWindowDigit (x index : Nat) : Nat :=
  addressValue (x.testBit (2 * index)) (x.testBit (2 * index + 1))

/-- Natural binary weight selected by one two-bit window. -/
def selectedWindowWeight (x index : Nat) : Nat :=
  selectedWindowDigit x index * 2 ^ (2 * index)

/-- Modular product contribution selected by one two-bit window. -/
def selectedWindowContribution (N coefficient x index : Nat) : Nat :=
  (selectedWindowDigit x index * coefficient * 2 ^ (2 * index)) % N

/-- Grouping two adjacent binary weights produces the corresponding radix-four
window weight. -/
theorem selectedWindowWeight_eq_twoBits (x index : Nat) :
    selectedWindowWeight x index =
      Nat.FixedWidth.ModularAccumulate.selectedBitWeight
          x (2 * index) +
        Nat.FixedWidth.ModularAccumulate.selectedBitWeight
          x (2 * index + 1) := by
  cases hlow : x.testBit (2 * index) <;>
    cases hhigh : x.testBit (2 * index + 1) <;>
    simp [selectedWindowWeight, selectedWindowDigit, addressValue,
      Nat.FixedWidth.ModularAccumulate.selectedBitWeight,
      hlow, hhigh, pow_succ]
  all_goals ring_nf

/-- One window contribution is the modular sum of its two ordinary binary
stage contributions. -/
theorem selectedWindowContribution_eq_twoBits
    (N coefficient x index : Nat) :
    selectedWindowContribution N coefficient x index =
      (Nat.FixedWidth.ModularAccumulate.selectedBitContribution
          N coefficient x (2 * index) +
        Nat.FixedWidth.ModularAccumulate.selectedBitContribution
          N coefficient x (2 * index + 1)) % N := by
  rw [Nat.FixedWidth.ModularAccumulate.selectedBitContribution,
    Nat.FixedWidth.ModularAccumulate.selectedBitContribution,
    ← Nat.add_mod]
  unfold selectedWindowContribution
  rw [← Nat.mul_add, ← selectedWindowWeight_eq_twoBits]
  unfold selectedWindowWeight selectedWindowDigit
  ring_nf

/-- Radix-four accumulation of the first `count` two-bit windows. -/
def accumulateWindows (N coefficient x initial : Nat) : Nat → Nat
  | 0 => initial % N
  | count + 1 =>
      (accumulateWindows N coefficient x initial count +
        selectedWindowContribution N coefficient x count) % N

@[simp] theorem accumulateWindows_zero
    (N coefficient x initial : Nat) :
    accumulateWindows N coefficient x initial 0 = initial % N :=
  rfl

@[simp] theorem accumulateWindows_succ
    (N coefficient x initial count : Nat) :
    accumulateWindows N coefficient x initial (count + 1) =
      (accumulateWindows N coefficient x initial count +
        selectedWindowContribution N coefficient x count) % N :=
  rfl

theorem accumulateWindows_lt {N coefficient x initial count : Nat}
    (hNpos : 0 < N) :
    accumulateWindows N coefficient x initial count < N := by
  cases count <;> exact Nat.mod_lt _ hNpos

/-- The radix-four recurrence is exactly the ordinary binary recurrence after
twice as many bit stages. -/
theorem accumulateWindows_eq_accumulateSelected
    (N coefficient x initial count : Nat) :
    accumulateWindows N coefficient x initial count =
      Nat.FixedWidth.ModularAccumulate.accumulateSelected
        N coefficient x initial (2 * count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [accumulateWindows_succ, ih,
        selectedWindowContribution_eq_twoBits]
      rw [show 2 * (count + 1) = (2 * count + 1) + 1 by omega]
      rw [Nat.FixedWidth.ModularAccumulate.accumulateSelected_succ]
      rw [show 2 * count + 1 = (2 * count) + 1 by omega]
      rw [Nat.FixedWidth.ModularAccumulate.accumulateSelected_succ]
      simp [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- Scanning every two-bit window reconstructs the complete even-width
multiplier. -/
theorem accumulateWindows_eq_add_mul_mod_of_lt_two_pow
    {N coefficient x initial half : Nat}
    (hx : x < 2 ^ width half) :
    accumulateWindows N coefficient x initial half =
      (initial + coefficient * x) % N := by
  rw [accumulateWindows_eq_accumulateSelected]
  exact
    Nat.FixedWidth.ModularAccumulate.accumulateSelected_eq_add_mul_mod_of_lt_two_pow
      (n := width half) hx

/-- The three classical residues addressed by one radix-four digit. -/
def rowConstant (half N : Nat)
    (coefficient : PlainAdder.Word (width half))
    (window : Fin half) (digit : Nat) : PlainAdder.Word (width half) :=
  tableConstant (width half) N coefficient (2 * window.val) digit

/-- Physical gate list for one two-bit window on the complete multiplier
layout. -/
def windowGates (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    List (EncodedBit.GateSpec (FullLayout.encoding (width half))) :=
  FullLayout.qromWindowGates (width half) N
    (rowConstant half N coefficient window 1)
    (rowConstant half N coefficient window 2)
    (rowConstant half N coefficient window 3)
    (lowBit half window) (highBit half window)
    (lowBit_highBit_ne half window)

/-- Program for one exact radix-four window. -/
def windowProgram (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    UnitaryCircuit (Qubits (FullLayout.encoding (width half)).width) :=
  FullLayout.qromWindowProgram (width half) N
    (rowConstant half N coefficient window 1)
    (rowConstant half N coefficient window 2)
    (rowConstant half N coefficient window 3)
    (lowBit half window) (highBit half window)
    (lowBit_highBit_ne half window)

/-- Basis action of one exact radix-four window. -/
def windowStep (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    FullLayout.Registers (width half) → FullLayout.Registers (width half) :=
  FullLayout.qromWindowStep (width half) N
    (rowConstant half N coefficient window 1)
    (rowConstant half N coefficient window 2)
    (rowConstant half N coefficient window 3)
    (lowBit half window) (highBit half window)
    (lowBit_highBit_ne half window)

theorem window_realizes (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    UnitaryCircuit.Realizes (FullLayout.encoding (width half))
      (windowProgram half N coefficient window)
      (windowStep half N coefficient window) :=
  FullLayout.qromWindow_realizes _ _ _ _ _ _ _ _

theorem selectedLookupConstant_rowConstant_val
    (half N : Nat) (coefficient x : PlainAdder.Word (width half))
    (window : Fin half) (hNpos : 0 < N) (hN : N < 2 ^ width half) :
    (FullLayout.selectedLookupConstant
      (x.val.testBit (lowBit half window).val)
      (x.val.testBit (highBit half window).val)
      (rowConstant half N coefficient window 1)
      (rowConstant half N coefficient window 2)
      (rowConstant half N coefficient window 3)).val =
        selectedWindowContribution N coefficient.val x.val window.val := by
  cases hlow : x.val.testBit (2 * window.val) <;>
    cases hhigh : x.val.testBit (2 * window.val + 1) <;>
    simp [FullLayout.selectedLookupConstant, rowConstant, lowBit, highBit,
      selectedWindowContribution, selectedWindowDigit, addressValue,
      hlow, hhigh, tableConstant_val, hNpos, hN]

/-- One physical radix-four window contributes exactly its selected modular
product residue and restores every work field. -/
theorem windowStep_cleanEndpoint (half N : Nat)
    (coefficient x : PlainAdder.Word (width half))
    (window : Fin half) (accumulator : Nat)
    (hNpos : 0 < N) (hN : N < 2 ^ width half)
    (haccumulator : accumulator < N) :
    windowStep half N coefficient window
        (MAU.Multiplication.Accumulate.VBECircuit.cleanState
          (width half) N x accumulator) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanState
        (width half) N x
        ((accumulator +
          selectedWindowContribution N coefficient.val x.val window.val) % N) := by
  have h := FullLayout.qromWindowStep_cleanEndpoint
    (width half) N
    (rowConstant half N coefficient window 1)
    (rowConstant half N coefficient window 2)
    (rowConstant half N coefficient window 3)
    x (lowBit half window) (highBit half window)
    (lowBit_highBit_ne half window) accumulator hNpos hN
    (tableConstant_lt (width half) N coefficient (2 * window.val) 1 hNpos hN)
    (tableConstant_lt (width half) N coefficient (2 * window.val) 2 hNpos hN)
    (tableConstant_lt (width half) N coefficient (2 * window.val) 3 hNpos hN)
    haccumulator
  rw [selectedLookupConstant_rowConstant_val
    half N coefficient x window hNpos hN] at h
  exact h

/-! ## Complete windowed multiply-accumulate fold -/

/-- Ordered one-add QROM programs, one for each two-bit window. -/
def windowPrograms (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    List (UnitaryCircuit (Qubits (FullLayout.encoding (width half)).width)) :=
  List.ofFn fun window : Fin half => windowProgram half N coefficient window

/-- Semantic steps aligned entry-for-entry with `windowPrograms`. -/
def windowSteps (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    List (FullLayout.Registers (width half) →
      FullLayout.Registers (width half)) :=
  List.ofFn fun window : Fin half => windowStep half N coefficient window

/-- Flat primitive list of the complete even-width windowed MAC. -/
def macGates (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    List (EncodedBit.GateSpec (FullLayout.encoding (width half))) :=
  (List.ofFn fun window : Fin half => window).flatMap
    (windowGates half N coefficient)

/-- Folded semantic action of all two-bit windows. -/
def macStep (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    FullLayout.Registers (width half) → FullLayout.Registers (width half) :=
  UnitaryCircuit.Realizes.stepList (windowSteps half N coefficient)

/-- The complete windowed MAC circuit is compiled from its one flat primitive
list. -/
def macProgram (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    UnitaryCircuit (Qubits (FullLayout.encoding (width half)).width) :=
  EncodedBit.GateSpec.programList (macGates half N coefficient)

private theorem stepList_flatMap_windowGates (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    ∀ windows : List (Fin half), ∀ state,
      EncodedBit.GateSpec.stepList
          (windows.flatMap (windowGates half N coefficient)) state =
        UnitaryCircuit.Realizes.stepList
          (windows.map (windowStep half N coefficient)) state
  | [], _ => rfl
  | window :: rest, state => by
      change
        EncodedBit.GateSpec.stepList
            (windowGates half N coefficient window ++
              rest.flatMap (windowGates half N coefficient)) state =
          UnitaryCircuit.Realizes.stepList
            (rest.map (windowStep half N coefficient))
            (windowStep half N coefficient window state)
      rw [EncodedBit.GateSpec.stepList_append]
      change
        EncodedBit.GateSpec.stepList
            (rest.flatMap (windowGates half N coefficient))
            (windowStep half N coefficient window state) = _
      exact stepList_flatMap_windowGates half N coefficient rest
        (windowStep half N coefficient window state)

theorem macStep_eq_gateList (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (state) :
    EncodedBit.GateSpec.stepList (macGates half N coefficient) state =
      macStep half N coefficient state := by
  simpa [macGates, macStep, windowSteps, List.map_ofFn,
    Function.comp_def] using
    stepList_flatMap_windowGates half N coefficient
      (List.ofFn fun window : Fin half => window) state

theorem mac_realizes (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    UnitaryCircuit.Realizes (FullLayout.encoding (width half))
      (macProgram half N coefficient) (macStep half N coefficient) := by
  apply UnitaryCircuit.Realizes.congrStep (EncodedBit.GateSpec.realizesList _)
  exact macStep_eq_gateList half N coefficient

/-- Prefix of the actual two-bit-window semantic schedule. -/
def macPrefixStep (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (count : Nat) :
    FullLayout.Registers (width half) → FullLayout.Registers (width half) :=
  UnitaryCircuit.Realizes.stepList ((windowSteps half N coefficient).take count)

@[simp] theorem macPrefixStep_zero (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (state) :
    macPrefixStep half N coefficient 0 state = state :=
  rfl

@[simp] theorem windowSteps_length (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    (windowSteps half N coefficient).length = half := by
  simp [windowSteps]

theorem windowSteps_get (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    (windowSteps half N coefficient).get
        ⟨window.val, by simp⟩ =
      windowStep half N coefficient window := by
  simp [windowSteps]

theorem macPrefixStep_succ (half N : Nat)
    (coefficient : PlainAdder.Word (width half))
    (window : Fin half) (state) :
    macPrefixStep half N coefficient (window.val + 1) state =
      windowStep half N coefficient window
        (macPrefixStep half N coefficient window.val state) := by
  unfold macPrefixStep
  let schedule := windowSteps half N coefficient
  have hlen : window.val < schedule.length := by
    simp [schedule]
  rw [UnitaryCircuit.Realizes.stepList_take_succ schedule window.val hlen]
  have hget : schedule.get ⟨window.val, hlen⟩ =
      windowStep half N coefficient window := by
    simpa [schedule] using windowSteps_get half N coefficient window
  rw [hget]

theorem macPrefixStep_full (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    macPrefixStep half N coefficient half = macStep half N coefficient := by
  funext state
  unfold macPrefixStep macStep
  rw [List.take_of_length_le]
  simp

/-- Prefix invariant for the actual window schedule. -/
theorem macPrefixStep_cleanEndpoint (half N : Nat)
    (coefficient x : PlainAdder.Word (width half))
    (initial : Nat) (hNpos : 0 < N) (hN : N < 2 ^ width half)
    (hinitial : initial < N) :
    ∀ count, ∀ _hcount : count ≤ half,
      macPrefixStep half N coefficient count
          (MAU.Multiplication.Accumulate.VBECircuit.cleanState
            (width half) N x initial) =
        MAU.Multiplication.Accumulate.VBECircuit.cleanState
          (width half) N x
          (accumulateWindows N coefficient.val x.val initial count) := by
  intro count
  induction count with
  | zero =>
      intro _hcount
      rw [accumulateWindows_zero, Nat.mod_eq_of_lt hinitial]
      rfl
  | succ count ih =>
      intro hcountSucc
      have hcountLt : count < half := Nat.lt_of_succ_le hcountSucc
      let window : Fin half := ⟨count, hcountLt⟩
      have ihCount := ih (Nat.le_of_lt hcountLt)
      rw [show count + 1 = window.val + 1 by rfl,
        macPrefixStep_succ half N coefficient window, ihCount]
      simpa [window, accumulateWindows_succ] using
        windowStep_cleanEndpoint half N coefficient x window
          (accumulateWindows N coefficient.val x.val initial count)
          hNpos hN (accumulateWindows_lt hNpos)

/-- Complete even-width clean endpoint: one flat physical gate list adds the
fixed product to the accumulator modulo `N`. -/
theorem macStep_cleanEndpoint (half N : Nat)
    (coefficient x : PlainAdder.Word (width half))
    (initial : Nat) (hNpos : 0 < N) (hN : N < 2 ^ width half)
    (hinitial : initial < N) :
    macStep half N coefficient
        (MAU.Multiplication.Accumulate.VBECircuit.cleanState
          (width half) N x initial) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanState
        (width half) N x ((initial + coefficient.val * x.val) % N) := by
  rw [← macPrefixStep_full]
  rw [macPrefixStep_cleanEndpoint half N coefficient x initial
    hNpos hN hinitial half (Nat.le_refl half)]
  rw [accumulateWindows_eq_add_mul_mod_of_lt_two_pow (ZMod.val_lt x)]

/-- High-level clean-state bridge for the actual windowed MAC circuit. -/
theorem macStep_cleanEmbedding (half N : Nat) (a : ZMod N)
    (x : MAU.Multiplication.Accumulate.Data N)
    (hNpos : 0 < N) (hN : N < 2 ^ width half)
    (hx : x.FlagClean) :
    macStep half N (a.val : PlainAdder.Word (width half))
        (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
          (width half) N x) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
        (width half) N (x.addScaled a) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  let aWord : PlainAdder.Word (width half) :=
    (a.val : PlainAdder.Word (width half))
  let xWord : PlainAdder.Word (width half) :=
    (x.multiplicand.val : PlainAdder.Word (width half))
  have haWordVal : aWord.val = a.val :=
    ZMod.val_natCast_of_lt (lt_trans (ZMod.val_lt a) hN)
  have hxWordVal : xWord.val = x.multiplicand.val :=
    ZMod.val_natCast_of_lt (lt_trans (ZMod.val_lt x.multiplicand) hN)
  have haccumulator :
      (x.addScaled a).accumulator.val =
        (x.accumulator.val + a.val * x.multiplicand.val) % N := by
    rw [MAU.Multiplication.Accumulate.Data.addScaled_accumulator,
      ZMod.val_add, ZMod.val_mul, Nat.add_mod_mod]
  have hxFlag : x.flag = false := hx
  have hinput :
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
          (width half) N x =
        MAU.Multiplication.Accumulate.VBECircuit.cleanState
          (width half) N xWord x.accumulator.val := by
    simp only [MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState, xWord]
    rw [hxFlag]
  have houtput :
      MAU.Multiplication.Accumulate.VBECircuit.cleanState
          (width half) N xWord
          ((x.accumulator.val + aWord.val * xWord.val) % N) =
        MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
          (width half) N (x.addScaled a) := by
    simp only [MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.Data.addScaled_multiplicand,
      MAU.Multiplication.Accumulate.Data.addScaled_flag]
    rw [hxFlag, haccumulator, haWordVal, hxWordVal]
  rw [hinput]
  rw [macStep_cleanEndpoint half N aWord xWord x.accumulator.val
    hNpos hN (ZMod.val_lt x.accumulator)]
  exact houtput

/-! ### Exact inverse windowed MAC -/

/-- The inverse windowed MAC is literally the reverse physical gate list. -/
def macInverseGates (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    List (EncodedBit.GateSpec (FullLayout.encoding (width half))) :=
  (macGates half N coefficient).reverse

/-- Folded action of the reverse physical gate list. -/
def macInverseStep (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    FullLayout.Registers (width half) → FullLayout.Registers (width half) :=
  EncodedBit.GateSpec.stepList (macInverseGates half N coefficient)

/-- Circuit compiled from the same reverse physical gate list. -/
def macInverseProgram (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    UnitaryCircuit (Qubits (FullLayout.encoding (width half)).width) :=
  EncodedBit.GateSpec.programList (macInverseGates half N coefficient)

theorem macInverse_realizes (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    UnitaryCircuit.Realizes (FullLayout.encoding (width half))
      (macInverseProgram half N coefficient)
      (macInverseStep half N coefficient) :=
  EncodedBit.GateSpec.realizesList _

/-- Reversing the actual flattened gate list restores every physical state. -/
theorem macInverseStep_after_macStep (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (state) :
    macInverseStep half N coefficient
        (macStep half N coefficient state) = state := by
  rw [← macStep_eq_gateList]
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (macGates half N coefficient) state

/-- On a clean forward endpoint, the reverse gate list restores the complete
physical input state. -/
theorem macInverseStep_cleanEmbedding (half N : Nat) (a : ZMod N)
    (x : MAU.Multiplication.Accumulate.Data N)
    (hNpos : 0 < N) (hN : N < 2 ^ width half)
    (hx : x.FlagClean) :
    macInverseStep half N (a.val : PlainAdder.Word (width half))
        (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
          (width half) N (x.addScaled a)) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
        (width half) N x := by
  rw [← macStep_cleanEmbedding half N a x hNpos hN hx]
  exact macInverseStep_after_macStep half N _ _

/-! ### Width-only primitive bounds -/

/-- Every indexed one-add window obeys the same linear primitive bound. -/
theorem windowGates_length_le (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    (windowGates half N coefficient window).length ≤
      54 * width half + 51 := by
  exact FullLayout.qromWindowGates_length_le _ _ _ _ _ _ _ _

private theorem flatMap_windowGates_length_le (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    ∀ windows : List (Fin half),
      (windows.flatMap (windowGates half N coefficient)).length ≤
        windows.length * (54 * width half + 51)
  | [] => by simp
  | window :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hwindow := windowGates_length_le half N coefficient window
      have hrest := flatMap_windowGates_length_le half N coefficient rest
      calc
        (windowGates half N coefficient window).length +
              (List.flatMap (windowGates half N coefficient) rest).length ≤
            (54 * width half + 51) +
              rest.length * (54 * width half + 51) :=
          Nat.add_le_add hwindow hrest
        _ = (rest.length + 1) * (54 * width half + 51) := by ring

/-- The complete even-width windowed MAC has a quadratic primitive bound. -/
theorem macGates_length_le (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    (macGates half N coefficient).length ≤ 108 * half ^ 2 + 51 * half := by
  have h := flatMap_windowGates_length_le half N coefficient
    (List.ofFn fun window : Fin half => window)
  simp only [macGates, List.length_ofFn] at h ⊢
  calc
    (List.flatMap (windowGates half N coefficient)
        (List.ofFn fun window : Fin half => window)).length ≤
        half * (54 * width half + 51) := h
    _ = 108 * half ^ 2 + 51 * half := by
      unfold width
      ring

/-- Closed source-slot bound for one complete in-place windowed multiplier. -/
def multiplierPrimitiveBound (half : Nat) : Nat :=
  216 * half ^ 2 + 108 * half

/-! ### Native Toffoli accounting of the full MAC fold -/

/-- Exact Toffoli coordinate of one indexed window. -/
def windowToffoliCount (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) : Nat :=
  FullLayout.qromWindowToffoliCount (width half)
    (rowConstant half N coefficient window 1)
    (rowConstant half N coefficient window 2)
    (rowConstant half N coefficient window 3)

theorem windowGates_toffoliMultiplicity_sum (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    ((windowGates half N coefficient window).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      windowToffoliCount half N coefficient window := by
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact FullLayout.qromWindowProgram_toffoli_count_eq _ _ _ _ _ _ _ _

theorem windowToffoliCount_le (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) (window : Fin half) :
    windowToffoliCount half N coefficient window ≤
      32 * width half + 2 :=
  FullLayout.qromWindowToffoliCount_le _ _ _ _

/-- Exact sum of the indexed one-window coordinates. -/
def macToffoliCount (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) : Nat :=
  ((List.ofFn fun window : Fin half => window).map
    (windowToffoliCount half N coefficient)).sum

private theorem flatMap_windowGates_toffoliMultiplicity_sum
    (half N : Nat) (coefficient : PlainAdder.Word (width half)) :
    ∀ windows : List (Fin half),
      (((windows.flatMap (windowGates half N coefficient)).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum) =
        (windows.map (windowToffoliCount half N coefficient)).sum
  | [] => rfl
  | window :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [windowGates_toffoliMultiplicity_sum,
        flatMap_windowGates_toffoliMultiplicity_sum half N coefficient rest]

theorem macProgram_toffoli_count_eq (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (macProgram half N coefficient).eventCost =
      macToffoliCount half N coefficient := by
  rw [macProgram, EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact flatMap_windowGates_toffoliMultiplicity_sum half N coefficient
    (List.ofFn fun window : Fin half => window)

private theorem sum_windowToffoliCount_le (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    ∀ windows : List (Fin half),
      (windows.map (windowToffoliCount half N coefficient)).sum ≤
        windows.length * (32 * width half + 2)
  | [] => by simp
  | window :: rest => by
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hwindow := windowToffoliCount_le half N coefficient window
      have hrest := sum_windowToffoliCount_le half N coefficient rest
      calc
        windowToffoliCount half N coefficient window +
              (rest.map (windowToffoliCount half N coefficient)).sum ≤
            (32 * width half + 2) +
              rest.length * (32 * width half + 2) :=
          Nat.add_le_add hwindow hrest
        _ = rest.length.succ * (32 * width half + 2) := by
          rw [Nat.succ_mul rest.length (32 * width half + 2)]
          exact Nat.add_comm _ _

/-- Closed quadratic Toffoli upper bound for the complete even-width MAC. -/
theorem macToffoliCount_le (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    macToffoliCount half N coefficient ≤ 64 * half ^ 2 + 2 * half := by
  have h := sum_windowToffoliCount_le half N coefficient
    (List.ofFn fun window : Fin half => window)
  simp only [macToffoliCount, List.length_ofFn] at h ⊢
  unfold width at h
  nlinarith

/-- The same closed bound projected from the actual MAC circuit. -/
theorem macProgram_toffoli_count_le (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (macProgram half N coefficient).eventCost ≤
      64 * half ^ 2 + 2 * half := by
  rw [macProgram_toffoli_count_eq]
  exact macToffoliCount_le half N coefficient

/-! ## Complete in-place multiplication by a unit -/

/-- Fixed-width representation of the residue underlying a unit. -/
def unitWord (half : Nat) {N : Nat} (u : (ZMod N)ˣ) :
    PlainAdder.Word (width half) :=
  ((u : ZMod N).val : PlainAdder.Word (width half))

/-- Forward windowed MAC, physical word swap, and reverse windowed MAC for the
inverse unit, all on the same established full layout. -/
def multiplicationGates (half N : Nat) (u : (ZMod N)ˣ) :
    List (EncodedBit.GateSpec (FullLayout.encoding (width half))) :=
  macGates half N (unitWord half u) ++
    EncodedBit.Word.swapGates
      (MAU.Multiplication.VBECircuit.multiplicandWord (width half))
      (MAU.Multiplication.VBECircuit.accumulatorWord (width half))
      (MAU.Multiplication.VBECircuit.multiplicand_accumulator_diagonal_ne
        (width half)) ++
    macInverseGates half N (unitWord half (u⁻¹))

/-- Complete exact windowed multiplication circuit. -/
def multiplicationProgram (half N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit (Qubits (FullLayout.encoding (width half)).width) :=
  EncodedBit.GateSpec.programList (multiplicationGates half N u)

/-- Folded action of the complete physical gate list. -/
def multiplicationStep (half N : Nat) (u : (ZMod N)ˣ) :
    FullLayout.Registers (width half) → FullLayout.Registers (width half) :=
  EncodedBit.GateSpec.stepList (multiplicationGates half N u)

theorem multiplication_realizes (half N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (FullLayout.encoding (width half))
      (multiplicationProgram half N u) (multiplicationStep half N u) :=
  EncodedBit.GateSpec.realizesList _

/-- Every primitive addressed by the complete program lies in its declared
physical encoding. -/
theorem multiplicationProgram_physical_idx_subset_range
    (half N : Nat) (u : (ZMod N)ˣ) :
    (multiplicationProgram half N u).physical_idx ⊆
      List.range (FullLayout.encoding (width half)).width :=
  EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- Clean physical endpoint of the single composed windowed circuit. -/
theorem multiplicationStep_cleanEndpoint (half N : Nat)
    (u : (ZMod N)ˣ) (x : ZMod N)
    (hNpos : 0 < N) (hN : N < 2 ^ width half) :
    multiplicationStep half N u
        (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
          (width half) N (MAU.Multiplication.cleanInput x)) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
        (width half) N (MAU.Multiplication.cleanOutput u x) := by
  simp only [multiplicationStep, multiplicationGates,
    EncodedBit.GateSpec.stepList_append]
  rw [macStep_eq_gateList]
  change
    macInverseStep half N (unitWord half (u⁻¹))
        (MAU.Multiplication.VBECircuit.swapStep (width half)
          (macStep half N (unitWord half u)
            (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
              (width half) N (MAU.Multiplication.cleanInput x)))) = _
  simp only [unitWord]
  rw [macStep_cleanEmbedding half N (u : ZMod N)
    (MAU.Multiplication.cleanInput x) hNpos hN (by rfl)]
  rw [MAU.Multiplication.VBECircuit.swapStep_cleanEmbedding
    (width half) N
    ((MAU.Multiplication.cleanInput x).addScaled (u : ZMod N)) hNpos hN]
  rw [MAU.Multiplication.swapMacRegisters_addScaled_cleanInput]
  exact macInverseStep_cleanEmbedding half N
    (((u⁻¹ : (ZMod N)ˣ) : ZMod N))
    (MAU.Multiplication.cleanOutput u x) hNpos hN (by rfl)

/-- Encoded-basis correctness of the actual complete circuit. -/
theorem multiplicationProgram_applyNormalized_cleanEndpoint (half N : Nat)
    (u : (ZMod N)ˣ) (x : ZMod N)
    (hNpos : 0 < N) (hN : N < 2 ^ width half) :
    (multiplicationProgram half N u).applyNormalized
        (NormalizedVector.ket
          ((FullLayout.encoding (width half)).encode
            (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
              (width half) N (MAU.Multiplication.cleanInput x)))) =
      NormalizedVector.ket
        ((FullLayout.encoding (width half)).encode
          (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
            (width half) N (MAU.Multiplication.cleanOutput u x))) := by
  simpa only [multiplicationStep_cleanEndpoint half N u x hNpos hN] using
    (multiplication_realizes half N u).apply_encoded_ket
      (MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding
        (width half) N (MAU.Multiplication.cleanInput x))

/-- The forward MAC, word swap, and inverse MAC fit the closed source-slot
bound used by the native-control exponentiation envelope. -/
theorem multiplicationGates_length_le_multiplierPrimitiveBound
    (half N : Nat) (u : (ZMod N)ˣ) :
    (multiplicationGates half N u).length ≤ multiplierPrimitiveBound half := by
  have hforward := macGates_length_le half N (unitWord half u)
  have hinverse := macGates_length_le half N (unitWord half (u⁻¹))
  have hswap :
      (EncodedBit.Word.swapGates
        (MAU.Multiplication.VBECircuit.multiplicandWord (width half))
        (MAU.Multiplication.VBECircuit.accumulatorWord (width half))
        (MAU.Multiplication.VBECircuit.multiplicand_accumulator_diagonal_ne
          (width half))).length = 3 * width half := by
    exact EncodedBit.Word.swapGates_length _ _ _
  simp only [multiplicationGates, macInverseGates, List.length_append,
    List.length_reverse]
  rw [hswap]
  calc
    (macGates half N (unitWord half u)).length + 3 * width half +
          (macGates half N (unitWord half u⁻¹)).length ≤
        (108 * half ^ 2 + 51 * half) + 3 * width half +
          (108 * half ^ 2 + 51 * half) :=
      Nat.add_le_add (Nat.add_le_add hforward le_rfl) hinverse
    _ = multiplierPrimitiveBound half := by
      unfold multiplierPrimitiveBound width
      ring

/-! ### Native Toffoli accounting of complete multiplication -/

theorem macGates_toffoliMultiplicity_sum (half N : Nat)
    (coefficient : PlainAdder.Word (width half)) :
    ((macGates half N coefficient).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      macToffoliCount half N coefficient := by
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact macProgram_toffoli_count_eq half N coefficient

/-- Exact coefficient-sensitive Toffoli coordinate of the complete circuit. -/
def multiplicationToffoliCount (half N : Nat) (u : (ZMod N)ˣ) : Nat :=
  macToffoliCount half N (unitWord half u) +
    macToffoliCount half N (unitWord half (u⁻¹))

theorem multiplicationGates_toffoliMultiplicity_sum
    (half N : Nat) (u : (ZMod N)ˣ) :
    ((multiplicationGates half N u).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      multiplicationToffoliCount half N u := by
  simp only [multiplicationGates, List.map_append, List.sum_append,
    macInverseGates, List.map_reverse, List.sum_reverse,
    macGates_toffoliMultiplicity_sum,
    EncodedBit.Word.swapGates_toffoliMultiplicity_sum, Nat.add_zero]
  rfl

/-- Exact Toffoli projection of the same complete circuit used by the endpoint
proof. -/
theorem multiplicationProgram_toffoli_count_eq
    (half N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (multiplicationProgram half N u).eventCost =
      multiplicationToffoliCount half N u := by
  rw [multiplicationProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact multiplicationGates_toffoliMultiplicity_sum half N u

/-- Closed quadratic Toffoli upper bound of the complete in-place circuit. -/
theorem multiplicationToffoliCount_le (half N : Nat) (u : (ZMod N)ˣ) :
    multiplicationToffoliCount half N u ≤
      128 * half ^ 2 + 4 * half := by
  have hforward := macToffoliCount_le half N (unitWord half u)
  have hinverse := macToffoliCount_le half N (unitWord half (u⁻¹))
  unfold multiplicationToffoliCount
  omega

theorem multiplicationProgram_toffoli_count_le
    (half N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (multiplicationProgram half N u).eventCost ≤
      128 * half ^ 2 + 4 * half := by
  rw [multiplicationProgram_toffoli_count_eq]
  exact multiplicationToffoliCount_le half N u

/-- The even-width windowed construction keeps exactly the established VBE
logical layout width. -/
theorem encoding_width (half : Nat) :
    (FullLayout.encoding (width half)).width = 5 * width half + 4 :=
  MAU.Multiplication.Accumulate.VBECircuit.encoding_width (width half)

/-- For every positive even width, the proved windowed bound is strictly below
the exact Toffoli count of the former VBE multiplication circuit. -/
theorem multiplicationProgram_toffoli_count_lt_vbe
    (half N : Nat) (u : (ZMod N)ˣ) (hhalf : 0 < half) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (multiplicationProgram half N u).eventCost <
      ResourcePool.count (.gate (.builtin "toffoli"))
        (MAU.Multiplication.VBECircuit.multiplicationProgram
          (width half) N u).eventCost := by
  rw [MAU.Multiplication.VBECircuit.multiplicationProgram_toffoli_count_eq]
  calc
    ResourcePool.count (.gate (.builtin "toffoli"))
        (multiplicationProgram half N u).eventCost ≤
        128 * half ^ 2 + 4 * half :=
      multiplicationProgram_toffoli_count_le half N u
    _ < 60 * width half ^ 2 := by
      unfold width
      nlinarith

end

end MAU.Multiplication.Windowed.Even
end QuantumAlg

end
