/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Step
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding

/-!
# HRS carry with the first dirty bit eliminated

For input width `w >= 2`, this internal carry interface contains `w` input
bits, `w - 2` borrowed bits, and one xor-output bit: exactly `2w - 1` wires.
The right register stores the borrowed bits below the output bit. Widths
zero and one retain only that output bit beside the input.

The optimized first stage omits `g_0`. The last stage uses the output wire
directly, and reversing only the lower prefix restores every other joint
input component [HRS16, paper.tex:187-205,232-245]. These internal borrowed
bits are not additional external ancillas of the final recursive adder.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.GateSpec
open BinaryLabelEncoding

/-- Input word and the combined borrowed/output word, with no unused padding. -/
abbrev CarryRegisters (width : Nat) := Fin (2 ^ width) × Fin (2 ^ (width - 2 + 1))

/-- The highest right-word bit is the output; every lower bit is borrowed. -/
def carryEncoding (width : Nat) : BinaryLabelEncoding (CarryRegisters width) :=
  prod (finIdentity width) (finIdentity (width - 2 + 1))

/-- An input bit, indexed from the least significant bit. -/
def carryInputBit (width : Nat) (bit : Fin width) : EncodedBit (carryEncoding width) :=
  prodLeftBit (finIdentity width) (finIdentity (width - 2 + 1))
    (finIdentityBit width (WireAddress.littleEndianWire bit))

/-- A right-word bit, including the final output bit. -/
def carryWorkBit (width : Nat) (bit : Fin (width - 2 + 1)) :
    EncodedBit (carryEncoding width) :=
  prodRightBit (finIdentity width) (finIdentity (width - 2 + 1))
    (finIdentityBit (width - 2 + 1) (WireAddress.littleEndianWire bit))

/-- The explicit xor-output always exists, including at width zero. -/
def carryOutputBit (width : Nat) : EncodedBit (carryEncoding width) :=
  carryWorkBit width ⟨width - 2, by omega⟩

lemma hrsCarryInputBit_get (width : Nat) (bit : Fin width) (state : CarryRegisters width) :
    (carryInputBit width bit).get state = state.1.val.testBit bit.val := by
  change state.1.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

lemma hrsCarryWorkBit_get (width : Nat) (bit : Fin (width - 2 + 1))
    (state : CarryRegisters width) :
    (carryWorkBit width bit).get state = state.2.val.testBit bit.val := by
  change state.2.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private lemma input_ne_input (width : Nat) (i j : Fin width) (hne : i ≠ j) :
    (carryInputBit width i).wire ≠ (carryInputBit width j).wire := by
  intro h
  have hval := congrArg Fin.val h
  change width - 1 - i.val = width - 1 - j.val at hval
  apply hne
  apply Fin.ext
  omega

private lemma work_ne_work (width : Nat) (i j : Fin (width - 2 + 1)) (hne : i ≠ j) :
    (carryWorkBit width i).wire ≠ (carryWorkBit width j).wire := by
  intro h
  have hval := congrArg Fin.val h
  change width + (width - 2 + 1 - 1 - i.val) =
    width + (width - 2 + 1 - 1 - j.val) at hval
  apply hne
  apply Fin.ext
  omega

private lemma input_ne_work (width : Nat) (i : Fin width) (j : Fin (width - 2 + 1)) :
    (carryInputBit width i).wire ≠ (carryWorkBit width j).wire := by
  intro h
  have hval := congrArg Fin.val h
  change width - 1 - i.val = width + (width - 2 + 1 - 1 - j.val) at hval
  omega

/-- Input position used by prefix stage `index`, after eliminating `g_0`. -/
def carryPrefixInput (width index : Nat) (h : index + 2 ≤ width) :
    EncodedBit (carryEncoding width) :=
  carryInputBit width ⟨index + 1, by omega⟩

/-- Stage `index` writes the carry after input bit `index + 1`. -/
def carryPrefixWork (width index : Nat) (h : index + 2 ≤ width) :
    EncodedBit (carryEncoding width) :=
  carryWorkBit width ⟨index, by omega⟩

/-- Literal optimized carry prefix. Lower borrowed bits may remain toggled
until the final cleanup; all input bits are restored at each stage. -/
def carryPrefix (width : Nat) (constant : Fin (2 ^ width)) :
    (index : Nat) → index + 2 ≤ width → List (EncodedBit.GateSpec (carryEncoding width))
  | 0, h =>
      baseCarryGates (carryInputBit width ⟨0, by omega⟩)
        (carryPrefixInput width 0 h) (carryPrefixWork width 0 h)
        (input_ne_input width _ _ (by intro heq; have := congrArg Fin.val heq; simp at this))
        (input_ne_work width _ _) (input_ne_work width _ _)
        (constant.val.testBit 0) (constant.val.testBit 1)
  | index + 1, h =>
      propagateCarryGates (carryPrefixInput width (index + 1) h)
        (carryPrefixWork width index (by omega)) (carryPrefixWork width (index + 1) h)
        (input_ne_work width _ _) (input_ne_work width _ _)
        (work_ne_work width _ _ (by
          intro heq
          have hval := congrArg Fin.val heq
          change index = index + 1 at hval
          omega))
        (constant.val.testBit (index + 2)) (carryPrefix width constant index (by omega))

/-- The lower prefix to reverse after retaining the selected output toggle. -/
def carryLowerPrefix (width : Nat) (constant : Fin (2 ^ width)) :
    (index : Nat) → index + 2 ≤ width → List (EncodedBit.GateSpec (carryEncoding width))
  | 0, _ => []
  | index + 1, _ => carryPrefix width constant index (by omega)

private lemma prefix_disjoint (width : Nat) (constant : Fin (2 ^ width))
    (index : Nat) (h : index + 2 ≤ width) (observed : EncodedBit (carryEncoding width))
    (hinput : ∀ bit : Fin width, bit.val ≤ index + 1 →
      (carryInputBit width bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin (width - 2 + 1), bit.val ≤ index →
      (carryWorkBit width bit).wire ≠ observed.wire) :
    ∀ gate, gate ∈ carryPrefix width constant index h → bitDisjoint observed gate := by
  induction index with
  | zero =>
      have hlow := hinput ⟨0, by omega⟩ (by simp)
      have hhigh := hinput ⟨1, by omega⟩ (by simp)
      have hout := hwork 0 (by simp)
      intro gate hgate
      have hall : (carryPrefix width constant 0 h).Forall (bitDisjoint observed) := by
        cases hc0 : constant.val.testBit 0 <;> cases hc1 : constant.val.testBit 1 <;>
          simp [carryPrefix, baseCarryGates, carryPrefixInput, carryPrefixWork,
            bitDisjoint, hc0, hc1, hlow, hhigh, hout]
      exact List.forall_iff_forall_mem.mp hall gate hgate
  | succ index ih =>
      have hin := hinput ⟨index + 2, by omega⟩
        (by change index + 2 ≤ index + 1 + 1; omega)
      have hprevious := hwork ⟨index, by omega⟩
        (by change index ≤ index + 1; omega)
      have hout := hwork ⟨index + 1, by omega⟩
        (by change index + 1 ≤ index + 1; omega)
      have hlower := ih (by omega)
        (fun bit hbit => hinput bit (by omega)) (fun bit hbit => hwork bit (by omega))
      have hlowerAll := List.forall_iff_forall_mem.mpr hlower
      intro gate hgate
      have hall : (carryPrefix width constant (index + 1) h).Forall
          (bitDisjoint observed) := by
        cases hc : constant.val.testBit (index + 2) <;>
          simp [carryPrefix, propagateCarryGates, carryPrefixInput, carryPrefixWork,
            bitDisjoint, hc, hin, hprevious, hout, hlowerAll]
      exact List.forall_iff_forall_mem.mp hall gate hgate

private lemma prefix_disjoint_higher_input (width : Nat) (constant : Fin (2 ^ width))
    (index : Nat) (h : index + 2 ≤ width) (bit : Fin width) (hlt : index + 1 < bit.val) :
    ∀ gate, gate ∈ carryPrefix width constant index h →
      bitDisjoint (carryInputBit width bit) gate := by
  apply prefix_disjoint
  · intro other hother
    apply input_ne_input
    intro heq
    have := congrArg Fin.val heq
    omega
  · intro other _
    exact (input_ne_work width bit other).symm

private lemma prefix_disjoint_higher_work (width : Nat) (constant : Fin (2 ^ width))
    (index : Nat) (h : index + 2 ≤ width) (bit : Fin (width - 2 + 1))
    (hlt : index < bit.val) :
    ∀ gate, gate ∈ carryPrefix width constant index h →
      bitDisjoint (carryWorkBit width bit) gate := by
  apply prefix_disjoint
  · intro other _
    exact input_ne_work width other bit
  · intro other hother
    apply work_ne_work
    intro heq
    have := congrArg Fin.val heq
    omega

private lemma lower_disjoint_output (width : Nat) (constant : Fin (2 ^ width))
    (index : Nat) (h : index + 2 ≤ width) :
    ∀ gate, gate ∈ carryLowerPrefix width constant index h →
      bitDisjoint (carryPrefixWork width index h) gate := by
  cases index with
  | zero => simp [carryLowerPrefix]
  | succ index =>
      exact prefix_disjoint_higher_work width constant index (by omega)
        ⟨index + 1, by omega⟩ (by change index < index + 1; omega)

private lemma carry_false (a b : Bool) : Bool.carry a b false = (a && b) := by
  cases a <;> cases b <;> rfl

/-- Each optimized prefix adds one carry-controlled output flip to its lower
prefix. Its selected readout records the carry as a toggle, never as a clean bit. -/
lemma hrsCarryPrefix_action (width : Nat) (constant : Fin (2 ^ width))
    (index : Nat) (h : index + 2 ≤ width) (state : CarryRegisters width) :
    (stepList (carryPrefix width constant index h) state =
      if Nat.BinaryArithmetic.natAddCarry state.1.val constant.val (index + 2) then
        (carryPrefixWork width index h).flip
          (stepList (carryLowerPrefix width constant index h) state)
      else stepList (carryLowerPrefix width constant index h) state) ∧
    ((carryPrefixWork width index h).get
        (stepList (carryPrefix width constant index h) state) =
      ((carryPrefixWork width index h).get state ^^
        Nat.BinaryArithmetic.natAddCarry state.1.val constant.val (index + 2))) := by
  induction index with
  | zero =>
      have hstep : stepList (carryPrefix width constant 0 h) state =
          if Nat.BinaryArithmetic.natAddCarry state.1.val constant.val 2 then
            (carryPrefixWork width 0 h).flip state else state := by
        dsimp only [carryPrefix, carryPrefixInput, carryPrefixWork]
        rw [hrsBaseCarry_step]
        simp only [hrsCarryInputBit_get,
          Nat.BinaryArithmetic.natAddCarry, carry_false]
      constructor
      · simpa only [carryLowerPrefix, stepList, id_eq] using hstep
      · rw [hstep]
        cases hc : Nat.BinaryArithmetic.natAddCarry state.1.val constant.val 2 <;>
          simp [EncodedBit.get_flip_self]
  | succ index ih =>
      have hinput := prefix_disjoint_higher_input width constant index (by omega)
        ⟨index + 2, by omega⟩ (by change index + 1 < index + 2; omega)
      have houtput := prefix_disjoint_higher_work width constant index (by omega)
        ⟨index + 1, by omega⟩ (by change index < index + 1; omega)
      have hprevious := (ih (by omega)).2
      dsimp only [carryPrefixWork] at hprevious
      have hstep : stepList (carryPrefix width constant (index + 1) h) state =
          if Nat.BinaryArithmetic.natAddCarry state.1.val constant.val (index + 1 + 2) then
            (carryPrefixWork width (index + 1) h).flip
              (stepList (carryPrefix width constant index (by omega)) state)
          else stepList (carryPrefix width constant index (by omega)) state := by
        dsimp only [carryPrefix, carryPrefixInput, carryPrefixWork]
        rw [hrsPropagateCarry_step _ _ _ _ _ _ _ _ hinput houtput]
        rw [hprevious, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
        simp only [hrsCarryInputBit_get,
          Nat.BinaryArithmetic.natAddCarry]
        rfl
      constructor
      · exact hstep
      · have hget := stepList_get_of_bitDisjoint
          (carryPrefix width constant index (by omega))
          (carryPrefixWork width (index + 1) h) houtput state
        rw [hstep]
        cases hc : Nat.BinaryArithmetic.natAddCarry state.1.val constant.val
            (index + 1 + 2) <;>
          simp [EncodedBit.get_flip_self, hget]

/-- Mathematical carry out of a fixed-width constant addition, xor-written
into an arbitrary initial output bit. -/
def carryOutput (width : Nat) (constant : Fin (2 ^ width))
    (state : CarryRegisters width) : CarryRegisters width :=
  if decide (2 ^ width ≤ state.1.val + constant.val)
    then (carryOutputBit width).flip state else state

/-- The actual carry list uses no scratch for input widths zero or one.
At larger widths the last prefix writes directly into the output wire. -/
def carryGates : (width : Nat) → Fin (2 ^ width) →
    List (EncodedBit.GateSpec (carryEncoding width))
  | 0, _ => []
  | 1, constant =>
      if constant.val.testBit 0 then
        [.cnot (carryInputBit 1 0) (carryOutputBit 1) (input_ne_work 1 _ _)]
      else []
  | width + 2, constant =>
      carryPrefix (width + 2) constant width (by omega) ++
        (carryLowerPrefix (width + 2) constant width (by omega)).reverse

/-- Compile the carry from its actual primitive list. -/
def carryProgram (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (carryEncoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (carryGates width constant)

/-- All input and borrowed components are restored, with only the carry output
toggled. The statement includes the empty input and the one-bit input. -/
lemma hrsCarry_step (width : Nat) (constant : Fin (2 ^ width))
    (state : CarryRegisters width) :
    stepList (carryGates width constant) state = carryOutput width constant state := by
  have hcarry := Nat.BinaryArithmetic.natAddCarry_eq_decide_two_pow_le
    state.1.isLt constant.isLt
  match width with
  | 0 =>
      have hclear : decide (2 ^ 0 ≤ state.1.val + constant.val) = false := by
        exact hcarry.symm
      rw [carryOutput, hclear]
      rfl
  | 1 =>
      have hcarryOne : decide (2 ^ 1 ≤ state.1.val + constant.val) =
          (state.1.val.testBit 0 && constant.val.testBit 0) := by
        rw [← hcarry]
        exact carry_false _ _
      rw [carryOutput, hcarryOne]
      cases hc : constant.val.testBit 0 <;>
        simp [carryGates, stepList, step,
          EncodedBit.cnotStep, hrsCarryInputBit_get, hc]
  | width + 2 =>
      rw [carryGates, stepList_append, (hrsCarryPrefix_action
        (width + 2) constant width (by omega) state).1]
      rw [hrsCarry_uncompute_lower _ _
        (lower_disjoint_output (width + 2) constant width (by omega))]
      rw [hcarry]
      rfl

/-- Exact amplitudes preserve arbitrary joint borrowed-state coherence. -/
lemma hrsCarry_realizes (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes (carryEncoding width) (carryProgram width constant) environment
      (carryOutput width constant) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (carryGates width constant) (hrsCarry_step width constant) environment

/-- The entire input word is restored, without any basis-value restriction. -/
lemma hrsCarry_restores_input (width : Nat) (constant : Fin (2 ^ width))
    (state : CarryRegisters width) :
    (stepList (carryGates width constant) state).1 = state.1 := by
  rw [hrsCarry_step]
  unfold carryOutput
  split <;> rfl

/-- Every internal borrowed bit is restored, independently of the output value. -/
lemma hrsCarry_restores_borrowed (width : Nat) (constant : Fin (2 ^ width))
    (bit : Fin (width - 2)) (state : CarryRegisters width) :
    (stepList (carryGates width constant) state).2.val.testBit bit.val =
      state.2.val.testBit bit.val := by
  let observed := carryWorkBit width ⟨bit.val, by omega⟩
  have hne : (carryOutputBit width).wire ≠ observed.wire := by
    apply work_ne_work
    intro heq
    have := congrArg Fin.val heq
    dsimp [observed] at this
    omega
  have hget := EncodedBit.get_flip_of_wire_ne (carryOutputBit width) observed hne state
  have hrestored : observed.get (stepList (carryGates width constant) state) =
      observed.get state := by
    rw [hrsCarry_step]
    unfold carryOutput
    split
    · exact hget
    · rfl
  simpa only [observed, hrsCarryWorkBit_get] using hrestored

/-- The selected output is an xor-output, including when initially dirty. -/
lemma hrsCarry_output_get (width : Nat) (constant : Fin (2 ^ width))
    (state : CarryRegisters width) :
    (carryOutputBit width).get (stepList (carryGates width constant) state) =
      ((carryOutputBit width).get state ^^ decide (2 ^ width ≤ state.1.val + constant.val)) := by
  rw [hrsCarry_step]
  unfold carryOutput
  cases hc : decide (2 ^ width ≤ state.1.val + constant.val) <;>
    simp [EncodedBit.get_flip_self]

/-- The actual interface is exactly the input, internal borrowed bits, and output. -/
lemma hrsCarry_interface (width : Nat) :
    (carryEncoding width).width = width + (width - 2) + 1 ∧
      (QubitLayout.canonical (carryEncoding width).width).systemIdx =
        List.range (width + (width - 2) + 1) := by
  have hwidth : (carryEncoding width).width = width + (width - 2) + 1 := by
    change width + (width - 2 + 1) = width + (width - 2) + 1
    omega
  constructor
  · exact hwidth
  · rw [hwidth]
    exact QubitLayout.canonical_systemIdx (width + (width - 2) + 1)

/-- For at least two input bits the concrete interface occupies `2w - 1` wires. -/
lemma hrsCarry_width_of_two_le (width : Nat) (h : 2 ≤ width) :
    (carryEncoding width).width = 2 * width - 1 := by
  change width + (width - 2 + 1) = 2 * width - 1
  omega

end

end QuantumAlg.MAU.Addition.HRS
