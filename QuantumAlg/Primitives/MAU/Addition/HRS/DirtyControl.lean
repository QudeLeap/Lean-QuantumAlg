/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Step
import all QuantumAlg.Primitives.MAU.Addition.TTK.Layout

/-!
# Dirty-bit lowering for a controlled TTK Toffoli

The HRS route permits controlled additions in its incrementer
[HRS16, paper.tex:219-224]. Adding a control to an existing Toffoli is
implemented here by four actual Toffolis. The proof reuses the HRS
dirty-toggle identity [HRS16, paper.tex:187-195]. An unused operand wire
serves as temporary storage and is restored for every input value.

The selected wire belongs to the existing two operand words; it is not
an additional ancilla or an assumed clean bit.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Four actual Toffolis, with a borrowed work wire restored immediately. -/
def dirtyControlledToffoliGates (control a b target work : EncodedBit encoding)
    (hca : control.wire ≠ a.wire) (hcw : control.wire ≠ work.wire)
    (haw : a.wire ≠ work.wire) (hbw : b.wire ≠ work.wire)
    (hbt : b.wire ≠ target.wire) (hwt : work.wire ≠ target.wire) :
    List (EncodedBit.GateSpec encoding) :=
  let toggle := EncodedBit.GateSpec.toffoli control a work hca hcw haw
  let copy := EncodedBit.GateSpec.toffoli b work target hbw hbt hwt
  [copy, toggle, copy, toggle]

/-- The literal lowering has exact triple-control action and restores the
borrowed wire, including its coherence with every other input. -/
theorem hrsDirtyControlledToffoli_step (control a b target work : EncodedBit encoding)
    (hca : control.wire ≠ a.wire) (hcw : control.wire ≠ work.wire)
    (haw : a.wire ≠ work.wire) (hbw : b.wire ≠ work.wire)
    (hbt : b.wire ≠ target.wire) (hwt : work.wire ≠ target.wire)
    (hcb : control.wire ≠ b.wire) (hct : control.wire ≠ target.wire)
    (hab : a.wire ≠ b.wire) (hat : a.wire ≠ target.wire) (state : Data) :
    stepList (dirtyControlledToffoliGates control a b target work hca hcw haw hbw hbt hwt)
        state =
      if (control.get state && a.get state) && b.get state
        then target.flip state else state := by
  let toggle := EncodedBit.GateSpec.toffoli control a work hca hcw haw
  have hinput : ∀ gate, gate ∈ [toggle] → bitDisjoint b gate := by
    intro gate hgate
    have heq : gate = toggle := List.mem_singleton.mp hgate
    subst gate
    exact ⟨hcb, hab, hbw.symm⟩
  have houtput : ∀ gate, gate ∈ [toggle] → bitDisjoint target gate := by
    intro gate hgate
    have heq : gate = toggle := List.mem_singleton.mp hgate
    subst gate
    exact ⟨hct, hat, hwt⟩
  have hshape : dirtyControlledToffoliGates control a b target work
        hca hcw haw hbw hbt hwt =
      propagateCarryGates b work target hbw hbt hwt false [toggle] ++ [toggle].reverse := rfl
  rw [hshape, stepList_append, hrsPropagateCarry_step _ _ _ _ _ _ _ _ hinput houtput,
    hrsCarry_uncompute_lower _ _ houtput]
  have hwork : work.get (stepList [toggle] state) =
      (work.get state ^^ (control.get state && a.get state)) :=
    EncodedBit.toffoliStep_get_target control a work state
  rw [hwork, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
  cases control.get state <;> cases a.get state <;> cases b.get state <;> rfl

/-- A lowered controlled Toffoli contains exactly four native Toffoli leaves. -/
theorem hrsDirtyControlledToffoli_weight (control a b target work : EncodedBit encoding)
    (hca : control.wire ≠ a.wire) (hcw : control.wire ≠ work.wire)
    (haw : a.wire ≠ work.wire) (hbw : b.wire ≠ work.wire)
    (hbt : b.wire ≠ target.wire) (hwt : work.wire ≠ target.wire)
    (weight : Resource.Event .quantum → Nat) :
    ((dirtyControlledToffoliGates control a b target work hca hcw haw hbw hbt hwt).map
      fun gate => weight gate.event).sum = 4 * weight (.gate (.builtin "toffoli")) := by
  simp [dirtyControlledToffoliGates, event]
  omega

/-- Three distinct operand wires require at least two bits in each equal-width word. -/
theorem hrsTwoLe_of_toffoli (n : Nat) (a b target : EncodedBit (TTK.encoding n))
    (hab : a.wire ≠ b.wire) (hat : a.wire ≠ target.wire)
    (hbt : b.wire ≠ target.wire) : 2 ≤ n := by
  have ha := a.wire.isLt
  have hb := b.wire.isLt
  have ht := target.wire.isLt
  have ha' : a.wire.val < 2 * n := by simpa only [TTK.ttkEncoding_width] using ha
  have hb' : b.wire.val < 2 * n := by simpa only [TTK.ttkEncoding_width] using hb
  have ht' : target.wire.val < 2 * n := by simpa only [TTK.ttkEncoding_width] using ht
  have hab' : a.wire.val ≠ b.wire.val := fun heq => hab (Fin.ext heq)
  have hat' : a.wire.val ≠ target.wire.val := fun heq => hat (Fin.ext heq)
  have hbt' : b.wire.val ≠ target.wire.val := fun heq => hbt (Fin.ext heq)
  omega

/-- Choose an idle wire from the first two bits of both existing operand words. -/
def spareOperandBit (n : Nat) (hn : 2 ≤ n) (a b target : EncodedBit (TTK.encoding n)) :
    EncodedBit (TTK.encoding n) :=
  let left0 := TTK.leftBit n ⟨0, by omega⟩
  let left1 := TTK.leftBit n ⟨1, by omega⟩
  let right0 := TTK.rightBit n ⟨0, by omega⟩
  let right1 := TTK.rightBit n ⟨1, by omega⟩
  if left0.wire ≠ a.wire ∧ left0.wire ≠ b.wire ∧ left0.wire ≠ target.wire then left0
  else if left1.wire ≠ a.wire ∧ left1.wire ≠ b.wire ∧ left1.wire ≠ target.wire then left1
  else if right0.wire ≠ a.wire ∧ right0.wire ≠ b.wire ∧ right0.wire ≠ target.wire then right0
  else right1

/-- Four distinct existing candidate wires cannot all be occupied by three gate wires. -/
theorem hrsSpareOperandBit_disjoint (n : Nat) (hn : 2 ≤ n)
    (a b target : EncodedBit (TTK.encoding n)) :
    (spareOperandBit n hn a b target).wire ≠ a.wire ∧
      (spareOperandBit n hn a b target).wire ≠ b.wire ∧
      (spareOperandBit n hn a b target).wire ≠ target.wire := by
  unfold spareOperandBit
  dsimp only
  split
  · assumption
  · split
    · assumption
    · split
      · assumption
      · simp only [ne_eq, Fin.ext_iff,
          TTK.ttkLeftBit_wire_val, TTK.ttkRightBit_wire_val] at *
        omega

end

end QuantumAlg.MAU.Addition.HRS
