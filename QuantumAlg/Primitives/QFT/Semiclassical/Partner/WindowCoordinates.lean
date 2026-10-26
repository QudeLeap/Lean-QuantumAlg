/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Windows
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import Lean.Elab.Tactic.Omega

/-!
# Coordinates of symbolic chronological Fourier windows

Each bit in a recursively concatenated window tuple occupies the same
MSB-first position as in the original complete Fourier word. Widths remain
symbolic, including zero-width windows. These maps only describe mathematical
labels; they do not rearrange physical wires or execute a circuit.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

private def prefixPosition (head tail : Nat) (index : Fin head) : Fin (tail + head) :=
  ⟨index.val, by have := index.isLt; omega⟩

private def suffixPosition (head tail : Nat) (index : Fin tail) : Fin (tail + head) :=
  ⟨head + index.val, by have := index.isLt; omega⟩

/-- The leading block keeps every original MSB-first coordinate. -/
private lemma blockBits_prefix (headCount tailCount : Nat)
    (front : Bits headCount) (tail : Bits tailCount) (index : Fin headCount) :
    tupleCoordinates (tailCount + headCount)
        (blockBits headCount tailCount front tail)
        (prefixPosition headCount tailCount index) =
      tupleCoordinates headCount front index := by
  induction headCount with
  | zero => exact index.elim0
  | succ count ih =>
      rcases front with ⟨head, rest⟩
      cases index using Fin.cases with
      | zero =>
          calc
            _ = head := by
              have position : prefixPosition (count + 1) tailCount
                  (0 : Fin (count + 1)) = 0 := Fin.ext rfl
              rw [position]
              simpa only [blockBits, Nat.add_succ, Nat.add_zero] using
                (tupleCoordinates_head (tailCount + count) head
                  (blockBits count tailCount rest tail))
            _ = _ := (tupleCoordinates_head count head rest).symm
      | succ index =>
          have shifted : prefixPosition (count + 1) tailCount index.succ =
              (prefixPosition count tailCount index).succ := by
            apply Fin.ext
            simp only [prefixPosition, Fin.val_succ]
          rw [shifted]
          calc
            _ = tupleCoordinates (tailCount + count)
                  (blockBits count tailCount rest tail)
                    (prefixPosition count tailCount index) := by
              simpa only [blockBits, Nat.add_succ] using
                (tupleCoordinates_tail (tailCount + count) head
                  (blockBits count tailCount rest tail)
                  (prefixPosition count tailCount index))
            _ = tupleCoordinates count rest index := ih rest index
            _ = _ := (tupleCoordinates_tail count head rest index).symm

/-- The trailing block starts exactly after the leading block. -/
private lemma blockBits_suffix (headCount tailCount : Nat)
    (front : Bits headCount) (tail : Bits tailCount) (index : Fin tailCount) :
    tupleCoordinates (tailCount + headCount)
        (blockBits headCount tailCount front tail)
        (suffixPosition headCount tailCount index) =
      tupleCoordinates tailCount tail index := by
  induction headCount with
  | zero =>
      simp only [blockBits, suffixPosition, Nat.add_zero, Nat.zero_add]
  | succ count ih =>
      rcases front with ⟨head, rest⟩
      have shifted : suffixPosition (count + 1) tailCount index =
          (suffixPosition count tailCount index).succ := by
        apply Fin.ext
        simp only [suffixPosition, Fin.val_succ]
        omega
      rw [shifted]
      calc
        _ = tupleCoordinates (tailCount + count)
              (blockBits count tailCount rest tail)
                (suffixPosition count tailCount index) := by
          simpa only [blockBits, Nat.add_succ] using
            (tupleCoordinates_tail (tailCount + count) head
              (blockBits count tailCount rest tail)
              (suffixPosition count tailCount index))
        _ = tupleCoordinates tailCount tail index := ih rest

/-- Read one symbolic window without flattening or expanding the other windows. -/
def windowBlock : (widths : List Nat) → WindowBits widths →
    (index : Fin widths.length) → Bits (widths.get index)
  | [], _, index => index.elim0
  | _ :: _, chunks, ⟨0, _⟩ => chunks.1
  | _ :: tail, chunks, ⟨position + 1, bound⟩ =>
      windowBlock tail chunks.2 ⟨position, by simpa using bound⟩

/-- The original full-word position of a bit in one symbolic window. -/
def windowPosition (widths : List Nat) (index : Fin widths.length)
    (bit : Fin (widths.get index)) : Fin (windowWidth widths) :=
  ⟨(widths.take index.val).sum + bit.val, by
    have bounded : (widths.take (index.val + 1)).sum ≤ widths.sum := by
      calc
        _ ≤ (widths.take (index.val + 1)).sum +
              (widths.drop (index.val + 1)).sum := Nat.le_add_right _ _
        _ = widths.sum := by
          rw [← List.sum_append, List.take_append_drop]
    rw [List.take_succ_eq_append_getElem index.isLt,
      List.sum_append, List.sum_singleton] at bounded
    rw [qftPartner_windowWidth_sum]
    have bitBound : bit.val < widths[index.val] := by
      simpa only [List.get_eq_getElem] using bit.isLt
    omega⟩

/-- The physical coordinate is the sum of earlier window widths plus the local bit index. -/
lemma windowPosition_val (widths : List Nat)
    (index : Fin widths.length) (bit : Fin (widths.get index)) :
    (windowPosition widths index bit).val =
      (widths.take index.val).sum + bit.val := rfl

/-- Every original MSB-first full-word bit is the corresponding window bit. -/
lemma windowBits_coordinate : ∀ (widths : List Nat)
    (chunks : WindowBits widths) (index : Fin widths.length)
    (bit : Fin (widths.get index)),
    tupleCoordinates (windowWidth widths) (windowBits widths chunks)
        (windowPosition widths index bit) =
      tupleCoordinates (widths.get index) (windowBlock widths chunks index) bit := by
  intro widths
  induction widths with
  | nil =>
      intro chunks index bit
      exact index.elim0
  | cons head tail ih =>
      intro chunks index bit
      cases index using Fin.cases with
      | zero =>
          have position : windowPosition (head :: tail) 0 bit =
              prefixPosition head (windowWidth tail) bit := by
            apply Fin.ext
            simp only [windowPosition_val, Fin.val_zero, List.take_zero,
              List.sum_nil, Nat.zero_add, prefixPosition]
          rw [position]
          exact blockBits_prefix head (windowWidth tail) chunks.1
            (windowBits tail chunks.2) bit
      | succ index =>
          have position : windowPosition (head :: tail) index.succ bit =
              suffixPosition head (windowWidth tail)
                (windowPosition tail index bit) := by
            apply Fin.ext
            simp only [windowPosition_val, Fin.val_succ, List.take_succ_cons,
              List.sum_cons, suffixPosition]
            omega
          rw [position]
          exact (blockBits_suffix head (windowWidth tail) chunks.1
            (windowBits tail chunks.2) (windowPosition tail index bit)).trans
            (ih chunks.2 index bit)


/-- Every full-word position belongs to an actual window and one of its own bits. -/
lemma windowPosition_covers : ∀ (widths : List Nat) (position : Fin (windowWidth widths)),
    ∃ index : Fin widths.length, ∃ bit : Fin (widths.get index),
      windowPosition widths index bit = position := by
  intro widths
  induction widths with
  | nil =>
      intro position
      exact position.elim0
  | cons head tail ih =>
      intro position
      by_cases inside : position.val < head
      · refine ⟨⟨0, Nat.succ_pos _⟩, ⟨position.val, inside⟩, ?_⟩
        apply Fin.ext
        simp only [windowPosition_val, List.take_zero, List.sum_nil, Nat.zero_add]
      · have tailBound : position.val - head < windowWidth tail := by
          have bound := position.isLt
          change position.val < windowWidth tail + head at bound
          omega
        obtain ⟨index, bit, same⟩ := ih ⟨position.val - head, tailBound⟩
        refine ⟨index.succ, bit, ?_⟩
        apply Fin.ext
        have offset := congrArg Fin.val same
        simp only [windowPosition_val] at offset ⊢
        simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons]
        omega

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
