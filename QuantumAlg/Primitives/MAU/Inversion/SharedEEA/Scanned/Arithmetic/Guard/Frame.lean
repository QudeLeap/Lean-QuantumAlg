/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Append
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Pattern

/-!
# Physical phase and divisor predicates with arbitrary original Iter

Phase1, Phase2 and optional Sign are original source controls. Original
Ctrl is the output; one original Work1 bit is restored dirty work.
The separate original Iter can therefore control each actual pattern,
including during dirty-work conjunction with a computed window test.
No new quantum system is allocated.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

/-- The literal original Phase1, Phase2, Sign, Iter and Ctrl positions. -/
def flag (width : Nat) (index : Fin 5) : EncodedBit (encoding width) :=
  sourceBit width (![phase1Bit width, phase2Bit width, signBit width,
    iterationBit width, controlBit width] index)

private lemma flag_wire (width : Nat) (index : Fin 5) :
    (flag width index).wire.val = 2 * (width + 3) + 4 * width.size + index.val := by
  fin_cases index <;>
    first | exact phase1Bit_wire width | exact phase2Bit_wire width |
      exact signBit_wire width | exact iterationBit_wire width | exact controlBit_wire width

private lemma flag_ne (width : Nat) (left right : Fin 5) (different : left ≠ right) :
    (flag width left).wire ≠ (flag width right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [flag_wire, flag_wire] at values
  apply different
  apply Fin.ext
  omega

/-- One actual original operand bit is arbitrary borrowed work, restored within every pattern. -/
def work (width : Nat) : EncodedBit (encoding width) :=
  sourceBit width (firstWordBit width ⟨0, by omega⟩)

private lemma work_wire (width : Nat) : (work width).wire.val = 0 := rfl

private lemma flag_work_ne (width : Nat) (index : Fin 5) :
    (flag width index).wire ≠ (work width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [flag_wire, work_wire] at values
  omega

/-- A public prefix includes Sign only when the instruction predicate actually reads Sign. -/
def flags (width count : Nat) (bound : count ≤ 3) :
    Word.OneDirtyLayout (encoding := encoding width) count where
  source := ⟨fun index => flag width ⟨index.val, by have := index.isLt; omega⟩⟩
  output := flag width 4
  work := work width
  source_injective := by
    intro left right same
    apply Fin.ext
    have values := congrArg Fin.val same
    simp only [flag_wire] at values
    omega
  source_output_ne := by
    intro index
    apply flag_ne
    intro same
    have values := congrArg Fin.val same
    change index.val = 4 at values
    have within := index.isLt
    omega
  source_work_ne := fun index => flag_work_ne width _
  work_output_ne := (flag_work_ne width 4).symm

/-- Complete original divisor-length sources retain their declared physical order. -/
def divisor (width : Nat) : Word (encoding width) width.size :=
  ⟨fun index => sourceBit width (divisorLengthBit width index)⟩

private lemma divisor_wire (width : Nat) (index : Fin width.size) :
    ((divisor width).bit index).wire.val = 2 * (width + 3) + 2 * width.size + index.val := by
  rw [divisor, sourceBit_wire, divisorLengthBit_wire]

private lemma flag_divisor_ne (width : Nat) (left : Fin 5) (right : Fin width.size) :
    (flag width left).wire ≠ ((divisor width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [flag_wire, divisor_wire] at values
  have within := right.isLt
  omega

private lemma divisor_work_ne (width : Nat) (index : Fin width.size) :
    ((divisor width).bit index).wire ≠ (work width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [divisor_wire, work_wire] at values
  omega

/-- Extend the same physical phase controls by all untruncated divisor-length bits. -/
def flagsDivisor (width count : Nat) (bound : count ≤ 3) :
    Word.OneDirtyLayout (encoding := encoding width) (count + width.size) :=
  (flags width count bound).appendSources (divisor width)
    (by
      intro left right same
      apply Fin.ext
      have values := congrArg Fin.val same
      simp only [divisor_wire] at values
      omega)
    (fun left right => flag_divisor_ne width _ right)
    (fun index => (flag_divisor_ne width 4 index).symm)
    (divisor_work_ne width)

/-- Original Iter is separate from every actual phase source. -/
lemma iteration_flags_ne (width count : Nat) (bound : count ≤ 3) (index : Fin count) :
    (flag width 3).wire ≠ ((flags width count bound).source.bit index).wire := by
  apply flag_ne
  intro same
  have values := congrArg Fin.val same
  change 3 = index.val at values
  have within := index.isLt
  omega

/-- Original Iter is also separate from the complete phase-and-divisor pattern sources. -/
lemma iteration_flagsDivisor_ne (width count : Nat) (bound : count ≤ 3)
    (index : Fin (count + width.size)) :
    (flag width 3).wire ≠ ((flagsDivisor width count bound).source.bit index).wire := by
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simpa only [flagsDivisor, Word.OneDirtyLayout.appendSources, Fin.append_left] using
      iteration_flags_ne width count bound index
  · simpa only [flagsDivisor, Word.OneDirtyLayout.appendSources, Fin.append_right] using
      flag_divisor_ne width 3 index

/-- Neither original Ctrl nor the borrowed original operand aliases original Iter. -/
lemma iteration_output_work_ne (width : Nat) :
    (flag width 3).wire ≠ (flag width 4).wire ∧
      (flag width 3).wire ≠ (work width).wire :=
  ⟨flag_ne width 3 4 (by decide), flag_work_ne width 3⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
