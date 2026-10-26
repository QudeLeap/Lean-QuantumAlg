/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Selector
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout

/-!
# Original physical ports for the whole-digit enable

The selected digit comprises its existing stream top and its current address
suffix. The output is original pool address bit one, at560; original address
bit zero at559 is arbitrary borrowed work. Both return to their required pool
values before a QROM or inversion uses the pool. No new system is allocated.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

open QuantumAlg.EncodedBit

def outputBit : EncodedBit encoding := poolPrefixBit ⟨1, by decide⟩

def workBit : EncodedBit encoding := poolPrefixBit ⟨0, by decide⟩

lemma outputBit_wire : outputBit.wire.val = 560 := poolPrefixBit_wire _

lemma workBit_wire : workBit.wire.val = 559 := poolPrefixBit_wire _

lemma outputBit_clean (state : Raw) (clean : Frame.CleanPool state.1) :
    outputBit.get state = false := poolPrefixBit_clean _ state clean

def digitBit (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) : EncodedBit encoding :=
  Fin.cases (streamBit stream)
    (fun index => addressBit ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩) index

lemma digitBit_wire (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) :
    (digitBit stream width bounded index).wire.val =
      if index.val = 0 then (if stream.val = 0 then 836 else 838)
      else 839 + (index.val - 1) := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact streamBit_wire stream
  · exact addressBit_wire _

lemma digitBit_injective (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    Function.Injective (fun index => (digitBit stream width bounded index).wire) := by
  intro left right same
  apply Fin.ext
  have positions := congrArg Fin.val same
  rw [digitBit_wire, digitBit_wire] at positions
  have leftBound := left.isLt
  have rightBound := right.isLt
  split_ifs at positions <;> omega

private lemma digitBit_after_pool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) : 836 ≤ (digitBit stream width bounded index).wire.val := by
  rw [digitBit_wire]
  split_ifs <;> omega

def layout (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    Word.OneDirtyLayout (encoding := encoding) (width + 1) where
  source := ⟨digitBit stream width bounded⟩
  output := outputBit
  work := workBit
  source_injective := digitBit_injective stream width bounded
  source_output_ne := by
    intro index same
    have afterPool := digitBit_after_pool stream width bounded index
    have positions : (digitBit stream width bounded index).wire.val = outputBit.wire.val :=
      congrArg (fun wire : Fin encoding.width => wire.val) same
    rw [outputBit_wire] at positions
    omega
  source_work_ne := by
    intro index same
    have afterPool := digitBit_after_pool stream width bounded index
    have positions : (digitBit stream width bounded index).wire.val = workBit.wire.val :=
      congrArg (fun wire : Fin encoding.width => wire.val) same
    rw [workBit_wire] at positions
    omega
  work_output_ne := by
    intro same
    have positions := congrArg Fin.val same
    rw [workBit_wire, outputBit_wire] at positions
    omega

def fullLayout (stream : Fin 2) : Word.OneDirtyLayout (encoding := encoding) 16 :=
  layout stream 15 (by omega)

def tailLayout (stream : Fin 2) : Word.OneDirtyLayout (encoding := encoding) 4 :=
  layout stream 3 (by omega)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
