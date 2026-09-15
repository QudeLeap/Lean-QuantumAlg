/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Circuit
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual dependency depth of finite modular exponentiation

Full multiplication precedes division and remainder materialization. Every
exponent slot retains that square dependency before its actual classical
selection. The bounds use the same selected path for arbitrary native event
durations, with six units per declared exponent bit as the unit-cost bound.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent duration sum of one full-product reduction. -/
def multiplyDepth (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.mulFull width width)) +
    duration (.classicalOperation (.divRem (width + width) (width + 1))) +
    duration (.classicalOperation (.wordResize (width + 1) width))

/-- The two actual scratch scopes do not erase the three arithmetic dependencies. -/
theorem nativePower_scopedMultiply_depth
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (scopedMultiply left right modulus output).Path) :
    (scopedMultiply left right modulus output).depth duration path =
      multiplyDepth width duration := by
  change duration (.classicalOperation (.mulFull width width)) +
    (duration (.classicalOperation (.divRem (width + width) (width + 1))) +
      duration (.classicalOperation (.wordResize (width + 1) width))) = _
  exact (Nat.add_assoc _ _ _).symm

/-- Actual selection admits at most two complete sequential reductions per exponent slot. -/
theorem nativePower_bit_depth_le (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (duration : Resource.Event kind → Nat) (path : (bitCircuit base modulus output bit).Path) :
    (bitCircuit base modulus output bit).depth duration path ≤
      2 * multiplyDepth width duration := by
  rcases path with ⟨squarePath, value, selectedPath⟩
  cases value with
  | bit value =>
      cases value
      · change (scopedMultiply (wordRead output) (wordRead output) modulus output).depth
          duration squarePath + 0 ≤ _
        rw [nativePower_scopedMultiply_depth]
        omega
      · change (scopedMultiply (wordRead output) base modulus output).Path at selectedPath
        change (scopedMultiply (wordRead output) (wordRead output) modulus output).depth
          duration squarePath + (scopedMultiply (wordRead output) base modulus output).depth
            duration selectedPath ≤ _
        rw [nativePower_scopedMultiply_depth, nativePower_scopedMultiply_depth]
        omega

/-- The finite sequence adds the actual depth of every selected square-and-multiply step. -/
theorem nativePower_fold_depth_le (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    (duration : Resource.Event kind → Nat) :
    ∀ path : (foldBits base modulus output bits).Path,
      (foldBits base modulus output bits).depth duration path ≤
        bits.length * (2 * multiplyDepth width duration) := by
  induction bits with
  | nil => intro path; exact Nat.zero_le _
  | cons bit rest ih =>
      intro path
      change (bitCircuit base modulus output bit).depth duration path.1 +
        (foldBits base modulus output rest).depth duration path.2 ≤ _
      have first := nativePower_bit_depth_le base modulus output bit duration path.1
      have later := ih path.2
      calc
        _ ≤ 2 * multiplyDepth width duration +
            rest.length * (2 * multiplyDepth width duration) := Nat.add_le_add first later
        _ = (bit :: rest).length * (2 * multiplyDepth width duration) :=
          (Nat.add_comm _ _).trans (Nat.succ_mul _ _).symm

/-- The declared exponent width supplies the actual exponent circuit's duration budget. -/
theorem nativePower_exponent_depth_le {exponentWidth : Nat}
    (base : CInputRef ctx (.unsignedWord width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (exponentCircuit base exponent modulus output).Path) :
    (exponentCircuit base exponent modulus output).depth duration path ≤
      exponentWidth * (2 * multiplyDepth width duration) := by
  simpa only [exponentCircuit, List.length_ofFn] using
    nativePower_fold_depth_le base modulus output
      (List.ofFn (fun index : Fin exponentWidth => CInputRef.wordBitGet exponent index))
      duration path

/-- At unit duration the actual exponent circuit takes at most six steps per declared bit. -/
theorem nativePower_exponent_unitDepth_le {exponentWidth : Nat}
    (base : CInputRef ctx (.unsignedWord width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (exponentCircuit base exponent modulus output).Path) :
    (exponentCircuit base exponent modulus output).depth (fun _ => 1) path ≤ 6 * exponentWidth := by
  simpa only [multiplyDepth, Nat.mul_comm] using
    nativePower_exponent_depth_le base exponent modulus output (fun _ => 1) path

end QuantumAlg.ClassicalRoutines.Modular.NativePower
