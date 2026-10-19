/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Circuit
import Lean.Elab.Tactic.Omega

/-!
# Exact reads of the actual truncating-subtraction instructions

The comparison stores the real underflow predicate. Self-XOR clears the
actual output for every initial value, while the actual wrapping subtraction
is exact on the other branch. The non-underflow condition is established by
the preceding comparison; it is not an extra caller precondition.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual comparison bit records the current unsigned underflow condition. -/
lemma nativeSub_compare_read (left right : CInputRef ctx (.unsignedWord width))
    (store : Store (context ctx)) :
    ((store.applyOp (compareOp left right)).read (.storage (decision ctx).toCStorageRef)).toBool =
      decide ((store.read (underRead left)).toNat < (store.read (underRead right)).toNat) := by
  change ((store.applyOp (compareOp left right)).read
    (.storage (compareOp left right).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  rfl

/-- The actual self-XOR instruction clears every original output word, including width zero. -/
lemma nativeSub_clear_read (output : CWriteRef ctx (.unsignedWord width))
    (store : Store (context ctx)) :
    ((store.applyOp (clearOp output)).read
      (.storage (underWrite output).toCStorageRef)).toNat = 0 := by
  change ((store.applyOp (clearOp output)).read
    (.storage (clearOp output).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  change (((store.read (underRead (.storage output.toCStorageRef))).toNat ^^^
    (store.read (underRead (.storage output.toCStorageRef))).toNat) % 2 ^ width) = 0
  rw [Nat.xor_self, Nat.zero_mod]

/-- In the accepted branch, the actual native subtraction has no modular wraparound. -/
lemma nativeSub_subtract_read (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx))
    (ordered : (store.read (underRead right)).toNat ≤ (store.read (underRead left)).toNat) :
    ((store.applyOp (subtractOp left right output)).read
      (.storage (underWrite output).toCStorageRef)).toNat =
      (store.read (underRead left)).toNat - (store.read (underRead right)).toNat := by
  change ((store.applyOp (subtractOp left right output)).read
    (.storage (subtractOp left right output).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  change ((store.read (underRead left)).toNat + 2 ^ width -
    (store.read (underRead right)).toNat) % 2 ^ width = _
  have split : (store.read (underRead left)).toNat + 2 ^ width -
      (store.read (underRead right)).toNat =
      ((store.read (underRead left)).toNat - (store.read (underRead right)).toNat) +
        2 ^ width := by
    rw [Nat.add_comm (store.read (underRead left)).toNat (2 ^ width),
      Nat.add_sub_assoc ordered,
      Nat.add_comm (2 ^ width) ((store.read (underRead left)).toNat -
        (store.read (underRead right)).toNat)]
  have fits : (store.read (underRead left)).toNat - (store.read (underRead right)).toNat <
      2 ^ width := (Nat.sub_le _ _).trans_lt (store.read (underRead left)).toNat_lt
  rw [split]
  simp [Nat.mod_eq_of_lt fits]

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
