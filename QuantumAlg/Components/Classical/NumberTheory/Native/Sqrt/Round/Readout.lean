/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Round

/-!
# Exact stored arithmetic of the actual square-root round

The real full-width multiplication never truncates a candidate square.
Addition has its exact declared modular behavior, comparison reads the
actual input and square cells, and the conditional copy and right shift
have their actual stored values. These identities require no initialization
or distinctness assumptions. The later generated layout supplies the
separation needed to compose their reads across multiple instructions.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual candidate addition has exactly the declared word modulus. -/
theorem nativeSqrt_add_read (refs : RoundRefs ctx width) (store : Store ctx) :
    ((store.applyOp (addOp refs)).read (.storage refs.candidate.toCStorageRef)).toNat =
      ((store.read (.storage refs.root.toCStorageRef)).toNat +
        (store.read (.storage refs.half.toCStorageRef)).toNat) % 2 ^ width := by
  change ((store.applyOp (addOp refs)).read
    (.storage (addOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  rfl

/-- The actual twice-width square equals the untruncated mathematical product. -/
theorem nativeSqrt_square_read (refs : RoundRefs ctx width) (store : Store ctx) :
    ((store.applyOp (squareOp refs)).read (.storage refs.square.toCStorageRef)).toNat =
      (store.read (.storage refs.candidate.toCStorageRef)).toNat *
        (store.read (.storage refs.candidate.toCStorageRef)).toNat := by
  change ((store.applyOp (squareOp refs)).read
    (.storage (squareOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact ClassicalOp.eval_mulFull_exact width width ctx _ refs.square _

/-- The strict comparison is the actual stored Boolean controlling the copy. -/
theorem nativeSqrt_compare_read (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) (store : Store ctx) :
    ((store.applyOp (compareOp input refs)).read (.storage refs.tooLarge.toCStorageRef)).toBool =
      decide ((store.read input).toNat <
        (store.read (.storage refs.square.toCStorageRef)).toNat) := by
  change ((store.applyOp (compareOp input refs)).read
    (.storage (compareOp input refs).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  rfl

/-- The selected copy stores the entire tested candidate in the actual root cell. -/
theorem nativeSqrt_copy_read (refs : RoundRefs ctx width) (store : Store ctx) :
    ((store.applyOp (copyOp refs)).read (.storage refs.root.toCStorageRef)).toNat =
      (store.read (.storage refs.candidate.toCStorageRef)).toNat := by
  change ((store.applyOp (copyOp refs)).read
    (.storage (copyOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  rfl

/-- The next actual binary increment is the old increment divided by two, without truncation. -/
theorem nativeSqrt_shift_read (refs : RoundRefs ctx width) (store : Store ctx) :
    ((store.applyOp (shiftOp refs)).read (.storage refs.half.toCStorageRef)).toNat =
      (store.read (.storage refs.half.toCStorageRef)).toNat / 2 := by
  change ((store.applyOp (shiftOp refs)).read
    (.storage (shiftOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  change ((store.read (.storage refs.half.toCStorageRef)).toNat / 2) % 2 ^ width = _
  exact Nat.mod_eq_of_lt
    ((Nat.div_le_self _ _).trans_lt (store.read (.storage refs.half.toCStorageRef)).toNat_lt)

/-- Both actual branches expose the root chosen by the real comparison result. -/
theorem nativeSqrt_select_read (refs : RoundRefs ctx width) (store : Store ctx) :
    ((selectStep refs store).1.read (.storage refs.root.toCStorageRef)).toNat =
      if (store.read (.storage refs.tooLarge.toCStorageRef)).toBool then
        (store.read (.storage refs.root.toCStorageRef)).toNat
      else (store.read (.storage refs.candidate.toCStorageRef)).toNat := by
  unfold selectStep
  cases flagRead : store.read (.storage refs.tooLarge.toCStorageRef) with
  | bit flag =>
      cases flag with
      | false => exact nativeSqrt_copy_read refs store
      | true => rfl

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
