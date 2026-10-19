/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout.Reads
import Mathlib.Data.List.Nodup

/-!
# Physical key separation of the actual recovery fields

Every field is constructed from a genuinely fresh workspace head. Its key
remains unchanged under subsequent lifts, so different field positions have
different keys and every original input read is disjoint from all fields.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private lemma first_field_key (modulusWidth candidateWidth : Nat)
    (field : RecoveryField) (rest : List RecoveryField) :
    (recoveryFieldCell ctx modulusWidth candidateWidth (field :: rest) 0).key =
      ctx.canonicalFreshKey :=
  nativeRecovery_writeUnderFields_key modulusWidth candidateWidth rest
    (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey
      (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)

/-- Every actual recovery field key is absent from its entire original context. -/
lemma nativeRecovery_field_fresh (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) (index : Fin fields.length) :
    (recoveryFieldCell ctx modulusWidth candidateWidth fields index).key ∉ ctx.keys := by
  induction fields generalizing ctx with
  | nil => exact Fin.elim0 index
  | cons field rest ih =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rw [first_field_key]
        exact ctx.canonicalFreshKey_fresh
      · have absent := ih (ctx := ctx.addWorkspace ctx.canonicalFreshKey
          (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh) tail
        intro present
        apply absent
        exact List.mem_cons_of_mem ctx.canonicalFreshKey present

/-- Different actual field positions always name different real storage keys. -/
lemma nativeRecovery_field_injective (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) :
    Function.Injective (fun index : Fin fields.length =>
      (recoveryFieldCell ctx modulusWidth candidateWidth fields index).key) := by
  induction fields generalizing ctx with
  | nil => intro index; exact Fin.elim0 index
  | cons field rest ih =>
      have headDifferent (tail : Fin rest.length) :
          (recoveryFieldCell ctx modulusWidth candidateWidth (field :: rest) 0).key ≠
            (recoveryFieldCell ctx modulusWidth candidateWidth (field :: rest) tail.succ).key := by
        intro same
        have absent := nativeRecovery_field_fresh
          (ctx := ctx.addWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
          modulusWidth candidateWidth rest tail
        apply absent
        have sameKey : ctx.canonicalFreshKey =
            (recoveryFieldCell
              (ctx.addWorkspace ctx.canonicalFreshKey
                (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
              modulusWidth candidateWidth rest tail).key :=
          (first_field_key modulusWidth candidateWidth field rest).symm.trans same
        rw [← sameKey]
        exact List.mem_cons_self
      intro first second
      refine Fin.cases ?_ (fun firstTail => ?_) first
      · exact Fin.cases (fun _ => rfl)
          (fun secondTail same => False.elim (headDifferent secondTail same)) second
      · refine Fin.cases (fun same => False.elim (headDifferent firstTail same.symm))
          (fun secondTail same => ?_) second
        exact congrArg Fin.succ
          (ih (ctx := ctx.addWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field)
            ctx.canonicalFreshKey_fresh) same)

/-- Every structural original input is automatically separate from each actual recovery write. -/
lemma nativeRecovery_field_input_separate (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField) (index : Fin fields.length) {shape : CShape}
    (input : CInputRef ctx shape) :
    (recoveryFieldCell ctx modulusWidth candidateWidth fields index).key ∉
      (underRecoveryFields modulusWidth candidateWidth fields input).storageKeys := by
  rw [nativeRecovery_underFields_keys]
  intro present
  exact nativeRecovery_field_fresh modulusWidth candidateWidth fields index
    (input.storageKeys_subset_context present)

/-- The real cursor cells satisfy the separation used by the actual advancement proof. -/
lemma nativeRecovery_cursor_distinct (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    let cells := (recoveryCells ctx modulusWidth candidateWidth).cursor
    [cells.older.key, cells.previous.key, cells.numerator.key,
      cells.denominator.key, cells.candidate.key, cells.active.key].Nodup := by
  have positions : ([4, 5, 2, 3, 6, 8] : List (Fin recoveryFields.length)).Nodup := by decide
  exact positions.map (nativeRecovery_field_injective modulusWidth candidateWidth recoveryFields)

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
