/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Persistent.Reads
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Narrow.Readout

/-!
# Actual persistent selector positions beneath local recovery scopes

The local eligibility bit is a fresh lexical cell outside the original
persistent latches. The original persistent selector's actual four-cell
allocation supplies all remaining distinctness facts. The general internal
statement records only these positional facts; its concrete layout instance
requires no caller initialization, input-value or aliasing premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width resultWidth : Nat}

private def persistentKey (original : FirstAccepted.Refs ctx resultWidth)
    (index : Fin 4) : StorageKey :=
  ([original.take.key, original.available.key, original.selected.key,
    original.accepted.key] : List StorageKey).get index

private lemma persistentKey_ne (original : FirstAccepted.Refs ctx resultWidth)
    (unique : ([original.take.key, original.available.key, original.selected.key,
      original.accepted.key] : List StorageKey).Nodup)
    (left right : Fin 4) (different : left ≠ right) :
    persistentKey original left ≠ persistentKey original right := by
  intro same
  exact different (unique.injective_get same)

/-- Actual local allocation separates its eligibility bit from every original writable cell. -/
lemma nativeQuadratic_persistent_eligibility_free
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    {shape : CShape} (output : CWriteRef ctx shape) :
    (underWrite output width).key ∉
      (FirstAccepted.cellRead (pairRefs modulus).selection.accepted).storageKeys := by
  have localFree := nativeQuadratic_persistent_local_key_free
    (CInputRef.storage output.toCStorageRef) width 3
  have support := nativeQuadratic_persistent_underRead_keys
    (CInputRef.storage output.toCStorageRef) width
  intro present
  have same : output.key = (pairRefs modulus).selection.accepted.key :=
    List.mem_singleton.mp present
  exact localFree (support.symm ▸ (List.mem_singleton.mpr same.symm))

/-- Intrinsic persistent identities suffice for the final actual narrowing selector. -/
lemma nativeQuadratic_persistent_narrow_separated
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (unique : ([original.take.key, original.available.key, original.selected.key,
      original.accepted.key] : List StorageKey).Nodup) :
    NarrowSelection.Separated (FirstAccepted.cellRead (pairRefs modulus).selection.accepted)
      (persistentRefs original width) where
  availableEligible := nativeQuadratic_persistent_eligibility_free modulus original.available
  availableAccepted := persistentKey_ne original unique 1 3 (by decide)
  takeAccepted := persistentKey_ne original unique 0 3 (by decide)
  availableSelected := persistentKey_ne original unique 1 2 (by decide)
  takeSelected := persistentKey_ne original unique 0 2 (by decide)
  acceptedSelected := persistentKey_ne original unique 3 2 (by decide)

/-- The real outer persistent selector automatically supplies every required position fact. -/
lemma nativeQuadratic_persistent_allocated_separated
    (modulus : CInputRef (SelectionLayout.context ctx resultWidth)
      (.unsignedWord (RSA.quadraticWordWidth width))) :
    NarrowSelection.Separated (FirstAccepted.cellRead (pairRefs modulus).selection.accepted)
      (persistentRefs (SelectionLayout.refs ctx resultWidth) width) :=
  nativeQuadratic_persistent_narrow_separated modulus (SelectionLayout.refs ctx resultWidth)
    (SelectionLayout.nativeRecovery_selection_nodup ctx resultWidth)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout
