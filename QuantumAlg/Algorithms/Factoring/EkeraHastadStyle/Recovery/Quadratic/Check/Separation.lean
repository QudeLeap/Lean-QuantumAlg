/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Layout.Store
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Readout

/-!
# Intrinsic separation of both actual quadratic checks

Actual context key uniqueness discharges all positions used by the shared
range and native remainder circuits. The two range results are distinct, the
shared comparison and equality cells cannot overwrite them, and the reused
old remainder cell cannot alias the fresh zero word or either validity bit.
These are facts about the constructed layout, not caller preconditions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def cellKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 5) : StorageKey :=
  (internalKeys ctx width).get ⟨index.val, by change index.val < 5; exact index.isLt⟩

private lemma cellKey_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 5) (different : left ≠ right) :
    cellKey ctx width left ≠ cellKey ctx width right := by
  intro same
  have positions := (nativeQuadratic_checkLayout_nodup ctx width).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- Every new checker cell is outside every lifted actual source read. -/
lemma nativeQuadratic_checkLayout_new_free {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (key : StorageKey)
    (internal : key ∈ internalKeys ctx width) :
    key ∉ (underRead input width).storageKeys := by
  rw [nativeQuadratic_checkLayout_underRead_keys]
  intro present
  exact List.disjoint_left.mp (nativeQuadratic_checkLayout_disjoint ctx width)
    internal (input.storageKeys_subset_context present)

private lemma source_free {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (index : Fin 5) :
    cellKey ctx width index ∉ (underRead input width).storageKeys :=
  nativeQuadratic_checkLayout_new_free input width _ (List.get_mem (internalKeys ctx width) _)

/-- The reused original remainder destination lies outside each fresh checker cell. -/
lemma nativeQuadratic_checkLayout_original_ne {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) (key : StorageKey)
    (internal : key ∈ internalKeys ctx width) :
    (underWrite output width).key ≠ key := by
  rw [nativeQuadratic_checkLayout_underWrite_key]
  intro same
  have original : output.key ∈ ctx.keys :=
    (CInputRef.storage output.toCStorageRef).storageKeys_subset_context
      (List.mem_singleton.mpr rfl)
  exact List.disjoint_left.mp (nativeQuadratic_checkLayout_disjoint ctx width)
    internal (same ▸ original)

private lemma original_ne {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) (index : Fin 5) :
    (underWrite output width).key ≠ cellKey ctx width index :=
  nativeQuadratic_checkLayout_original_ne output width _ (List.get_mem (internalKeys ctx width) _)

/-- The actual lower-candidate interface satisfies every internal check separation fact. -/
lemma nativeQuadratic_first_check_separated (inputs : Operands ctx width) :
    Check.Separated (pairRefs inputs).first where
  validModulus := source_free inputs.modulus width 1
  validCandidate := source_free inputs.first width 1
  validZero := fun present => cellKey_ne ctx width 1 4 (by decide)
    (List.mem_singleton.mp present)
  upperModulus := source_free inputs.modulus width 3
  upperCandidate := source_free inputs.first width 3
  upperZero := fun present => cellKey_ne ctx width 3 4 (by decide)
    (List.mem_singleton.mp present)
  upperValid := cellKey_ne ctx width 3 1 (by decide)
  remainderZero := fun present => original_ne inputs.remainder width 4
    (List.mem_singleton.mp present)
  remainderValid := original_ne inputs.remainder width 1
  dividesValid := cellKey_ne ctx width 2 1 (by decide)

/-- The actual upper-candidate interface independently satisfies the same complete contract. -/
lemma nativeQuadratic_second_check_separated (inputs : Operands ctx width) :
    Check.Separated (pairRefs inputs).second where
  validModulus := source_free inputs.modulus width 0
  validCandidate := source_free inputs.second width 0
  validZero := fun present => cellKey_ne ctx width 0 4 (by decide)
    (List.mem_singleton.mp present)
  upperModulus := source_free inputs.modulus width 3
  upperCandidate := source_free inputs.second width 3
  upperZero := fun present => cellKey_ne ctx width 3 4 (by decide)
    (List.mem_singleton.mp present)
  upperValid := cellKey_ne ctx width 3 0 (by decide)
  remainderZero := fun present => original_ne inputs.remainder width 4
    (List.mem_singleton.mp present)
  remainderValid := original_ne inputs.remainder width 0
  dividesValid := cellKey_ne ctx width 2 0 (by decide)

/-- The two actual persistent validity bits remain distinct until selection consumes them. -/
lemma nativeQuadratic_checkLayout_valid_distinct (ctx : RuntimeCtx kind) (width : Nat) :
    (firstValid ctx width).key ≠ (secondValid ctx width).key :=
  cellKey_ne ctx width 1 0 (by decide)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout
