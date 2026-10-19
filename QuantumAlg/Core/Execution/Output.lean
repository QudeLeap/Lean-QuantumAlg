/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Store
import Mathlib.Data.List.Perm.Basic

/-!
# Complete live-storage output manifests

An output lists every live storage key exactly once. Its shaped classical
result is either the unique unit value or a structural read of existing
storage. Neither operation allocates a cell, changes a quantum state, or
removes an unobserved resource from the manifest.

State promises are separate specification obligations. This descriptor carries
no claimed quantum state or proof of restoration.
-/

namespace QuantumAlg

/-- Closed observations of the actual final classical store. -/
public inductive OutputRead {kind : ProblemKind} (post : RuntimeCtx kind) : CShape → Type where
  /-- A result with no classical payload requires no extra storage. -/
  | unit : OutputRead post .unit
  /-- Read an existing typed structural reference. -/
  | read {shape : CShape} (input : CInputRef post shape) : OutputRead post shape
  /-- Pair two actual observations, including a payload-free observation on either side. -/
  | product {left right : CShape} (first : OutputRead post left)
      (second : OutputRead post right) : OutputRead post (.product left right)

namespace OutputRead

variable {kind : ProblemKind} {post : RuntimeCtx kind} {shape : CShape}

/-- Obtain the result from the final store without transforming that store. -/
@[expose] public def eval : {shape : CShape} → OutputRead post shape →
    Execution.Store post → shape.Value
  | _, .unit, _ => .unit
  | _, .read input, store => store.read input
  | _, .product first second, store => .product (first.eval store) (second.eval store)

/-- The unit observation returns the unique payload-free value. -/
@[simp] lemma eval_unit (store : Execution.Store post) :
    (OutputRead.unit : OutputRead post .unit).eval store = .unit := rfl

/-- A non-unit observation delegates directly to the existing typed store read. -/
@[simp] lemma eval_read (input : CInputRef post shape) (store : Execution.Store post) :
    (OutputRead.read input).eval store = store.read input := rfl

/-- The output observes exactly the value written to its underlying cell. -/
lemma eval_read_write_same (store : Execution.Store post)
    (written : CWriteRef post shape) (value : shape.Value) :
    (OutputRead.read (.storage written.toCStorageRef)).eval
      (store.write written value) = value :=
  Execution.Store.read_write_same store written value

/-- Pairing output observations reads the same final store and allocates no payload. -/
@[simp] public lemma eval_product {left right : CShape}
    (first : OutputRead post left) (second : OutputRead post right)
    (store : Execution.Store post) :
    (first.product second).eval store = .product (first.eval store) (second.eval store) := rfl

end OutputRead

/-- A complete manifest together with a structural classical result observation. -/
public structure Output {kind : ProblemKind} (post : RuntimeCtx kind) (shape : CShape) where
  /-- Every actual live storage key, in the declared output order. -/
  listing : List StorageKey
  /-- Reordering is allowed, but omission, duplication, and invented keys are not. -/
  complete : listing.Perm post.keys
  /-- The classical result is read from existing storage or has the unit shape. -/
  result : OutputRead post shape

namespace Output

variable {kind : ProblemKind} {post : RuntimeCtx kind} {shape : CShape}

/-- Explicitly expose all live resources in context order with the chosen result readout. -/
@[expose] public def all (post : RuntimeCtx kind) (result : OutputRead post shape) :
    Output post shape where
  listing := post.keys
  complete := List.Perm.refl _
  result := result

/-- The context-order manifest retains every original live key. -/
@[simp] lemma all_listing (post : RuntimeCtx kind) (result : OutputRead post shape) :
    (all post result).listing = post.keys := rfl

/-- Obtain the shaped result through the manifest's actual store observation. -/
@[expose] public def eval (output : Output post shape)
    (store : Execution.Store post) : shape.Value :=
  output.result.eval store

/-- The canonical complete manifest uses exactly its supplied structural readout. -/
@[simp] lemma all_eval (post : RuntimeCtx kind) (result : OutputRead post shape)
    (store : Execution.Store post) :
    (all post result).eval store = result.eval store := rfl

/-- A complete output cannot list the same live resource twice. -/
lemma listing_nodup (output : Output post shape) : output.listing.Nodup :=
  output.complete.symm.nodup post.keysNodup

/-- A key is listed precisely when it is live in the output context. -/
lemma mem_listing_iff (output : Output post shape) (key : StorageKey) :
    key ∈ output.listing ↔ key ∈ post.keys :=
  output.complete.mem_iff

/-- Every actual entry, including borrowed storage and complete layout banks, is listed. -/
lemma entry_key_mem_listing (output : Output post shape) (entry : RuntimeEntry kind)
    (live : entry ∈ post.entries) : entry.key ∈ output.listing :=
  (output.mem_listing_iff entry.key).mpr (List.mem_map_of_mem live)

/-- Every listed key names an actual live entry; a manifest cannot invent storage. -/
lemma exists_entry_of_mem_listing (output : Output post shape) (key : StorageKey)
    (listed : key ∈ output.listing) :
    ∃ entry ∈ post.entries, entry.key = key :=
  List.mem_map.mp ((output.mem_listing_iff key).mp listed)

/-- The complete manifest contains exactly as many keys as there are live entries. -/
lemma listing_length (output : Output post shape) :
    output.listing.length = post.entries.length := by
  simpa only [RuntimeCtx.keys, List.length_map] using output.complete.length_eq

end Output

end QuantumAlg
