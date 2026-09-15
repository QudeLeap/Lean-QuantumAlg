/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Context.Relabeling

/-!
# Exact preservation of unchanged physical entries

When a placement map fixes every actual identity in a layout or context, the
complete original descriptor is unchanged. Storage keys, role, shape and every
wire record are retained together. These laws allow several mapped local
instructions to share precisely the same physical workspace entries.
-/

namespace QuantumAlg

namespace QuantumLayout

/-- Fixing every actual physical identity preserves the complete layout descriptor. -/
theorem relabel_eq_self {count : Nat} (layout : QuantumLayout count) (physical : Nat ↪ Nat)
    (fixed : ∀ identity ∈ layout.identities, physical identity = identity) :
    layout.relabel physical = layout := by
  have wires : (layout.relabel physical).wire = layout.wire := by
    funext index
    have identity := fixed (layout.wire index).identity (List.mem_ofFn.mpr ⟨index, rfl⟩)
    have record :=
      congrArg (fun value => QuantumWire.mk value (layout.wire index).dimension) identity
    exact record.trans (by cases layout.wire index; rfl)
  cases layout
  unfold relabel
  congr 1

end QuantumLayout

namespace OwnedCopyBank

/-- Fixing the complete bank's physical identities preserves every original member layout. -/
theorem relabel_eq_self {copies systems : Nat} (bank : OwnedCopyBank copies systems)
    (physical : Nat ↪ Nat)
    (fixed : ∀ identity ∈ bank.identities, physical identity = identity) :
    bank.relabel physical = bank := by
  have layouts : (bank.relabel physical).layouts = bank.layouts := by
    funext index
    apply QuantumLayout.relabel_eq_self
    intro identity present
    apply fixed identity
    obtain ⟨position, equal⟩ := List.mem_ofFn.mp present
    apply List.mem_map.mpr
    refine ⟨(bank.layouts index).wire position, ?_, equal⟩
    apply List.mem_flatMap.mpr
    exact ⟨bank.layouts index, List.mem_ofFn.mpr ⟨index, rfl⟩,
      List.mem_ofFn.mpr ⟨position, rfl⟩⟩
  cases bank
  simpa only [relabel, ofLayouts, OwnedCopyBank.mk.injEq] using layouts

end OwnedCopyBank

namespace RuntimeEntry

/-- Fixed keys and physical identities preserve the complete entry, including its ownership role. -/
theorem relabel_eq_self {kind : ProblemKind} (entry : RuntimeEntry kind)
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) (fixedKey : keys entry.key = entry.key)
    (fixedWires : ∀ identity ∈ entry.physicalIdx, physical identity = identity) :
    entry.relabel keys physical = entry := by
  cases entry with
  | storage key role shape =>
      exact congrArg (fun key => RuntimeEntry.storage (kind := kind) key role shape) fixedKey
  | borrowedLayout key layout =>
      have same : layout.relabel physical = layout := QuantumLayout.relabel_eq_self _ _ (by
        simpa only [physicalIdx, quantumWires, ← layout_identities_eq_map_wires] using fixedWires)
      exact congrArg₂ (fun key layout => RuntimeEntry.borrowedLayout key layout) fixedKey same
  | ownedLayout key layout =>
      have same : layout.relabel physical = layout := QuantumLayout.relabel_eq_self _ _ (by
        simpa only [physicalIdx, quantumWires, ← layout_identities_eq_map_wires] using fixedWires)
      exact congrArg₂ (fun key layout => RuntimeEntry.ownedLayout key layout) fixedKey same
  | ownedCopies key bank =>
      exact congrArg₂ (fun key bank => RuntimeEntry.ownedCopies key bank) fixedKey
        (OwnedCopyBank.relabel_eq_self _ _ fixedWires)

end RuntimeEntry

namespace RuntimeCtx

/-- Fixing all actually present keys and physical identities preserves the entire sealed context. -/
theorem relabel_eq_self {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (fixedKeys : ∀ key ∈ ctx.keys, keys key = key)
    (fixedWires : ∀ identity ∈ ctx.physicalIdx, physical identity = identity) :
    ctx.relabel keys physical = ctx := by
  have entries : (ctx.relabel keys physical).entries = ctx.entries := by
    change ctx.entries.map (RuntimeEntry.relabel keys physical) = ctx.entries
    conv_rhs => rw [← List.map_id ctx.entries]
    apply List.map_congr_left
    intro entry present
    apply RuntimeEntry.relabel_eq_self
    · exact fixedKeys entry.key (List.mem_map_of_mem present)
    · intro identity member
      apply fixedWires identity
      rw [physicalIdx_eq_flatMap]
      exact List.mem_flatMap.mpr ⟨entry, present, member⟩
  cases ctx
  simpa only [relabel, RuntimeCtx.mk.injEq] using entries

end RuntimeCtx

end QuantumAlg
