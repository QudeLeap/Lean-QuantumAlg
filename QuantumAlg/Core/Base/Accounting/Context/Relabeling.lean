/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Quantum.Relabeling

/-!
# Injective placement of complete live contexts

Storage keys and physical wire identities have separate injective maps. Every
entry retains its constructor, role, classical shape and ordered quantum
dimensions. A layout bank remains one globally disjoint bank, and the mapped
context retains every original entry. This descriptor changes no runtime state;
an executable placement must map native operations and references consistently.
-/

namespace QuantumAlg

namespace OwnedCopyBank

variable {copies systems : Nat}

private theorem mapped_wires (bank : OwnedCopyBank copies systems) (physical : Nat ↪ Nat) :
    (List.ofFn fun index => (bank.layouts index).relabel physical).flatMap QuantumLayout.wires =
      bank.quantumWires.map (QuantumWire.relabel physical) := by
  have ordered :
      (List.ofFn fun index => (bank.layouts index).relabel physical) =
        (List.ofFn bank.layouts).map (fun layout => layout.relabel physical) := by
    rw [List.map_ofFn]
    rfl
  rw [ordered]
  simp only [quantumWires, List.flatMap_map, List.map_flatMap, QuantumLayout.relabel_wires]

/-- Place every system of a bank with the same global injective physical map. -/
def relabel (bank : OwnedCopyBank copies systems) (physical : Nat ↪ Nat) :
    OwnedCopyBank copies systems :=
  ofLayouts (fun index => (bank.layouts index).relabel physical) (by
    rw [mapped_wires, List.map_map]
    simpa only [List.map_map, Function.comp_def, QuantumWire.relabel, quantumWires] using
      (List.nodup_map_iff physical.injective).mpr bank.identitiesNodup)

/-- The complete bank wire list is mapped in its original copy and system order. -/
theorem relabel_quantumWires (bank : OwnedCopyBank copies systems) (physical : Nat ↪ Nat) :
    (bank.relabel physical).quantumWires =
      bank.quantumWires.map (QuantumWire.relabel physical) :=
  mapped_wires bank physical

/-- Every native space coordinate counts the same finite-dimensional systems. -/
theorem relabel_space (bank : OwnedCopyBank copies systems) (physical : Nat ↪ Nat) :
    (bank.relabel physical).space = bank.space := by
  ext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change SpacePool.count (.quantumSystems dimension) (space (bank.relabel physical)) =
        SpacePool.count (.quantumSystems dimension) (space bank)
      rw [count_quantumSystems_space, count_quantumSystems_space, relabel_quantumWires]
      rw [List.map_map]
      rfl

end OwnedCopyBank

namespace RuntimeEntry

variable {kind : ProblemKind}

/-- Place an entry without changing its role, shape or quantum dimensions. -/
def relabel (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    RuntimeEntry kind → RuntimeEntry kind
  | .storage key role shape => .storage (keys key) role shape
  | .borrowedLayout key layout => .borrowedLayout (keys key) (layout.relabel physical)
  | .ownedLayout key layout => .ownedLayout (keys key) (layout.relabel physical)
  | .ownedCopies key bank => .ownedCopies (keys key) (bank.relabel physical)

/-- The declared storage key is mapped by the prescribed storage embedding. -/
theorem relabel_key (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (entry : RuntimeEntry kind) : (entry.relabel keys physical).key = keys entry.key := by
  cases entry <;> rfl

/-- Physical placement maps every original wire, including all bank members. -/
theorem relabel_quantumWires (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (entry : RuntimeEntry kind) :
    (entry.relabel keys physical).quantumWires =
      entry.quantumWires.map (QuantumWire.relabel physical) := by
  cases entry with
  | storage => rfl
  | borrowedLayout => exact QuantumLayout.relabel_wires _ _
  | ownedLayout => exact QuantumLayout.relabel_wires _ _
  | ownedCopies => exact OwnedCopyBank.relabel_quantumWires _ _

/-- Placement retains the complete resident space of an entry. -/
theorem relabel_residentSpace (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (entry : RuntimeEntry kind) :
    (entry.relabel keys physical).residentSpace = entry.residentSpace := by
  cases entry with
  | storage => rfl
  | borrowedLayout => rfl
  | ownedLayout => rfl
  | ownedCopies => exact OwnedCopyBank.relabel_space _ _

/-- The original ownership role gives exactly the same auxiliary-space contribution. -/
theorem relabel_auxiliarySpace (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (entry : RuntimeEntry kind) :
    (entry.relabel keys physical).auxiliarySpace = entry.auxiliarySpace := by
  cases entry with
  | storage key role shape => cases role <;> rfl
  | borrowedLayout => rfl
  | ownedLayout => rfl
  | ownedCopies => exact OwnedCopyBank.relabel_space _ _

end RuntimeEntry

namespace RuntimeCtx

variable {kind : ProblemKind}

private theorem mapped_keys (entries : List (RuntimeEntry kind))
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (entries.map (RuntimeEntry.relabel keys physical)).map RuntimeEntry.key =
      (entries.map RuntimeEntry.key).map keys := by
  simp only [List.map_map, Function.comp_def, RuntimeEntry.relabel_key]

private theorem mapped_wires (entries : List (RuntimeEntry kind))
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (entries.map (RuntimeEntry.relabel keys physical)).flatMap RuntimeEntry.quantumWires =
      (entries.flatMap RuntimeEntry.quantumWires).map (QuantumWire.relabel physical) := by
  simp only [List.flatMap_map, List.map_flatMap, RuntimeEntry.relabel_quantumWires]

/-- Place every entry, with global freshness and non-overlap derived from the two embeddings. -/
def relabel (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    RuntimeCtx kind where
  entries := ctx.entries.map (RuntimeEntry.relabel keys physical)
  keysNodup := by
    rw [mapped_keys]
    exact (List.nodup_map_iff keys.injective).mpr ctx.keysNodup
  identitiesNodup := by
    rw [mapped_wires, List.map_map]
    simpa only [List.map_map, Function.comp_def, QuantumWire.relabel] using
      (List.nodup_map_iff physical.injective).mpr ctx.identitiesNodup

/-- The complete storage-key list has its original order and multiplicity. -/
theorem relabel_keys (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) : (ctx.relabel keys physical).keys = ctx.keys.map keys :=
  mapped_keys ctx.entries keys physical

/-- All original wires remain present in the mapped complete live context. -/
theorem relabel_quantumWires (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (ctx.relabel keys physical).quantumWires =
      ctx.quantumWires.map (QuantumWire.relabel physical) :=
  mapped_wires ctx.entries keys physical

/-- The native circuit physical layout must use exactly this mapped identity list. -/
theorem relabel_physicalIdx (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (ctx.relabel keys physical).physicalIdx = ctx.physicalIdx.map physical := by
  simp only [physicalIdx, relabel_quantumWires, List.map_map]
  rfl

/-- Physical placement preserves the total number of actual quantum systems. -/
theorem relabel_systemCount (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) : (ctx.relabel keys physical).systemCount = ctx.systemCount := by
  simp only [systemCount, relabel_quantumWires, List.length_map]

/-- Complete resident space is unchanged; no entry is filtered from the count. -/
theorem relabel_residentSpace (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (ctx.relabel keys physical).residentSpace = ctx.residentSpace := by
  change (ctx.entries.map _).foldr _ _ = ctx.entries.foldr _ _
  induction ctx.entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, List.foldr_cons, RuntimeEntry.relabel_residentSpace, ih]

/-- Auxiliary space retains every original role without reclassifying caller storage. -/
theorem relabel_auxiliarySpace (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (ctx.relabel keys physical).auxiliarySpace = ctx.auxiliarySpace := by
  change (ctx.entries.map _).foldr _ _ = ctx.entries.foldr _ _
  induction ctx.entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, List.foldr_cons, RuntimeEntry.relabel_auxiliarySpace, ih]

end RuntimeCtx

end QuantumAlg
