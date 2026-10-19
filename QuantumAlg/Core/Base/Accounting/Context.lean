/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Kind
public import QuantumAlg.Core.Base.Accounting.Shape
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Space
public import QuantumAlg.Core.Base.Layout.Quantum
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Disjoint
public import Batteries.Data.List.Basic

/-!
# Typed live-storage contexts

A context records actual classical cells and actual finite-dimensional quantum
wires. Storage keys and physical wire identities are both globally unique.
Every quantum wire, including every member of a layout bank, contributes to
one context-wide joint register. No state or independence assumption is stored
in the placement descriptor.

Resident space counts all live entries. Auxiliary space uses their fixed
storage roles: borrowed input, supplied quantum interface, and designated
output storage are excluded, while workspace, retained values, and
algorithm-owned quantum storage are included.
Designating one output cell does not remove any other entry or change a
quantum state. Complete Output and state restoration are execution contracts;
they are not context filters or liveness shortcuts.
-/

section

namespace QuantumAlg

/-- Stable identity of one live storage entry. -/
public structure StorageKey where
  /-- Numeric identity used to reject duplicate live entries. -/
  id : Nat
deriving DecidableEq

/-- Fixed accounting role of a classical storage cell. -/
public inductive StorageRole where
  /-- Caller-supplied input remains resident but is excluded from auxiliary
  space, as for a read-only input tape [CGM+25, main.tex:231]. -/
  | borrowedInput
  /-- Read/write work storage [CGM+25, main.tex:231]. -/
  | workspace
  /-- Intermediate values kept for later use or uncomputation
  [RNSL17, ECDLP.tex:446]. -/
  | retained
  /-- Dedicated output storage remains resident and is excluded from
  auxiliary space [CGM+25, main.tex:529]. This role does not end execution. -/
  | finalOutput
deriving DecidableEq

private lemma layout_identities_eq_map_wires {systemCount : Nat}
    (layout : QuantumLayout systemCount) :
    layout.identities = layout.wires.map QuantumWire.identity := by
  simp only [QuantumLayout.identities, QuantumLayout.wires, List.map_ofFn]
  rfl

private lemma layout_dimensionCount_eq_count_wires {systemCount : Nat}
    (layout : QuantumLayout systemCount) (dimension : ℕ+) :
    layout.dimensionCount dimension =
      (layout.wires.map QuantumWire.dimension).count dimension := by
  simp only [QuantumLayout.dimensionCount, QuantumLayout.dimensions,
    QuantumLayout.wires, List.map_ofFn]
  rfl

private lemma dimensionCount_ofWires (wires : List QuantumWire)
    (distinct : (wires.map QuantumWire.identity).Nodup) (dimension : ℕ+) :
    (QuantumLayout.ofWires wires distinct).dimensionCount dimension =
      (wires.map QuantumWire.dimension).count dimension := by
  rw [layout_dimensionCount_eq_count_wires, QuantumLayout.wires_ofWires]

/-- A finite family of actual layouts with one global non-overlap certificate.
This is a placement descriptor: all of its wires enter the same joint state,
without a separate state payload or a separability promise. -/
public structure OwnedCopyBank (copyCount systemsPerCopy : Nat) where
  private mk ::
  /-- Actual physical placement of each supplied group of systems. -/
  layouts : Fin copyCount → QuantumLayout systemsPerCopy
  /-- No physical identity occurs in two positions anywhere in the bank. -/
  identitiesNodup :
    (((List.ofFn layouts).flatMap QuantumLayout.wires).map QuantumWire.identity).Nodup

namespace OwnedCopyBank

/-- Construct the bank from its layouts and actual global identity certificate. -/
public def ofLayouts {copyCount systemsPerCopy : Nat}
    (layouts : Fin copyCount → QuantumLayout systemsPerCopy)
    (distinct :
      (((List.ofFn layouts).flatMap QuantumLayout.wires).map QuantumWire.identity).Nodup) :
    OwnedCopyBank copyCount systemsPerCopy :=
  ⟨layouts, distinct⟩

/-- Every actual wire in copy/index order. -/
public def quantumWires {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) : List QuantumWire :=
  (List.ofFn bank.layouts).flatMap QuantumLayout.wires

/-- Physical identities of all the bank's wires. -/
public def identities {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) : List Nat :=
  bank.quantumWires.map QuantumWire.identity

/-- The bank's complete physical layout, with every member included. -/
public def layout {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) :
    QuantumLayout bank.quantumWires.length :=
  QuantumLayout.ofWires bank.quantumWires bank.identitiesNodup

@[simp] lemma layout_wires {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) :
    bank.layout.wires = bank.quantumWires :=
  QuantumLayout.wires_ofWires bank.quantumWires bank.identitiesNodup

@[simp] lemma layout_identities {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) :
    bank.layout.identities = bank.identities := by
  rw [layout_identities_eq_map_wires, layout_wires]
  rfl

/-- Native space derived from the dimensions of all the bank's actual wires. -/
public def space {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) : SpacePool .quantum :=
  SpacePool.ofQuantumLayout bank.layout

@[simp] lemma count_classicalBits_space {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) :
    SpacePool.count .classicalBits bank.space = 0 := rfl

@[simp] lemma count_quantumSystems_space {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) bank.space =
      (bank.quantumWires.map QuantumWire.dimension).count dimension :=
  dimensionCount_ofWires bank.quantumWires bank.identitiesNodup dimension

end OwnedCopyBank

/-- One live storage entry. Only quantum contexts admit quantum layouts. -/
public inductive RuntimeEntry : ProblemKind → Type where
  | storage {kind : ProblemKind}
      (key : StorageKey) (role : StorageRole) (shape : CShape) : RuntimeEntry kind
  /-- Caller-owned physical systems. Restoration is an execution obligation,
  not a consequence of this placement tag [RNSL17, ECDLP.tex:302]. -/
  | borrowedLayout (key : StorageKey) {systemCount : Nat}
      (layout : QuantumLayout systemCount) : RuntimeEntry .quantum
  /-- Caller-supplied systems that the algorithm may transform and retain.
  They are part of the input/output interface, rather than borrowed state that
  must be restored or algorithm-allocated auxiliary storage. -/
  | suppliedLayout (key : StorageKey) {systemCount : Nat}
      (layout : QuantumLayout systemCount) : RuntimeEntry .quantum
  /-- Algorithm-owned systems, with actual finite dimensions and identities. -/
  | ownedLayout (key : StorageKey) {systemCount : Nat}
      (layout : QuantumLayout systemCount) : RuntimeEntry .quantum
  /-- An owned family of actual layouts; all members remain in the joint frame. -/
  | ownedCopies (key : StorageKey) {copyCount systemsPerCopy : Nat}
      (bank : OwnedCopyBank copyCount systemsPerCopy) : RuntimeEntry .quantum

namespace RuntimeEntry

/-- Stable storage key of an entry. -/
public def key {kind : ProblemKind} : RuntimeEntry kind → StorageKey
  | .storage key _ _ => key
  | .borrowedLayout key _ => key
  | .suppliedLayout key _ => key
  | .ownedLayout key _ => key
  | .ownedCopies key _ => key

/-- All physical wire records owned or borrowed by this entry. -/
@[implicit_reducible]
public def quantumWires {kind : ProblemKind} : RuntimeEntry kind → List QuantumWire
  | .storage _ _ _ => []
  | .borrowedLayout _ layout => layout.wires
  | .suppliedLayout _ layout => layout.wires
  | .ownedLayout _ layout => layout.wires
  | .ownedCopies _ bank => bank.quantumWires

/-- Actual physical identities, independent of the dimensions attached to them. -/
public def physicalIdx {kind : ProblemKind} (entry : RuntimeEntry kind) : List Nat :=
  entry.quantumWires.map QuantumWire.identity

/-- Native resident space includes every live entry. -/
public def residentSpace {kind : ProblemKind} : RuntimeEntry kind → SpacePool kind
  | .storage _ _ shape => SpacePool.ofShape shape
  | .borrowedLayout _ layout => SpacePool.ofQuantumLayout layout
  | .suppliedLayout _ layout => SpacePool.ofQuantumLayout layout
  | .ownedLayout _ layout => SpacePool.ofQuantumLayout layout
  | .ownedCopies _ bank => bank.space

/-- Native auxiliary space is derived from fixed roles, without removing wires. -/
public def auxiliarySpace {kind : ProblemKind} : RuntimeEntry kind → SpacePool kind
  | .storage _ .borrowedInput _ => 0
  | .storage _ .workspace shape => SpacePool.ofShape shape
  | .storage _ .retained shape => SpacePool.ofShape shape
  | .storage _ .finalOutput _ => 0
  | .borrowedLayout _ _ => 0
  | .suppliedLayout _ _ => 0
  | .ownedLayout _ layout => SpacePool.ofQuantumLayout layout
  | .ownedCopies _ bank => bank.space

/-- An entry's quantum-space coordinate counts exactly its actual matching wires. -/
lemma residentSpace_quantumSystems (entry : RuntimeEntry .quantum) (dimension : ℕ+) :
    entry.residentSpace (.quantumSystems dimension) =
      (entry.quantumWires.map QuantumWire.dimension).count dimension := by
  cases entry with
  | storage => rfl
  | borrowedLayout _ layout => exact layout_dimensionCount_eq_count_wires layout dimension
  | suppliedLayout _ layout => exact layout_dimensionCount_eq_count_wires layout dimension
  | ownedLayout _ layout => exact layout_dimensionCount_eq_count_wires layout dimension
  | ownedCopies _ bank => exact bank.count_quantumSystems_space dimension

end RuntimeEntry

/-- A sealed live context with readable entries and invariant certificates.
There is no terminal flag or detached footprint: every entry remains live
until a separately typed execution transition changes the context. -/
public structure RuntimeCtx (kind : ProblemKind) where
  private mk ::
  /-- Actual live entries, in stable construction order. -/
  entries : List (RuntimeEntry kind)
  /-- Storage identities are globally unique. -/
  keysNodup : (entries.map RuntimeEntry.key).Nodup
  /-- Every physical identity occurs once, even across dimensions and banks. -/
  identitiesNodup :
    ((entries.flatMap RuntimeEntry.quantumWires).map QuantumWire.identity).Nodup

namespace RuntimeCtx

/-- Construct a complete live context from its actual entries and global uniqueness proofs. -/
public def ofEntries {kind : ProblemKind} (entries : List (RuntimeEntry kind))
    (keysNodup : (entries.map RuntimeEntry.key).Nodup)
    (identitiesNodup :
      ((entries.flatMap RuntimeEntry.quantumWires).map QuantumWire.identity).Nodup) :
    RuntimeCtx kind :=
  ⟨entries, keysNodup, identitiesNodup⟩

/-- Live storage keys in stable entry order. -/
public def keys {kind : ProblemKind} (ctx : RuntimeCtx kind) : List StorageKey :=
  ctx.entries.map RuntimeEntry.key

/-- Deterministic fresh key for an internal lexical storage scope. -/
public def canonicalFreshKey {kind : ProblemKind} (ctx : RuntimeCtx kind) : StorageKey :=
  ⟨(ctx.keys.map StorageKey.id).foldr Nat.max 0 + 1⟩

/-- The deterministic lexical key is absent from its source context. -/
lemma canonicalFreshKey_fresh {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    canonicalFreshKey ctx ∉ ctx.keys := by
  intro member
  have memberIds : (canonicalFreshKey ctx).id ∈ ctx.keys.map StorageKey.id :=
    List.mem_map_of_mem member
  have bounded : (canonicalFreshKey ctx).id ≤
      (ctx.keys.map StorageKey.id).foldr Nat.max 0 :=
    List.le_max_of_le' 0 memberIds le_rfl
  exact (Nat.not_succ_le_self _) (by simpa [canonicalFreshKey] using bounded)

/-- The canonical key is available for the next actual storage allocation. -/
public lemma runtimeCtx_canonicalFreshKey_fresh {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    ctx.canonicalFreshKey ∉ ctx.keys := canonicalFreshKey_fresh ctx

/-- Every live physical quantum wire, including all members of every bank. -/
@[reducible] public def quantumWires {kind : ProblemKind}
    (ctx : RuntimeCtx kind) : List QuantumWire :=
  ctx.entries.flatMap RuntimeEntry.quantumWires

/-- Physical identities of the complete live joint frame. -/
public def physicalIdx {kind : ProblemKind} (ctx : RuntimeCtx kind) : List Nat :=
  ctx.quantumWires.map QuantumWire.identity

/-- Physical identities are the identities of the complete live wire list. -/
public lemma physicalIdx_eq_map_quantumWires {kind : ProblemKind}
    (ctx : RuntimeCtx kind) :
    ctx.physicalIdx = ctx.quantumWires.map QuantumWire.identity := by rfl

/-- Entry-wise and context-wide physical projections use the same identities. -/
lemma physicalIdx_eq_flatMap {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    ctx.physicalIdx = ctx.entries.flatMap RuntimeEntry.physicalIdx := by
  simp only [physicalIdx, quantumWires, List.map_flatMap]
  rfl

/-- Number of actual finite-dimensional systems; this is not a qubit count. -/
@[reducible] public def systemCount {kind : ProblemKind} (ctx : RuntimeCtx kind) : Nat :=
  ctx.quantumWires.length

@[simp] lemma physicalIdx_length {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    ctx.physicalIdx.length = ctx.systemCount := by
  simp only [physicalIdx, List.length_map, systemCount]

/-- One actual layout for every live quantum wire. Classical contexts derive
an empty layout, so the same state interpreter can handle both problem kinds. -/
@[reducible] public def quantumLayout {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    QuantumLayout ctx.systemCount :=
  QuantumLayout.ofWires ctx.quantumWires ctx.identitiesNodup

/-- The joint quantum register is determined by actual wire dimensions. -/
public abbrev register {kind : ProblemKind} (ctx : RuntimeCtx kind) : Register :=
  ctx.quantumLayout.register

public lemma quantumLayout_wires {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    ctx.quantumLayout.wires = ctx.quantumWires :=
  QuantumLayout.wires_ofWires ctx.quantumWires ctx.identitiesNodup

@[simp] lemma quantumLayout_identities {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    ctx.quantumLayout.identities = ctx.physicalIdx := by
  rw [layout_identities_eq_map_wires, quantumLayout_wires]
  rfl

/-- The public joint layout carries exactly the live context's physical identities. -/
public lemma runtimeCtx_quantumLayout_identities {kind : ProblemKind}
    (ctx : RuntimeCtx kind) : ctx.quantumLayout.identities = ctx.physicalIdx :=
  quantumLayout_identities ctx

private lemma classicalEntries_quantumWires (entries : List (RuntimeEntry .classical)) :
    entries.flatMap RuntimeEntry.quantumWires = [] := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases entry
      exact ih

@[simp] lemma quantumWires_classical (ctx : RuntimeCtx .classical) :
    ctx.quantumWires = [] :=
  classicalEntries_quantumWires ctx.entries

lemma systemCount_classical (ctx : RuntimeCtx .classical) :
    ctx.systemCount = 0 := by
  simp only [systemCount, quantumWires_classical, List.length_nil]

/-- The empty live context. -/
@[reducible] public def empty {kind : ProblemKind} : RuntimeCtx kind where
  entries := []
  keysNodup := by simp
  identitiesNodup := by simp

/-- The empty context has no live storage keys. -/
@[simp] public lemma keys_empty {kind : ProblemKind} :
    (empty : RuntimeCtx kind).keys = [] := by rfl

private lemma empty_quantumWires_eq {kind : ProblemKind} :
    (empty : RuntimeCtx kind).quantumWires = [] := rfl

/-- An empty context contains no physical quantum wires. -/
public lemma runtimeCtx_empty_quantumWires {kind : ProblemKind} :
    (empty : RuntimeCtx kind).quantumWires = [] := empty_quantumWires_eq

private lemma empty_physicalIdx_eq {kind : ProblemKind} :
    (empty : RuntimeCtx kind).physicalIdx = [] := rfl

/-- An empty context has no occupied physical identities. -/
public lemma runtimeCtx_empty_physicalIdx {kind : ProblemKind} :
    (empty : RuntimeCtx kind).physicalIdx = [] := empty_physicalIdx_eq

@[implicit_reducible]
private def addStorage {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (role : StorageRole) (shape : CShape)
    (fresh : key ∉ ctx.keys) : RuntimeCtx kind where
  entries := .storage key role shape :: ctx.entries
  keysNodup := List.nodup_cons.mpr ⟨fresh, ctx.keysNodup⟩
  identitiesNodup := ctx.identitiesNodup

/-- Add borrowed classical input with storage derived from its closed shape. -/
public def addBorrowedInput {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  addStorage ctx key .borrowedInput shape fresh

/-- Add classical workspace with storage derived from its closed shape. -/
public def addWorkspace {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  addStorage ctx key .workspace shape fresh

/-- Keep a new intermediate classical value live for subsequent instructions. -/
@[implicit_reducible]
public def addRetained {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  addStorage ctx key .retained shape fresh

/-- Retaining a classical cell adds exactly its fresh storage key. -/
@[simp] public lemma keys_addRetained {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).keys = key :: ctx.keys := by rfl

/-- Add dedicated output storage without removing or retagging any live entry. -/
public def addFinalOutput {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  addStorage ctx key .finalOutput shape fresh

@[simp] lemma quantumWires_addBorrowedInput {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addBorrowedInput key shape fresh).quantumWires = ctx.quantumWires := rfl

@[simp] lemma quantumWires_addWorkspace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addWorkspace key shape fresh).quantumWires = ctx.quantumWires := rfl

@[simp] lemma quantumWires_addRetained {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).quantumWires = ctx.quantumWires := rfl

@[simp] lemma quantumWires_addFinalOutput {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addFinalOutput key shape fresh).quantumWires = ctx.quantumWires := rfl

/-- Adding a classical result cell preserves the full joint quantum carrier. -/
@[simp] lemma register_addRetained {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).register = ctx.register := rfl

/-- Allocating a retained classical cell preserves every physical quantum wire. -/
public lemma runtimeCtx_quantumWires_addRetained {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).quantumWires = ctx.quantumWires :=
  quantumWires_addRetained ctx key shape fresh

/-- Allocating a retained classical cell preserves the exact complete quantum register. -/
public lemma runtimeCtx_register_addRetained {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).register = ctx.register :=
  register_addRetained ctx key shape fresh

/-- Add borrowed systems after checking key freshness and physical disjointness. -/
@[reducible] public def addBorrowedLayout (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) : RuntimeCtx .quantum where
  entries := .borrowedLayout key layout :: ctx.entries
  keysNodup := List.nodup_cons.mpr ⟨fresh, ctx.keysNodup⟩
  identitiesNodup := by
    change ((layout.wires ++ ctx.quantumWires).map QuantumWire.identity).Nodup
    rw [List.map_append, ← layout_identities_eq_map_wires]
    exact layout.identities_nodup.append ctx.identitiesNodup disjoint

/-- Add a caller-supplied mutable quantum interface after checking key
freshness and physical disjointness. These systems stay resident, may change,
and do not contribute to auxiliary space. -/
@[reducible] public def addSuppliedLayout (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) : RuntimeCtx .quantum where
  entries := .suppliedLayout key layout :: ctx.entries
  keysNodup := List.nodup_cons.mpr ⟨fresh, ctx.keysNodup⟩
  identitiesNodup := by
    change ((layout.wires ++ ctx.quantumWires).map QuantumWire.identity).Nodup
    rw [List.map_append, ← layout_identities_eq_map_wires]
    exact layout.identities_nodup.append ctx.identitiesNodup disjoint

/-- Add owned systems with their actual dimensions and physical placement. -/
@[reducible] public def addOwnedLayout (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) : RuntimeCtx .quantum where
  entries := .ownedLayout key layout :: ctx.entries
  keysNodup := List.nodup_cons.mpr ⟨fresh, ctx.keysNodup⟩
  identitiesNodup := by
    change ((layout.wires ++ ctx.quantumWires).map QuantumWire.identity).Nodup
    rw [List.map_append, ← layout_identities_eq_map_wires]
    exact layout.identities_nodup.append ctx.identitiesNodup disjoint

/-- Allocating an owned layout adds exactly its fresh storage key. -/
@[simp] public lemma keys_addOwnedLayout (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {systemCount : Nat} (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addOwnedLayout key layout fresh disjoint).keys = key :: ctx.keys := by rfl

private lemma quantumWires_addOwnedLayout_eq (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {systemCount : Nat} (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addOwnedLayout key layout fresh disjoint).quantumWires =
      layout.wires ++ ctx.quantumWires := rfl

/-- Allocating an owned layout prepends its actual wires to the existing complete layout. -/
public lemma runtimeCtx_quantumWires_addOwnedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addOwnedLayout key layout fresh disjoint).quantumWires =
      layout.wires ++ ctx.quantumWires :=
  quantumWires_addOwnedLayout_eq ctx key layout fresh disjoint

private lemma quantumWires_addSuppliedLayout_eq (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addSuppliedLayout key layout fresh disjoint).quantumWires =
      layout.wires ++ ctx.quantumWires := rfl

/-- Adding a supplied interface prepends its actual wires to the complete layout. -/
public lemma runtimeCtx_quantumWires_addSuppliedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addSuppliedLayout key layout fresh disjoint).quantumWires =
      layout.wires ++ ctx.quantumWires :=
  quantumWires_addSuppliedLayout_eq ctx key layout fresh disjoint

/-- Add every wire of an owned layout bank to the same context-wide joint frame. -/
@[reducible] public def addOwnedCopies (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {copyCount systemsPerCopy : Nat} (bank : OwnedCopyBank copyCount systemsPerCopy)
    (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint bank.identities ctx.physicalIdx) : RuntimeCtx .quantum where
  entries := .ownedCopies key bank :: ctx.entries
  keysNodup := List.nodup_cons.mpr ⟨fresh, ctx.keysNodup⟩
  identitiesNodup := by
    change ((bank.quantumWires ++ ctx.quantumWires).map QuantumWire.identity).Nodup
    rw [List.map_append]
    exact bank.identitiesNodup.append ctx.identitiesNodup disjoint

/-- Resident space derived by folding every live entry. -/
public def residentSpace {kind : ProblemKind} (ctx : RuntimeCtx kind) : SpacePool kind :=
  ctx.entries.foldr (fun entry total => entry.residentSpace + total) 0

/-- Auxiliary space derived from the same entries and their fixed roles. -/
public def auxiliarySpace {kind : ProblemKind} (ctx : RuntimeCtx kind) : SpacePool kind :=
  ctx.entries.foldr (fun entry total => entry.auxiliarySpace + total) 0

/-- Decidable key-level separation of two sealed contexts. -/
public def KeysDisjoint {kind : ProblemKind} (left right : RuntimeCtx kind) : Prop :=
  Disjoint left.keys.toFinset right.keys.toFinset

instance instDecidableKeysDisjoint {kind : ProblemKind}
    (left right : RuntimeCtx kind) : Decidable (KeysDisjoint left right) := by
  unfold KeysDisjoint
  infer_instance

/-- Decidable physical separation, independent of each system's dimension. -/
public def PhysicallyDisjoint {kind : ProblemKind} (left right : RuntimeCtx kind) : Prop :=
  Disjoint left.physicalIdx.toFinset right.physicalIdx.toFinset

instance instDecidablePhysicallyDisjoint {kind : ProblemKind}
    (left right : RuntimeCtx kind) : Decidable (PhysicallyDisjoint left right) := by
  unfold PhysicallyDisjoint
  infer_instance

/-- Both storage-key and physical-identity separation. -/
public def StorageDisjoint {kind : ProblemKind} (left right : RuntimeCtx kind) : Prop :=
  KeysDisjoint left right ∧ PhysicallyDisjoint left right

/-- Storage separation includes separation of live storage keys. -/
public lemma keysDisjoint_of_storageDisjoint {kind : ProblemKind}
    {left right : RuntimeCtx kind} (disjoint : StorageDisjoint left right) :
    KeysDisjoint left right := disjoint.1

/-- Storage separation includes separation of physical wire identities. -/
public lemma physicallyDisjoint_of_storageDisjoint {kind : ProblemKind}
    {left right : RuntimeCtx kind} (disjoint : StorageDisjoint left right) :
    PhysicallyDisjoint left right :=
  disjoint.2

instance instDecidableStorageDisjoint {kind : ProblemKind}
    (left right : RuntimeCtx kind) : Decidable (StorageDisjoint left right) := by
  unfold StorageDisjoint
  infer_instance

/-- The decidable key guard is equivalent to list disjointness. -/
lemma keysDisjoint_iff_listDisjoint {kind : ProblemKind}
    (left right : RuntimeCtx kind) :
    KeysDisjoint left right ↔ List.Disjoint left.keys right.keys :=
  List.disjoint_toFinset_iff_disjoint

/-- The decidable physical guard is equivalent to list disjointness. -/
public lemma physicallyDisjoint_iff_listDisjoint {kind : ProblemKind}
    (left right : RuntimeCtx kind) :
    PhysicallyDisjoint left right ↔ List.Disjoint left.physicalIdx right.physicalIdx :=
  List.disjoint_toFinset_iff_disjoint

/-- Storage separation can be checked on the two observable lists. -/
public lemma storageDisjoint_iff_listDisjoint {kind : ProblemKind}
    (left right : RuntimeCtx kind) :
    StorageDisjoint left right ↔
      List.Disjoint left.keys right.keys ∧
        List.Disjoint left.physicalIdx right.physicalIdx :=
  and_congr (keysDisjoint_iff_listDisjoint left right)
    (physicallyDisjoint_iff_listDisjoint left right)

/-- Append two contexts only after checking both forms of physical ownership. -/
public def disjointUnion {kind : ProblemKind} (left right : RuntimeCtx kind)
    (disjoint : StorageDisjoint left right) : RuntimeCtx kind where
  entries := left.entries ++ right.entries
  keysNodup := by
    rw [List.map_append]
    exact left.keysNodup.append right.keysNodup
      ((keysDisjoint_iff_listDisjoint left right).mp disjoint.1)
  identitiesNodup := by
    rw [List.flatMap_append, List.map_append]
    exact left.identitiesNodup.append right.identitiesNodup
      ((physicallyDisjoint_iff_listDisjoint left right).mp disjoint.2)

@[simp] public lemma keys_disjointUnion {kind : ProblemKind}
    (left right : RuntimeCtx kind) (disjoint : StorageDisjoint left right) :
    (disjointUnion left right disjoint).keys = left.keys ++ right.keys := by
  simp [keys, disjointUnion]

@[simp] public lemma quantumWires_disjointUnion {kind : ProblemKind}
    (left right : RuntimeCtx kind) (disjoint : StorageDisjoint left right) :
    (disjointUnion left right disjoint).quantumWires =
      left.quantumWires ++ right.quantumWires := by
  simp only [quantumWires, disjointUnion, List.flatMap_append]

@[simp] public lemma physicalIdx_disjointUnion {kind : ProblemKind}
    (left right : RuntimeCtx kind) (disjoint : StorageDisjoint left right) :
    (disjointUnion left right disjoint).physicalIdx =
      left.physicalIdx ++ right.physicalIdx := by
  simp only [physicalIdx, quantumWires_disjointUnion, List.map_append]

lemma systemCount_disjointUnion {kind : ProblemKind}
    (left right : RuntimeCtx kind) (disjoint : StorageDisjoint left right) :
    (disjointUnion left right disjoint).systemCount = left.systemCount + right.systemCount := by
  simp only [systemCount, quantumWires_disjointUnion, List.length_append]

private lemma foldSpace_append {kind : ProblemKind}
    (project : RuntimeEntry kind → SpacePool kind)
    (left right : List (RuntimeEntry kind)) :
    (left ++ right).foldr (fun entry total => project entry + total) 0 =
      left.foldr (fun entry total => project entry + total) 0 +
        right.foldr (fun entry total => project entry + total) 0 := by
  induction left with
  | nil =>
      ext axis
      simp
  | cons entry entries ih =>
      simp only [List.cons_append, List.foldr_cons]
      rw [ih]
      ext axis
      exact (Nat.add_assoc _ _ _).symm

@[simp] public lemma residentSpace_disjointUnion {kind : ProblemKind}
    (left right : RuntimeCtx kind) (disjoint : StorageDisjoint left right) :
    (disjointUnion left right disjoint).residentSpace =
      left.residentSpace + right.residentSpace := by
  exact foldSpace_append RuntimeEntry.residentSpace left.entries right.entries

@[simp] lemma auxiliarySpace_disjointUnion {kind : ProblemKind}
    (left right : RuntimeCtx kind) (disjoint : StorageDisjoint left right) :
    (disjointUnion left right disjoint).auxiliarySpace =
      left.auxiliarySpace + right.auxiliarySpace := by
  exact foldSpace_append RuntimeEntry.auxiliarySpace left.entries right.entries

@[simp] public lemma residentSpace_empty {kind : ProblemKind} :
    residentSpace (empty : RuntimeCtx kind) = 0 := by rfl

@[simp] lemma auxiliarySpace_empty {kind : ProblemKind} :
    auxiliarySpace (empty : RuntimeCtx kind) = 0 := rfl

@[simp] lemma residentSpace_addBorrowedInput {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addBorrowedInput key shape fresh).residentSpace =
      SpacePool.ofShape shape + ctx.residentSpace := rfl

@[simp] lemma auxiliarySpace_addBorrowedInput {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addBorrowedInput key shape fresh).auxiliarySpace = ctx.auxiliarySpace := by
  ext axis
  simp [auxiliarySpace, addBorrowedInput, addStorage, RuntimeEntry.auxiliarySpace]

@[simp] lemma residentSpace_addWorkspace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addWorkspace key shape fresh).residentSpace =
      SpacePool.ofShape shape + ctx.residentSpace := rfl

@[simp] lemma auxiliarySpace_addWorkspace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addWorkspace key shape fresh).auxiliarySpace =
      SpacePool.ofShape shape + ctx.auxiliarySpace := rfl

@[simp] public lemma residentSpace_addRetained {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).residentSpace =
      SpacePool.ofShape shape + ctx.residentSpace := by rfl

@[simp] lemma auxiliarySpace_addRetained {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).auxiliarySpace =
      SpacePool.ofShape shape + ctx.auxiliarySpace := rfl

@[simp] lemma residentSpace_addFinalOutput {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addFinalOutput key shape fresh).residentSpace =
      SpacePool.ofShape shape + ctx.residentSpace := rfl

@[simp] lemma auxiliarySpace_addFinalOutput {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ctx.addFinalOutput key shape fresh).auxiliarySpace = ctx.auxiliarySpace := by
  ext axis
  simp [auxiliarySpace, addFinalOutput, addStorage, RuntimeEntry.auxiliarySpace]

@[simp] lemma residentSpace_addBorrowedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addBorrowedLayout key layout fresh disjoint).residentSpace =
      SpacePool.ofQuantumLayout layout + ctx.residentSpace := rfl

@[simp] lemma auxiliarySpace_addBorrowedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addBorrowedLayout key layout fresh disjoint).auxiliarySpace = ctx.auxiliarySpace := by
  ext axis
  simp [auxiliarySpace, RuntimeEntry.auxiliarySpace]

@[simp] lemma residentSpace_addSuppliedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addSuppliedLayout key layout fresh disjoint).residentSpace =
      SpacePool.ofQuantumLayout layout + ctx.residentSpace := rfl

@[simp] lemma auxiliarySpace_addSuppliedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addSuppliedLayout key layout fresh disjoint).auxiliarySpace = ctx.auxiliarySpace := by
  ext axis
  simp [auxiliarySpace, RuntimeEntry.auxiliarySpace]

@[simp] public lemma residentSpace_addOwnedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addOwnedLayout key layout fresh disjoint).residentSpace =
      SpacePool.ofQuantumLayout layout + ctx.residentSpace := by rfl

@[simp] lemma auxiliarySpace_addOwnedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addOwnedLayout key layout fresh disjoint).auxiliarySpace =
      SpacePool.ofQuantumLayout layout + ctx.auxiliarySpace := rfl

@[simp] lemma residentSpace_addOwnedCopies (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {copyCount systemCount : Nat}
    (bank : OwnedCopyBank copyCount systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint bank.identities ctx.physicalIdx) :
    (ctx.addOwnedCopies key bank fresh disjoint).residentSpace =
      bank.space + ctx.residentSpace := rfl

@[simp] lemma auxiliarySpace_addOwnedCopies (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {copyCount systemCount : Nat}
    (bank : OwnedCopyBank copyCount systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint bank.identities ctx.physicalIdx) :
    (ctx.addOwnedCopies key bank fresh disjoint).auxiliarySpace =
      bank.space + ctx.auxiliarySpace := rfl

private lemma residentSpace_quantumSystems_entries
    (entries : List (RuntimeEntry .quantum)) (dimension : ℕ+) :
    (entries.foldr
      (fun (entry : RuntimeEntry .quantum) (total : SpacePool .quantum) =>
        entry.residentSpace + total) 0)
        (.quantumSystems dimension) =
      ((entries.flatMap RuntimeEntry.quantumWires).map QuantumWire.dimension).count dimension := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      change entry.residentSpace (.quantumSystems dimension) +
          (entries.foldr
            (fun (entry : RuntimeEntry .quantum) (total : SpacePool .quantum) =>
              entry.residentSpace + total) 0)
            (.quantumSystems dimension) =
        ((entry.quantumWires ++ entries.flatMap RuntimeEntry.quantumWires).map
          QuantumWire.dimension).count dimension
      rw [List.map_append, List.count_append, RuntimeEntry.residentSpace_quantumSystems, ih]

/-- The resident ledger and the complete joint layout count exactly the same
systems at every dimension, including all bank members. -/
lemma residentSpace_quantumSystems (ctx : RuntimeCtx .quantum) (dimension : ℕ+) :
    ctx.residentSpace (.quantumSystems dimension) =
      ctx.quantumLayout.dimensionCount dimension := by
  rw [quantumLayout, dimensionCount_ofWires]
  exact residentSpace_quantumSystems_entries ctx.entries dimension

end RuntimeCtx

namespace AccountingContextFixtures

private def key0 : StorageKey := ⟨0⟩
private def key1 : StorageKey := ⟨1⟩
private def key2 : StorageKey := ⟨2⟩

private def workspace : RuntimeCtx .classical :=
  RuntimeCtx.empty.addWorkspace key0 (.bits 8) (by decide)

private def withOutput : RuntimeCtx .classical :=
  workspace.addFinalOutput key1 .bit (by decide)

/-- Designating output storage retains the existing workspace and its charge. -/
example : withOutput.keys = [key1, key0] := by decide
example : withOutput.residentSpace .classicalBits = 9 := by decide
example : withOutput.auxiliarySpace .classicalBits = 8 := by decide

/-- One actual system with its declared dimension and physical identity. -/
private def oneSystem (identity : Nat) (dimension : ℕ+) : QuantumLayout 1 :=
  QuantumLayout.uniform 1 dimension (fun _ => identity)
    (fun _ _ _ => Subsingleton.elim _ _)

private def qubitContext : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout key0 (oneSystem 10 2) (by decide)
    (List.disjoint_toFinset_iff_disjoint.mp (by decide))

private def mixedContext : RuntimeCtx .quantum :=
  qubitContext.addBorrowedLayout key1 (oneSystem 11 3) (by decide)
    (List.disjoint_toFinset_iff_disjoint.mp (by decide))

/-- The complete joint frame contains both dimensions without a binary encoding. -/
example : mixedContext.systemCount = 2 := by decide
example : mixedContext.physicalIdx = [11, 10] := by decide
example : mixedContext.residentSpace (.quantumSystems 2) = 1 := by decide
example : mixedContext.residentSpace (.quantumSystems 3) = 1 := by decide
example : mixedContext.auxiliarySpace (.quantumSystems 2) = 1 := by decide
example : mixedContext.auxiliarySpace (.quantumSystems 3) = 0 := by decide
example : mixedContext.quantumLayout.basisCardinality = 6 := by decide

/-- Changing the advertised dimension does not make an occupied identity fresh. -/
example : ¬List.Disjoint (oneSystem 10 3).identities qubitContext.physicalIdx := by
  rw [← List.disjoint_toFinset_iff_disjoint]
  decide

/-- A physically separate wire still cannot reuse a live storage key. -/
example : ¬key0 ∉ qubitContext.keys := by decide

private def bankLayouts : Fin 2 → QuantumLayout 1 :=
  fun copy => oneSystem (20 + copy.val) (if copy.val = 0 then 2 else 3)

private def mixedBank : OwnedCopyBank 2 1 :=
  OwnedCopyBank.ofLayouts bankLayouts (by decide)

private def bankContext : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedCopies key0 mixedBank (by decide)
    (List.disjoint_toFinset_iff_disjoint.mp (by decide))

private def bankAndQubit : RuntimeCtx .quantum :=
  bankContext.addOwnedLayout key2 (oneSystem 22 2) (by decide)
    (List.disjoint_toFinset_iff_disjoint.mp (by decide))

/-- Every bank member contributes to the same joint register as ordinary layouts. -/
example : bankContext.systemCount = 2 := by decide
example : bankContext.quantumLayout.basisCardinality = 6 := by decide
example : bankAndQubit.systemCount = 3 := by decide
example : bankAndQubit.quantumLayout.basisCardinality = 12 := by decide
example : bankAndQubit.residentSpace (.quantumSystems 2) = 2 := by decide
example : bankAndQubit.residentSpace (.quantumSystems 3) = 1 := by decide

/-- Overlapping banks cannot supply the actual identity certificate. -/
example : ¬(((List.ofFn (fun _ : Fin 2 => oneSystem 20 3)).flatMap
      QuantumLayout.wires).map QuantumWire.identity).Nodup := by
  decide

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example : RuntimeEntry .classical := .borrowedLayout key0 (oneSystem 10 3)

end AccountingContextFixtures

end QuantumAlg

end
