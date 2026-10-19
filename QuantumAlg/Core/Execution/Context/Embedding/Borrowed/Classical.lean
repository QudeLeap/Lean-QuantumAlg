/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Borrowed
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Context.Permutation.Store
import all QuantumAlg.Core.Execution.Context.Relabeling.Store
import all QuantumAlg.Core.Execution.Context.Union.Store
import all QuantumAlg.Core.Execution.Borrowed.Classical
import Mathlib.Logic.Function.Basic

/-!
# Joint borrowed classical labels through physical placement

The caller's borrowed classical label depends only on the original local
borrowed label and the unchanged complete complement store. This factorization
retains the complement tag jointly with the quantum state; it does not average
over tags or require that conditional input states satisfy admission. The map
only reexpresses existing finite labels and performs no runtime allocation.
-/

namespace QuantumAlg.Execution

private lemma readBorrowedCells_storage_eq {kind : ProblemKind}
    {key : StorageKey} {shape : CShape} {entries : List (RuntimeEntry kind)}
    (first second : Cells entries)
    (same : readBorrowedCells entries first = readBorrowedCells entries second)
    (slot : RuntimeEntrySlot (.storage key .borrowedInput shape) entries) :
    Cells.read first slot = Cells.read second slot := by
  induction slot with
  | here => exact congrArg CShape.Value.first same
  | @there entry entries slot ih =>
      apply ih first.2 second.2
      cases entry with
      | storage key role shape =>
          cases role with
          | borrowedInput => exact congrArg CShape.Value.second same
          | workspace | retained | finalOutput => exact same
      | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies => exact same

private lemma readBorrowedCells_eq_of_storage {kind : ProblemKind}
    (entries : List (RuntimeEntry kind)) (first second : Cells entries)
    (same : ∀ key shape (slot : RuntimeEntrySlot (.storage key .borrowedInput shape) entries),
      Cells.read first slot = Cells.read second slot) :
    readBorrowedCells entries first = readBorrowedCells entries second := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      have tailSame := ih first.2 second.2
        (fun key shape slot => same key shape (.there slot))
      cases entry with
      | storage key role shape =>
          cases role with
          | borrowedInput => exact congrArg₂ CShape.Value.product (same key shape .here) tailSame
          | workspace | retained | finalOutput => exact tailSame
      | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies => exact tailSame

namespace Store

/-- Equal complete borrowed labels agree at every original borrowed storage cell. -/
lemma store_borrowed_read_eq_of_label {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (first second : Store ctx)
    (same : first.readBorrowedClassical = second.readBorrowedClassical)
    {shape : CShape} (ref : CStorageRef ctx shape) (borrowed : ref.role = .borrowedInput) :
    first.read (.storage ref) = second.read (.storage ref) := by
  obtain ⟨key, role, slot⟩ := ref
  cases borrowed
  exact readBorrowedCells_storage_eq first.cells second.cells same slot

/-- The actual borrowed storage reads determine the whole joint classical label. -/
lemma store_borrowed_label_eq_of_reads {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (first second : Store ctx)
    (same : ∀ {shape} (ref : CStorageRef ctx shape), ref.role = .borrowedInput →
      first.read (.storage ref) = second.read (.storage ref)) :
    first.readBorrowedClassical = second.readBorrowedClassical :=
  readBorrowedCells_eq_of_storage ctx.entries first.cells second.cells
    (fun key _shape slot => same ⟨key, .borrowedInput, slot⟩ rfl)

end Store

private lemma relabelCells_borrowed_congr {kind : ProblemKind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (entries : List (RuntimeEntry kind)) (first second : Cells entries)
    (same : readBorrowedCells entries first = readBorrowedCells entries second) :
    readBorrowedCells (entries.map (RuntimeEntry.relabel keys physical))
      (ContextRelabeling.cellsEquiv keys physical entries first) =
    readBorrowedCells (entries.map (RuntimeEntry.relabel keys physical))
      (ContextRelabeling.cellsEquiv keys physical entries second) := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | storage key role shape =>
          cases role with
          | borrowedInput =>
              exact congrArg₂ CShape.Value.product (congrArg CShape.Value.first same)
                (ih first.2 second.2 (congrArg CShape.Value.second same))
          | workspace | retained | finalOutput => exact ih first.2 second.2 same
      | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies =>
          exact ih first.2 second.2 same

private lemma joinCells_borrowed_congr {kind : ProblemKind}
    (left right : List (RuntimeEntry kind)) (first second : Cells left) (frame : Cells right)
    (same : readBorrowedCells left first = readBorrowedCells left second) :
    readBorrowedCells (left ++ right) (ContextUnion.joinCells left right first frame) =
      readBorrowedCells (left ++ right) (ContextUnion.joinCells left right second frame) := by
  induction left with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | storage key role shape =>
          cases role with
          | borrowedInput =>
              exact congrArg₂ CShape.Value.product (congrArg CShape.Value.first same)
                (ih first.2 second.2 (congrArg CShape.Value.second same))
          | workspace | retained | finalOutput => exact ih first.2 second.2 same
      | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies =>
          exact ih first.2 second.2 same

private lemma permutation_borrowed_congr {kind : ProblemKind}
    {source target : RuntimeCtx kind} (permuted : source.entries.Perm target.entries)
    (first second : Store source)
    (same : first.readBorrowedClassical = second.readBorrowedClassical) :
    (ContextPermutation.store permuted first).readBorrowedClassical =
      (ContextPermutation.store permuted second).readBorrowedClassical := by
  apply Store.store_borrowed_label_eq_of_reads
  intro shape ref borrowed
  obtain ⟨original, rfl⟩ := ContextPermutation.storage_surjective permuted ref
  rw [ContextPermutation.store_read_storage, ContextPermutation.store_read_storage]
  exact Store.store_borrowed_read_eq_of_label first second same original borrowed

end QuantumAlg.Execution

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- The complete complement tag and original local borrowed label fix the caller label. -/
lemma contextEmbedding_borrowedClassical_join_congr
    (first second : Store localCtx) (frame : Store placement.frame)
    (same : first.readBorrowedClassical = second.readBorrowedClassical) :
    (placement.store.symm (first, frame)).readBorrowedClassical =
      (placement.store.symm (second, frame)).readBorrowedClassical := by
  apply permutation_borrowed_congr placement.covers
  exact joinCells_borrowed_congr _ _ _ _ frame.cells
    (relabelCells_borrowed_congr placement.keys placement.physical localCtx.entries
      first.cells second.cells same)

private lemma borrowedClassical_factors :
    Function.FactorsThrough
      (fun stores : Store localCtx × Store placement.frame =>
        (placement.store.symm stores).readBorrowedClassical)
      (fun stores => (stores.1.readBorrowedClassical, stores.2)) := by
  intro first second same
  obtain ⟨localFirst, frameFirst⟩ := first
  obtain ⟨localSecond, frameSecond⟩ := second
  have localSame := congrArg Prod.fst same
  have frameSame := congrArg Prod.snd same
  change frameFirst = frameSecond at frameSame
  cases frameSame
  exact placement.contextEmbedding_borrowedClassical_join_congr _ _ _ localSame

/-- Recover the caller borrowed label while retaining the entire finite complement tag. -/
def borrowedClassicalJoin :
    localCtx.borrowedClassicalShape.Value × Store placement.frame →
      caller.borrowedClassicalShape.Value :=
  Function.extend
    (fun stores : Store localCtx × Store placement.frame =>
      (stores.1.readBorrowedClassical, stores.2))
    (fun stores => (placement.store.symm stores).readBorrowedClassical)
    (fun _ => CShape.initialValue caller.borrowedClassicalShape)

/-- On every actual finite store, the factored label is precisely the original caller read. -/
lemma contextEmbedding_borrowedClassicalJoin_eval
    (localStore : Store localCtx) (frameStore : Store placement.frame) :
    placement.borrowedClassicalJoin (localStore.readBorrowedClassical, frameStore) =
      (placement.store.symm (localStore, frameStore)).readBorrowedClassical :=
  placement.borrowedClassical_factors.extend_apply _ (localStore, frameStore)

/-- Splitting preserves the caller label as one joint function of local and complement data. -/
lemma contextEmbedding_borrowedClassicalJoin_split (store : Store caller) :
    placement.borrowedClassicalJoin
      ((placement.store store).1.readBorrowedClassical, (placement.store store).2) =
        store.readBorrowedClassical := by
  rw [placement.contextEmbedding_borrowedClassicalJoin_eval,
    Equiv.symm_apply_apply]

end

end QuantumAlg.ContextEmbedding
