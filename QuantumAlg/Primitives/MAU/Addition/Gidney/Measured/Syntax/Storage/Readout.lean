/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Storage.Word

/-!
# Readback from the actual chronological carry-record bank

Later writes to distinct bank cells retain earlier physical outcomes. The
last-write formula covers arbitrary original Stores and arbitrary repeated
writes as well. A consistent complete set of physical outcomes fixes every
later paid phase read [G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.RecordBank

noncomputable section

open Execution Instruction

variable {ctx : RuntimeCtx .quantum} {records : Nat}

/-- The last physical outcome written at one supplied bank index. -/
def writtenOutcome (index : Fin records) : List (Fin records × Fin 2) → Option (Fin 2)
  | [] => none
  | pair :: rest =>
      match writtenOutcome index rest with
      | some value => some value
      | none => if pair.1 = index then some pair.2 else none

/-- The actual chronological writes have exactly their last-write readback, or the old value. -/
lemma read_writeOutcomes (bank : RecordBank ctx records) (index : Fin records)
    (writes : List (Fin records × Fin 2)) (store : Store ctx) :
    (writeOutcomes bank.output store writes).read (.storage (bank.output index).toCStorageRef) =
      match writtenOutcome index writes with
      | some value => .finite value
      | none => store.read (.storage (bank.output index).toCStorageRef) := by
  induction writes generalizing store with
  | nil => rfl
  | cons pair rest ih =>
      rw [writeOutcomes, ih, writtenOutcome]
      cases later : writtenOutcome index rest with
      | some value => rfl
      | none =>
          by_cases same : pair.1 = index
          · rw [if_pos same, same, bank.read_write_same]
          · rw [if_neg same, bank.read_write_other store pair.1 index same pair.2]

private lemma writtenOutcome_of_absent (index : Fin records)
    (writes : List (Fin records × Fin 2)) (absent : index ∉ writes.map Prod.fst) :
    writtenOutcome index writes = none := by
  revert absent
  induction writes with
  | nil => intro _; rfl
  | cons entry tail ih =>
      intro absent
      have different : entry.1 ≠ index := by
        intro equal
        apply absent
        simp only [List.map_cons, List.mem_cons]
        exact Or.inl equal.symm
      have tailAbsent : index ∉ tail.map Prod.fst := by
        intro member
        exact absent (List.mem_cons_of_mem _ member)
      rw [writtenOutcome, ih tailAbsent, if_neg different]

/-- Consistent physical outcomes determine the last value of every index actually written. -/
lemma writtenOutcome_of_consistent (outcome : Fin records → Fin 2)
    (writes : List (Fin records × Fin 2))
    (consistent : ∀ pair ∈ writes, pair.2 = outcome pair.1)
    (index : Fin records) (present : index ∈ writes.map Prod.fst) :
    writtenOutcome index writes = some (outcome index) := by
  revert consistent present
  induction writes with
  | nil => intro _ present; simp at present
  | cons pair rest ih =>
      intro consistent present
      have restConsistent : ∀ entry ∈ rest, entry.2 = outcome entry.1 :=
        fun entry member => consistent entry (List.mem_cons_of_mem _ member)
      by_cases later : index ∈ rest.map Prod.fst
      · rw [writtenOutcome, ih restConsistent later]
      · have same : pair.1 = index := by
          have equal : index = pair.1 := by
            simpa only [List.map_cons, List.mem_cons, later, or_false] using present
          exact equal.symm
        rw [writtenOutcome, writtenOutcome_of_absent index rest later, if_pos same,
          consistent pair (List.mem_cons_self), same]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.RecordBank
