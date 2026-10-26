/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Availability

/-!
# The retained assignment determined by actual nonrepeated physical record writes

This assignment is proof-side notation for actual measurement outcomes.
Distinct physical destination indices ensure that every written value agrees
with it, without restricting any original Store or fabricating a runtime
phase computation [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

variable {records : Nat}

/-- Read a retained assignment from the actual physical write values; unwritten cells use zero. -/
def retainedAssignment (writes : List (Fin records × Fin 2)) (index : Fin records) : Fin 2 :=
  (writes.lookup index).getD 0

private lemma lookup_of_nodup (writes : List (Fin records × Fin 2))
    (distinct : (writes.map Prod.fst).Nodup) (entry : Fin records × Fin 2)
    (present : entry ∈ writes) : writes.lookup entry.1 = some entry.2 := by
  induction writes with
  | nil => simp at present
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      have unique : key ∉ tail.map Prod.fst ∧ (tail.map Prod.fst).Nodup :=
        List.nodup_cons.mp distinct
      rcases List.mem_cons.mp present with same | later
      · subst entry
        exact List.lookup_cons_self
      · have different : entry.1 ≠ key := by
          intro same
          apply unique.1
          rw [← same]
          exact List.mem_map.mpr ⟨entry, later, rfl⟩
        have actual := ih unique.2 later
        have keyDiff : (entry.1 == key) = false := beq_eq_false_iff_ne.mpr different
        simpa only [List.lookup_cons, keyDiff] using actual

/-- Every unique actual physical write agrees with the assignment extracted from those writes. -/
lemma retainedAssignment_consistent (writes : List (Fin records × Fin 2))
    (distinct : (writes.map Prod.fst).Nodup) :
    ∀ entry ∈ writes, entry.2 = retainedAssignment writes entry.1 := by
  intro entry present
  rw [retainedAssignment, lookup_of_nodup writes distinct entry present, Option.getD_some]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
