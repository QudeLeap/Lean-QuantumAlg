/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Geometry
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection

/-!
# Compatible head and tail bank coordinates

The recursive tail selects the same original physical tail positions. Its
complement contains the actual measured head and the original full-bank
complement. All equations follow those positions and preserve their values.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- The recursive tail retains the original physical position injection. -/
def tailPhysicalWires {n : Nat} (wires : Fin (n + 1) ↪ Fin ctx.systemCount) :
    Fin n ↪ Fin ctx.systemCount :=
  ⟨fun index => wires index.succ,
    fun _ _ same => Fin.succ_injective n (wires.injective same)⟩

/-- The selected recursive tail tuple is exactly the outer tuple's tail. -/
lemma tailBankCoordinates_selected {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index) :
    (bankCoordinates (tailPhysicalWires wires) (fun i => qubits i.succ) basis).1 =
      (bankCoordinates wires qubits basis).1.2 := by
  apply tupleCoordinates_injective n
  funext index
  exact (congrFun
    (bankCoordinates_values (tailPhysicalWires wires) (fun i => qubits i.succ) basis)
    index).trans (bankCoordinates_tail_values wires qubits basis index).symm

/-- Every actual tail position is in the full selected bank. -/
lemma tailPhysicalWires_selection_subset {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount) :
    (physicalBankEmbedding (tailPhysicalWires wires)).selection ⊆
      (physicalBankEmbedding wires).selection := by
  intro position member
  rcases (physicalBankEmbedding_member (tailPhysicalWires wires) position).mp member with
    ⟨index, equal⟩
  exact (physicalBankEmbedding_member wires position).mpr ⟨index.succ, equal⟩

/-- The measured head is an actual untouched complementary position of the recursive tail. -/
lemma head_not_mem_tail_selection {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount) :
    wires 0 ∉ (physicalBankEmbedding (tailPhysicalWires wires)).selection := by
  intro selected
  rcases (physicalBankEmbedding_member (tailPhysicalWires wires) (wires 0)).mp selected with
    ⟨index, equal⟩
  exact Fin.succ_ne_zero index (wires.injective equal)

/-- Outside the recursive tail, a position is the head or outside the entire bank. -/
lemma outside_tail_selection_iff {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount) (position : Fin ctx.systemCount) :
    position ∉ (physicalBankEmbedding (tailPhysicalWires wires)).selection ↔
      position = wires 0 ∨ position ∉ (physicalBankEmbedding wires).selection := by
  constructor
  · intro outside
    by_cases head : position = wires 0
    · exact Or.inl head
    · right
      intro selected
      rcases (physicalBankEmbedding_member wires position).mp selected with ⟨index, equal⟩
      revert equal
      refine Fin.cases ?_ (fun index => ?_) index
      · intro equal
        exact head equal.symm
      · intro equal
        exact outside
          ((physicalBankEmbedding_member (tailPhysicalWires wires) position).mpr ⟨index, equal⟩)
  · rintro (head | outside)
    · rw [head]
      exact head_not_mem_tail_selection wires
    · exact fun selected => outside (tailPhysicalWires_selection_subset wires selected)

/-- Recursive tail-complement agreement preserves the real head and entire original complement. -/
lemma tailBankCoordinates_complement_eq_iff {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (row column : ctx.register.Index) :
    (bankCoordinates (tailPhysicalWires wires) (fun i => qubits i.succ) row).2 =
        (bankCoordinates (tailPhysicalWires wires) (fun i => qubits i.succ) column).2 ↔
      (bankCoordinates wires qubits row).1.1 = (bankCoordinates wires qubits column).1.1 ∧
        (bankCoordinates wires qubits row).2 = (bankCoordinates wires qubits column).2 := by
  rw [bankCoordinates_complement_eq_iff (tailPhysicalWires wires)
    (fun i => qubits i.succ) row column,
    bankCoordinates_complement_eq_iff wires qubits row column,
    bankCoordinates_head_value, bankCoordinates_head_value]
  constructor
  · intro same
    constructor
    · exact congrArg
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)))
        (same (wires 0) (head_not_mem_tail_selection wires))
    · intro position outside
      exact same position (fun selected => outside
        (tailPhysicalWires_selection_subset wires selected))
  · rintro ⟨head, complement⟩ position outside
    rcases (outside_tail_selection_iff wires position).mp outside with (equal | unselected)
    · subst position
      apply Fin.ext
      exact congrArg (fun bit : Fin 2 => bit.val) head
    · exact complement position unselected

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
