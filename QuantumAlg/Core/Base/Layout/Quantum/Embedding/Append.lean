/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Append.Embedding
public import QuantumAlg.Core.Base.Layout.Quantum.Embedding.Composition
import all QuantumAlg.Core.Base.Layout.Quantum.Append.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Composition

/-!
# Joining disjoint subsystems of the same physical layout

Both position maps retain their original physical wires. Their disjointness is
checked in the final ambient layout, so a shared control cannot be hidden by
placing its two users inside different local words.
-/

namespace QuantumAlg.QuantumLayout.Embedding

variable {leftCount rightCount count : Nat}
  {left : QuantumLayout leftCount} {right : QuantumLayout rightCount}
  {ambient : QuantumLayout count}

/-- Disjoint ambient positions imply disjoint original physical identities. -/
public lemma embedding_identities_disjoint
    (first : Embedding left ambient) (second : Embedding right ambient)
    (separate : Disjoint first.selection second.selection) :
    List.Disjoint left.identities right.identities := by
  apply List.disjoint_left.mpr
  intro identity inLeft inRight
  obtain ⟨i, leftEq⟩ := List.mem_ofFn.mp inLeft
  obtain ⟨j, rightEq⟩ := List.mem_ofFn.mp inRight
  have same : first.position i = second.position j := by
    apply ambient.identityInjective
    change (ambient.wire (first.position i)).identity =
      (ambient.wire (second.position j)).identity
    rw [first.wire_eq, second.wire_eq]
    exact leftEq.trans rightEq.symm
  apply Finset.disjoint_left.mp separate (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  exact same.symm ▸ Finset.mem_map_of_mem _ (Finset.mem_univ j)

/-- Append the two original subsystems without changing any ambient position. -/
public def append (first : Embedding left ambient) (second : Embedding right ambient)
    (separate : Disjoint first.selection second.selection) :
    Embedding (QuantumLayout.append left right
      (embedding_identities_disjoint first second separate)) ambient where
  position :=
    { toFun := Fin.addCases first.position second.position
      inj' := by
        intro i j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · intro same
          have equal : first.position i = first.position j := by
            simpa only [Fin.addCases_left] using same
          exact congrArg (Fin.castAdd rightCount) (first.position.injective equal)
        · intro same
          have equal : first.position i = second.position j := by
            simpa only [Fin.addCases_left, Fin.addCases_right] using same
          exfalso
          apply Finset.disjoint_left.mp separate
            (Finset.mem_map_of_mem _ (Finset.mem_univ i))
          exact equal.symm ▸ Finset.mem_map_of_mem _ (Finset.mem_univ j)
        · intro same
          have equal : second.position i = first.position j := by
            simpa only [Fin.addCases_left, Fin.addCases_right] using same
          exfalso
          apply Finset.disjoint_left.mp separate
            (Finset.mem_map_of_mem _ (Finset.mem_univ j))
          exact equal ▸ Finset.mem_map_of_mem _ (Finset.mem_univ i)
        · intro same
          have equal : second.position i = second.position j := by
            simpa only [Fin.addCases_right] using same
          exact congrArg (Fin.natAdd leftCount) (second.position.injective equal) }
  wire_eq := by
    intro index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · change ambient.wire (Fin.addCases first.position second.position
        (Fin.castAdd rightCount i)) = _
      rw [Fin.addCases_left]
      simpa [QuantumLayout.append] using first.wire_eq i
    · change ambient.wire (Fin.addCases first.position second.position
        (Fin.natAdd leftCount i)) = _
      rw [Fin.addCases_right]
      simpa [QuantumLayout.append] using second.wire_eq i

/-- The joined position map keeps the original left positions. -/
@[simp] public lemma embedding_append_position_left
    (first : Embedding left ambient) (second : Embedding right ambient)
    (separate : Disjoint first.selection second.selection) (i : Fin leftCount) :
    (append first second separate).position (Fin.castAdd rightCount i) = first.position i := by
  change Fin.addCases (motive := fun _ => Fin count)
    first.position second.position (Fin.castAdd rightCount i) = _
  exact Fin.addCases_left i

/-- The joined position map keeps the original right positions. -/
@[simp] public lemma embedding_append_position_right
    (first : Embedding left ambient) (second : Embedding right ambient)
    (separate : Disjoint first.selection second.selection) (i : Fin rightCount) :
    (append first second separate).position (Fin.natAdd leftCount i) = second.position i := by
  change Fin.addCases (motive := fun _ => Fin count)
    first.position second.position (Fin.natAdd leftCount i) = _
  exact Fin.addCases_right i

/-- The joined support is exactly the union of the two original supports. -/
public lemma embedding_append_selection
    (first : Embedding left ambient) (second : Embedding right ambient)
    (separate : Disjoint first.selection second.selection) :
    (append first second separate).selection = first.selection ∪ second.selection := by
  ext index
  simp only [selection, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, same⟩
    revert same
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · intro same
      exact Or.inl ⟨i, by simpa only [embedding_append_position_left] using same⟩
    · intro same
      exact Or.inr ⟨i, by simpa only [embedding_append_position_right] using same⟩
  · rintro (⟨i, same⟩ | ⟨i, same⟩)
    · exact ⟨Fin.castAdd rightCount i, by
        simpa only [embedding_append_position_left] using same⟩
    · exact ⟨Fin.natAdd leftCount i, by
        simpa only [embedding_append_position_right] using same⟩

/-- Including the original left segment through the join recovers its placement. -/
public lemma embedding_append_left
    (first : Embedding left ambient) (second : Embedding right ambient)
    (separate : Disjoint first.selection second.selection) :
    compose (QuantumLayout.appendLeftEmbedding left right
      (embedding_identities_disjoint first second separate)) (append first second separate) =
      first := by
  apply embedding_ext
  intro index
  change (append first second separate).position (Fin.castAdd rightCount index) = _
  exact embedding_append_position_left first second separate index

/-- Including the original right segment through the join recovers its placement. -/
public lemma embedding_append_right
    (first : Embedding left ambient) (second : Embedding right ambient)
    (separate : Disjoint first.selection second.selection) :
    compose (QuantumLayout.appendRightEmbedding left right
      (embedding_identities_disjoint first second separate)) (append first second separate) =
      second := by
  apply embedding_ext
  intro index
  change (append first second separate).position (Fin.natAdd leftCount index) = _
  exact embedding_append_position_right first second separate index

end QuantumAlg.QuantumLayout.Embedding
