/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source.Primitive
public import QuantumAlg.Core.Base.Layout.Quantum.Embedding.Composition
import all QuantumAlg.Primitives.QFT.Source.Primitive
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Composition
import all QuantumAlg.Core.Base.Gate.Placement.Construction

/-!
# Actual disjoint subsystems of the Fourier wire reversal

The prefix layout contains exactly the outer `count` wires from each end.
The next symmetric pair occupies the two new positions, so parallelism is
certified on physical selections without counting spectators as active wires.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

open QFTPrimitive (layout)

/-- The lower position of a symmetric pair in the final wire reversal. -/
public def swapLeft (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨index.val, lt_of_lt_of_le index.isLt (Nat.div_le_self n 2)⟩

/-- The upper position of the same symmetric pair. -/
public def swapRight (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨n - 1 - index.val, by have bounded := index.isLt; omega⟩

lemma swap_distinct (n : Nat) (index : Fin (n / 2)) :
    swapLeft n index ≠ swapRight n index := by
  intro same
  have value := congrArg Fin.val same
  have bounded := index.isLt
  simp only [swapLeft, swapRight] at value
  omega

namespace ReverseLayout

noncomputable section

/-- Each prefix position names precisely one original outer physical wire. -/
def positions (n count : Nat) (bounded : count ≤ n / 2) : Fin (count + count) ↪ Fin n where
  toFun := Fin.addCases
    (fun index => ⟨index.val, by have bound := index.isLt; omega⟩)
    (fun index => ⟨n - 1 - index.val, by have bound := index.isLt; omega⟩)
  inj' := by
    intro left right
    refine Fin.addCases (fun first => ?_) (fun first => ?_) left <;>
      refine Fin.addCases (fun second => ?_) (fun second => ?_) right
    all_goals
      intro same
      have values := congrArg Fin.val same
      simp only [Fin.addCases_left, Fin.addCases_right] at values
    · exact congrArg (Fin.castAdd count) (Fin.ext values)
    · have firstBound := first.isLt
      have secondBound := second.isLt
      omega
    · have firstBound := first.isLt
      have secondBound := second.isLt
      omega
    · apply congrArg (Fin.natAdd count)
      apply Fin.ext
      have firstBound := first.isLt
      have secondBound := second.isLt
      omega

/-- The subsystem carries the same physical wire records as the complete bank. -/
def subsystem (n count : Nat) (bounded : count ≤ n / 2) : QuantumLayout (count + count) where
  wire index := (layout n).wire (positions n count bounded index)
  identityInjective := fun _ _ same =>
    (positions n count bounded).injective ((layout n).identityInjective same)

/-- Include exactly the prefix subsystem in the original bank. -/
def complete (n count : Nat) (bounded : count ≤ n / 2) :
    QuantumLayout.Embedding (subsystem n count bounded) (layout n) where
  position := positions n count bounded
  wire_eq _ := rfl

/-- Ordered positions of the next actual symmetric pair. -/
def pairPositions (n : Nat) (index : Fin (n / 2)) : Fin 2 ↪ Fin n where
  toFun := ![swapLeft n index, swapRight n index]
  inj' := by
    intro first second same
    fin_cases first <;> fin_cases second
    · rfl
    · exact False.elim (swap_distinct n index same)
    · exact False.elim (swap_distinct n index same.symm)
    · rfl

/-- The original native SWAP occurrence, with its complete ambient placement. -/
def application (n : Nat) (index : Fin (n / 2)) :
    GateModel.Application FourierGate.model (layout n) :=
  GateModel.Application.ofPositions FourierGate.model .swap (layout n)
    (pairPositions n index) (fun _ => rfl)

/-- The next pair's actual two-wire layout contains no other bank system. -/
abbrev pair (n : Nat) (index : Fin (n / 2)) : QuantumLayout 2 :=
  (application n index).occurrence.placement.layout

/-- Earlier outer wires occupy the corresponding positions in the enlarged prefix. -/
def earlierPositions (count : Nat) : Fin (count + count) ↪ Fin (count + 1 + (count + 1)) where
  toFun := Fin.addCases
    (fun index => Fin.castAdd (count + 1) index.castSucc)
    (fun index => Fin.natAdd (count + 1) index.castSucc)
  inj' := by
    intro left right
    refine Fin.addCases (fun first => ?_) (fun first => ?_) left <;>
      refine Fin.addCases (fun second => ?_) (fun second => ?_) right
    all_goals
      intro same
      have values := congrArg Fin.val same
      simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd,
        Fin.val_natAdd, Fin.val_castSucc] at values
    · exact congrArg (Fin.castAdd count) (Fin.ext values)
    · have firstBound := first.isLt
      omega
    · have secondBound := second.isLt
      omega
    · exact congrArg (Fin.natAdd count) (Fin.ext (by omega))

/-- Enlarging the active subsystem keeps every earlier physical position. -/
lemma earlier_positions (n count : Nat) (bounded : count + 1 ≤ n / 2)
    (index : Fin (count + count)) :
    positions n (count + 1) bounded (earlierPositions count index) =
      positions n count (Nat.le_of_succ_le bounded) index := by
  change (positions n (count + 1) bounded).toFun ((earlierPositions count).toFun index) =
    (positions n count (Nat.le_of_succ_le bounded)).toFun index
  dsimp only [positions, earlierPositions]
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index <;>
    simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castSucc]

/-- The earlier prefix is included without changing any wire record. -/
def earlier (n count : Nat) (bounded : count + 1 ≤ n / 2) :
    QuantumLayout.Embedding (subsystem n count (Nat.le_of_succ_le bounded))
      (subsystem n (count + 1) bounded) where
  position := earlierPositions count
  wire_eq index := congrArg (layout n).wire (earlier_positions n count bounded index)

/-- The new pair fills the last position of each outer half. -/
def nextPositions (count : Nat) : Fin 2 ↪ Fin (count + 1 + (count + 1)) where
  toFun := ![Fin.castAdd (count + 1) (Fin.last count),
    Fin.natAdd (count + 1) (Fin.last count)]
  inj' := by
    intro first second same
    fin_cases first <;> fin_cases second <;> try rfl
    all_goals
      have values := congrArg Fin.val same
      simp at values

/-- The two new subsystem positions are exactly the next original symmetric pair. -/
lemma next_positions (n count : Nat) (bounded : count + 1 ≤ n / 2)
    (index : Fin 2) :
    positions n (count + 1) bounded (nextPositions count index) =
      pairPositions n ⟨count, Nat.lt_of_succ_le bounded⟩ index := by
  change (positions n (count + 1) bounded).toFun ((nextPositions count).toFun index) =
    (pairPositions n ⟨count, Nat.lt_of_succ_le bounded⟩).toFun index
  dsimp only [positions, nextPositions, pairPositions]
  fin_cases index <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
      Fin.addCases_left, Fin.addCases_right, swapLeft, swapRight, Fin.val_last]

/-- The next pair's actual physical wires occur at those two new positions. -/
def next (n count : Nat) (bounded : count + 1 ≤ n / 2) :
    QuantumLayout.Embedding (pair n ⟨count, Nat.lt_of_succ_le bounded⟩)
      (subsystem n (count + 1) bounded) where
  position := nextPositions count
  wire_eq index := congrArg (layout n).wire (next_positions n count bounded index)

/-- Every earlier physical wire differs from both wires of the next pair. -/
lemma disjoint (n count : Nat) (bounded : count + 1 ≤ n / 2) :
    Disjoint (earlier n count bounded).selection (next n count bounded).selection := by
  apply Finset.disjoint_left.mpr
  intro position inEarlier inNext
  obtain ⟨first, _, firstSame⟩ := Finset.mem_map.mp inEarlier
  obtain ⟨second, _, secondSame⟩ := Finset.mem_map.mp inNext
  have same : earlierPositions count first = nextPositions count second :=
    firstSame.trans secondSame.symm
  change (earlierPositions count).toFun first = (nextPositions count).toFun second at same
  dsimp only [earlierPositions, nextPositions] at same
  have values := congrArg Fin.val same
  revert values
  fin_cases second <;>
    refine Fin.addCases (fun index => ?_) (fun index => ?_) first
  all_goals
    intro values
    have bound := index.isLt
    simp only [Fin.addCases_left, Fin.addCases_right, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc, Fin.val_last] at values
    omega

/-- Composing earlier-prefix placements gives the original complete-bank inclusion. -/
lemma earlier_complete (n count : Nat) (bounded : count + 1 ≤ n / 2) :
    QuantumLayout.Embedding.compose (earlier n count bounded) (complete n (count + 1) bounded) =
      complete n count (Nat.le_of_succ_le bounded) := by
  apply QuantumLayout.Embedding.embedding_ext
  exact earlier_positions n count bounded

/-- Composing the new pair's placements gives the original addressed native occurrence. -/
lemma next_complete (n count : Nat) (bounded : count + 1 ≤ n / 2) :
    QuantumLayout.Embedding.compose (next n count bounded) (complete n (count + 1) bounded) =
      (application n ⟨count, Nat.lt_of_succ_le bounded⟩).embedding := by
  apply QuantumLayout.Embedding.embedding_ext
  exact next_positions n count bounded

end

end ReverseLayout

end QuantumAlg.QuantumFourierTransform.Source
