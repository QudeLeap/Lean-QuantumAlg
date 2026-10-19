/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Ports
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Composition
import all QuantumAlg.Components.QubitPrimitive

/-!
# Disjoint physical pairs in the final measured-arithmetic exchange

Only the selected A and Y wires belong to each active prefix. The complete
frame is recovered by its actual inclusion, retaining X and every history
wire as spectators. Distinct pairs have disjoint physical selections.
-/

namespace QuantumAlg.MeasuredUncompute.FrameSwapLayout

noncomputable section

open ProductPlacement FramePorts

abbrev layout (width : Nat) := (QubitLayout.canonical (frameEncoding width).width).toQuantum

def left (width : Nat) (index : Fin width) := ((accumulator width).bit index).wire

def right (width : Nat) (index : Fin width) := ((numerator width).bit index).wire

lemma distinct (width : Nat) (index : Fin width) : left width index ≠ right width index :=
  accumulator_numerator_ne width index index

def positions (width count : Nat) (bounded : count ≤ width) :
    Fin (count + count) ↪ Fin (frameEncoding width).width where
  toFun := Fin.addCases
    (fun index => left width ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩)
    (fun index => right width ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩)
  inj' := by
    intro first second
    refine Fin.addCases (fun i => ?_) (fun i => ?_) first <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) second
    all_goals
      intro same
      have values := congrArg Fin.val same
      simp only [Fin.addCases_left, Fin.addCases_right, left, right,
        accumulator_wire, numerator_wire] at values
    · exact congrArg (Fin.castAdd count) (Fin.ext values)
    · have ib := i.isLt; omega
    · have jb := j.isLt; omega
    · exact congrArg (Fin.natAdd count) (Fin.ext (by omega))

def subsystem (width count : Nat) (bounded : count ≤ width) : QuantumLayout (count + count) where
  wire index := (layout width).wire (positions width count bounded index)
  identityInjective := fun _ _ same =>
    (positions width count bounded).injective ((layout width).identityInjective same)

def complete (width count : Nat) (bounded : count ≤ width) :
    QuantumLayout.Embedding (subsystem width count bounded) (layout width) where
  position := positions width count bounded
  wire_eq _ := rfl

@[implicit_reducible] def application (width : Nat) (index : Fin width) :
    GateModel.Application AlgorithmGate.model (layout width) :=
  GateModel.Application.ofPositions AlgorithmGate.model .cnot (layout width)
    ⟨![left width index, right width index], by
      intro first second same
      fin_cases first <;> fin_cases second <;> try rfl
      · exact False.elim (distinct width index same)
      · exact False.elim (distinct width index same.symm)⟩ (fun _ => rfl)

@[implicit_reducible] def reverseApplication (width : Nat) (index : Fin width) :
    GateModel.Application AlgorithmGate.model (layout width) :=
  GateModel.Application.ofPositions AlgorithmGate.model .cnot (layout width)
    ⟨![right width index, left width index], by
      intro first second same
      fin_cases first <;> fin_cases second <;> try rfl
      · exact False.elim (distinct width index same.symm)
      · exact False.elim (distinct width index same)⟩ (fun _ => rfl)

def earlierPositions (count : Nat) : Fin (count + count) ↪ Fin (count + 1 + (count + 1)) where
  toFun := Fin.addCases
    (fun index => Fin.castAdd (count + 1) index.castSucc)
    (fun index => Fin.natAdd (count + 1) index.castSucc)
  inj' := by
    intro first second
    refine Fin.addCases (fun i => ?_) (fun i => ?_) first <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) second
    all_goals
      intro same
      have values := congrArg Fin.val same
      simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd,
        Fin.val_natAdd, Fin.val_castSucc] at values
    · exact congrArg (Fin.castAdd count) (Fin.ext values)
    · have ib := i.isLt; omega
    · have jb := j.isLt; omega
    · exact congrArg (Fin.natAdd count) (Fin.ext (by omega))

lemma earlier_positions (width count : Nat) (bounded : count + 1 ≤ width)
    (index : Fin (count + count)) :
    positions width (count + 1) bounded (earlierPositions count index) =
      positions width count (Nat.le_of_succ_le bounded) index := by
  change (positions width (count + 1) bounded).toFun ((earlierPositions count).toFun index) =
    (positions width count (Nat.le_of_succ_le bounded)).toFun index
  dsimp only [positions, earlierPositions]
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index <;>
    simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castSucc]

def earlier (width count : Nat) (bounded : count + 1 ≤ width) :
    QuantumLayout.Embedding (subsystem width count (Nat.le_of_succ_le bounded))
      (subsystem width (count + 1) bounded) where
  position := earlierPositions count
  wire_eq index := congrArg (layout width).wire (earlier_positions width count bounded index)

def nextPositions (count : Nat) : Fin 2 ↪ Fin (count + 1 + (count + 1)) where
  toFun := ![Fin.castAdd (count + 1) (Fin.last count),
    Fin.natAdd (count + 1) (Fin.last count)]
  inj' := by
    intro first second same
    fin_cases first <;> fin_cases second <;> try rfl
    all_goals
      have values := congrArg Fin.val same
      simp at values

lemma next_positions (width count : Nat) (bounded : count + 1 ≤ width)
    (index : Fin 2) :
    positions width (count + 1) bounded (nextPositions count index) =
      (application width ⟨count, Nat.lt_of_succ_le bounded⟩).embedding.position index := by
  change (positions width (count + 1) bounded).toFun ((nextPositions count).toFun index) =
    ![left width ⟨count, Nat.lt_of_succ_le bounded⟩,
      right width ⟨count, Nat.lt_of_succ_le bounded⟩] index
  dsimp only [positions, nextPositions]
  fin_cases index <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
      Fin.addCases_left, Fin.addCases_right, Fin.val_last]

def next (width count : Nat) (bounded : count + 1 ≤ width) :
    QuantumLayout.Embedding
      (application width ⟨count, Nat.lt_of_succ_le bounded⟩).occurrence.placement.layout
      (subsystem width (count + 1) bounded) where
  position := nextPositions count
  wire_eq index := congrArg (layout width).wire (next_positions width count bounded index)

lemma disjoint (width count : Nat) (bounded : count + 1 ≤ width) :
    Disjoint (earlier width count bounded).selection (next width count bounded).selection := by
  apply Finset.disjoint_left.mpr
  intro position inEarlier inNext
  obtain ⟨first, _, firstSame⟩ := Finset.mem_map.mp inEarlier
  obtain ⟨second, _, secondSame⟩ := Finset.mem_map.mp inNext
  have same : earlierPositions count first = nextPositions count second :=
    firstSame.trans secondSame.symm
  change (earlierPositions count).toFun first = (nextPositions count).toFun second at same
  dsimp only [earlierPositions, nextPositions] at same
  revert same
  refine Fin.addCases (fun index => ?_) (fun index => ?_) first <;> intro same
  all_goals fin_cases second
  · have values := congrArg Fin.val same
    simp only [Fin.addCases_left] at values
    change index.val = count at values
    exact (Nat.ne_of_lt index.isLt) values
  · have values := congrArg Fin.val same
    simp only [Fin.addCases_left] at values
    change index.val = count + 1 + count at values
    have bound := index.isLt
    omega
  · have values := congrArg Fin.val same
    simp only [Fin.addCases_right] at values
    change count + 1 + index.val = count at values
    omega
  · have values := congrArg Fin.val same
    simp only [Fin.addCases_right] at values
    change count + 1 + index.val = count + 1 + count at values
    have bound := index.isLt
    omega

lemma earlier_complete (width count : Nat) (bounded : count + 1 ≤ width) :
    QuantumLayout.Embedding.compose (earlier width count bounded)
        (complete width (count + 1) bounded) =
      complete width count (Nat.le_of_succ_le bounded) := by
  apply QuantumLayout.Embedding.embedding_ext
  exact earlier_positions width count bounded

lemma next_complete (width count : Nat) (bounded : count + 1 ≤ width) :
    QuantumLayout.Embedding.compose (next width count bounded)
        (complete width (count + 1) bounded) =
      (application width ⟨count, Nat.lt_of_succ_le bounded⟩).embedding := by
  apply QuantumLayout.Embedding.embedding_ext
  exact next_positions width count bounded

end

end QuantumAlg.MeasuredUncompute.FrameSwapLayout
