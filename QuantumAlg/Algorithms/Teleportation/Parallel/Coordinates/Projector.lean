/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Physical
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument
import all QuantumAlg.Algorithms.Teleportation.Channel
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Execution.Store

/-!
# Stored measurement outcomes in the native tensor coordinates

Each actual result cell identifies the corresponding measured Alice wire.
The complete physical projector is the tensor of the source's two-bit
projectors selected by those stored outcomes [dW19, qcnotes.tex:802,804].
Both measured Alice systems and Bob's remaining system stay in the output
register; the identities neither discard a subsystem nor assume that the
unknown inputs factor between blocks [dW19, qcnotes.tex:809].
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.ProjectorCoordinates

noncomputable section

open Execution StoreInstrument PhysicalNative
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The source's head label consists of Alice's first two physical positions. -/
def binaryAlice (label : Fin 8) : Fin 4 :=
  finProdFinEquiv ((BinaryBasis.bigEndianEquiv 3).symm label 0,
    (BinaryBasis.bigEndianEquiv 3).symm label 1)

lemma binaryAlice_eq_head (label : Fin 8) :
    binaryAlice label = (finProdFinEquiv.symm label : Fin 4 × Fin 2).1 := by
  fin_cases label <;> decide

private lemma bitValue_decide (value : Fin 2) :
    bitValue (decide (value.val = 1)) = value := by
  fin_cases value <;> simp [bitValue]

/-- The correction selector decodes the real finite cell values without changing either bit. -/
lemma stored_outcome_label (count : Nat) (stored : Store (context count)) (block : Fin count) :
    outcomeValue (storedBits (stored.read (resultInput count)) block).1
      (storedBits (stored.read (resultInput count)) block).2 =
      finProdFinEquiv
        ((stored.read (.storage
          (resultCell count (finProdFinEquiv (block, 0))).toCStorageRef)).toFin,
         (stored.read (.storage
          (resultCell count (finProdFinEquiv (block, 1))).toCStorageRef)).toFin) :=
  congrArg finProdFinEquiv (Prod.ext (bitValue_decide _) (bitValue_decide _))

/-- The wire measured into each actual cell is the corresponding native Alice coordinate. -/
lemma native_measured_value (count : Nat) (labels : Fin count → Fin 8)
    (block : Fin count) (side : Fin 2) :
    (((contextBankBasis count).symm labels)
      (measuredPosition count (finProdFinEquiv (block, side)))).val =
      ((BinaryBasis.bigEndianEquiv 3).symm (labels block)
        (side.castLE (by decide))).val := by
  let readAt : Fin count × Fin 2 → Nat := fun pair =>
    (((contextBankBasis count).symm labels)
      (position count (wireIndex pair.1 (pair.2.castLE (by decide))))).val
  change readAt ((finProdFinEquiv (m := count) (n := 2)).symm
    (finProdFinEquiv (block, side))) = _
  exact (congrArg readAt ((finProdFinEquiv (m := count) (n := 2)).symm_apply_apply
    (block, side))).trans
      (contextBankBasis_symm_wire_value count labels block (side.castLE (by decide)))

/-- Actual whole-store selection agrees with the original source's head projector in every block. -/
lemma matchesStored_native_iff (count : Nat) (stored : Store (context count))
    (labels : Fin count → Fin 8) :
    matchesStored count stored ((contextBankBasis count).symm labels) ↔
      ∀ block : Fin count, binaryAlice (labels block) =
        outcomeValue (storedBits (stored.read (resultInput count)) block).1
          (storedBits (stored.read (resultInput count)) block).2 := by
  constructor
  · intro matched block
    rw [stored_outcome_label]
    change finProdFinEquiv ((BinaryBasis.bigEndianEquiv 3).symm (labels block) 0,
      (BinaryBasis.bigEndianEquiv 3).symm (labels block) 1) = _
    apply congrArg finProdFinEquiv
    apply Prod.ext
    · apply Fin.ext
      exact (native_measured_value count labels block 0).symm.trans
        (matched (finProdFinEquiv (block, 0)))
    · apply Fin.ext
      exact (native_measured_value count labels block 1).symm.trans
        (matched (finProdFinEquiv (block, 1)))
  · intro matched index
    obtain ⟨⟨block, side⟩, rfl⟩ := finProdFinEquiv.surjective index
    have encoded := (matched block).trans (stored_outcome_label count stored block)
    have pair := finProdFinEquiv.injective encoded
    fin_cases side
    · exact (native_measured_value count labels block 0).trans
        (congrArg (fun value : Fin 2 × Fin 2 => value.1.val) pair)
    · exact (native_measured_value count labels block 1).trans
        (congrArg (fun value : Fin 2 × Fin 2 => value.2.val) pair)

/-- The source square projector retains Alice's measured systems and Bob's original coordinate. -/
def sourceProjector (outcome : Fin 4) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal fun label => if binaryAlice label = outcome then 1 else 0

/-- The actual square projector is exactly the tensor of source projectors for the stored bits. -/
lemma actualProjector_native_entry (count : Nat) (stored : Store (context count))
    (row column : Fin count → Fin 8) :
    actualProjector count stored ((contextBankBasis count).symm row)
      ((contextBankBasis count).symm column) =
      ∏ block : Fin count, sourceProjector
        (outcomeValue (storedBits (stored.read (resultInput count)) block).1
          (storedBits (stored.read (resultInput count)) block).2)
        (row block) (column block) := by
  by_cases same : row = column
  · subst column
    simp only [actualProjector, sourceProjector, Matrix.diagonal_apply_eq]
    by_cases matched : matchesStored count stored ((contextBankBasis count).symm row)
    · have allMatched := (matchesStored_native_iff count stored row).mp matched
      rw [if_pos matched]
      symm
      apply Finset.prod_eq_one
      intro block _
      exact if_pos (allMatched block)
    · have notAll : ¬(∀ block : Fin count, binaryAlice (row block) =
          outcomeValue (storedBits (stored.read (resultInput count)) block).1
            (storedBits (stored.read (resultInput count)) block).2) :=
        fun allMatched => matched ((matchesStored_native_iff count stored row).mpr allMatched)
      rw [if_neg matched]
      symm
      obtain ⟨block, absent⟩ := not_forall.mp notAll
      exact Finset.prod_eq_zero (Finset.mem_univ block) (if_neg absent)
  · have different : (contextBankBasis count).symm row ≠
        (contextBankBasis count).symm column := fun equality =>
      same ((contextBankBasis count).symm.injective equality)
    rw [actualProjector, Matrix.diagonal_apply_ne _ different]
    have differentAt : ∃ block, row block ≠ column block := by
      by_contra absent
      apply same
      funext block
      exact not_not.mp (fun different => absent ⟨block, different⟩)
    obtain ⟨block, differentBlock⟩ := differentAt
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ block)
    exact Matrix.diagonal_apply_ne _ differentBlock

end

end QuantumAlg.QuantumTeleportation.Parallel.ProjectorCoordinates
