/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Store
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import all QuantumAlg.Core.Execution.Store.WritePrefix

/-!
# Original chronological tuples and the same real output writes

Coordinates select the existing measured tuple. The Store equations retain
every unrelated old value and describe the actual chronological writes; they
do not execute frequency packing or introduce an input-state promise.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (Bits tupleCoordinates)

/-- A suffix of the original tuple keeps the original chronological coordinate offset. -/
def readoutTail {bits : Nat} (record : Fin bits → Fin 2) :
    (remaining position : Nat) → position + remaining ≤ bits → Bits remaining
  | 0, _, _ => ()
  | remaining + 1, position, bounded =>
      (record ⟨position, by omega⟩, readoutTail record remaining (position + 1) (by omega))

/-- Every suffix coordinate is its unchanged original output coordinate. -/
lemma readoutTail_coordinates {bits : Nat} (record : Fin bits → Fin 2)
    (remaining position : Nat) (bounded : position + remaining ≤ bits) (index : Fin remaining) :
    tupleCoordinates remaining (readoutTail record remaining position bounded) index =
      record ⟨position + index.val, by have bound := index.isLt; omega⟩ := by
  induction remaining generalizing position with
  | zero => exact Fin.elim0 index
  | succ remaining induction =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · simp only [readoutTail, QuantumFourierTransform.Semiclassical.tupleCoordinates_head]
        congr 1
      · rw [readoutTail, QuantumFourierTransform.Semiclassical.tupleCoordinates_tail, induction]
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega

/-- Selecting the full original tuple leaves that existing tuple unchanged. -/
lemma readoutTail_all {bits : Nat} (outcome : Bits bits) :
    readoutTail (tupleCoordinates bits outcome) bits 0 (by omega) = outcome := by
  apply QuantumFourierTransform.Semiclassical.tupleCoordinates_injective bits
  funext index
  rw [readoutTail_coordinates]
  congr 1
  exact Fin.ext (by simp)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ChronologicalCtx := context base noQuantum m ell width

variable {bits : Nat} (selection : Fin bits → Fin (resultBits m ell))

/-- The canonical output bank has distinct real storage keys before any execution. -/
lemma resultCell_key_injective :
    Function.Injective (fun index => (resultCell base noQuantum m ell width index).key) := by
  intro first second same
  have indices := cells_distinct base noQuantum m ell width same
  have values : (Fin.castAdd (width - 2) first).val =
      (Fin.castAdd (width - 2) second).val := congrArg Fin.val indices
  exact Fin.ext values

/-- The real suffix extends exactly the same chronological Store prefix. -/
lemma exponentOutputStore_prefix (record : Fin bits → Fin 2)
    (original : Store (ChronologicalCtx base noQuantum m ell width))
    (remaining position : Nat) (bounded : position + remaining ≤ bits) :
    exponentOutputStore base noQuantum m ell width selection remaining position bounded
        (Store.writePrefix (fun index => resultCell base noQuantum m ell width (selection index))
          (fun index => .finite (record index)) original position (by omega))
        (readoutTail record remaining position bounded) =
      Store.writePrefix (fun index => resultCell base noQuantum m ell width (selection index))
        (fun index => .finite (record index)) original (position + remaining) bounded := by
  induction remaining generalizing position with
  | zero => rfl
  | succ remaining induction =>
      change exponentOutputStore base noQuantum m ell width selection remaining (position + 1)
        (by omega)
        (Store.writePrefix (fun index => resultCell base noQuantum m ell width (selection index))
          (fun index => .finite (record index)) original (position + 1) (by omega))
        (readoutTail record remaining (position + 1) (by omega)) = _
      have next := induction (position + 1) (by omega)
      have offset : (position + 1) + remaining = position + (remaining + 1) := by omega
      simpa only [offset] using next

/-- All retained writes are the same real ordered prefix, including unrelated original cells. -/
lemma exponentOutputStore_all (original : Store (ChronologicalCtx base noQuantum m ell width))
    (outcome : Bits bits) :
    exponentOutputStore base noQuantum m ell width selection bits 0 (by omega) original outcome =
      Store.writePrefix (fun index => resultCell base noQuantum m ell width (selection index))
        (fun index => .finite (tupleCoordinates bits outcome index)) original bits le_rfl := by
  have whole := exponentOutputStore_prefix base noQuantum m ell width selection
    (tupleCoordinates bits outcome) original bits 0 (by omega)
  simpa only [readoutTail_all, Nat.zero_add, Store.writePrefix] using whole

/-- Every selected real output cell retains its own actual chronological measured value. -/
lemma exponentOutputStore_read (separate : Function.Injective selection)
    (original : Store (ChronologicalCtx base noQuantum m ell width)) (outcome : Bits bits)
    (index : Fin bits) :
    (exponentOutputStore base noQuantum m ell width selection bits 0 (by omega) original
      outcome).read
        (.storage (resultCell base noQuantum m ell width (selection index)).toCStorageRef) =
      .finite (tupleCoordinates bits outcome index) := by
  rw [exponentOutputStore_all]
  exact Store.read_writePrefix_all
    (fun selected => resultCell base noQuantum m ell width (selection selected))
    (fun selected => .finite (tupleCoordinates bits outcome selected))
    ((resultCell_key_injective base noQuantum m ell width).comp separate) original index

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
