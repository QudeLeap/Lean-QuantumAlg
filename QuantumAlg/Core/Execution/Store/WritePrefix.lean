/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import Lean.Elab.Tactic.Omega

/-!
# Retaining all actual values in distinct writable cells

Distinctness is checked at actual storage keys, rather than equality of
references or ownership roles. The original store and arbitrary old values
are retained. These definitions describe the real writes, not a packing
instruction or a second interpreter.
-/

namespace QuantumAlg.Execution.Store

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {n : Nat}
  {shapes : Fin n → CShape}

/-- The first literal writes in increasing physical outcome order. -/
def writePrefix (outputs : ∀ index, CWriteRef ctx (shapes index))
    (values : ∀ index, (shapes index).Value) (original : Store ctx) :
    (count : Nat) → count ≤ n → Store ctx
  | 0, _ => original
  | count + 1, bounded =>
      (writePrefix outputs values original count (Nat.le_of_succ_le bounded)).write
        (outputs ⟨count, Nat.lt_of_succ_le bounded⟩)
        (values ⟨count, Nat.lt_of_succ_le bounded⟩)

/-- The ordered real writes split into the head write and the identical tail sequence. -/
lemma writePrefix_head_tail {shapes : Fin (n + 1) → CShape}
    (outputs : ∀ index, CWriteRef ctx (shapes index))
    (values : ∀ index, (shapes index).Value) (original : Store ctx)
    (count : Nat) (bounded : count + 1 ≤ n + 1) :
    writePrefix outputs values original (count + 1) bounded =
      writePrefix (fun index : Fin n => outputs index.succ)
        (fun index : Fin n => values index.succ)
        (original.write (outputs 0) (values 0)) count
        (Nat.le_of_succ_le_succ bounded) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [writePrefix, Fin.succ_mk] using
        congrArg
          (fun previous : Store ctx => previous.write
            (outputs ⟨count + 1, Nat.lt_of_succ_le bounded⟩)
            (values ⟨count + 1, Nat.lt_of_succ_le bounded⟩))
          (ih (Nat.le_of_succ_le bounded))

/-- The complete finite ordered sequence is a genuine head write followed by all tail writes. -/
lemma writePrefix_all_head_tail {shapes : Fin (n + 1) → CShape}
    (outputs : ∀ index, CWriteRef ctx (shapes index))
    (values : ∀ index, (shapes index).Value) (original : Store ctx) :
    writePrefix outputs values original (n + 1) le_rfl =
      writePrefix (fun index : Fin n => outputs index.succ)
        (fun index : Fin n => values index.succ)
        (original.write (outputs 0) (values 0)) n le_rfl :=
  writePrefix_head_tail outputs values original n le_rfl

/-- Every already written distinct cell retains its own actual value. -/
lemma read_writePrefix (outputs : ∀ index, CWriteRef ctx (shapes index))
    (values : ∀ index, (shapes index).Value)
    (separate : Function.Injective (fun index => (outputs index).key))
    (original : Store ctx) (count : Nat) (bounded : count ≤ n)
    (index : Fin n) (written : index.val < count) :
    (writePrefix outputs values original count bounded).read
      (.storage (outputs index).toCStorageRef) = values index := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [writePrefix]
      by_cases same : index = ⟨count, Nat.lt_of_succ_le bounded⟩
      · subst index
        exact read_write_same _ _ _
      · rw [read_write_other _ _ _ _ (fun equal => same (separate equal).symm)]
        exact ih (Nat.le_of_succ_le bounded) (by
          have different : index.val ≠ count := fun equal => same (Fin.ext equal)
          omega)

/-- All finite output values can be read individually without runtime integer packing. -/
lemma read_writePrefix_all (outputs : ∀ index, CWriteRef ctx (shapes index))
    (values : ∀ index, (shapes index).Value)
    (separate : Function.Injective (fun index => (outputs index).key))
    (original : Store ctx) (index : Fin n) :
    (writePrefix outputs values original n le_rfl).read
      (.storage (outputs index).toCStorageRef) = values index :=
  read_writePrefix outputs values separate original n le_rfl index index.isLt

end

end QuantumAlg.Execution.Store

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

/-- Every canonical retained measurement cell reads its own value after all real writes. -/
lemma read_writePrefix_all {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) (values : Fin count → Fin dimension)
    (original : Store (context ctx dimension count)) (index : Fin count) :
    (Store.writePrefix (reference ctx dimension count)
      (fun selected => CShape.Value.finite (values selected)) original count le_rfl).read
        (.storage (reference ctx dimension count index).toCStorageRef) =
      .finite (values index) :=
  Store.read_writePrefix_all (reference ctx dimension count)
    (fun selected => CShape.Value.finite (values selected))
    (reference_key_injective ctx dimension count) original index

end

end QuantumAlg.Execution.MeasurementCells
