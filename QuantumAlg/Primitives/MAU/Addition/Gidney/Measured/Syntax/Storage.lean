/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Distinct actual storage cells for the retained carry outcomes

The native compiler permits arbitrary caller-provided destinations. Corrected
addition uses this bank to keep every measured carry available until both paid
phase passes. The existing allocator supplies the bank with fresh distinct
keys. Every original caller Store remains admitted [G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

open Execution

/-- Existing finite measurement destinations with distinct live storage identities. -/
structure RecordBank {kind : ProblemKind} (ctx : RuntimeCtx kind) (records : Nat) where
  output : Fin records → CWriteRef ctx (.finite 2)
  distinct : Function.Injective (fun index => (output index).key)

namespace RecordBank

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {records : Nat}

/-- The same actual finite-cell allocator supplies all cells and their distinct-key proof. -/
def allocated (ctx : RuntimeCtx kind) (records : Nat) :
    RecordBank (MeasurementCells.context ctx 2 records) records where
  output := MeasurementCells.reference ctx 2 records
  distinct := MeasurementCells.reference_key_injective ctx 2 records

/-- Each measurement reads back its exact actual stored outcome, regardless of the old Store. -/
lemma read_write_same (bank : RecordBank ctx records) (store : Store ctx)
    (index : Fin records) (outcome : Fin 2) :
    (store.write (bank.output index) (.finite outcome)).read
      (.storage (bank.output index).toCStorageRef) = .finite outcome :=
  Store.read_write_same store _ _

/-- Every later measurement at another bank index retains the earlier actual stored outcome. -/
lemma read_write_other (bank : RecordBank ctx records) (store : Store ctx)
    (written observed : Fin records) (different : written ≠ observed) (outcome : Fin 2) :
    (store.write (bank.output written) (.finite outcome)).read
        (.storage (bank.output observed).toCStorageRef) =
      store.read (.storage (bank.output observed).toCStorageRef) :=
  Store.read_write_other store _ _ _ (fun same => different (bank.distinct same))

end RecordBank

end

end QuantumAlg.MAU.Addition.Gidney.Measured
