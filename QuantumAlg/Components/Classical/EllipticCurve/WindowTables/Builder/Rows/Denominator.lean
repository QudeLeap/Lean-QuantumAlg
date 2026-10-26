/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Arithmetic
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.ReadWrite

/-!
# Actual binary-layer secant-denominator values

The original six-operation shared subtraction and single vector write read
the preceding actual Store. Their exact result is the seed x coordinate
minus the old-row x coordinate on its original canonical-right domain.
No extra inverse, quotient or denominator computation enters the program.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Total caller Store of the original arithmetic and subsequent real C overwrite. -/
def denominatorStore (seed row : Fin length) (store : Store ctx) : Store ctx :=
  let computed := store.write frame.work.temporary
    (subValue (store.read (rowRead frame.arrays.x seed))
      (store.read (rowRead frame.arrays.x row)) (store.read (wordRead frame.modulus)))
  computed.applyOp (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary))

/-- Exactly the original finite-word subtraction is written into the actual selected C row. -/
lemma denominatorStore_read_result (seed row : Fin length) (store : Store ctx) :
    (frame.denominatorStore seed row store).read (rowRead frame.arrays.c row) =
      subValue (store.read (rowRead frame.arrays.x seed))
        (store.read (rowRead frame.arrays.x row)) (store.read (wordRead frame.modulus)) := by
  rw [denominatorStore, rowWrite_read_same]
  exact Store.read_write_same _ _ _

/-- Its field interpretation is the original finite-coordinate secant denominator. -/
lemma denominatorStore_result_cast (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord)
    (canonical : (store.read (rowRead frame.arrays.x row)).toNat < spec.modulus) :
    (((frame.denominatorStore seed row store).read (rowRead frame.arrays.c row)).toNat :
      ZMod spec.modulus) = (store.read (rowRead frame.arrays.x seed)).toNat -
        (store.read (rowRead frame.arrays.x row)).toNat := by
  rw [frame.denominatorStore_read_result seed row store, loaded]
  exact subValue_cast spec _ _ canonical

/-- The actual secant denominator word is canonical on that same original domain. -/
lemma denominatorStore_result_canonical (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord)
    (canonical : (store.read (rowRead frame.arrays.x row)).toNat < spec.modulus) :
    ((frame.denominatorStore seed row store).read (rowRead frame.arrays.c row)).toNat <
      spec.modulus := by
  rw [frame.denominatorStore_read_result seed row store, loaded]
  exact subValue_canonical spec _ _ canonical

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The existing subtraction path precedes the existing C-write path on its actual output Store. -/
def denominatorRecord (seed row : Fin length) (environment : model.Environment) :
    Store ctx → Store ctx × (frame.denominatorRow (model := model) seed row).Path :=
  Circuit.sequenceStoreRecord
    (subIntoWord (rowRead frame.arrays.x seed) (rowRead frame.arrays.x row)
      frame.modulus frame.work.temporary)
    (BitWord.instruction (execution := model)
      (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary)))
    (subIntoWordStep (environment := environment) (rowRead frame.arrays.x seed)
      (rowRead frame.arrays.x row) frame.modulus frame.work.temporary)
    (BitWord.instructionStep (execution := model)
      (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary)))

/-- The finite-word Store above is the original actual seven-operation record's returned Store. -/
lemma denominatorRecord_store (seed row : Fin length) (environment : model.Environment)
    (store : Store ctx) :
    (frame.denominatorRecord seed row environment store).1 =
      frame.denominatorStore seed row store := by
  change ((subIntoWordStep (environment := environment) (rowRead frame.arrays.x seed)
    (rowRead frame.arrays.x row) frame.modulus frame.work.temporary store).1.applyOp
      (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary))) = _
  rw [sharedSubIntoWordStep_store]
  rfl

/-- Every original quantum-reference block and history is retained by that same actual record. -/
lemma denominatorRow_execute (seed row : Fin length) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.denominatorRow (model := model) seed row).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.denominatorRecord seed row environment entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  Circuit.execute_sequenceStoreRecord (model := model) _ _ environment _ _
    (sharedSubIntoWord_execute _ _ _ _)
    (fun _ {_} _ initial => BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model) _ initial) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
