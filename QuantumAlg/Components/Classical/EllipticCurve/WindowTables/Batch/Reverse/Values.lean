/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Execution
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Separation

/-!
# Exact actual reverse-batch cell values

The first multiply saves the output inverse in the existing temporary word.
The second multiply consumes the original denominator before its overwrite.
All prefix rows and all other denominator rows are retained by the actual
three-instruction-group record, with no extra table or scalar allocation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : BatchFrame ctx width length)

omit [BitWord.Selected model] in
private lemma inverse_temporary_ne : frame.work.inverse.key ≠ frame.work.temporary.key := by
  intro same
  have distinct := frame.work.distinct
  simp [same] at distinct

/-- The selected C overwrite contains the old inverse times the original saved prefix product. -/
lemma reverseRecord_read_denominator (index : Fin length) (store : Store ctx) :
    (frame.reverseRecord (model := model) index store).1.read
      (rowRead frame.denominators index) =
      multiplyValue (store.read (wordRead frame.work.inverse))
        (store.read (rowRead frame.prefixes index)) (store.read frame.modulus) := by
  let first := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.prefixes index) frame.modulus frame.work.temporary store).1
  let second := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.denominators index) frame.modulus frame.work.inverse first).1
  change (second.applyOp (rowWriteOp frame.denominators index
    (wordRead frame.work.temporary))).read (rowRead frame.denominators index) = _
  rw [rowWrite_read_same]
  have retained := nativePower_scopedMultiply_read_other (model := model)
    (wordRead frame.work.inverse) (rowRead frame.denominators index) frame.modulus
    frame.work.inverse (wordRead frame.work.temporary)
    (by
      change frame.work.inverse.key ∉ [frame.work.temporary.key]
      simpa only [List.mem_singleton] using inverse_temporary_ne frame) first
  exact retained.trans (nativePower_scopedMultiply_result _ _ _ _ store)

/-- The running inverse consumes the original denominator before that same row is replaced. -/
lemma reverseRecord_read_inverse (index : Fin length)
    (modulusFree : frame.work.temporary.key ∉ frame.modulus.storageKeys) (store : Store ctx) :
    (frame.reverseRecord (model := model) index store).1.read (wordRead frame.work.inverse) =
      multiplyValue (store.read (wordRead frame.work.inverse))
        (store.read (rowRead frame.denominators index)) (store.read frame.modulus) := by
  let first := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.prefixes index) frame.modulus frame.work.temporary store).1
  let second := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.denominators index) frame.modulus frame.work.inverse first).1
  change (second.applyOp (rowWriteOp frame.denominators index
    (wordRead frame.work.temporary))).read (wordRead frame.work.inverse) = _
  have retained := rowWrite_read_word frame.denominators index
    (wordRead frame.work.temporary) frame.work.inverse second
  change (second.applyOp (rowWriteOp frame.denominators index
    (wordRead frame.work.temporary))).read (wordRead frame.work.inverse) =
      second.read (wordRead frame.work.inverse) at retained
  rw [retained]
  change ((scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.denominators index) frame.modulus frame.work.inverse first).1).read _ = _
  rw [nativePower_scopedMultiply_result]
  have oldInverse := nativePower_scopedMultiply_read_other (model := model)
    (wordRead frame.work.inverse) (rowRead frame.prefixes index) frame.modulus
    frame.work.temporary (wordRead frame.work.inverse)
    (by
      change frame.work.temporary.key ∉ [frame.work.inverse.key]
      simpa only [List.mem_singleton] using Ne.symm (inverse_temporary_ne frame)) store
  have oldDenominator := nativePower_scopedMultiply_read_other (model := model)
    (wordRead frame.work.inverse) (rowRead frame.prefixes index) frame.modulus
    frame.work.temporary (rowRead frame.denominators index)
    (by
      change frame.work.temporary.key ∉ [frame.denominators.key]
      simpa only [List.mem_singleton] using
        word_array_key_ne frame.work.temporary frame.denominators) store
  have oldModulus := nativePower_scopedMultiply_read_other (model := model)
    (wordRead frame.work.inverse) (rowRead frame.prefixes index) frame.modulus
    frame.work.temporary frame.modulus modulusFree store
  change first.read (wordRead frame.work.inverse) = _ at oldInverse
  change first.read (rowRead frame.denominators index) = _ at oldDenominator
  change first.read frame.modulus = _ at oldModulus
  rw [oldInverse, oldDenominator, oldModulus]

/-- Every original prefix row survives all actual reverse-step writes. -/
lemma reverseRecord_read_prefix (index observed : Fin length) (store : Store ctx) :
    (frame.reverseRecord (model := model) index store).1.read (rowRead frame.prefixes observed) =
      store.read (rowRead frame.prefixes observed) := by
  let first := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.prefixes index) frame.modulus frame.work.temporary store).1
  let second := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.denominators index) frame.modulus frame.work.inverse first).1
  change (second.applyOp (rowWriteOp frame.denominators index
    (wordRead frame.work.temporary))).read (rowRead frame.prefixes observed) = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (rowWriteOp frame.denominators index (wordRead frame.work.temporary))
    (rowRead frame.prefixes observed)
    (by
      change frame.denominators.key ∉ [frame.prefixes.key]
      simpa only [List.mem_singleton] using frame.separate)]
  exact (nativePower_scopedMultiply_read_other (model := model)
    (wordRead frame.work.inverse) (rowRead frame.denominators index) frame.modulus
    frame.work.inverse (rowRead frame.prefixes observed)
    (by
      change frame.work.inverse.key ∉ [frame.prefixes.key]
      simpa only [List.mem_singleton] using word_array_key_ne frame.work.inverse frame.prefixes)
    first).trans
    (nativePower_scopedMultiply_read_other (model := model)
      (wordRead frame.work.inverse) (rowRead frame.prefixes index) frame.modulus
      frame.work.temporary (rowRead frame.prefixes observed)
      (by
        change frame.work.temporary.key ∉ [frame.prefixes.key]
        simpa only [List.mem_singleton] using
          word_array_key_ne frame.work.temporary frame.prefixes) store)

/-- Other C rows, including the identity row zero, retain their original stored values. -/
lemma reverseRecord_read_other_denominator (index observed : Fin length)
    (different : observed ≠ index) (store : Store ctx) :
    (frame.reverseRecord (model := model) index store).1.read
      (rowRead frame.denominators observed) = store.read (rowRead frame.denominators observed) := by
  let first := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.prefixes index) frame.modulus frame.work.temporary store).1
  let second := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.denominators index) frame.modulus frame.work.inverse first).1
  change (second.applyOp (rowWriteOp frame.denominators index
    (wordRead frame.work.temporary))).read (rowRead frame.denominators observed) = _
  rw [rowWrite_read_other _ _ _ _ _ different]
  exact (nativePower_scopedMultiply_read_other (model := model)
    (wordRead frame.work.inverse) (rowRead frame.denominators index) frame.modulus
    frame.work.inverse (rowRead frame.denominators observed)
    (by
      change frame.work.inverse.key ∉ [frame.denominators.key]
      simpa only [List.mem_singleton] using
        word_array_key_ne frame.work.inverse frame.denominators) first).trans
    (nativePower_scopedMultiply_read_other (model := model)
      (wordRead frame.work.inverse) (rowRead frame.prefixes index) frame.modulus
      frame.work.temporary (rowRead frame.denominators observed)
      (by
        change frame.work.temporary.key ∉ [frame.denominators.key]
        simpa only [List.mem_singleton] using
          word_array_key_ne frame.work.temporary frame.denominators) store)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
