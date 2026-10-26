/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Frame
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Read

/-!
# Actual row-write protection of supplied constant and base inputs

All five arrays and four persistent scalar words are the frame's original
outputs. Structural zero, one, curve and base inputs avoid these keys by
the original frame's placement proof. Only exact read preservation is used;
no value or additional runtime contract is attached to those inputs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- The original five arrays and four scalar words, in physical frame order. -/
def outputKeys : List StorageKey :=
  [frame.arrays.x.key, frame.arrays.y.key, frame.arrays.c.key, frame.arrays.d.key,
    frame.arrays.e.key, frame.work.product.key, frame.work.inverse.key,
    frame.work.temporary.key, frame.work.slope.key]

/-- Every actual row output avoids each original protected structural input. -/
lemma outputKey_free (key : StorageKey) (inside : key ∈ frame.outputKeys)
    (input : CInputRef ctx (.unsignedWord width))
    (source : input ∈ [frame.zero, frame.one, frame.curveA, frame.baseX, frame.baseY]) :
    key ∉ input.storageKeys :=
  frame.protectedReads input source key inside

/-- Any original array or scalar result write retains the supplied zero word exactly. -/
lemma write_read_zero {shape : CShape} (output : CWriteRef ctx shape)
    (inside : output.key ∈ frame.outputKeys) (store : Store ctx) (value : shape.Value) :
    (store.write output value).read frame.zero = store.read frame.zero :=
  Store.read_write_of_not_mem_storageKeys _ _ _ _
    (frame.outputKey_free output.key inside frame.zero (by simp))

/-- Any original array or scalar result write retains the supplied one word exactly. -/
lemma write_read_one {shape : CShape} (output : CWriteRef ctx shape)
    (inside : output.key ∈ frame.outputKeys) (store : Store ctx) (value : shape.Value) :
    (store.write output value).read frame.one = store.read frame.one :=
  Store.read_write_of_not_mem_storageKeys _ _ _ _
    (frame.outputKey_free output.key inside frame.one (by simp))

/-- Any original array or scalar result write retains the supplied curve coefficient exactly. -/
lemma write_read_curveA {shape : CShape} (output : CWriteRef ctx shape)
    (inside : output.key ∈ frame.outputKeys) (store : Store ctx) (value : shape.Value) :
    (store.write output value).read frame.curveA = store.read frame.curveA :=
  Store.read_write_of_not_mem_storageKeys _ _ _ _
    (frame.outputKey_free output.key inside frame.curveA (by simp))

/-- An actual row instruction with an original output key preserves the supplied zero word. -/
lemma applyOp_read_zero {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (inside : op.outputRef.key ∈ frame.outputKeys) (store : Store ctx) :
    (store.applyOp op).read frame.zero = store.read frame.zero :=
  Store.read_applyOp_of_not_mem_storageKeys _ _ _
    (frame.outputKey_free op.outputRef.key inside frame.zero (by simp))

/-- An actual row instruction with an original output key preserves the supplied one word. -/
lemma applyOp_read_one {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (inside : op.outputRef.key ∈ frame.outputKeys) (store : Store ctx) :
    (store.applyOp op).read frame.one = store.read frame.one :=
  Store.read_applyOp_of_not_mem_storageKeys _ _ _
    (frame.outputKey_free op.outputRef.key inside frame.one (by simp))

/-- An actual row instruction with an original output key preserves the curve coefficient. -/
lemma applyOp_read_curveA {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (inside : op.outputRef.key ∈ frame.outputKeys) (store : Store ctx) :
    (store.applyOp op).read frame.curveA = store.read frame.curveA :=
  Store.read_applyOp_of_not_mem_storageKeys _ _ _
    (frame.outputKey_free op.outputRef.key inside frame.curveA (by simp))

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution Modular.NativePower

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Every real array-row overwrite preserves the widened shared modulus by its typed shape. -/
lemma rowWrite_read_modulus
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (input : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (store.applyOp (rowWriteOp array index input)).read (wordRead modulus) =
      store.read (wordRead modulus) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  change array.key ∉ [modulus.key]
  simpa only [List.mem_singleton] using Ne.symm (modulus_array_key_ne modulus array)

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
