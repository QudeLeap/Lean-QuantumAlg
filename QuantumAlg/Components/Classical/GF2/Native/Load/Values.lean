/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Load.Semantics

/-!
# Original row values written by the actual GF(2) loader

The decoder uses the original most-significant-bit-first convention. Its
fresh temporary cannot alias any caller read. Each real row execution is
exactly one matrix update on the caller's complete store, and the complete
loader performs those updates in increasing row order. No initial matrix
or temporary contents are a correctness premise.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private lemma word_eq_of_nat (left right : CShape.Value (.unsignedWord width))
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

private lemma rowDecode_value (input : CInputRef ctx (.bits width))
    (loader : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (separate : loader.key ∉ input.storageKeys) :
    ((rowDecodeStep input loader (store.applyOp (rowClearOp loader))).1.read
      (.storage loader.toCStorageRef)) =
        .unsignedWord (ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian (store.read input))) := by
  have preserved := Store.read_applyOp_of_not_mem_storageKeys store
    (rowClearOp loader) input separate
  have source : TerminalDecode.decodeInputFromBitRefs .bigEndian
      (store.applyOp (rowClearOp loader)) (fun index => .bitsGet input index) =
        TerminalDecode.decodeInput .bigEndian (store.read input) := by
    change (⟨.bigEndian, fun index =>
      (((store.applyOp (rowClearOp loader)).read input).bitGet index).toBool⟩ :
        ClassicalAlgorithms.TerminalDecode.Input width) = _
    rw [preserved]
    cases store.read input
    rfl
  apply word_eq_of_nat
  exact (TerminalDecode.terminalDecode_intoFromBitRefs_read_output .bigEndian
    (fun index => .bitsGet input index) loader (store.applyOp (rowClearOp loader))
    (fun _ => separate)).trans (congrArg (fun value =>
      (ClassicalAlgorithms.TerminalDecode.eval value).val) source)

/-- The actual row body writes the original big-endian value after clearing its real decoder. -/
lemma gf2RowBody_read_matrix (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (sourceSeparate : loader.key ∉ input.storageKeys) (matrixSeparate : loader.key ≠ matrix.key) :
    ((rowBodyStep input row matrix loader store).1.read (.storage matrix.toCStorageRef)) =
      CShape.vectorWrite (store.read (.storage matrix.toCStorageRef)) row
        (.unsignedWord (ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian (store.read input)))) := by
  let cleared := store.applyOp (rowClearOp loader)
  let decoded := (rowDecodeStep input loader cleared).1
  have separated : loader.key ∉ (CInputRef.storage matrix.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using matrixSeparate
  have preserved : decoded.read (.storage matrix.toCStorageRef) =
      store.read (.storage matrix.toCStorageRef) :=
    (TerminalDecode.terminalDecode_fold_read_other loader _ cleared _ separated).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (rowClearOp loader) _ separated)
  change (decoded.applyOp (rowWriteOp row matrix loader)).read
    (.storage matrix.toCStorageRef) = _
  refine (Store.read_applyOp_output decoded (rowWriteOp row matrix loader)).trans ?_
  change CShape.vectorWrite (decoded.read (.storage matrix.toCStorageRef)) row
    (decoded.read (.storage loader.toCStorageRef)) = _
  rw [preserved, rowDecode_value input loader store sourceSeparate]

/-- Every structural read outside the two actual written cells survives the complete row body. -/
lemma gf2RowBody_read_other (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (matrixSeparate : matrix.key ∉ other.storageKeys)
    (loaderSeparate : loader.key ∉ other.storageKeys) :
    (rowBodyStep input row matrix loader store).1.read other = store.read other := by
  change ((rowDecodeStep input loader (store.applyOp (rowClearOp loader))).1.applyOp
    (rowWriteOp row matrix loader)).read other = _
  exact (Store.read_applyOp_of_not_mem_storageKeys _ (rowWriteOp row matrix loader)
    other matrixSeparate).trans
    ((TerminalDecode.terminalDecode_fold_read_other loader _ _ other loaderSeparate).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (rowClearOp loader) other loaderSeparate))

omit [BitWord.Selected model] in
private lemma loader_fresh {shape : CShape} (input : CInputRef ctx shape) :
    (rowCell ctx width).key ∉
      (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh).storageKeys := by
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

/-- The one-word lexical scope supplies every separation needed for the original row value. -/
lemma gf2LoadRow_read_matrix (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (store : Store ctx) :
    (loadRowStep input matrix row store).1.read (.storage matrix.toCStorageRef) =
      CShape.vectorWrite (store.read (.storage matrix.toCStorageRef)) row
        (.unsignedWord (ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian (store.read (.vectorGet input row))))) := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  have matrixSeparate : (rowCell ctx width).key ≠ matrix.key := by
    simpa only [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys,
      List.mem_singleton] using (loader_fresh (width := width) (.storage matrix.toCStorageRef))
  have written := gf2RowBody_read_matrix
    ((CInputRef.vectorGet input row).underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) row
    (matrix.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
    (rowCell ctx width)
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
    (loader_fresh (.vectorGet input row)) matrixSeparate
  refine written.trans ?_
  rw [Store.read_pushWorkspace_underWorkspace]
  exact congrArg (fun value => CShape.vectorWrite value row _)
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh (.storage matrix.toCStorageRef))

/-- Popping the real temporary leaves every other caller read unchanged. -/
lemma gf2LoadRow_read_other (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : matrix.key ∉ other.storageKeys) :
    (loadRowStep input matrix row store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  refine (gf2RowBody_read_other _ row _ _ _
    (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) ?_ (loader_fresh other)).trans ?_
  · rw [CInputRef.storageKeys_underWorkspace]
    exact separate
  · exact Store.read_pushWorkspace_underWorkspace store _ _ _ other

/-- The complete caller store equals the original matrix-row update, without a workspace premise. -/
lemma gf2LoadRow_store (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (store : Store ctx) :
    (loadRowStep input matrix row store).1 = store.write matrix
      (CShape.vectorWrite (store.read (.storage matrix.toCStorageRef)) row
        (.unsignedWord (ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian (store.read (.vectorGet input row)))))) := by
  apply Store.store_eq_write_of_read_frame _ _ matrix _
    (gf2LoadRow_read_matrix input matrix row store)
  intro shape other separate
  apply gf2LoadRow_read_other input matrix row store (.storage other)
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

/-- The whole actual loader applies its original row updates in increasing-index order. -/
lemma gf2LoadMatrix_store (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (store : Store ctx) :
    (loadMatrixStep input matrix store).1 =
      (List.ofFn (fun row : Fin rowCount => fun current : Store ctx => current.write matrix
        (CShape.vectorWrite (current.read (.storage matrix.toCStorageRef)) row
          (.unsignedWord (ClassicalAlgorithms.TerminalDecode.eval
            (TerminalDecode.decodeInput .bigEndian (current.read (.vectorGet input row)))))))).foldl
        (fun current update => update current) store := by
  refine (Circuit.forRangeStoreRecord_store rowCount
    (loadRow (model := model) input matrix)
    (loadRowStep (model := model) input matrix) store).trans ?_
  congr 2
  funext row current
  exact gf2LoadRow_store input matrix row current

end

end QuantumAlg.ClassicalRoutines.GF2.Native
