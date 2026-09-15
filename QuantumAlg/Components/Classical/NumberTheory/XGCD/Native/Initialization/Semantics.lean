/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Initialization
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Encoding
import all QuantumAlg.Components.Classical.NumberTheory.GCD.RemainderSemantics

/-!
# Actual initial values of the seven extended-Euclidean cells

Internal key separation comes from real lexical allocation. Its actual initial
values establish the original coefficient basis, with no caller coefficient
promise. The separate zero value belongs to the enclosing freshly retained
result; it is not an additional caller workspace condition.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem preserve_index (cells : Cells ctx (stateShapes width))
    (distinct : cells.Distinct) {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (written observed : Fin 7)
    (outputKey : op.outputRef.key = stateKey cells written) (different : written ≠ observed)
    (store : Store ctx) :
    (store.applyOp op).read (.storage (cellAt cells observed).ref.toCStorageRef) =
      store.read (.storage (cellAt cells observed).ref.toCStorageRef) := by
  apply Store.read_write_other
  intro same
  exact different (xgcdNativeState_key_injective cells distinct (outputKey.symm.trans same))

private theorem preserve_cell (cells : Cells ctx (stateShapes width))
    (distinct : cells.Distinct) {input output observedShape : CShape}
    (op : ClassicalOp input output ctx ctx) (written observed : Fin 7)
    (cell : CWriteRef ctx observedShape)
    (outputKey : op.outputRef.key = stateKey cells written)
    (observedKey : cell.key = stateKey cells observed) (different : written ≠ observed)
    (store : Store ctx) :
    (store.applyOp op).read (GCD.cellRead cell) = store.read (GCD.cellRead cell) := by
  apply Store.read_write_other
  intro same
  exact different (xgcdNativeState_key_injective cells distinct
    (outputKey.symm.trans (same.trans observedKey)))

private theorem preserve_caller {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) {input output observed : CShape}
    (op : ClassicalOp input output ctx ctx) (written : Fin 7)
    (outputKey : op.outputRef.key = stateKey cells written)
    (other : CInputRef outer observed) (store : Store ctx) :
    (store.applyOp op).read (transport.liftInput other) =
      store.read (transport.liftInput other) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  rw [outputKey]
  exact xgcdNativeState_input_separated cells transport separated other written

/-- Every transported caller read survives all six actual initialization writes. -/
theorem xgcdNativeInitialization_read_caller {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport)
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef outer shape) (store : Store ctx) :
    (initializationStore cells input zero store).read (transport.liftInput other) =
      store.read (transport.liftInput other) := by
  unfold initializationStore
  rw [preserve_caller cells transport separated (GCD.negateActiveOp (activeCell cells)) 6 rfl,
    preserve_caller cells transport separated
      (GCD.testActiveOp (firstCell cells) zero (activeCell cells)) 6 rfl,
    preserve_caller cells transport separated (incrementSecondRightOp cells) 5 rfl,
    preserve_caller cells transport separated (incrementFirstLeftOp cells) 2 rfl,
    preserve_caller cells transport separated (copySecondOp cells input) 1 rfl,
    preserve_caller cells transport separated (copyFirstOp cells input) 0 rfl]

private theorem preserve_unwritten (cells : Cells ctx (stateShapes width))
    (distinct : cells.Distinct)
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (observed : Fin 7)
    (firstFree : (0 : Fin 7) ≠ observed) (secondFree : (1 : Fin 7) ≠ observed)
    (firstLeftFree : (2 : Fin 7) ≠ observed) (secondRightFree : (5 : Fin 7) ≠ observed)
    (activeFree : (6 : Fin 7) ≠ observed) (store : Store ctx) :
    (initializationStore cells input zero store).read
        (.storage (cellAt cells observed).ref.toCStorageRef) =
      store.read (.storage (cellAt cells observed).ref.toCStorageRef) := by
  unfold initializationStore
  rw [preserve_index cells distinct (GCD.negateActiveOp (activeCell cells))
      6 observed rfl activeFree,
    preserve_index cells distinct (GCD.testActiveOp (firstCell cells) zero (activeCell cells))
      6 observed rfl activeFree,
    preserve_index cells distinct (incrementSecondRightOp cells) 5 observed rfl secondRightFree,
    preserve_index cells distinct (incrementFirstLeftOp cells) 2 observed rfl firstLeftFree,
    preserve_index cells distinct (copySecondOp cells input) 1 observed rfl secondFree,
    preserve_index cells distinct (copyFirstOp cells input) 0 observed rfl firstFree]

/-- Actual fresh state cells attain the original operands, coefficient basis, and activity. -/
theorem xgcdNativeInitialization_store_values {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) (store : Store ctx)
    (initialized : cells.Initialized store)
    (zeroValue : (store.read (transport.liftInput zero)).toNat = 0) :
    let final := initializationStore cells
      (transport.liftInput input) (transport.liftInput zero) store
    final.read (GCD.cellRead (firstCell cells)) = (store.read (transport.liftInput input)).first ∧
      final.read (GCD.cellRead (secondCell cells)) =
        (store.read (transport.liftInput input)).second ∧
      final.read (GCD.cellRead (firstLeftCell cells)) =
        CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 1 ∧
      final.read (GCD.cellRead (firstRightCell cells)) =
        CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 0 ∧
      final.read (GCD.cellRead (secondLeftCell cells)) =
        CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 0 ∧
      final.read (GCD.cellRead (secondRightCell cells)) =
        CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 1 ∧
      (final.read (GCD.cellRead (activeCell cells))).toBool =
        !decide ((store.read (transport.liftInput input)).first.toNat = 0) := by
  let liftedInput := transport.liftInput input
  let liftedZero := transport.liftInput zero
  let copiedFirst := store.applyOp (copyFirstOp cells liftedInput)
  let copiedBoth := copiedFirst.applyOp (copySecondOp cells liftedInput)
  let leftBasis := copiedBoth.applyOp (incrementFirstLeftOp cells)
  let bothBasis := leftBasis.applyOp (incrementSecondRightOp cells)
  let tested := bothBasis.applyOp (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells))
  let final := tested.applyOp (GCD.negateActiveOp (activeCell cells))
  have copiedFirstValue : copiedFirst.read (GCD.cellRead (firstCell cells)) =
      (store.read liftedInput).first :=
    Store.read_applyOp_output store (copyFirstOp cells liftedInput)
  have copiedFirstInput : copiedFirst.read liftedInput = store.read liftedInput :=
    preserve_caller cells transport separated (copyFirstOp cells liftedInput) 0 rfl input store
  have copiedSecondValue : copiedBoth.read (GCD.cellRead (secondCell cells)) =
      (store.read liftedInput).second := by
    have actual := Store.read_applyOp_output copiedFirst (copySecondOp cells liftedInput)
    change copiedBoth.read (GCD.cellRead (secondCell cells)) =
      (copiedFirst.read liftedInput).second at actual
    exact actual.trans (congrArg CShape.Value.second copiedFirstInput)
  have bothFirst : bothBasis.read (GCD.cellRead (firstCell cells)) =
      (store.read liftedInput).first := by
    change (((copiedFirst.applyOp (copySecondOp cells liftedInput)).applyOp
      (incrementFirstLeftOp cells)).applyOp (incrementSecondRightOp cells)).read _ = _
    rw [preserve_cell cells distinct (incrementSecondRightOp cells) 5 0 (firstCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (incrementFirstLeftOp cells) 2 0 (firstCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (copySecondOp cells liftedInput) 1 0 (firstCell cells)
        rfl rfl (by decide)]
    exact copiedFirstValue
  have bothZero : bothBasis.read liftedZero = store.read liftedZero := by
    change ((((store.applyOp (copyFirstOp cells liftedInput)).applyOp
      (copySecondOp cells liftedInput)).applyOp (incrementFirstLeftOp cells)).applyOp
        (incrementSecondRightOp cells)).read _ = _
    rw [preserve_caller cells transport separated (incrementSecondRightOp cells) 5 rfl,
      preserve_caller cells transport separated (incrementFirstLeftOp cells) 2 rfl,
      preserve_caller cells transport separated (copySecondOp cells liftedInput) 1 rfl,
      preserve_caller cells transport separated (copyFirstOp cells liftedInput) 0 rfl]
  have leftInitial : copiedBoth.read (GCD.cellRead (firstLeftCell cells)) =
      CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 0 := by
    change ((store.applyOp (copyFirstOp cells liftedInput)).applyOp
      (copySecondOp cells liftedInput)).read _ = _
    rw [preserve_cell cells distinct (copySecondOp cells liftedInput) 1 2 (firstLeftCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (copyFirstOp cells liftedInput) 0 2 (firstLeftCell cells)
        rfl rfl (by decide)]
    exact xgcdNativeState_initial_value cells store initialized 2
  have leftBasisValue : leftBasis.read (GCD.cellRead (firstLeftCell cells)) =
      CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 1 := by
    have actual := Store.read_applyOp_output copiedBoth (incrementFirstLeftOp cells)
    change leftBasis.read (GCD.cellRead (firstLeftCell cells)) =
      Resource.WordUnaryOpcode.eval .increment (PureXGCD.executionCoefficientWidth width)
        (copiedBoth.read (GCD.cellRead (firstLeftCell cells))) at actual
    rw [leftInitial] at actual
    simpa only [Resource.WordUnaryOpcode.eval, CShape.wordOfNat, CShape.Value.toNat,
      Nat.zero_mod, Nat.zero_add] using actual
  have rightInitial : leftBasis.read (GCD.cellRead (secondRightCell cells)) =
      CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 0 := by
    change (((store.applyOp (copyFirstOp cells liftedInput)).applyOp
      (copySecondOp cells liftedInput)).applyOp (incrementFirstLeftOp cells)).read _ = _
    rw [preserve_cell cells distinct (incrementFirstLeftOp cells) 2 5 (secondRightCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (copySecondOp cells liftedInput) 1 5 (secondRightCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (copyFirstOp cells liftedInput) 0 5 (secondRightCell cells)
        rfl rfl (by decide)]
    exact xgcdNativeState_initial_value cells store initialized 5
  have rightBasisValue : bothBasis.read (GCD.cellRead (secondRightCell cells)) =
      CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) 1 := by
    have actual := Store.read_applyOp_output leftBasis (incrementSecondRightOp cells)
    change bothBasis.read (GCD.cellRead (secondRightCell cells)) =
      Resource.WordUnaryOpcode.eval .increment (PureXGCD.executionCoefficientWidth width)
        (leftBasis.read (GCD.cellRead (secondRightCell cells))) at actual
    rw [rightInitial] at actual
    simpa only [Resource.WordUnaryOpcode.eval, CShape.wordOfNat, CShape.Value.toNat,
      Nat.zero_mod, Nat.zero_add] using actual
  change final.read _ = _ ∧ final.read _ = _ ∧ final.read _ = _ ∧
    final.read _ = _ ∧ final.read _ = _ ∧ final.read _ = _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (tested.applyOp (GCD.negateActiveOp (activeCell cells))).read _ = _
    rw [preserve_cell cells distinct (GCD.negateActiveOp (activeCell cells)) 6 0 (firstCell cells)
        rfl rfl (by decide)]
    change (bothBasis.applyOp (GCD.testActiveOp (firstCell cells) liftedZero
      (activeCell cells))).read _ = _
    rw [preserve_cell cells distinct
      (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells)) 6 0 (firstCell cells)
        rfl rfl (by decide)]
    exact bothFirst
  · change (((((copiedBoth.applyOp (incrementFirstLeftOp cells)).applyOp
      (incrementSecondRightOp cells)).applyOp
        (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells))).applyOp
          (GCD.negateActiveOp (activeCell cells))).read _) = _
    rw [preserve_cell cells distinct (GCD.negateActiveOp (activeCell cells)) 6 1 (secondCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct
        (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells)) 6 1 (secondCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (incrementSecondRightOp cells) 5 1 (secondCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (incrementFirstLeftOp cells) 2 1 (secondCell cells)
        rfl rfl (by decide)]
    exact copiedSecondValue
  · change ((((leftBasis.applyOp (incrementSecondRightOp cells)).applyOp
      (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells))).applyOp
        (GCD.negateActiveOp (activeCell cells))).read _) = _
    rw [preserve_cell cells distinct (GCD.negateActiveOp (activeCell cells)) 6 2
        (firstLeftCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct
        (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells)) 6 2
        (firstLeftCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct (incrementSecondRightOp cells) 5 2 (firstLeftCell cells)
        rfl rfl (by decide)]
    exact leftBasisValue
  · exact (preserve_unwritten cells distinct liftedInput liftedZero 3
      (by decide) (by decide) (by decide) (by decide) (by decide) store).trans
        (xgcdNativeState_initial_value cells store initialized 3)
  · exact (preserve_unwritten cells distinct liftedInput liftedZero 4
      (by decide) (by decide) (by decide) (by decide) (by decide) store).trans
        (xgcdNativeState_initial_value cells store initialized 4)
  · change (((bothBasis.applyOp
      (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells))).applyOp
        (GCD.negateActiveOp (activeCell cells))).read _) = _
    rw [preserve_cell cells distinct (GCD.negateActiveOp (activeCell cells)) 6 5
        (secondRightCell cells)
        rfl rfl (by decide),
      preserve_cell cells distinct
        (GCD.testActiveOp (firstCell cells) liftedZero (activeCell cells)) 6 5
        (secondRightCell cells)
        rfl rfl (by decide)]
    exact rightBasisValue
  · change ((tested.applyOp (GCD.negateActiveOp (activeCell cells))).read _).toBool = _
    rw [GCD.negate_read, GCD.test_read, bothFirst, bothZero, zeroValue]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
