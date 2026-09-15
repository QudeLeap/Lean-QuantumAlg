/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Initialization.Semantics

/-!
# The original extended-Euclidean initial state in actual storage

All six mathematical fields are read from the real remainder and coefficient
cells. The seventh cell records activity separately. Exact signed decoding
uses the unchanged execution width, including at zero operand width.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Read the original mathematical state from the six actual arithmetic cells. -/
def storedState (cells : Cells ctx (stateShapes width)) (store : Store ctx) : PureXGCD.State where
  first := (store.read (GCD.cellRead (firstCell cells))).toNat
  second := (store.read (GCD.cellRead (secondCell cells))).toNat
  firstLeftCoefficient := decodeRawSignedWord (store.read (GCD.cellRead (firstLeftCell cells)))
  firstRightCoefficient := decodeRawSignedWord (store.read (GCD.cellRead (firstRightCell cells)))
  secondLeftCoefficient := decodeRawSignedWord (store.read (GCD.cellRead (secondLeftCell cells)))
  secondRightCoefficient := decodeRawSignedWord (store.read (GCD.cellRead (secondRightCell cells)))

private theorem executionWidth_two_le (width : Nat) :
    2 ≤ PureXGCD.executionCoefficientWidth width := by
  exact (Nat.le_add_left 2 _).trans (Nat.le_max_right _ _)

private theorem initialCoefficient_range (width value : Nat) (small : value ≤ 1) :
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
      (PureXGCD.executionCoefficientWidth width) (value : Int) := by
  have widthBound := executionWidth_two_le width
  have capacity : (2 : Int) ≤ 2 ^ (PureXGCD.executionCoefficientWidth width - 1) := by
    calc
      (2 : Int) = 2 ^ (1 : Nat) := by norm_num
      _ ≤ 2 ^ (PureXGCD.executionCoefficientWidth width - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  unfold ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
  omega

private theorem initialCoefficient_decode (width value : Nat) (small : value ≤ 1) :
    decodeRawSignedWord
      (CShape.wordOfNat (PureXGCD.executionCoefficientWidth width) value) = (value : Int) := by
  apply rawSignedRepresents_decode_eq
  · exact ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_pos width
  · change ((value % CShape.wordModulus (PureXGCD.executionCoefficientWidth width) : Nat) : Int) ≡
      (value : Int) [ZMOD (CShape.wordModulus (PureXGCD.executionCoefficientWidth width) : Int)]
    exact Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  · exact initialCoefficient_range width value small

/-- Actual fresh initialization realizes the original six-field mathematical initial state. -/
theorem xgcdNativeInitialization_state {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) (store : Store ctx)
    (initialized : cells.Initialized store)
    (zeroValue : (store.read (transport.liftInput zero)).toNat = 0) :
    storedState cells (initializationStore cells
      (transport.liftInput input) (transport.liftInput zero) store) =
      PureXGCD.initialState (GCD.decodeOperands (store.read (transport.liftInput input))) := by
  have values := xgcdNativeInitialization_store_values cells distinct transport separated
    input zero store initialized zeroValue
  rcases values with ⟨first, second, firstLeft, firstRight, secondLeft, secondRight, _⟩
  unfold storedState
  rw [first, second, firstLeft, firstRight, secondLeft, secondRight,
    initialCoefficient_decode width 1 (by omega), initialCoefficient_decode width 0 (by omega)]
  cases value : store.read (transport.liftInput input) with
  | product left right =>
      cases left
      cases right
      rfl

/-- The actual Boolean activity cell agrees with the leading mathematical remainder. -/
theorem xgcdNativeInitialization_activity {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) (store : Store ctx)
    (initialized : cells.Initialized store)
    (zeroValue : (store.read (transport.liftInput zero)).toNat = 0) :
    let final := initializationStore cells
      (transport.liftInput input) (transport.liftInput zero) store
    (final.read (GCD.cellRead (activeCell cells))).toBool =
      decide ((storedState cells final).first ≠ 0) := by
  have values := xgcdNativeInitialization_store_values cells distinct transport separated
    input zero store initialized zeroValue
  dsimp only
  rw [values.2.2.2.2.2.2]
  change _ = decide (((_ : Store ctx).read (GCD.cellRead (firstCell cells))).toNat ≠ 0)
  rw [values.1]
  simp only [decide_not]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
