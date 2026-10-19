/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.Program

/-!
# Exact actual source-basis values and original caller frame

The actual first row represents both original decoded samples and one. The
actual initialized lower-row powers represent the source lattice modulus.
All four original zero coordinates and every read outside the five supplied
write identities survive the complete chronological circuit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeLoading

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N width : Nat}

/-- Both actual native power loaders preserve the complete frame outside their two outputs. -/
lemma powerRowsInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (m ell : Nat) (output : RawOutputRefs ctx width)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (b21 : output.b21.key ∉ other.storageKeys) (b32 : output.b32.key ∉ other.storageKeys) :
    (powerRowsStep m ell output store).1.read other = store.read other := by
  change (Word.PowerOfTwo.step (ell + m) output.b32
    (Word.PowerOfTwo.step (ell + m) output.b21 store).1).1.read other = _
  rw [Word.PowerOfTwo.into_callerFrame _ _ _ other b32,
    Word.PowerOfTwo.into_callerFrame _ _ _ other b21]

/-- The complete actual basis loader preserves every read outside its original five write cells. -/
lemma loadBasisInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (b11 : output.b11.key ∉ other.storageKeys)
    (b12 : output.b12.key ∉ other.storageKeys) (b13 : output.b13.key ∉ other.storageKeys)
    (b21 : output.b21.key ∉ other.storageKeys) (b32 : output.b32.key ∉ other.storageKeys) :
    (basisStep m ell pair output store).1.read other = store.read other := by
  change (powerRowsStep m ell output (firstRowStep pair output store).1).1.read other = _
  rw [powerRowsInto_callerFrame _ _ _ _ other b21 b32]
  exact loadFirstBasisRowInto_callerFrame pair output store other b11 b12 b13

/-- Actual lower-row power loading preserves all previously materialized first-row values. -/
lemma powerRowsInto_firstRow {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (separation : Separation pair output)
    (store : Store ctx) (cell : FirstRowCell) :
    (powerRowsStep m ell output store).1.read (firstRowInput output cell) =
      store.read (firstRowInput output cell) :=
  powerRowsInto_callerFrame m ell output store _ (separation.firstRowAvoidsB21 cell)
    (separation.firstRowAvoidsB32 cell)

/-- Every original zero coordinate is unchanged through the full actual basis loader. -/
lemma loadBasisInto_zeroFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (separation : Separation pair output)
    (store : Store ctx) (cell : ZeroCell) :
    (basisStep m ell pair output store).1.read (zeroCellInput output cell) =
      store.read (zeroCellInput output cell) :=
  loadBasisInto_callerFrame m ell pair output store _
    (separation.zeroCellAvoidsFirstRow cell).1 (separation.zeroCellAvoidsFirstRow cell).2.1
    (separation.zeroCellAvoidsFirstRow cell).2.2
    (separation.zeroCellAvoidsB21 cell) (separation.zeroCellAvoidsB32 cell)

/-- Original nine-cell raw basis semantics and the complete actual five-write caller frame. -/
structure BasisOutcome (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (before after : Store ctx) : Prop where
  b11 : RawSignedRepresents (after.read (writeInput output.b11))
    ((before.read (writeInput pair.first.j)).toNat : Int)
  b12 : RawSignedRepresents (after.read (writeInput output.b12))
    ((before.read (writeInput pair.second.j)).toNat : Int)
  b13 : RawSignedRepresents (after.read (writeInput output.b13)) 1
  b21 : RawSignedRepresents (after.read (writeInput output.b21)) ((2 : Int) ^ (ell + m))
  b32 : RawSignedRepresents (after.read (writeInput output.b32)) ((2 : Int) ^ (ell + m))
  zeros : InitialZeros output after
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    output.b11.key ∉ other.storageKeys → output.b12.key ∉ other.storageKeys →
      output.b13.key ∉ other.storageKeys → output.b21.key ∉ other.storageKeys →
        output.b32.key ∉ other.storageKeys → after.read other = before.read other

/-- The actual native circuit realizes all original basis values and the original complete frame. -/
lemma loadBasisInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (separation : Separation pair output)
    (store : Store ctx) (zeros : InitialZeros output store) :
    BasisOutcome m ell pair output store (basisStep m ell pair output store).1 := by
  have first := loadFirstBasisRowInto_correct pair output separation.first store
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, loadBasisInto_callerFrame m ell pair output store⟩
  · change RawSignedRepresents
      ((powerRowsStep m ell output (firstRowStep pair output store).1).1.read
        (firstRowInput output .b11)) _
    rw [powerRowsInto_firstRow m ell pair output separation]
    exact first.first
  · change RawSignedRepresents
      ((powerRowsStep m ell output (firstRowStep pair output store).1).1.read
        (firstRowInput output .b12)) _
    rw [powerRowsInto_firstRow m ell pair output separation]
    exact first.second
  · change RawSignedRepresents
      ((powerRowsStep m ell output (firstRowStep pair output store).1).1.read
        (firstRowInput output .b13)) 1
    rw [powerRowsInto_firstRow m ell pair output separation]
    exact first.third
  · change RawSignedRepresents
      ((Word.PowerOfTwo.step (ell + m) output.b32
        (Word.PowerOfTwo.step (ell + m) output.b21 (firstRowStep pair output store).1).1).1.read
        (writeInput output.b21)) _
    rw [Word.PowerOfTwo.into_callerFrame _ _ _ _ separation.b21AvoidsB32]
    exact loadPowerOfTwoInto_represents _ _ _
  · exact loadPowerOfTwoInto_represents _ _ _
  · intro cell
    rw [loadBasisInto_zeroFrame m ell pair output separation]
    exact zeros cell

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis
