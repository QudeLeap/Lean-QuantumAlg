/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.RowLoading.Resources

/-!
# Original actual raw basis-loading separation

The original nine basis words retain their identities and roles. Five supplied
words are written; the four caller-initialized zero words are preserved. This
keeps the complete original caller frame while constant-loading instructions
remove the old initial-zero premises on the three written constant words.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeLoading

noncomputable section

/-- Actual structural read of one original writable raw basis word. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- The three independently written cells of the first basis row. -/
inductive FirstRowCell where
  | b11
  | b12
  | b13

/-- Structural read of one first-row cell. -/
def firstRowInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : RawOutputRefs ctx width) : FirstRowCell → CInputRef ctx (.unsignedWord width)
  | .b11 => writeInput output.b11
  | .b12 => writeInput output.b12
  | .b13 => writeInput output.b13

/-- Storage identity of one first-row cell. -/
def firstRowKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : RawOutputRefs ctx width) : FirstRowCell → StorageKey
  | .b11 => output.b11.toCStorageRef.key
  | .b12 => output.b12.toCStorageRef.key
  | .b13 => output.b13.toCStorageRef.key

/-- The four raw basis cells that must remain caller-initialized zero. -/
inductive ZeroCell where
  | b22
  | b23
  | b31
  | b33

/-- Structural read of one caller-initialized zero basis cell. -/
def zeroCellInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : RawOutputRefs ctx width) : ZeroCell → CInputRef ctx (.unsignedWord width)
  | .b22 => writeInput output.b22
  | .b23 => writeInput output.b23
  | .b31 => writeInput output.b31
  | .b33 => writeInput output.b33

/-- Storage identity of one caller-initialized zero basis cell. -/
def zeroCellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : RawOutputRefs ctx width) : ZeroCell → StorageKey
  | .b22 => output.b22.toCStorageRef.key
  | .b23 => output.b23.toCStorageRef.key
  | .b31 => output.b31.toCStorageRef.key
  | .b33 => output.b33.toCStorageRef.key

/-- The original exact source, written-cell and preserved-zero separation package. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N width : Nat} (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) : Prop where
  first : FirstBasisRowSeparation pair output
  b21AvoidsFirstRow : ∀ cell : FirstRowCell,
    firstRowKey output cell ∉ (writeInput output.b21).storageKeys
  b32AvoidsFirstRow : ∀ cell : FirstRowCell,
    firstRowKey output cell ∉ (writeInput output.b32).storageKeys
  firstRowAvoidsB21 : ∀ cell : FirstRowCell,
    output.b21.key ∉ (firstRowInput output cell).storageKeys
  firstRowAvoidsB32 : ∀ cell : FirstRowCell,
    output.b32.key ∉ (firstRowInput output cell).storageKeys
  b32AvoidsB21 : output.b21.key ∉ (writeInput output.b32).storageKeys
  b21AvoidsB32 : output.b32.key ∉ (writeInput output.b21).storageKeys
  zeroCellAvoidsFirstRow : ∀ cell : ZeroCell,
    output.b11.key ∉ (zeroCellInput output cell).storageKeys ∧
      output.b12.key ∉ (zeroCellInput output cell).storageKeys ∧
        output.b13.key ∉ (zeroCellInput output cell).storageKeys
  zeroCellAvoidsB21 : ∀ cell : ZeroCell,
    output.b21.key ∉ (zeroCellInput output cell).storageKeys
  zeroCellAvoidsB32 : ∀ cell : ZeroCell,
    output.b32.key ∉ (zeroCellInput output cell).storageKeys

/-- The original four unmodified basis words carry the caller's zero representation. -/
def InitialZeros {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : RawOutputRefs ctx width) (store : Store ctx) : Prop :=
  ∀ cell : ZeroCell, RawSignedRepresents (store.read (zeroCellInput output cell)) 0

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis
