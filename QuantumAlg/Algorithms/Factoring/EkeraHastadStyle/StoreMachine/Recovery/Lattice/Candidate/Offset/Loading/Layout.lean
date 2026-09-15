/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate
import all QuantumAlg.Components.Classical.ConstantWord.Signed.Resources

/-!
# Original offset cells and distinct storage identities
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeOffsetMaterializer

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

/-- Three caller-owned coordinates for one materialized offset. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the offset stage. -/
  offset : LatticeState.PointRefs ctx width

/-- Names of the three offset words written by the materializer. -/
inductive MutableCell where
  | first | second | third
deriving DecidableEq

/-- Resolve one named offset word to its caller-owned write reference. -/
def mutableRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : MutableCell → CWriteRef ctx (LatticeState.RawSignedWordShape width)
  | .first => refs.offset.first
  | .second => refs.offset.second
  | .third => refs.offset.third

/-- The storage identity of one materialized offset coordinate. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (cell : MutableCell) : StorageKey :=
  (mutableRef refs cell).toCStorageRef.key

/-- Distinct caller-owned offset coordinates are required for sequential writes. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  mutableInjective : Function.Injective (mutableKey refs)


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeOffsetMaterializer
