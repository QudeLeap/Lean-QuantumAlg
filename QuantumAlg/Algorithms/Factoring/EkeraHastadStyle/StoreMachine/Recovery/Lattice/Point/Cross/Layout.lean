/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate

/-!
# Actual cross-product input and scratch separation

Named source coordinates and five writable words describe the caller's existing
storage. Separation refers only to those actual storage keys.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

/-- The six source coordinates of one point cross product. -/
inductive SourceCell where
  | leftFirst
  | leftSecond
  | leftThird
  | rightFirst
  | rightSecond
  | rightThird
deriving DecidableEq

/-- Structural read of one named source coordinate. -/
abbrev sourceInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (left right : LatticeState.PointRefs ctx width) :
    SourceCell → CInputRef ctx (LatticeState.RawSignedWordShape width)
  | .leftFirst => LatticeState.coordinateInput left.first
  | .leftSecond => LatticeState.coordinateInput left.second
  | .leftThird => LatticeState.coordinateInput left.third
  | .rightFirst => LatticeState.coordinateInput right.first
  | .rightSecond => LatticeState.coordinateInput right.second
  | .rightThird => LatticeState.coordinateInput right.third

/-- The five mutable words used by one point cross product. -/
inductive MutableCell where
  | outputFirst
  | outputSecond
  | outputThird
  | productLeft
  | productRight
deriving DecidableEq

/-- Resolve a named mutable cross-product word. -/
abbrev mutableRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : LatticeState.PointRefs ctx width)
    (productLeft productRight :
      CWriteRef ctx (LatticeState.RawSignedWordShape width)) :
    MutableCell → CWriteRef ctx (LatticeState.RawSignedWordShape width)
  | .outputFirst => output.first
  | .outputSecond => output.second
  | .outputThird => output.third
  | .productLeft => productLeft
  | .productRight => productRight

/-- Storage identity of one named mutable cross-product word. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : LatticeState.PointRefs ctx width)
    (productLeft productRight :
      CWriteRef ctx (LatticeState.RawSignedWordShape width)) :
    MutableCell → StorageKey :=
  fun cell => (mutableRef output productLeft productRight cell).toCStorageRef.key

/-- Separation of all sources from all writes and pairwise separation of the
five mutable cells. -/
structure PointCrossSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight :
      CWriteRef ctx (LatticeState.RawSignedWordShape width)) : Prop where
  sourceAvoidsMutable : ∀ source cell,
    mutableKey output productLeft productRight cell ∉
      (sourceInput left right source).storageKeys
  mutableInjective : Function.Injective
    (mutableKey output productLeft productRight)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross
