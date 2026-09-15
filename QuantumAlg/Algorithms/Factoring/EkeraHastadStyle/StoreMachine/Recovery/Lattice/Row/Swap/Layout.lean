/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Movement

/-!
# Actual row-swap layout

The original six row coordinates and shared scratch occupy seven distinct
words. No initial scratch value is required by the ordered copy schedule.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap

noncomputable section

/-- The seven mutable words involved in a point swap. -/
inductive PointSwapCell where
  | leftFirst
  | leftSecond
  | leftThird
  | rightFirst
  | rightSecond
  | rightThird
  | scratch
deriving DecidableEq

/-- Resolve a named point-swap cell to its concrete mutable word. -/
abbrev pointSwapCellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (LatticeState.RawSignedWordShape width)) :
    PointSwapCell → CWriteRef ctx (LatticeState.RawSignedWordShape width)
  | .leftFirst => left.first
  | .leftSecond => left.second
  | .leftThird => left.third
  | .rightFirst => right.first
  | .rightSecond => right.second
  | .rightThird => right.third
  | .scratch => scratch

/-- Concrete storage identity of one named point-swap cell. -/
def pointSwapCellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (LatticeState.RawSignedWordShape width)) :
    PointSwapCell → StorageKey :=
  fun cell => (pointSwapCellRef left right scratch cell).toCStorageRef.key

/-- The two points and their shared scratch occupy distinct mutable words. -/
structure PointSwapSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (LatticeState.RawSignedWordShape width)) : Prop where
  keyInjective : Function.Injective (pointSwapCellKey left right scratch)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap
