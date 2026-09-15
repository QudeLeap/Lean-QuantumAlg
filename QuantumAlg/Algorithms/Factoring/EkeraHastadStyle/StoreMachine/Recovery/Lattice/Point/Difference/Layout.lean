/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate

/-!
# Caller-owned raw point difference layout

The original six sources avoid the three pairwise distinct difference cells.
The three outputs may initially contain arbitrary raw words.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine

noncomputable section

/-- Caller-owned points for one coordinatewise raw difference. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The point from which the target is subtracted. -/
  point : LatticeState.PointRefs ctx width
  /-- The target point read by the subtraction. -/
  target : LatticeState.PointRefs ctx width
  /-- Workspace receiving `point - target`. -/
  difference : LatticeState.PointRefs ctx width

/-- The six read-only point and target coordinates. -/
inductive SourceCell where
  | pointFirst | pointSecond | pointThird
  | targetFirst | targetSecond | targetThird
deriving DecidableEq

/-- The three independently overwritten difference coordinates. -/
inductive DifferenceCell where
  | first | second | third
deriving DecidableEq

/-- Resolve a named read-only coordinate to its structural input reference. -/
def sourceInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    SourceCell → CInputRef ctx (.unsignedWord width)
  | .pointFirst => LatticeState.coordinateInput refs.point.first
  | .pointSecond => LatticeState.coordinateInput refs.point.second
  | .pointThird => LatticeState.coordinateInput refs.point.third
  | .targetFirst => LatticeState.coordinateInput refs.target.first
  | .targetSecond => LatticeState.coordinateInput refs.target.second
  | .targetThird => LatticeState.coordinateInput refs.target.third

/-- Resolve a named destination coordinate to its caller-owned write reference. -/
abbrev differenceRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    DifferenceCell → CWriteRef ctx (.unsignedWord width)
  | .first => refs.difference.first
  | .second => refs.difference.second
  | .third => refs.difference.third

/-- Storage identity of one difference destination coordinate. -/
def differenceKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (cell : DifferenceCell) : StorageKey :=
  (differenceRef refs cell).toCStorageRef.key

/-- Complete source-versus-destination and destination-versus-destination separation. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  sourceAvoidsDifference : ∀ source difference,
    differenceKey refs difference ∉ (sourceInput refs source).storageKeys
  differenceInjective : Function.Injective (differenceKey refs)

/-- Original point coordinate supplying the selected subtraction. -/
abbrev pointSource : DifferenceCell → SourceCell
  | .first => .pointFirst
  | .second => .pointSecond
  | .third => .pointThird

/-- Original target coordinate supplying the selected subtraction. -/
abbrev targetSource : DifferenceCell → SourceCell
  | .first => .targetFirst
  | .second => .targetSecond
  | .third => .targetThird

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine
