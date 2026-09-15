/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot.Refresh

/-!
# Original candidate-point cells and separation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

/-- Caller-owned cells for constructing one candidate lattice point. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The reduced lattice basis whose rows are combined. -/
  basis : LatticeState.BasisRefs ctx width
  /-- The three nearest-plane center coefficients. -/
  center : LatticeState.PointRefs ctx width
  /-- One caller-supplied three-coordinate candidate offset. -/
  offset : LatticeState.PointRefs ctx width
  /-- Workspace for the coordinatewise sum `center + offset`. -/
  coefficient : LatticeState.PointRefs ctx width
  /-- Caller-owned destination for the resulting lattice point. -/
  point : LatticeState.PointRefs ctx width
  /-- Shared low-word product scratch for the three output coordinates. -/
  product : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  productRole : product.toCStorageRef.role = .workspace

/-- All read-only basis, center, and offset coordinates used by the adapter. -/
inductive SourceCell where
  | basisFirstFirst | basisFirstSecond | basisFirstThird
  | basisSecondFirst | basisSecondSecond | basisSecondThird
  | basisThirdFirst | basisThirdSecond | basisThirdThird
  | centerFirst | centerSecond | centerThird
  | offsetFirst | offsetSecond | offsetThird
deriving DecidableEq

/-- Resolve one named source coordinate to its structural input reference. -/
def sourceInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    SourceCell → CInputRef ctx (.unsignedWord width)
  | .basisFirstFirst => LatticeState.coordinateInput refs.basis.first.first
  | .basisFirstSecond => LatticeState.coordinateInput refs.basis.first.second
  | .basisFirstThird => LatticeState.coordinateInput refs.basis.first.third
  | .basisSecondFirst => LatticeState.coordinateInput refs.basis.second.first
  | .basisSecondSecond => LatticeState.coordinateInput refs.basis.second.second
  | .basisSecondThird => LatticeState.coordinateInput refs.basis.second.third
  | .basisThirdFirst => LatticeState.coordinateInput refs.basis.third.first
  | .basisThirdSecond => LatticeState.coordinateInput refs.basis.third.second
  | .basisThirdThird => LatticeState.coordinateInput refs.basis.third.third
  | .centerFirst => LatticeState.coordinateInput refs.center.first
  | .centerSecond => LatticeState.coordinateInput refs.center.second
  | .centerThird => LatticeState.coordinateInput refs.center.third
  | .offsetFirst => LatticeState.coordinateInput refs.offset.first
  | .offsetSecond => LatticeState.coordinateInput refs.offset.second
  | .offsetThird => LatticeState.coordinateInput refs.offset.third

/-- Every word overwritten by the adapter. -/
inductive MutableCell where
  | coefficientFirst | coefficientSecond | coefficientThird
  | pointFirst | pointSecond | pointThird
  | product
deriving DecidableEq

/-- Resolve one named mutable cell to its caller-owned write reference. -/
def mutableRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    MutableCell → CWriteRef ctx (.unsignedWord width)
  | .coefficientFirst => refs.coefficient.first
  | .coefficientSecond => refs.coefficient.second
  | .coefficientThird => refs.coefficient.third
  | .pointFirst => refs.point.first
  | .pointSecond => refs.point.second
  | .pointThird => refs.point.third
  | .product => refs.product

/-- Storage identity of one mutable adapter word. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (cell : MutableCell) : StorageKey :=
  (mutableRef refs cell).toCStorageRef.key

/-- Complete source-versus-write and write-versus-write separation. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  sourceAvoidsMutable : ∀ source cell,
    mutableKey refs cell ∉ (sourceInput refs source).storageKeys
  mutableInjective : Function.Injective (mutableKey refs)

/-- The first coordinate of each basis row, viewed as one dot-product column. -/
def firstColumn {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) : LatticeState.PointRefs ctx width where
  first := basis.first.first
  firstRole := basis.first.firstRole
  second := basis.second.first
  secondRole := basis.second.firstRole
  third := basis.third.first
  thirdRole := basis.third.firstRole

/-- The second coordinate of each basis row, viewed as one dot-product column. -/
def secondColumn {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) : LatticeState.PointRefs ctx width where
  first := basis.first.second
  firstRole := basis.first.secondRole
  second := basis.second.second
  secondRole := basis.second.secondRole
  third := basis.third.second
  thirdRole := basis.third.secondRole

/-- The third coordinate of each basis row, viewed as one dot-product column. -/
def thirdColumn {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) : LatticeState.PointRefs ctx width where
  first := basis.first.third
  firstRole := basis.first.thirdRole
  second := basis.second.third
  secondRole := basis.second.thirdRole
  third := basis.third.third
  thirdRole := basis.third.thirdRole

/-- Raw modular representation of all three ordered basis rows. -/
def BasisRawRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (store : Store ctx)
    (refs : LatticeState.BasisRefs ctx width)
    (basis : NumberTheory.IntegerBasis3) : Prop :=
  LatticeArithmetic.PointRawRepresents store refs.first basis.first ∧
    LatticeArithmetic.PointRawRepresents store refs.second basis.second ∧
      LatticeArithmetic.PointRawRepresents store refs.third basis.third

/-- The three output coordinates in their original execution order. -/
inductive Coordinate where
  | first | second | third
deriving DecidableEq

/-- Resolve a coordinate in a caller-owned point. -/
abbrev pointRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (point : LatticeState.PointRefs ctx width) : Coordinate → CWriteRef ctx (.unsignedWord width)
  | .first => point.first
  | .second => point.second
  | .third => point.third

/-- Role of each caller-owned point coordinate. -/
theorem pointRef_role {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (point : LatticeState.PointRefs ctx width) (coordinate : Coordinate) :
    (pointRef point coordinate).toCStorageRef.role = .workspace := by
  cases coordinate
  · exact point.firstRole
  · exact point.secondRole
  · exact point.thirdRole

/-- Mutable identity of each coefficient output. -/
abbrev coefficientCell : Coordinate → MutableCell
  | .first => .coefficientFirst
  | .second => .coefficientSecond
  | .third => .coefficientThird

/-- Mutable identity of each lattice-point output. -/
abbrev pointCell : Coordinate → MutableCell
  | .first => .pointFirst
  | .second => .pointSecond
  | .third => .pointThird

/-- Source identity of each center coordinate. -/
abbrev centerSource : Coordinate → SourceCell
  | .first => .centerFirst
  | .second => .centerSecond
  | .third => .centerThird

/-- Source identity of each offset coordinate. -/
abbrev offsetSource : Coordinate → SourceCell
  | .first => .offsetFirst
  | .second => .offsetSecond
  | .third => .offsetThird

/-- Original basis column for the selected lattice-point output. -/
abbrev columnRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) : Coordinate → LatticeState.PointRefs ctx width
  | .first => firstColumn basis
  | .second => secondColumn basis
  | .third => thirdColumn basis

/-- Dot refresh reuses exactly the original point coordinate and product scratch. -/
def dotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (coordinate : Coordinate) : LatticeDotRefresh.Refs ctx width where
  dot := pointRef refs.point coordinate
  dotRole := pointRef_role refs.point coordinate
  product := refs.product
  productRole := refs.productRole

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine
