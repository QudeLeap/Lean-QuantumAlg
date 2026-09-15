/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot.Refresh

/-!
# Caller-owned Gram matrix layout

The six Gram entries share one product word. The nine basis coordinates avoid
all seven writable cells; the seven writable identities remain pairwise distinct.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine

open Execution

noncomputable section

/-- The six lower-triangular Gram entries and the shared product scratch. -/
inductive MetricCell where
  | g11
  | g21
  | g31
  | g22
  | g32
  | g33
  | product
deriving DecidableEq

/-- The nine fixed source coordinates of the ordered three-row basis. -/
inductive BasisCell where
  | firstFirst
  | firstSecond
  | firstThird
  | secondFirst
  | secondSecond
  | secondThird
  | thirdFirst
  | thirdSecond
  | thirdThird
deriving DecidableEq

/-- Seven caller-owned words used by one Gram snapshot. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Writable cell for the g 11 value. -/
  g11 : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  g11Role : g11.toCStorageRef.role = .workspace
  /-- Writable cell for the g 21 value. -/
  g21 : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  g21Role : g21.toCStorageRef.role = .workspace
  /-- Writable cell for the g 31 value. -/
  g31 : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  g31Role : g31.toCStorageRef.role = .workspace
  /-- Writable cell for the g 22 value. -/
  g22 : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  g22Role : g22.toCStorageRef.role = .workspace
  /-- Writable cell for the g 32 value. -/
  g32 : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  g32Role : g32.toCStorageRef.role = .workspace
  /-- Writable cell for the g 33 value. -/
  g33 : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  g33Role : g33.toCStorageRef.role = .workspace
  /-- Writable cell for the product value. -/
  product : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  productRole : product.toCStorageRef.role = .workspace

/-- Resolve a named Gram cell to its concrete writable word. -/
def metricCellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    MetricCell → CWriteRef ctx (LatticeState.RawSignedWordShape width)
  | .g11 => refs.g11
  | .g21 => refs.g21
  | .g31 => refs.g31
  | .g22 => refs.g22
  | .g32 => refs.g32
  | .g33 => refs.g33
  | .product => refs.product

/-- Concrete storage identity of one named Gram cell. -/
def metricCellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : MetricCell → StorageKey :=
  fun cell => (metricCellRef refs cell).toCStorageRef.key

/-- Structural read of one named source coordinate of an ordered basis. -/
def basisCellInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) :
    BasisCell → CInputRef ctx (LatticeState.RawSignedWordShape width)
  | .firstFirst => LatticeState.coordinateInput basis.first.first
  | .firstSecond => LatticeState.coordinateInput basis.first.second
  | .firstThird => LatticeState.coordinateInput basis.first.third
  | .secondFirst => LatticeState.coordinateInput basis.second.first
  | .secondSecond => LatticeState.coordinateInput basis.second.second
  | .secondThird => LatticeState.coordinateInput basis.second.third
  | .thirdFirst => LatticeState.coordinateInput basis.third.first
  | .thirdSecond => LatticeState.coordinateInput basis.third.second
  | .thirdThird => LatticeState.coordinateInput basis.third.third

/-- Source coordinates avoid all writes, whose seven identities are pairwise distinct. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width) : Prop where
  keyInjective : Function.Injective (metricCellKey refs)
  basisAvoids : ∀ source : BasisCell, ∀ target : MetricCell,
    metricCellKey refs target ∉ (basisCellInput basis source).storageKeys

/-- The six actual Gram outputs, excluding the shared product scratch. -/
inductive Entry where
  | g11 | g21 | g31 | g22 | g32 | g33
deriving DecidableEq

/-- One of the original three basis rows. -/
inductive Row where
  | first | second | third
deriving DecidableEq

/-- Named writable destination of one Gram entry. -/
abbrev entryCell : Entry → MetricCell
  | .g11 => .g11
  | .g21 => .g21
  | .g31 => .g31
  | .g22 => .g22
  | .g32 => .g32
  | .g33 => .g33

/-- Left row of the selected lower-triangular entry. -/
abbrev leftRow : Entry → Row
  | .g11 => .first
  | .g21 => .second
  | .g31 => .third
  | .g22 => .second
  | .g32 => .third
  | .g33 => .third

/-- Right row of the selected lower-triangular entry. -/
abbrev rightRow : Entry → Row
  | .g11 | .g21 | .g31 => .first
  | .g22 | .g32 => .second
  | .g33 => .third

/-- Resolve a basis row without introducing any storage. -/
abbrev rowRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) : Row → LatticeState.PointRefs ctx width
  | .first => basis.first
  | .second => basis.second
  | .third => basis.third

/-- Original integer value of one selected basis row. -/
abbrev rowValue (basis : NumberTheory.IntegerBasis3) : Row → NumberTheory.IntegerPoint3
  | .first => basis.first
  | .second => basis.second
  | .third => basis.third

/-- Original integer Gram entry, independent of the circuit and its store. -/
def entryValue (basis : NumberTheory.IntegerBasis3) (entry : Entry) : Int :=
  NumberTheory.integerPointDot (rowValue basis (leftRow entry)) (rowValue basis (rightRow entry))

/-- The selected dot refresh uses its destination and the common product word. -/
def entryRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (entry : Entry) : LatticeDotRefresh.Refs ctx width where
  dot := metricCellRef refs (entryCell entry)
  dotRole := by
    cases entry
    · exact refs.g11Role
    · exact refs.g21Role
    · exact refs.g31Role
    · exact refs.g22Role
    · exact refs.g32Role
    · exact refs.g33Role
  product := refs.product
  productRole := refs.productRole

/-- All original basis rows are represented in the actual store. -/
def BasisRawRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (store : Store ctx) (basis : LatticeState.BasisRefs ctx width)
    (value : NumberTheory.IntegerBasis3) : Prop :=
  ∀ row, LatticeArithmetic.PointRawRepresents store (rowRefs basis row) (rowValue value row)

/-- All six original integer Gram entries are represented in their actual cells. -/
def GramRawRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (store : Store ctx) (refs : Refs ctx width) (value : NumberTheory.IntegerBasis3) : Prop :=
  ∀ entry, ClassicalRoutines.NumberTheory.SignedWord.RawSignedRepresents
    (store.read (.storage (metricCellRef refs (entryCell entry)).toCStorageRef))
    (entryValue value entry)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine
