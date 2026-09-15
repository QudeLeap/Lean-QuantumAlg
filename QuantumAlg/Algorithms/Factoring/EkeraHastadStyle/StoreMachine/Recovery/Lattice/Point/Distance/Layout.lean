/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Difference.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Difference.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot.Refresh

/-!
# Squared-distance cells with explicit native initialization
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSquaredDistanceMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

/-- Caller-owned cells for one raw squared-distance calculation. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The point-target subtraction submachine and its three-coordinate output. -/
  difference : LatticePointDifferenceMachine.Refs ctx width
  /-- The actual dot refresh overwrites this word with the three coordinate squares. -/
  squaredDistance : CWriteRef ctx (.unsignedWord width)
  squaredDistanceRole : squaredDistance.toCStorageRef.role = .workspace
  /-- Shared low-word product scratch for the literal multiply-accumulate calls. -/
  product : CWriteRef ctx (.unsignedWord width)
  productRole : product.toCStorageRef.role = .workspace

/-- Original subtraction and self-dot separation; arbitrary initial scratch is accepted. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  difference : LatticePointDifferenceMachine.Separation refs.difference
  dot : LatticeDot.PointDotSeparation refs.difference.difference
    refs.difference.difference refs.squaredDistance refs.product

/-- Original distance and product cells viewed by the existing native dot refresh. -/
def dotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.squaredDistance
  dotRole := refs.squaredDistanceRole
  product := refs.product
  productRole := refs.productRole

/-- Only the two mathematical source points are needed at actual circuit entry. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (store : Store ctx) (refs : Refs ctx width)
    (pointValue targetValue : NumberTheory.IntegerPoint3) : Prop where
  point : LatticeArithmetic.PointRawRepresents store refs.difference.point pointValue
  target : LatticeArithmetic.PointRawRepresents store refs.difference.target targetValue

/-- Caller reads outside all five original write cells remain available. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.difference.difference.first.key ∉ other.storageKeys →
      refs.difference.difference.second.key ∉ other.storageKeys →
        refs.difference.difference.third.key ∉ other.storageKeys →
          refs.squaredDistance.key ∉ other.storageKeys → refs.product.key ∉ other.storageKeys →
            after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSquaredDistanceMachine
