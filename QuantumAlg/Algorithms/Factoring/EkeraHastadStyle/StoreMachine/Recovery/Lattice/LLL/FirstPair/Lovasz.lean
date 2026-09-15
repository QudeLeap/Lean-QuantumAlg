/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Comparison.Doubled.Correctness
import all QuantumAlg.Components.Classical.Comparison.Doubled.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Layout

/-!
# Actual first Lovasz decision

The actual Gram cells feed the shared doubled-word comparison. The original
capacity conditions recover the source first Lovasz test, while all six Gram
entries are retained and the scratch word is explicitly counted.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLovasz

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Caller-owned bit receiving the actual first Lovasz decision. -/
structure FirstLovaszRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) where
  passes : CWriteRef ctx .bit
  passesRole : passes.toCStorageRef.role = .workspace

/-- Original separation of the seven Gram words and the decision bit. -/
structure FirstLovaszSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (metric : LatticeMetricMachine.Refs ctx width) (refs : FirstLovaszRefs ctx) : Prop where
  metricKeyInjective : Function.Injective (LatticeMetricMachine.metricCellKey metric)
  metricAvoidsPass : ∀ cell : LatticeMetricMachine.MetricCell,
    refs.passes.key ∉
      (CInputRef.storage (LatticeMetricMachine.metricCellRef metric cell).toCStorageRef).storageKeys

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The common comparison reads the two actual squared-norm cells and uses the original scratch. -/
abbrev firstComparisonRefs (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) : ClassicalRoutines.Comparison.Doubled.Refs ctx width where
  left := .storage metric.g11.toCStorageRef
  right := .storage metric.g22.toCStorageRef
  doubled := metric.product
  passes := refs.passes

private theorem metric_avoids_product (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) (separation : FirstLovaszSeparation metric refs)
    (cell : LatticeMetricMachine.MetricCell) (different : cell ≠ .product) :
    metric.product.key ∉
      (CInputRef.storage
        (LatticeMetricMachine.metricCellRef metric cell).toCStorageRef).storageKeys := by
  change LatticeMetricMachine.metricCellKey metric .product ∉
    [LatticeMetricMachine.metricCellKey metric cell]
  simp only [List.mem_singleton]
  intro equal
  exact different (separation.metricKeyInjective equal).symm

/-- The original first-test layout discharges the common comparison's complete separation. -/
theorem firstComparison_separation (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) (separation : FirstLovaszSeparation metric refs) :
    ClassicalRoutines.Comparison.Doubled.Separation (firstComparisonRefs metric refs) := by
  refine ⟨metric_avoids_product metric refs separation .g11 (by decide),
    metric_avoids_product metric refs separation .g22 (by decide),
    separation.metricAvoidsPass .g11, separation.metricAvoidsPass .g22, ?_⟩
  have avoids := separation.metricAvoidsPass .product
  simpa only [CInputRef.storageKeys, List.mem_singleton, LatticeMetricMachine.metricCellRef]
    using avoids

/-- Execute the actual first Lovasz decision through the shared native comparison. -/
def firstLovaszInto (metric : LatticeMetricMachine.Refs ctx width) (refs : FirstLovaszRefs ctx) :
    Circuit ctx ctx :=
  ClassicalRoutines.Comparison.Doubled.compareInto (firstComparisonRefs metric refs)

/-- Actual chronological store of the first Lovasz decision. -/
def firstLovaszStore
    (metric : LatticeMetricMachine.Refs ctx width) (refs : FirstLovaszRefs ctx)
    (store : Store ctx) : Store ctx :=
  ClassicalRoutines.Comparison.Doubled.comparedStore (firstComparisonRefs metric refs) store

/-- Full actual first-test execution retains histories and quantum-reference correlations. -/
theorem firstLovaszInto_execute (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (firstLovaszInto metric refs).execute Reference state = state.mapClassical (fun entry =>
      (firstLovaszStore metric refs entry.1, (entry.2, ((), ((), ()))))) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_execute _ Reference state

/-- Original unsigned norm bounds give the actual first-test decision bit. -/
theorem firstLovaszInto_matches_rawNorms (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) (separation : FirstLovaszSeparation metric refs)
    (store : Store ctx) (firstNorm secondNorm : Nat)
    (firstRepresents : RawSignedRepresents (store.read (.storage metric.g11.toCStorageRef))
      (firstNorm : Int))
    (secondRepresents : RawSignedRepresents (store.read (.storage metric.g22.toCStorageRef))
      (secondNorm : Int))
    (firstFits : firstNorm < CShape.wordModulus width)
    (twiceSecondFits : 2 * secondNorm < CShape.wordModulus width) :
    ((firstLovaszStore metric refs store).read (.storage refs.passes.toCStorageRef)).toBool =
      decide (firstNorm ≤ 2 * secondNorm) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_correct _
    (firstComparison_separation metric refs separation) store firstNorm secondNorm
    firstRepresents secondRepresents firstFits twiceSecondFits

/-- The actual first-test bit matches the original basis predicate on the same numeric domain. -/
theorem firstLovaszInto_matches_firstLovasz (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) (separation : FirstLovaszSeparation metric refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (represented : LatticeMetricMachine.GramRawRepresents store metric basis)
    (g11Fits : NumberTheory.integerPointSquaredNorm basis.first < CShape.wordModulus width)
    (twiceG22Fits :
      2 * NumberTheory.integerPointSquaredNorm basis.second < CShape.wordModulus width) :
    ((firstLovaszStore metric refs store).read (.storage refs.passes.toCStorageRef)).toBool =
      basis.firstLovasz := by
  apply firstLovaszInto_matches_rawNorms metric refs separation store _ _ _ _ g11Fits twiceG22Fits
  · simpa only [LatticeMetricMachine.entryValue, LatticeMetricMachine.leftRow,
      LatticeMetricMachine.rightRow, LatticeMetricMachine.rowValue,
      NumberTheory.integerPointDot_self, LatticeMetricMachine.entryCell,
      LatticeMetricMachine.metricCellRef]
      using represented .g11
  · simpa only [LatticeMetricMachine.entryValue, LatticeMetricMachine.leftRow,
      LatticeMetricMachine.rightRow, LatticeMetricMachine.rowValue,
      NumberTheory.integerPointDot_self, LatticeMetricMachine.entryCell,
      LatticeMetricMachine.metricCellRef]
      using represented .g22

/-- Every arbitrary caller read outside the scratch word and actual decision bit survives. -/
theorem firstLovaszInto_callerFrame (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (scratch : metric.product.key ∉ other.storageKeys)
    (passes : refs.passes.key ∉ other.storageKeys) :
    (firstLovaszStore metric refs store).read other = store.read other :=
  ClassicalRoutines.Comparison.Doubled.compareInto_callerFrame _ store other scratch passes

/-- All six semantic Gram entries survive the actual first-test decision. -/
theorem firstLovaszInto_preservesGram (metric : LatticeMetricMachine.Refs ctx width)
    (refs : FirstLovaszRefs ctx) (separation : FirstLovaszSeparation metric refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (represented : LatticeMetricMachine.GramRawRepresents store metric basis) :
    LatticeMetricMachine.GramRawRepresents (firstLovaszStore metric refs store) metric basis := by
  intro entry
  rw [firstLovaszInto_callerFrame metric refs store _
    (metric_avoids_product metric refs separation (LatticeMetricMachine.entryCell entry)
      (by cases entry <;> decide))
    (separation.metricAvoidsPass (LatticeMetricMachine.entryCell entry))]
  exact represented entry

/-- The actual first Lovasz trace is the common independent three-operation formula. -/
theorem firstLovaszInto_events
    (metric : LatticeMetricMachine.Refs ctx width) (refs : FirstLovaszRefs ctx)
    (path : (firstLovaszInto metric refs).Path) :
    (firstLovaszInto metric refs).eventTrace path =
      ClassicalRoutines.Comparison.Doubled.comparisonTrace width :=
  ClassicalRoutines.Comparison.Doubled.compareInto_events (firstComparisonRefs metric refs) path

/-- Actual native multiplicities come from that same independent formula. -/
theorem firstLovaszInto_resourcePool
    (metric : LatticeMetricMachine.Refs ctx width) (refs : FirstLovaszRefs ctx)
    (path : (firstLovaszInto metric refs).Path) :
    (firstLovaszInto metric refs).resourcePool path =
      ResourcePool.ofList (ClassicalRoutines.Comparison.Doubled.comparisonTrace width) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_resourcePool
    (firstComparisonRefs metric refs) path

/-- The actual first Lovasz test has unit-duration serial depth three. -/
theorem firstLovaszInto_depth
    (metric : LatticeMetricMachine.Refs ctx width) (refs : FirstLovaszRefs ctx)
    (path : (firstLovaszInto metric refs).Path) :
    (firstLovaszInto metric refs).depth (fun _ => 1) path = 3 :=
  ClassicalRoutines.Comparison.Doubled.compareInto_depth (firstComparisonRefs metric refs) path

/-- The actual first test restores borrowed correlations jointly with external references. -/
theorem firstLovaszInto_borrowedRestored
    (metric : LatticeMetricMachine.Refs ctx width) (refs : FirstLovaszRefs ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (firstLovaszInto metric refs).BorrowedRestored Reference state
      ((firstLovaszInto metric refs).execute Reference state) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_borrowedRestored
    (firstComparisonRefs metric refs) Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLovasz
