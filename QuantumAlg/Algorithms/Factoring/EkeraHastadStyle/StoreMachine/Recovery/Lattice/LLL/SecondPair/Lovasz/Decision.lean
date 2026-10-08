/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Comparison.Doubled.Correctness
import all QuantumAlg.Components.Classical.Comparison.Doubled.Resources

/-!
# Actual second Lovasz area decision

The original two area inputs feed the common three-instruction comparison.
The actual decision equals the original area inequality under the same unsigned
capacity bounds, while both original inputs remain unchanged.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLovasz

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Original area reads, doubled-area scratch and second-test output bit. -/
structure SecondLovaszRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  area12 : CInputRef ctx (.unsignedWord width)
  area13 : CInputRef ctx (.unsignedWord width)
  doubled : CWriteRef ctx (.unsignedWord width)
  doubledRole : doubled.toCStorageRef.role = .workspace
  passes : CWriteRef ctx .bit
  passesRole : passes.toCStorageRef.role = .workspace

/-- The original two area inputs avoid both writes; the doubled word avoids the output bit. -/
structure SecondLovaszSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : SecondLovaszRefs ctx width) : Prop where
  area12AvoidsDoubled : refs.doubled.key ∉ refs.area12.storageKeys
  area13AvoidsDoubled : refs.doubled.key ∉ refs.area13.storageKeys
  area12AvoidsPass : refs.passes.key ∉ refs.area12.storageKeys
  area13AvoidsPass : refs.passes.key ∉ refs.area13.storageKeys
  doubledAvoidsPass : refs.passes.key ∉
    (CInputRef.storage refs.doubled.toCStorageRef).storageKeys

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The second test shares its actual original references with the common comparison. -/
abbrev secondComparisonRefs (refs : SecondLovaszRefs ctx width) :
    ClassicalRoutines.Comparison.Doubled.Refs ctx width where
  left := refs.area12
  right := refs.area13
  doubled := refs.doubled
  passes := refs.passes

/-- Original second-test separation suffices for the common actual comparison. -/
theorem secondComparison_separation (refs : SecondLovaszRefs ctx width)
    (separation : SecondLovaszSeparation refs) :
    ClassicalRoutines.Comparison.Doubled.Separation (secondComparisonRefs refs) := by
  refine ⟨separation.area12AvoidsDoubled, separation.area13AvoidsDoubled,
    separation.area12AvoidsPass, separation.area13AvoidsPass, ?_⟩
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.doubledAvoidsPass

/-- Execute the actual second Lovasz test on the original area inputs. -/
def secondLovaszInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : SecondLovaszRefs ctx width) :
    Circuit model ctx ctx :=
  ClassicalRoutines.Comparison.Doubled.compareInto (model := model)
    (secondComparisonRefs refs)

/-- Actual chronological store of the second area decision. -/
def secondLovaszStore (refs : SecondLovaszRefs ctx width) (store : Store ctx) : Store ctx :=
  ClassicalRoutines.Comparison.Doubled.comparedStore (secondComparisonRefs refs) store

/-- Full actual second-test execution preserves service history and reference correlations. -/
theorem secondLovaszInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : SecondLovaszRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondLovaszInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := ClassicalRoutines.Comparison.Doubled.executionStep (model := model)
          (secondComparisonRefs refs) entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_execute _ Reference state

/-- Original area representations and capacity bounds give the actual second-test decision bit. -/
theorem secondLovaszInto_matches_rawAreas (refs : SecondLovaszRefs ctx width)
    (separation : SecondLovaszSeparation refs) (store : Store ctx)
    (area12Value area13Value : Nat)
    (area12Represents : RawSignedRepresents (store.read refs.area12) (area12Value : Int))
    (area13Represents : RawSignedRepresents (store.read refs.area13) (area13Value : Int))
    (area12Fits : area12Value < CShape.wordModulus width)
    (twiceArea13Fits : 2 * area13Value < CShape.wordModulus width) :
    ((secondLovaszStore refs store).read (.storage refs.passes.toCStorageRef)).toBool =
      decide (area12Value ≤ 2 * area13Value) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_correct _
    (secondComparison_separation refs separation) store area12Value area13Value
    area12Represents area13Represents area12Fits twiceArea13Fits

/-- Every caller read outside the two actual output cells survives the second test. -/
theorem secondLovaszInto_callerFrame (refs : SecondLovaszRefs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (doubled : refs.doubled.key ∉ other.storageKeys)
    (passes : refs.passes.key ∉ other.storageKeys) :
    (secondLovaszStore refs store).read other = store.read other :=
  ClassicalRoutines.Comparison.Doubled.compareInto_callerFrame _ store other doubled passes

/-- Both original area readings survive the actual second-test decision. -/
theorem secondLovaszInto_preservesAreas (refs : SecondLovaszRefs ctx width)
    (separation : SecondLovaszSeparation refs) (store : Store ctx) :
    (secondLovaszStore refs store).read refs.area12 = store.read refs.area12 ∧
      (secondLovaszStore refs store).read refs.area13 = store.read refs.area13 :=
  ClassicalRoutines.Comparison.Doubled.compareInto_preserves_inputs _
    (secondComparison_separation refs separation) store

/-- The actual second Lovasz trace is the common independent three-operation formula. -/
theorem secondLovaszInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : SecondLovaszRefs ctx width)
    (path : (secondLovaszInto (model := model) refs).Path) :
    (secondLovaszInto (model := model) refs).eventTrace path =
      ClassicalRoutines.Comparison.Doubled.comparisonTrace (model := model) width :=
  ClassicalRoutines.Comparison.Doubled.compareInto_events (secondComparisonRefs refs) path

/-- Actual native multiplicities come from that same independent formula. -/
theorem secondLovaszInto_resourcePool
    {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (refs : SecondLovaszRefs ctx width)
    (path : (secondLovaszInto (model := model) refs).Path) :
    (secondLovaszInto (model := model) refs).resourcePool path =
      ResourcePool.ofList
        (ClassicalRoutines.Comparison.Doubled.comparisonTrace (model := model) width) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_resourcePool (secondComparisonRefs refs) path

/-- The actual second Lovasz test has unit-duration serial depth three. -/
theorem secondLovaszInto_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : SecondLovaszRefs ctx width)
    (path : (secondLovaszInto (model := model) refs).Path) :
    (secondLovaszInto (model := model) refs).depth (fun _ => 1) path = 3 :=
  ClassicalRoutines.Comparison.Doubled.compareInto_depth (secondComparisonRefs refs) path

/-- The actual second test restores borrowed correlations jointly with external references. -/
theorem secondLovaszInto_borrowedRestored {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : SecondLovaszRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondLovaszInto (model := model) refs).BorrowedRestored Reference state
      ((secondLovaszInto (model := model) refs).execute Reference state) :=
  ClassicalRoutines.Comparison.Doubled.compareInto_borrowedRestored
    (secondComparisonRefs refs) Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLovasz
