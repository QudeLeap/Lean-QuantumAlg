/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Point.Program

/-!
# Actual candidate-point caller frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Distinct original mutable cells have disjoint actual storage identities. -/
lemma mutable_avoids (refs : Refs ctx width) (separation : Separation refs)
    (saved written : MutableCell) (different : saved ≠ written) :
    mutableKey refs written ∉ (writeInput (mutableRef refs saved)).storageKeys := by
  change mutableKey refs written ∉ [mutableKey refs saved]
  simp only [List.mem_singleton]
  intro equal
  exact different (separation.mutableInjective equal.symm)

/-- Coefficient addition retains every source coordinate from the original inputs. -/
lemma coefficient_source_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (written : Coordinate) (source : SourceCell) :
    (store.applyOp (coefficientOp refs written)).read (sourceInput refs source) =
      store.read (sourceInput refs source) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  cases written with
  | first => exact separation.sourceAvoidsMutable source .coefficientFirst
  | second => exact separation.sourceAvoidsMutable source .coefficientSecond
  | third => exact separation.sourceAvoidsMutable source .coefficientThird

/-- Later coefficient writes preserve all other original coefficient coordinates. -/
lemma coefficient_output_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (written saved : Coordinate) (different : written ≠ saved) :
    (store.applyOp (coefficientOp refs written)).read
        (writeInput (pointRef refs.coefficient saved)) =
      store.read (writeInput (pointRef refs.coefficient saved)) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  cases written <;> cases saved
  · exact False.elim (different rfl)
  · exact mutable_avoids refs separation .coefficientSecond .coefficientFirst (by decide)
  · exact mutable_avoids refs separation .coefficientThird .coefficientFirst (by decide)
  · exact mutable_avoids refs separation .coefficientFirst .coefficientSecond (by decide)
  · exact False.elim (different rfl)
  · exact mutable_avoids refs separation .coefficientThird .coefficientSecond (by decide)
  · exact mutable_avoids refs separation .coefficientFirst .coefficientThird (by decide)
  · exact mutable_avoids refs separation .coefficientSecond .coefficientThird (by decide)
  · exact False.elim (different rfl)

/-- Actual additions frame every read outside the three coefficient outputs. -/
lemma coefficientInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ coordinate, (pointRef refs.coefficient coordinate).key ∉ other.storageKeys) :
    (coefficientStore refs store).read other = store.read other := by
  unfold coefficientStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ (avoids .third),
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ (avoids .second),
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ (avoids .first)]

/-- One actual dot refresh changes only its output coordinate and shared product word. -/
lemma coordinateCombination_callerFrame (refs : Refs ctx width) (coordinate : Coordinate)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (output : (pointRef refs.point coordinate).key ∉ other.storageKeys)
    (product : refs.product.key ∉ other.storageKeys) :
    (combinationStore refs coordinate store).read other = store.read other :=
  LatticeDotRefresh.refreshInto_callerFrame _ _ _ store other output product

/-- All three dot refreshes frame reads outside the point and shared product cells. -/
lemma pointInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (output : ∀ coordinate, (pointRef refs.point coordinate).key ∉ other.storageKeys)
    (product : refs.product.key ∉ other.storageKeys) :
    (pointStore refs store).read other = store.read other := by
  unfold pointStore
  rw [coordinateCombination_callerFrame _ _ _ other (output .third) product,
    coordinateCombination_callerFrame _ _ _ other (output .second) product,
    coordinateCombination_callerFrame _ _ _ other (output .first) product]

/-- The complete original seven-cell write footprint determines the caller frame. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ cell, mutableKey refs cell ∉ other.storageKeys) → after.read other = before.read other

/-- Every actual read outside the complete original write footprint remains unchanged. -/
lemma candidatePointInto_callerFrame [BitWord.Selected model]
    (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (candidateStep (model := model) refs store).1 := by
  intro shape other avoids
  change (pointStore refs (coefficientStore refs store)).read other = _
  rw [pointInto_callerFrame refs _ other
    (by
      intro coordinate
      cases coordinate with
      | first => exact avoids .pointFirst
      | second => exact avoids .pointSecond
      | third => exact avoids .pointThird) (avoids .product)]
  exact coefficientInto_callerFrame refs store other
    (by
      intro coordinate
      cases coordinate with
      | first => exact avoids .coefficientFirst
      | second => exact avoids .coefficientSecond
      | third => exact avoids .coefficientThird)

/-- Original basis representations follow any frame preserving their nine source reads. -/
lemma basis_of_source_frames (refs : Refs ctx width) (before after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) (rep : BasisRawRepresents before refs.basis basis)
    (frames : ∀ source,
      after.read (sourceInput refs source) = before.read (sourceInput refs source)) :
    BasisRawRepresents after refs.basis basis := by
  rcases rep with ⟨⟨a, b, c⟩, ⟨d, e, f⟩, ⟨g, h, i⟩⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · change RawSignedRepresents (after.read (sourceInput refs .basisFirstFirst)) _
    rw [frames .basisFirstFirst]
    exact a
  · change RawSignedRepresents (after.read (sourceInput refs .basisFirstSecond)) _
    rw [frames .basisFirstSecond]
    exact b
  · change RawSignedRepresents (after.read (sourceInput refs .basisFirstThird)) _
    rw [frames .basisFirstThird]
    exact c
  · change RawSignedRepresents (after.read (sourceInput refs .basisSecondFirst)) _
    rw [frames .basisSecondFirst]
    exact d
  · change RawSignedRepresents (after.read (sourceInput refs .basisSecondSecond)) _
    rw [frames .basisSecondSecond]
    exact e
  · change RawSignedRepresents (after.read (sourceInput refs .basisSecondThird)) _
    rw [frames .basisSecondThird]
    exact f
  · change RawSignedRepresents (after.read (sourceInput refs .basisThirdFirst)) _
    rw [frames .basisThirdFirst]
    exact g
  · change RawSignedRepresents (after.read (sourceInput refs .basisThirdSecond)) _
    rw [frames .basisThirdSecond]
    exact h
  · change RawSignedRepresents (after.read (sourceInput refs .basisThirdThird)) _
    rw [frames .basisThirdThird]
    exact i

/-- The original basis survives every actual coefficient addition. -/
lemma basis_after_coefficient (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : BasisRawRepresents store refs.basis basis) :
    BasisRawRepresents (coefficientStore refs store) refs.basis basis := by
  apply basis_of_source_frames refs store _ basis rep
  intro source
  unfold coefficientStore
  rw [coefficient_source_frame refs separation _ .third source,
    coefficient_source_frame refs separation _ .second source,
    coefficient_source_frame refs separation _ .first source]

/-- The original basis survives one actual dot refresh. -/
lemma basis_after_combination (refs : Refs ctx width) (separation : Separation refs)
    (coordinate : Coordinate) (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : BasisRawRepresents store refs.basis basis) :
    BasisRawRepresents (combinationStore refs coordinate store) refs.basis basis := by
  apply basis_of_source_frames refs store _ basis rep
  intro source
  apply coordinateCombination_callerFrame
  · cases coordinate with
    | first => exact separation.sourceAvoidsMutable source .pointFirst
    | second => exact separation.sourceAvoidsMutable source .pointSecond
    | third => exact separation.sourceAvoidsMutable source .pointThird
  · exact separation.sourceAvoidsMutable source .product

/-- Every coefficient survives the actual dot refresh, including reuse of product scratch. -/
lemma coefficient_after_combination (refs : Refs ctx width) (separation : Separation refs)
    (coordinate : Coordinate) (store : Store ctx) (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store refs.coefficient value) :
    LatticeArithmetic.PointRawRepresents (combinationStore refs coordinate store)
      refs.coefficient value := by
  refine ⟨?_, ?_, ?_⟩
  · rw [coordinateCombination_callerFrame refs coordinate store (writeInput refs.coefficient.first)
      (by
        cases coordinate with
        | first =>
          exact mutable_avoids refs separation .coefficientFirst .pointFirst (by decide)
        | second =>
          exact mutable_avoids refs separation .coefficientFirst .pointSecond (by decide)
        | third =>
          exact mutable_avoids refs separation .coefficientFirst .pointThird (by decide))
      (mutable_avoids refs separation .coefficientFirst .product (by decide))]
    exact rep.1
  · rw [coordinateCombination_callerFrame refs coordinate store (writeInput refs.coefficient.second)
      (by
        cases coordinate with
        | first =>
          exact mutable_avoids refs separation .coefficientSecond .pointFirst (by decide)
        | second =>
          exact mutable_avoids refs separation .coefficientSecond .pointSecond (by decide)
        | third =>
          exact mutable_avoids refs separation .coefficientSecond .pointThird (by decide))
      (mutable_avoids refs separation .coefficientSecond .product (by decide))]
    exact rep.2.1
  · rw [coordinateCombination_callerFrame refs coordinate store (writeInput refs.coefficient.third)
      (by
        cases coordinate with
        | first =>
          exact mutable_avoids refs separation .coefficientThird .pointFirst (by decide)
        | second =>
          exact mutable_avoids refs separation .coefficientThird .pointSecond (by decide)
        | third =>
          exact mutable_avoids refs separation .coefficientThird .pointThird (by decide))
      (mutable_avoids refs separation .coefficientThird .product (by decide))]
    exact rep.2.2

/-- Later dot refreshes preserve each previously computed output coordinate. -/
lemma combination_output_frame (refs : Refs ctx width) (separation : Separation refs)
    (written saved : Coordinate) (different : written ≠ saved) (store : Store ctx) :
    (combinationStore refs written store).read (writeInput (pointRef refs.point saved)) =
      store.read (writeInput (pointRef refs.point saved)) := by
  apply coordinateCombination_callerFrame
  · cases written <;> cases saved
    · exact False.elim (different rfl)
    · exact mutable_avoids refs separation .pointSecond .pointFirst (by decide)
    · exact mutable_avoids refs separation .pointThird .pointFirst (by decide)
    · exact mutable_avoids refs separation .pointFirst .pointSecond (by decide)
    · exact False.elim (different rfl)
    · exact mutable_avoids refs separation .pointThird .pointSecond (by decide)
    · exact mutable_avoids refs separation .pointFirst .pointThird (by decide)
    · exact mutable_avoids refs separation .pointSecond .pointThird (by decide)
    · exact False.elim (different rfl)
  · cases saved with
    | first => exact mutable_avoids refs separation .pointFirst .product (by decide)
    | second => exact mutable_avoids refs separation .pointSecond .product (by decide)
    | third => exact mutable_avoids refs separation .pointThird .product (by decide)

/-- Original complete separation entails every read exclusion of each native dot refresh. -/
lemma combination_separation (refs : Refs ctx width) (separation : Separation refs)
    (coordinate : Coordinate) :
    LatticeDotRefresh.Separation refs.coefficient (columnRefs refs.basis coordinate)
      (dotRefs refs coordinate) := by
  cases coordinate with
  | first =>
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · exact ⟨mutable_avoids refs separation .coefficientFirst .product (by decide),
        separation.sourceAvoidsMutable .basisFirstFirst .product,
        mutable_avoids refs separation .pointFirst .product (by decide),
        mutable_avoids refs separation .coefficientFirst .pointFirst (by decide),
        separation.sourceAvoidsMutable .basisFirstFirst .pointFirst,
        mutable_avoids refs separation .product .pointFirst (by decide)⟩
    · exact ⟨mutable_avoids refs separation .coefficientSecond .product (by decide),
        separation.sourceAvoidsMutable .basisSecondFirst .product,
        mutable_avoids refs separation .pointFirst .product (by decide),
        mutable_avoids refs separation .coefficientSecond .pointFirst (by decide),
        separation.sourceAvoidsMutable .basisSecondFirst .pointFirst,
        mutable_avoids refs separation .product .pointFirst (by decide)⟩
    · exact ⟨mutable_avoids refs separation .coefficientThird .product (by decide),
        separation.sourceAvoidsMutable .basisThirdFirst .product,
        mutable_avoids refs separation .pointFirst .product (by decide),
        mutable_avoids refs separation .coefficientThird .pointFirst (by decide),
        separation.sourceAvoidsMutable .basisThirdFirst .pointFirst,
        mutable_avoids refs separation .product .pointFirst (by decide)⟩
  | second =>
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · exact ⟨mutable_avoids refs separation .coefficientFirst .product (by decide),
        separation.sourceAvoidsMutable .basisFirstSecond .product,
        mutable_avoids refs separation .pointSecond .product (by decide),
        mutable_avoids refs separation .coefficientFirst .pointSecond (by decide),
        separation.sourceAvoidsMutable .basisFirstSecond .pointSecond,
        mutable_avoids refs separation .product .pointSecond (by decide)⟩
    · exact ⟨mutable_avoids refs separation .coefficientSecond .product (by decide),
        separation.sourceAvoidsMutable .basisSecondSecond .product,
        mutable_avoids refs separation .pointSecond .product (by decide),
        mutable_avoids refs separation .coefficientSecond .pointSecond (by decide),
        separation.sourceAvoidsMutable .basisSecondSecond .pointSecond,
        mutable_avoids refs separation .product .pointSecond (by decide)⟩
    · exact ⟨mutable_avoids refs separation .coefficientThird .product (by decide),
        separation.sourceAvoidsMutable .basisThirdSecond .product,
        mutable_avoids refs separation .pointSecond .product (by decide),
        mutable_avoids refs separation .coefficientThird .pointSecond (by decide),
        separation.sourceAvoidsMutable .basisThirdSecond .pointSecond,
        mutable_avoids refs separation .product .pointSecond (by decide)⟩
  | third =>
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · exact ⟨mutable_avoids refs separation .coefficientFirst .product (by decide),
        separation.sourceAvoidsMutable .basisFirstThird .product,
        mutable_avoids refs separation .pointThird .product (by decide),
        mutable_avoids refs separation .coefficientFirst .pointThird (by decide),
        separation.sourceAvoidsMutable .basisFirstThird .pointThird,
        mutable_avoids refs separation .product .pointThird (by decide)⟩
    · exact ⟨mutable_avoids refs separation .coefficientSecond .product (by decide),
        separation.sourceAvoidsMutable .basisSecondThird .product,
        mutable_avoids refs separation .pointThird .product (by decide),
        mutable_avoids refs separation .coefficientSecond .pointThird (by decide),
        separation.sourceAvoidsMutable .basisSecondThird .pointThird,
        mutable_avoids refs separation .product .pointThird (by decide)⟩
    · exact ⟨mutable_avoids refs separation .coefficientThird .product (by decide),
        separation.sourceAvoidsMutable .basisThirdThird .product,
        mutable_avoids refs separation .pointThird .product (by decide),
        mutable_avoids refs separation .coefficientThird .pointThird (by decide),
        separation.sourceAvoidsMutable .basisThirdThird .pointThird,
        mutable_avoids refs separation .product .pointThird (by decide)⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine
