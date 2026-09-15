/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Scoped
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Encoding
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Signed recurrence and exact live scratch of scoped coefficient updates

The two temporary coefficient words are actual lexical allocations. The
signed recurrence describes the persistent words after both cells have been
released, with internal scratch separation derived by the scoped circuit.
The original execution-width range remains an explicit mathematical input
to exact signed decoding. Space counts both live temporary words.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open Execution ClassicalAlgorithms ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Released lexical scratch leaves the exact modular recurrence in the persistent cells. -/
theorem xgcdScopedCoefficient_rawSignedRepresents
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width)) (different : first.key ≠ second.key)
    (store : Store ctx) (quotientValue firstValue secondValue : Int)
    (quotientRepresents : RawSignedRepresents (store.read quotient) quotientValue)
    (firstRepresents : RawSignedRepresents (store.read (coefficientRead first)) firstValue)
    (secondRepresents : RawSignedRepresents (store.read (coefficientRead second)) secondValue) :
    let final := (scopedCoefficientStep quotient first second store).1
    RawSignedRepresents (final.read (coefficientRead first))
        (secondValue - quotientValue * firstValue) ∧
      RawSignedRepresents (final.read (coefficientRead second)) firstValue := by
  have values := xgcdScopedCoefficient_store_values quotient first second different store
  dsimp only
  constructor
  · rw [values.1]
    exact rawSignedRepresents_sub _ _ secondValue (quotientValue * firstValue) secondRepresents
      (rawSignedRepresents_mulLow _ _ quotientValue firstValue
        quotientRepresents firstRepresents)
  · rw [values.2]
    exact firstRepresents

/-- In the original signed ranges, the actual parent-store words decode to both coefficients. -/
theorem xgcdScopedCoefficient_decode
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width)) (different : first.key ≠ second.key)
    (store : Store ctx) (quotientValue firstValue secondValue : Int)
    (quotientRepresents : RawSignedRepresents (store.read quotient) quotientValue)
    (firstRepresents : RawSignedRepresents (store.read (coefficientRead first)) firstValue)
    (secondRepresents : RawSignedRepresents (store.read (coefficientRead second)) secondValue)
    (widthPositive : 0 < width)
    (firstRange : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
      width (secondValue - quotientValue * firstValue))
    (secondRange : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width firstValue) :
    let final := (scopedCoefficientStep quotient first second store).1
    (BoundedSigned.decode (decodeWord (final.read (coefficientRead first)))).toInt =
        secondValue - quotientValue * firstValue ∧
      (BoundedSigned.decode (decodeWord (final.read (coefficientRead second)))).toInt =
        firstValue := by
  have represents := xgcdScopedCoefficient_rawSignedRepresents quotient first second different
    store quotientValue firstValue secondValue quotientRepresents firstRepresents secondRepresents
  exact ⟨rawSignedRepresents_decode_eq _ _ widthPositive represents.1 firstRange,
    rawSignedRepresents_decode_eq _ _ widthPositive represents.2 secondRange⟩

private theorem coefficientUpdateBody_visited
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody quotient first second product updated).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈
      (coefficientUpdateBody quotient first second product updated).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++ ([ctx] ++ ([ctx] ++ [ctx])) at present
  simpa only [List.mem_append, List.mem_singleton, or_self] using present

private theorem coefficientUpdateBody_resident
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody quotient first second product updated).Path) :
    (coefficientUpdateBody quotient first second product updated).peakResidentSpace path =
      ctx.residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rw [coefficientUpdateBody_visited quotient first second product updated path visited present]
  · exact (coefficientUpdateBody quotient first second product updated).input_residentSpace_le_peak
      path

private theorem coefficientUpdateBody_auxiliary
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody quotient first second product updated).Path) :
    (coefficientUpdateBody quotient first second product updated).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rw [coefficientUpdateBody_visited quotient first second product updated path visited present]
  · exact (coefficientUpdateBody quotient first second product updated).input_auxiliarySpace_le_peak
      path

/-- The peak counts both actual temporary words beside every original resident entry. -/
theorem xgcdScopedCoefficient_resident
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (path : (scopedCoefficientUpdate quotient first second).Path) :
    (scopedCoefficientUpdate quotient first second).peakResidentSpace path =
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace) := by
  let body := coefficientUpdateBody (coefficientUnderScratch quotient width)
    (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
    (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width)
  have inner : (coefficientProductCtx ctx width).residentSpace ≤
      (coefficientScratchCtx ctx width).residentSpace := fun _ => Nat.le_add_left _ _
  have outer : ctx.residentSpace ≤ (coefficientScratchCtx ctx width).residentSpace :=
    (show ctx.residentSpace ≤ (coefficientProductCtx ctx width).residentSpace from
      fun _ => Nat.le_add_left _ _).trans inner
  have innerPeak := (Circuit.peakResidentSpace_workspace
    (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (coefficientProductCtx ctx width).canonicalFreshKey_fresh body path).trans
    ((congrArg (SpacePool.max (coefficientProductCtx ctx width).residentSpace)
      (coefficientUpdateBody_resident (coefficientUnderScratch quotient width)
        (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
        (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width) path)).trans
          (SpacePool.max_eq_right inner))
  exact (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh
    (.workspace (coefficientProductCtx ctx width)
      (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh body)
    path).trans ((congrArg (SpacePool.max ctx.residentSpace) innerPeak).trans
      (SpacePool.max_eq_right outer))

/-- Auxiliary accounting charges the same two actual lexical words until their release. -/
theorem xgcdScopedCoefficient_auxiliary
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (path : (scopedCoefficientUpdate quotient first second).Path) :
    (scopedCoefficientUpdate quotient first second).peakAuxiliarySpace path =
      SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace) := by
  let body := coefficientUpdateBody (coefficientUnderScratch quotient width)
    (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
    (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width)
  have inner : (coefficientProductCtx ctx width).auxiliarySpace ≤
      (coefficientScratchCtx ctx width).auxiliarySpace := fun _ => Nat.le_add_left _ _
  have outer : ctx.auxiliarySpace ≤ (coefficientScratchCtx ctx width).auxiliarySpace :=
    (show ctx.auxiliarySpace ≤ (coefficientProductCtx ctx width).auxiliarySpace from
      fun _ => Nat.le_add_left _ _).trans inner
  have innerPeak := (Circuit.peakAuxiliarySpace_workspace
    (coefficientProductCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (coefficientProductCtx ctx width).canonicalFreshKey_fresh body path).trans
    ((congrArg (SpacePool.max (coefficientProductCtx ctx width).auxiliarySpace)
      (coefficientUpdateBody_auxiliary (coefficientUnderScratch quotient width)
        (coefficientWriteUnderScratch first) (coefficientWriteUnderScratch second)
        (coefficientProductCell ctx width) (coefficientUpdatedCell ctx width) path)).trans
          (SpacePool.max_eq_right inner))
  exact (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh
    (.workspace (coefficientProductCtx ctx width)
      (coefficientProductCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (coefficientProductCtx ctx width).canonicalFreshKey_fresh body)
    path).trans ((congrArg (SpacePool.max ctx.auxiliarySpace) innerPeak).trans
      (SpacePool.max_eq_right outer))

/-- Both scratch scopes retain the four real dependent operations at unit duration. -/
theorem xgcdScopedCoefficient_unitDepth
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (path : (scopedCoefficientUpdate quotient first second).Path) :
    (scopedCoefficientUpdate quotient first second).depth (fun _ => 1) path = 4 := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
