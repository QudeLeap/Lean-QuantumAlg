/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace

/-!
# Native space of all exponent systems and the shared measured workspace

Every indexed entry contributes exactly its actual dimension-two system.
The common ready context adds all exponent systems and one selector to the
single original arithmetic/history bank and finite measurement cells. No
exponent system is moved outside the actual resident accounting frame.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open MeasuredUncompute Execution

private theorem indexedEntry_resident (width index : Nat) :
    (indexedEntry width index).residentSpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact QuantumLayout.dimensionCount_uniform 1 2 dimension _ _

private theorem indexedEntry_auxiliary (width index : Nat) :
    (indexedEntry width index).auxiliarySpace = OwnedQubits.space 1 :=
  indexedEntry_resident width index

private theorem indexed_foldSpace (width : Nat) (indices : List Nat)
    (project : RuntimeEntry .quantum → SpacePool .quantum)
    (entrySpace : ∀ index, project (indexedEntry width index) = OwnedQubits.space 1) :
    (indices.map (indexedEntry width)).foldr (fun entry total => project entry + total) 0 =
      OwnedQubits.space indices.length := by
  induction indices with
  | nil =>
      funext axis
      cases axis <;> simp [OwnedQubits.space]
  | cons index indices ih =>
      simp only [List.map_cons, List.foldr_cons, entrySpace, ih, List.length_cons]
      funext axis
      cases axis with
      | classicalBits => rfl
      | quantumSystems dimension =>
          change (if (2 : ℕ+) = dimension then 1 else 0) +
            (if (2 : ℕ+) = dimension then indices.length else 0) =
              if (2 : ℕ+) = dimension then indices.length + 1 else 0
          split_ifs <;> omega

/-- The exact number of listed indexed qubits is charged at the native resident coordinate. -/
theorem indexedContext_resident (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    (indexedContext width indices distinct).residentSpace = OwnedQubits.space indices.length :=
  indexed_foldSpace width indices RuntimeEntry.residentSpace (indexedEntry_resident width)

/-- Every listed indexed qubit retains its actual owned auxiliary role. -/
theorem indexedContext_auxiliary (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    (indexedContext width indices distinct).auxiliarySpace = OwnedQubits.space indices.length :=
  indexed_foldSpace width indices RuntimeEntry.auxiliarySpace (indexedEntry_auxiliary width)

/-- Independent complete space has one measured arithmetic bank, all exponents and one selector. -/
def readySpace (width count : Nat) : SpacePool .quantum :=
  width • SpacePool.ofShape (.finite 2) +
    OwnedQubits.space (3 * width + 4 * width.size + 12 + count)

/-- The common actual context charges every original and indexed resident system exactly once. -/
theorem readyContext_resident (width count : Nat) :
    (readyContext width count).residentSpace =
      (NumeratorMeasurement.context width).residentSpace + OwnedQubits.space (count + 1) := by
  rw [readyContext, RuntimeCtx.residentSpace_disjointUnion, indexedContext_resident,
    List.length_range]

/-- The common actual auxiliary count retains the roles of every original and indexed entry. -/
theorem readyContext_auxiliary (width count : Nat) :
    (readyContext width count).auxiliarySpace =
      (NumeratorMeasurement.context width).auxiliarySpace + OwnedQubits.space (count + 1) := by
  rw [readyContext, RuntimeCtx.auxiliarySpace_disjointUnion, indexedContext_auxiliary,
    List.length_range]

private theorem ready_space_sum (width count : Nat) :
    InPlaceDivisionResources.space width + OwnedQubits.space (count + 1) =
      readySpace width count := by
  rw [InPlaceDivisionResources.space, add_assoc, ← InPlaceControlled.ownedSpace_add]
  have systems : 3 * width + 4 * width.size + 11 + (count + 1) =
      3 * width + 4 * width.size + 12 + count := by omega
  rw [systems]
  rfl

/-- The complete actual resident context meets the independent explicit common-space formula. -/
theorem readyContext_resident_exact (width count : Nat) :
    (readyContext width count).residentSpace = readySpace width count := by
  rw [readyContext_resident, InPlaceDivisionResources.context_resident]
  exact ready_space_sum width count

/-- The actual auxiliary context meets the same explicit formula from its original owned roles. -/
theorem readyContext_auxiliary_exact (width count : Nat) :
    (readyContext width count).auxiliarySpace = readySpace width count := by
  rw [readyContext_auxiliary, InPlaceDivisionResources.context_auxiliary]
  exact ready_space_sum width count

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
