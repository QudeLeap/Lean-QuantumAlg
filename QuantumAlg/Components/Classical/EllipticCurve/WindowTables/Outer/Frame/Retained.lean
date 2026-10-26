/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Frame
import all QuantumAlg.Core.Execution.Classical.Retained.Read

/-! # Shared table frames from actual retained cells -/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame

open QuantumAlg.Execution
noncomputable section

def ofRetainedCells {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat}
    (cells : RetainedCells.Cells ctx (sharedShapes width))
    (unique : cells.keys.Nodup) : Frame ctx width := by
  cases cells with
  | cons product rest =>
    cases rest with
    | cons inverse rest =>
      cases rest with
      | cons temporary rest =>
        cases rest with
        | cons slope rest =>
          cases rest with
          | cons modulus rest =>
            cases rest with
            | cons zero rest =>
              cases rest with
              | cons one rest =>
                cases rest with
                | cons curveA rest =>
                  cases rest with
                  | cons x rest =>
                    cases rest with
                    | cons y rest =>
                      cases rest
                      exact {
                        product := product.ref
                        inverse := inverse.ref
                        temporary := temporary.ref
                        slope := slope.ref
                        modulus := modulus.ref
                        zero := zero.ref
                        one := one.ref
                        curveA := curveA.ref
                        x := x.ref
                        y := y.ref
                        distinct := unique
                      }

/-- The frame retains exactly the original retained-cell key order. -/
lemma ofRetainedCells_keys {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (cells : RetainedCells.Cells ctx (sharedShapes width))
    (unique : cells.keys.Nodup) :
    List.ofFn (ofRetainedCells cells unique).keyAt = cells.keys := by
  cases cells with | cons _ rest =>
    cases rest with | cons _ rest =>
      cases rest with | cons _ rest =>
        cases rest with | cons _ rest =>
          cases rest with | cons _ rest =>
            cases rest with | cons _ rest =>
              cases rest with | cons _ rest =>
                cases rest with | cons _ rest =>
                  cases rest with | cons _ rest =>
                    cases rest with | cons _ rest =>
                      cases rest
                      rfl

/-- Every allocated frame cell is fresh for every original structural caller input. -/
lemma retained_key_avoids_original {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) {shape : CShape} (input : CInputRef ctx shape) (index : Fin 10) :
    (ofRetainedCells (RetainedCells.references ctx (sharedShapes width))
      (RetainedCells.references_keys_nodup ctx (sharedShapes width))).keyAt index ∉
        ((RetainedCells.transport ctx (sharedShapes width)).liftInput input).storageKeys := by
  rw [ClassicalWorkspace.Transport.liftInput_storageKeys]
  have member : (ofRetainedCells (RetainedCells.references ctx (sharedShapes width))
      (RetainedCells.references_keys_nodup ctx (sharedShapes width))).keyAt index ∈
        (RetainedCells.references ctx (sharedShapes width)).keys := by
    rw [← ofRetainedCells_keys _
      (RetainedCells.references_keys_nodup ctx (sharedShapes width))]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  intro present
  exact List.disjoint_left.mp (RetainedCells.references_keys_disjoint_base ctx
    (sharedShapes width)) member (CInputRef.storageKeys_subset_context input present)

/-- Actual retained initialization establishes both distinguished zero inputs. -/
lemma ofRetainedCells_zero_one_initial {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (cells : RetainedCells.Cells ctx (sharedShapes width))
    (unique : cells.keys.Nodup) (store : Store ctx)
    (initial : cells.Initialized store) :
    store.read (.storage (ofRetainedCells cells unique).zero.toCStorageRef) =
        CShape.initialValue (.unsignedWord width) ∧
      store.read (.storage (ofRetainedCells cells unique).one.toCStorageRef) =
        CShape.initialValue (.unsignedWord width) := by
  cases cells with | cons _ rest =>
    cases rest with | cons _ rest =>
      cases rest with | cons _ rest =>
        cases rest with | cons _ rest =>
          cases rest with | cons _ rest =>
            cases rest with | cons _ rest =>
              cases rest with | cons _ rest =>
                cases rest with | cons _ rest =>
                  cases rest with | cons _ rest =>
                    cases rest with | cons _ rest =>
                      cases rest
                      exact ⟨initial.2.2.2.2.2.1, initial.2.2.2.2.2.2.1⟩

/-- The two retained constant words both have numeric value zero before loading. -/
lemma ofRetainedCells_zero_one_initial_nat {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (cells : RetainedCells.Cells ctx (sharedShapes width))
    (unique : cells.keys.Nodup) (store : Store ctx) (initial : cells.Initialized store) :
    (store.read (.storage (ofRetainedCells cells unique).zero.toCStorageRef)).toNat = 0 ∧
      (store.read (.storage (ofRetainedCells cells unique).one.toCStorageRef)).toNat = 0 := by
  obtain ⟨zero, one⟩ := ofRetainedCells_zero_one_initial cells unique store initial
  rw [zero, one]
  exact ⟨rfl, rfl⟩

end
end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame
