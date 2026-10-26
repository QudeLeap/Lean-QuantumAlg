/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Unpack

/-!
# Coordinate projections from the two actual unpack writes

The complete raw values already proved for the two native unpack instructions
also determine their structural X and Y reads. This proof is generic in point
width and context; it neither assumes a particular curve nor creates data.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma unpacked_coordinate_reads (after : Store ctx)
    (raw : CWriteRef ctx (PointEquality.RawPointShape width))
    (value : CShape.Value (PointShape width))
    (written : after.read (.storage raw.toCStorageRef) =
      CShape.unpackEllipticCurvePoint width value) :
    after.read (.first (.second (.storage raw.toCStorageRef))) =
        .unsignedWord value.ellipticCurvePointX ∧
      after.read (.second (.second (.storage raw.toCStorageRef))) =
        .unsignedWord value.ellipticCurvePointY := by
  constructor
  · change (after.read (.storage raw.toCStorageRef)).second.first = _
    rw [written]
    cases value
    rfl
  · change (after.read (.storage raw.toCStorageRef)).second.second = _
    rw [written]
    cases value
    rfl

/-- Both structural coordinates of the first nominal point are actual Store reads. -/
lemma twoUnpackStore_base_coordinates
    (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (store : Store ctx) (distinct : rawBase.key ≠ rawTarget.key) :
    let after := twoUnpackStore base target rawBase rawTarget store
    after.read (.first (.second (.storage rawBase.toCStorageRef))) =
        .unsignedWord (store.read base).ellipticCurvePointX ∧
      after.read (.second (.second (.storage rawBase.toCStorageRef))) =
        .unsignedWord (store.read base).ellipticCurvePointY :=
  unpacked_coordinate_reads _ rawBase (store.read base)
    (twoUnpackStore_base base target rawBase rawTarget store distinct)

/-- Both structural coordinates of the second nominal point are actual Store reads. -/
lemma twoUnpackStore_target_coordinates
    (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (store : Store ctx) (baseFree : rawBase.key ∉ target.storageKeys) :
    let after := twoUnpackStore base target rawBase rawTarget store
    after.read (.first (.second (.storage rawTarget.toCStorageRef))) =
        .unsignedWord (store.read target).ellipticCurvePointX ∧
      after.read (.second (.second (.storage rawTarget.toCStorageRef))) =
        .unsignedWord (store.read target).ellipticCurvePointY :=
  unpacked_coordinate_reads _ rawTarget (store.read target)
    (twoUnpackStore_target base target rawBase rawTarget store baseFree)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation
