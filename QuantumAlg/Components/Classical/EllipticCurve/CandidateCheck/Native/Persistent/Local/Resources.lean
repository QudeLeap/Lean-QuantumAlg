/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Path
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources
import all QuantumAlg.Core.Execution.Local.Retained.Resources

/-!
# Actual local resources beside the persistent recovery destinations

The canonical actual path equivalence preserves every ordered native event
and every assigned dependency duration through the seven existing cells.
Their real resident and auxiliary shapes are counted once. No new path,
allocation, initial-value promise, or execution rule is introduced here.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ContextUnion ClassicalAlgorithms.EllipticCurve

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private def PathResources {base outer : RuntimeCtx kind}
    (code : Circuit base base) (extended : Circuit outer outer)
    (paths : code.Path ≃ extended.Path) : Prop :=
  (∀ path, extended.eventTrace (paths path) = code.eventTrace path) ∧
    ∀ duration path, extended.depth duration (paths path) = code.depth duration path

private theorem resources_beside {base outer : RuntimeCtx kind} (code : Circuit base base)
    (localCode : { code : Circuit outer outer // code.IsLocal })
    (paths : code.Path ≃ localCode.val.Path)
    (prior : PathResources code localCode.val paths) (shape : CShape) :
    PathResources code (besideCell localCode shape).val (besidePath localCode shape paths) := by
  constructor
  · intro path
    exact (Circuit.underRetained_eventTrace localCode.val localCode.property
      outer.canonicalFreshKey shape outer.canonicalFreshKey_fresh (paths path)).trans
        (prior.1 path)
  · intro duration path
    exact (Circuit.underRetained_depth localCode.val localCode.property
      outer.canonicalFreshKey shape outer.canonicalFreshKey_fresh duration (paths path)).trans
        (prior.2 duration path)

/-- One canonical actual path preserves every event and all native-duration assignments together. -/
theorem underPersistent_pathResources (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    PathResources code (underPersistent code supported width scalarWidth)
      (underPersistentPathEquiv code supported width scalarWidth) := by
  let original := (⟨code, supported⟩ : { code : Circuit ctx ctx // code.IsLocal })
  have accepted := @resources_beside _ _ _ code original (Equiv.refl _)
    ⟨fun _ => rfl, fun _ _ => rfl⟩ .bit
  have selected := @resources_beside _ _ _ code (besideCell original .bit) _ accepted
    (.unsignedWord scalarWidth)
  have inverse := @resources_beside _ _ _ code
    (besideCell (besideCell original .bit) (.unsignedWord scalarWidth)) _ selected .bit
  have candidate := @resources_beside _ _ _ code _ _ inverse (.unsignedWord scalarWidth)
  have reconstruction := @resources_beside _ _ _ code _ _ candidate .bit
  have verified := @resources_beside _ _ _ code _ _ reconstruction .bit
  exact @resources_beside _ _ _ code _ _ verified (PointShape width)

private theorem local_resident (code : Circuit ctx ctx) (supported : code.IsLocal)
    (path : code.Path) : code.peakResidentSpace path = ctx.residentSpace := by
  have upper := code.peakResidentSpace_le_of_visited path ctx.residentSpace (by
    intro visited present
    exact (congrArg RuntimeCtx.residentSpace
      (local_visited code supported path visited present)).le)
  have lower := code.residentSpace_le_peak_of_visited path ctx (local_pre_mem code supported path)
  exact le_antisymm upper lower

private theorem local_auxiliary (code : Circuit ctx ctx) (supported : code.IsLocal)
    (path : code.Path) : code.peakAuxiliarySpace path = ctx.auxiliarySpace := by
  have upper := code.peakAuxiliarySpace_le_of_visited path ctx.auxiliarySpace (by
    intro visited present
    exact (congrArg RuntimeCtx.auxiliarySpace
      (local_visited code supported path visited present)).le)
  have lower := code.auxiliarySpace_le_peak_of_visited path ctx (local_pre_mem code supported path)
  exact le_antisymm upper lower

private def LocalSpace {outer : RuntimeCtx kind} (code : Circuit outer outer) : Prop :=
  (∀ path, code.peakResidentSpace path = outer.residentSpace) ∧
    ∀ path, code.peakAuxiliarySpace path = outer.auxiliarySpace

private theorem local_space (code : Circuit ctx ctx) (supported : code.IsLocal) :
    LocalSpace code :=
  ⟨local_resident code supported, local_auxiliary code supported⟩

/-- Both exact peaks are the actual persistent context, whose seven shapes are counted once. -/
theorem underPersistent_space (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    LocalSpace (underPersistent code supported width scalarWidth) :=
  local_space _ (underPersistent_isLocal code supported width scalarWidth)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
