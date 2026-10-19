/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Resources
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Native step resources in the common measured scalar context

The actual indexed step has the original point body's ordered events and
serial depth bound. Its native resident and auxiliary peaks include the whole
common context throughout execution, regardless of which exponent is active.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

/-- Every original native point event appears in order on the corresponding complete step path. -/
lemma step_eventTrace {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (path : (MeasuredPointAddition.body E Q false).Path) :
    (step E Q active allowAllocation).eventTrace (stepPathEquiv E Q active allowAllocation path) =
      (MeasuredPointAddition.body E Q false).eventTrace path := by
  change (residentBody E Q active).eventTrace path = _
  exact MeasuredPointAddition.Placement.Framing.body_eventTrace (allowAllocation := false)
    E Q (storageMap p.size active) (physicalMap p.size active) (ambientContext p.size active)
    (ambient_disjoint p.size active) path

/-- The actual step satisfies the independent measured point event budget. -/
lemma step_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (path : (step E Q active allowAllocation).Path) :
    (step E Q active allowAllocation).resourcePool path ≤ MeasuredPointAddition.events p.size := by
  obtain ⟨original, rfl⟩ := (stepPathEquiv E Q active allowAllocation).surjective path
  exact (congrArg ResourcePool.ofList
    (step_eventTrace (allowAllocation := allowAllocation) E Q active original)).le.trans
    (MeasuredPointAddition.body_budget (allowAllocation := false) E Q original)

/-- The actual step satisfies the independent native point depth bound. -/
lemma step_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (path : (step E Q active allowAllocation).Path) :
    (step E Q active allowAllocation).depth (fun _ => 1) path ≤
      MeasuredPointAddition.depthBound p.size := by
  change (residentBody E Q active).depth (fun _ => 1) path ≤
    MeasuredPointAddition.depthBound p.size
  exact MeasuredPointAddition.Placement.Framing.body_depth (allowAllocation := false)
    E Q (storageMap p.size active) (physicalMap p.size active) (ambientContext p.size active)
    (ambient_disjoint p.size active) path

/-- Every actual step charges the entire common resident space, including inactive exponents. -/
lemma step_resident {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (path : (step E Q active allowAllocation).Path) :
    (step E Q active allowAllocation).peakResidentSpace path = readySpace p.size count := by
  exact (Circuit.peakResidentSpace_embed
    (ContextEmbedding.alongPermutation (framed_entries p.size active))
    (residentBody E Q active) path).trans (readyContext_resident_exact p.size count)

/-- The actual fixed-role auxiliary peak includes the same complete live common entries. -/
lemma step_auxiliary {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (path : (step E Q active allowAllocation).Path) :
    (step E Q active allowAllocation).peakAuxiliarySpace path = readySpace p.size count := by
  exact (Circuit.peakAuxiliarySpace_embed
    (ContextEmbedding.alongPermutation (framed_entries p.size active))
    (residentBody E Q active) path).trans (readyContext_auxiliary_exact p.size count)

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
