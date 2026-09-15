/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Resources
import all QuantumAlg.Core.Execution.Context.Permutation.Local.Resources

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
theorem step_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (path : (MeasuredPointAddition.body E Q).Path) :
    (step E Q active).eventTrace (stepPathEquiv E Q active path) =
      (MeasuredPointAddition.body E Q).eventTrace path :=
  (ContextPermutation.localCircuit_eventTrace (residentBody E Q active)
    (residentBody_local E Q active) (readyContext p.size count) (framed_entries p.size active)
    (MeasuredPointAddition.Placement.Framing.pathEquiv E Q (storageMap p.size active)
      (physicalMap p.size active) (ambientContext p.size active)
      (ambient_disjoint p.size active) path)).trans
        (MeasuredPointAddition.Placement.Framing.body_eventTrace E Q (storageMap p.size active)
          (physicalMap p.size active) (ambientContext p.size active)
          (ambient_disjoint p.size active) path)

/-- The actual step satisfies the independent measured point event budget. -/
theorem step_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (path : (step E Q active).Path) :
    (step E Q active).resourcePool path ≤ MeasuredPointAddition.events p.size := by
  obtain ⟨original, rfl⟩ := (stepPathEquiv E Q active).surjective path
  exact (congrArg ResourcePool.ofList (step_eventTrace E Q active original)).le.trans
    (MeasuredPointAddition.body_budget E Q original)

/-- The actual step satisfies the independent native point depth bound. -/
theorem step_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (path : (step E Q active).Path) :
    (step E Q active).depth (fun _ => 1) path ≤ MeasuredPointAddition.depthBound p.size := by
  obtain ⟨original, rfl⟩ := (ContextPermutation.localPathEquiv (residentBody E Q active)
    (residentBody_local E Q active) (readyContext p.size count)
    (framed_entries p.size active)).surjective path
  exact (ContextPermutation.localCircuit_depth (residentBody E Q active)
    (residentBody_local E Q active) (readyContext p.size count) (framed_entries p.size active)
    (fun _ => 1) original).le.trans
      (MeasuredPointAddition.Placement.Framing.body_depth E Q (storageMap p.size active)
        (physicalMap p.size active) (ambientContext p.size active)
        (ambient_disjoint p.size active) original)

/-- Every actual step charges the entire common resident space, including inactive exponents. -/
theorem step_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (path : (step E Q active).Path) :
    (step E Q active).peakResidentSpace path = readySpace p.size count := by
  exact (ContextPermutation.localCircuit_peakResidentSpace (residentBody E Q active)
    (residentBody_local E Q active) (framed_entries p.size active) path).trans
      ((ContextPermutation.resident_space (framed_entries p.size active)).trans
        (readyContext_resident_exact p.size count))

/-- The actual fixed-role auxiliary peak includes the same complete live common entries. -/
theorem step_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (path : (step E Q active).Path) :
    (step E Q active).peakAuxiliarySpace path = readySpace p.size count := by
  exact (ContextPermutation.localCircuit_peakAuxiliarySpace (residentBody E Q active)
    (residentBody_local E Q active) (framed_entries p.size active) path).trans
      ((ContextPermutation.auxiliary_space (framed_entries p.size active)).trans
        (readyContext_auxiliary_exact p.size count))

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
