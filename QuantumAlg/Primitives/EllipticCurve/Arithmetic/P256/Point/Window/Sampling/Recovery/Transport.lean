/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport

/-!
# Original sampling references beside the seven real recovery destinations

The allocating table sampler is instantiated in the complete retained context.
Its original writable cells, classical frame and physical quantum wire records
are transported structurally. This does not embed an allocating child as an
allocation-free circuit, allocate replacement result cells or rename a key.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Recovery

noncomputable section

open Execution ClassicalWorkspace ClassicalRoutines.EllipticCurve

private def underRetained {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ inner.keys) : Transport outer (inner.addRetained key shape fresh) where
  liftStorage ref := (transport.liftStorage ref).underRetained key shape fresh
  liftStorage_key ref := transport.liftStorage_key ref
  liftStorage_role ref := transport.liftStorage_role ref

/-- Lift through exactly the existing seven retained candidate-check cells. -/
def persistentTransport (ctx : RuntimeCtx .quantum) :
    Transport ctx
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) := by
  let first := underRetained (Transport.id ctx) ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh
  let latch := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentLatchCtx ctx
  let second := underRetained first latch.canonicalFreshKey (.unsignedWord 260)
    latch.canonicalFreshKey_fresh
  let selected :=
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentSelectedCtx ctx 260
  let third := underRetained second selected.canonicalFreshKey .bit selected.canonicalFreshKey_fresh
  let inverse := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentInverseCtx ctx 260
  let fourth := underRetained third inverse.canonicalFreshKey (.unsignedWord 260)
    inverse.canonicalFreshKey_fresh
  let candidate :=
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCandidateCtx ctx 260
  let fifth := underRetained fourth candidate.canonicalFreshKey .bit
    candidate.canonicalFreshKey_fresh
  let base := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentBaseCtx ctx 260
  let sixth := underRetained fifth base.canonicalFreshKey .bit base.canonicalFreshKey_fresh
  let accepted := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.acceptedCtx base
  exact underRetained sixth accepted.canonicalFreshKey (PointShape 256)
    accepted.canonicalFreshKey_fresh

/-- Classical retention leaves every complete ordered physical wire record unchanged. -/
lemma persistent_wires (ctx : RuntimeCtx .quantum) :
    ctx.quantumLayout.wires =
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx
        ctx 256 260).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, RuntimeCtx.quantumLayout_wires]
  rfl

/-- The allocating sampler uses the same original cells inside the retained caller. -/
def parameters {ctx : RuntimeCtx .quantum} (original : Sampling.Parameters ctx) :
    Sampling.Parameters
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) where
  sameWires := original.sameWires.trans (persistent_wires ctx)
  results := {
    cells := fun position => (persistentTransport ctx).liftWrite (original.results.cells position)
    distinct := by
      intro left right same
      apply original.results.distinct
      simpa only [Transport.liftWrite_key] using same }
  output := fun bit => (persistentTransport ctx).liftWrite (original.output bit)
  mask := (persistentTransport ctx).liftWrite original.mask
  parity := fun bit => (persistentTransport ctx).liftWrite (original.parity bit)
  temporary := (persistentTransport ctx).liftWrite original.temporary
  output_separate := by
    intro bit position
    simpa only [Transport.liftWrite_key] using original.output_separate bit position
  mask_separate := by
    intro position
    simpa only [Transport.liftWrite_key] using original.mask_separate position
  parity_separate := by
    intro bit position
    simpa only [Transport.liftWrite_key] using original.parity_separate bit position
  temporary_separate := by
    intro position
    simpa only [Transport.liftWrite_key] using original.temporary_separate position
  frame := original.frame.transport (persistentTransport ctx)
  modulus := original.modulus

end

end Recovery

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
