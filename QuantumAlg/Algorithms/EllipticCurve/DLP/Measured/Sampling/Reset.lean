/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Basis
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Resources

/-!
# Actual reset to the complete original sampling basis

Every already resident terminal wire is Z measured into the same original
numerator cell, corrected using that stored outcome, and shifted to its
specified original preparation value. Both public points and all existing
storage remain resident. Each final record retains its real measurement
history and conditional reference state; the reused result cell is not
silently returned to allocation's initial classical value.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution

private theorem range_isLocal {ctx : RuntimeCtx .quantum} (count : Nat)
    (body : Fin count → Circuit ctx ctx) (supported : ∀ index, (body index).IsLocal) :
    (Circuit.forRange count body).IsLocal := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨supported 0, ih _ (fun index => supported index.succ)⟩

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)

/-- Actual measurement and conditional correction prepare all existing original sampling wires. -/
def samplingReset : Circuit (PublicInput.terminal E exponentWidth)
    (PublicInput.terminal E exponentWidth) :=
  QuditShift.resetToBasis (samplingResetCells E exponentWidth)
    (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)

/-- Every real measurement, stored branch and unitary stays within the existing terminal context. -/
theorem samplingReset_isLocal :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).IsLocal :=
  range_isLocal _ _ (fun _ => ⟨⟨trivial, fun _ => trivial⟩, trivial⟩)

/-- Every complete final block has the specified basis ket and its actual reference coefficient. -/
theorem samplingReset_block_factor {Reference : Register} {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E exponentWidth) Reference History)
    (record : Store (PublicInput.terminal E exponentWidth) ×
      (History × (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path))
    (left right : (PublicInput.terminal E exponentWidth).register.Index)
    (refLeft refRight : Reference.Index) :
    (((samplingReset E fieldTail exponentWidth sameWidth fits seed).execute
      Reference state).block record).matrix (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := (PublicInput.terminal E exponentWidth).register)
        (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed) left *
      (((samplingReset E fieldTail exponentWidth sameWidth fits seed).execute
        Reference state).block record).matrix
          (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed, refLeft)
          (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed, refRight) *
      star (NormalizedVector.ket (R := (PublicInput.terminal E exponentWidth).register)
        (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed) right) :=
  QuditShift.resetToBasis_block_factor _ _ state record left right refLeft refRight

/-- Reset and seeding charge three actual native operations for every existing physical system. -/
theorem samplingReset_eventCount
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    ((samplingReset E fieldTail exponentWidth sameWidth fits seed).eventTrace path).length =
      3 * (PublicInput.terminal E exponentWidth).systemCount :=
  QuditShift.resetToBasis_eventCount _ _ path

/-- Arbitrary native durations retain the actual serial reset dependencies. -/
theorem samplingReset_duration (duration : Resource.Event .quantum → Nat)
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).depth duration path =
      (((samplingReset E fieldTail exponentWidth sameWidth fits seed).eventTrace path).map
        duration).sum :=
  QuditShift.resetToBasisOn_duration _ _ _ _ duration path

/-- The complete original terminal resident context is reused without any new allocation. -/
theorem samplingReset_resident
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).peakResidentSpace path =
      (PublicInput.terminal E exponentWidth).residentSpace :=
  QuditShift.resetToBasis_resident _ _ path

/-- Every original auxiliary role is retained, with no additional reset workspace. -/
theorem samplingReset_auxiliary
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).peakAuxiliarySpace path =
      (PublicInput.terminal E exponentWidth).auxiliarySpace :=
  QuditShift.resetToBasis_auxiliary _ _ path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
