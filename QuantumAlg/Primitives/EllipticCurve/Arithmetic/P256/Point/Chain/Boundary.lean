/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Reuse.Boundary
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Seed

/-!
# Full physical post-reset boundary of the point's reused inversion adjoint

The actual saved A value, reset Y, complete source complement and whole
pool determine the same generic reused boundary. Typed width transport
retains every original physical coordinate. Active residues have exactly
the original positive, bounded, coprime domain. The inactive sector is
handled by the separately proved arbitrary-source resident identity.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Boundary

noncomputable section

open MAU.Inversion.SharedEEA MAU.Inversion.SharedEEA.Scanned

private def sourceAt {width : Nat} (same : width = 256) (state : Frame.Raw) :
    ControlledResidentFrame.Data width := by
  cases same
  exact state

private lemma sourceAt_state {width : Nat} (same : width = 256) (state : Frame.Raw) :
    Inversion.Transport.state same (sourceAt same state) = state := by
  cases same
  exact Inversion.Transport.state_refl state

/-- The complete actual point label, transported only by the proved original word width. -/
def source (state : Frame.Raw) : ControlledResidentFrame.Data modulus.size :=
  sourceAt Inversion.modulus_size state

/-- A/Y's original physical reuse saves the reversed numerical A, explicitly. -/
def savedWord (state : Frame.Raw) : Fin (2 ^ modulus.size) :=
  WorkspaceReuse.reverseWord (WorkspaceReuse.largeWord (source state).1)

/-- The literal same forward's own adjoint on the original point bank. -/
def reusedBackward : Native.Circuit :=
  Inversion.Transport.program Inversion.modulus_size
    (ControlledResidentReuse.backward modulus Inversion.modulus_nontrivial)

/-- Complete physical retained readouts and actual reset establish the reused adjoint's input. -/
lemma source_result (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (state : Frame.Raw)
    (retained : ∀ bit : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get (source state).1.1.1 =
        bit.get (ControlledResident.result modulus input positive bounded 0
          (source state).1.1.2 (source state).2).1.1.1)
    (reset : (source state).1.2 = 0) :
    state = Inversion.Transport.state Inversion.modulus_size
      (ControlledResidentReuse.result modulus input positive bounded (savedWord state)
        (source state).1.1.2 (source state).2) := by
  have actual := ControlledResidentReuse.result_of_saved_reset modulus input coprime positive
    bounded (source state).1.1.2 (source state).2 (source state) retained rfl reset rfl
  have placed := congrArg (fun value : ControlledResidentFrame.Data modulus.size =>
    Inversion.Transport.state Inversion.modulus_size value) actual
  exact (sourceAt_state Inversion.modulus_size state).symm.trans placed

/-- The same-program dagger restores the whole initial source after saved/reset arithmetic. -/
lemma reusedBackward_saved_reset (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (state : Frame.Raw)
    (retained : ∀ bit : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get (source state).1.1.1 =
        bit.get (ControlledResident.result modulus input positive bounded 0
          (source state).1.1.2 (source state).2).1.1.1)
    (reset : (source state).1.2 = 0) (poolZero : (source state).1.1.2 = (0, (0, false)))
    (selected : (source state).2.2.1 = true) :
    reusedBackward.applyNormalized environment (Native.ket state) =
      Native.ket (Inversion.Transport.state Inversion.modulus_size
        (ControlledResidentReuse.initial modulus input (savedWord state)
          (source state).1.1.2 (source state).2)) := by
  have address := congrArg Prod.fst poolZero
  have cleanPrefix := congrArg (fun pool => pool.2.1) poolZero
  have borrow := congrArg (fun pool => pool.2.2) poolZero
  have actual := ControlledResidentReuse.backward_saved_reset modulus Inversion.modulus_nontrivial
    environment input coprime positive bounded (source state).1.1.2 address cleanPrefix borrow
    (source state).2 selected (source state) retained rfl reset rfl
  have placed := Inversion.Transport.program_apply Inversion.modulus_size _ environment _ _ actual
  simpa only [reusedBackward, savedWord, source, sourceAt_state] using placed

/-- Placing this same literal adjoint retains its exact native ledger. -/
lemma reusedBackward_eventTrace : reusedBackward.eventTrace =
    (ControlledResidentReuse.backward modulus Inversion.modulus_nontrivial).eventTrace :=
  Inversion.Transport.program_eventTrace Inversion.modulus_size _

/-- The actual adjoint schedule is unchanged by the typed physical-bank specialization. -/
lemma reusedBackward_quantumTime :
    reusedBackward.evaluatedEventDepth Resource.Event.quantumDuration =
      (ControlledResidentReuse.backward modulus Inversion.modulus_nontrivial).evaluatedEventDepth
        Resource.Event.quantumDuration :=
  Inversion.Transport.program_quantumTime Inversion.modulus_size _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Boundary
