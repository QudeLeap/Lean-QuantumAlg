/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Reuse.Initial

/-! # Complete reused forward boundary after actual product saving and Y reset -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Boundary

noncomputable section

open MAU.Inversion.SharedEEA MAU.Inversion.SharedEEA.Scanned

/-- Multiplication uses the actual reused forward after saving d times the original numerator. -/
def reusedForward : Native.Circuit :=
  Inversion.Transport.program Inversion.modulus_size
    (ControlledResidentReuse.forward modulus Inversion.modulus_nontrivial)

/-- Actual original initialization and physical reset identify the full reused forward input. -/
lemma source_initial (input : Fin (2 ^ modulus.size)) (state : Frame.Raw)
    (retained : ∀ bit : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get (source state).1.1.1 =
        bit.get (ControlledResident.initial modulus input 0
          (source state).1.1.2 (source state).2).1.1.1)
    (reset : (source state).1.2 = 0) :
    state = Inversion.Transport.state Inversion.modulus_size
      (ControlledResidentReuse.initial modulus input (savedWord state)
        (source state).1.1.2 (source state).2) := by
  have actual := ControlledResidentReuse.initial_of_saved_reset modulus input
    (source state).1.1.2 (source state).2 (source state) retained rfl reset rfl
  have placed := congrArg (fun value : ControlledResidentFrame.Data modulus.size =>
    Inversion.Transport.state Inversion.modulus_size value) actual
  exact (sourceAt_state Inversion.modulus_size state).symm.trans placed

/-- The real forward on reused Y consumes the original initialized source, including all history. -/
lemma reusedForward_saved_reset (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (state : Frame.Raw)
    (retained : ∀ bit : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get (source state).1.1.1 =
        bit.get (ControlledResident.initial modulus input 0
          (source state).1.1.2 (source state).2).1.1.1)
    (reset : (source state).1.2 = 0) (poolZero : (source state).1.1.2 = (0, (0, false)))
    (selected : (source state).2.2.1 = true) :
    reusedForward.applyNormalized environment (Native.ket state) =
      Native.ket (Inversion.Transport.state Inversion.modulus_size
        (ControlledResidentReuse.result modulus input positive bounded (savedWord state)
          (source state).1.1.2 (source state).2)) := by
  have address := congrArg Prod.fst poolZero
  have cleanPrefix := congrArg (fun pool => pool.2.1) poolZero
  have borrow := congrArg (fun pool => pool.2.2) poolZero
  have actual := ControlledResidentReuse.forward_saved_reset modulus Inversion.modulus_nontrivial
    environment input coprime positive bounded (source state).1.1.2 address cleanPrefix borrow
    (source state).2 selected (source state) retained rfl reset rfl
  have placed := Inversion.Transport.program_apply Inversion.modulus_size _ environment _ _ actual
  simpa only [reusedForward, savedWord, source, sourceAt_state] using placed

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Boundary
