/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Normal

/-!
# Inversion selected by the actual normal-point flag

The original N position selects the same complete generic forward.
The original C is retained even on the inactive zero-denominator branch;
W remains arbitrary restored work. The exact original input and result
frames are shared with the C-selected physical program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion.Normal

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

def program : Native.Circuit :=
  Transport.program modulus_size (ControlledResidentNormal.program modulus modulus_nontrivial)

lemma program_initial_active (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : Frame.Controls) (selected : flags.2.1 = true) :
    program.applyNormalized environment (Native.ket (initial input numerator pool flags)) =
      Native.ket (result input positive bounded numerator pool flags) :=
  Transport.program_apply modulus_size _ environment _ _
    (ControlledResidentNormal.program_initial_active modulus modulus_nontrivial environment
      input numerator coprime positive bounded pool addressZero prefixZero borrowZero flags
      selected)

private lemma transport_disabled_normal {width : Nat} (same : width = 256)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding width).width).toQuantum)
    (environment : OracleModel.empty.Interpretation)
    (actual : ∀ state : ControlledResidentFrame.Data width,
      state.1.1.2 = (0, (0, false)) → state.1.1.1.control = false → state.2.2.1 = false →
      body.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding width).encode state))) =
        NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding width).encode state)))
    (state : Frame.Raw) (clean : Frame.CleanPool state)
    (control : state.1.1.1.control = false) (disabled : state.2.2.1 = false) :
    (Transport.program same body).applyNormalized environment (Native.ket state) =
      Native.ket state := by
  cases same
  simpa only [Transport.state_refl] using
    (Transport.program_apply rfl body environment state state
      (actual state clean control disabled))

/-- Zero denominators and arbitrary original data remain admitted when the actual N flag is zero. -/
lemma program_apply_disabled (environment : OracleModel.empty.Interpretation)
    (state : Frame.Raw) (clean : Frame.CleanPool state)
    (control : state.1.1.1.control = false) (disabled : state.2.2.1 = false) :
    program.applyNormalized environment (Native.ket state) = Native.ket state := by
  apply transport_disabled_normal modulus_size _ environment _ state clean control disabled
  intro original pool originalControl originalDisabled
  have address := congrArg Prod.fst pool
  have cleanPrefix := congrArg (fun value => value.2.1) pool
  have borrow := congrArg (fun value => value.2.2) pool
  exact ControlledResidentNormal.program_apply_disabled modulus modulus_nontrivial environment
    original cleanPrefix address borrow originalControl originalDisabled

lemma dagger_result (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : Frame.Controls) (selected : flags.2.1 = true) :
    (program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
        (Native.ket (result input positive bounded numerator pool flags)) =
      Native.ket (initial input numerator pool flags) := by
  have actual := program_initial_active environment input numerator coprime positive bounded
    pool addressZero prefixZero borrowZero flags selected
  exact (congrArg (fun state => (program.dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment state)
    actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized program
      (program.dagger (AlgorithmGate.oracleFreeAdjoints .empty))
      (by
        rw [UnitaryCircuit.dagger_matrix,
          Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
            environment]
        exact Unitary.star_eq_inv _) _)

lemma program_eventTrace : program.eventTrace = Inversion.program.eventTrace :=
  ((Transport.program_eventTrace modulus_size _).trans
    (ControlledResidentNormal.program_eventTrace modulus modulus_nontrivial)).trans
      (Transport.program_eventTrace modulus_size _).symm

lemma program_quantumTime : program.evaluatedEventDepth Resource.Event.quantumDuration =
    Inversion.program.evaluatedEventDepth Resource.Event.quantumDuration :=
  ((Transport.program_quantumTime modulus_size _).trans
    (ControlledResidentNormal.program_quantumTime modulus modulus_nontrivial)).trans
      (Transport.program_quantumTime modulus_size _).symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion.Normal
