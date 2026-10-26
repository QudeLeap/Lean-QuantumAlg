/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Transport
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Reference
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Ports

/-!
# Complete P-256 inversion through the actual generic resident program

The public field modulus fixes one actual program. Every original source,
numerator, pool and C/N/W position belongs to the same physical point
frame used by multiplication. The generic complete proof supplies both
endpoints and the literal same-program adjoint, with no fixed-width gate
expansion. Active inputs retain the original positive coprime residue
domain. Inactive execution admits zero and arbitrary original metadata.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

def program : Native.Circuit :=
  Transport.program modulus_size (ControlledResident.program modulus modulus_nontrivial)

def initial (input numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : Frame.Controls) : Frame.Raw :=
  Transport.state modulus_size (ControlledResident.initial modulus input numerator pool flags)

def result (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : Frame.Controls) : Frame.Raw :=
  Transport.state modulus_size
    (ControlledResident.result modulus input positive bounded numerator pool flags)

lemma program_initial_active (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : Frame.Controls) (selected : flags.1 = true) :
    program.applyNormalized environment (Native.ket (initial input numerator pool flags)) =
      Native.ket (result input positive bounded numerator pool flags) :=
  Transport.program_apply modulus_size _ environment _ _
    (ControlledResident.program_initial_active modulus modulus_nontrivial environment
      input numerator coprime positive bounded pool addressZero prefixZero borrowZero flags
      selected)

private lemma transport_disabled {width : Nat} (same : width = 256)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding width).width).toQuantum)
    (environment : OracleModel.empty.Interpretation)
    (actual : ∀ state : ControlledResidentFrame.Data width,
      state.1.1.2 = (0, (0, false)) → state.1.1.1.control = false → state.2.1 = false →
      body.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding width).encode state))) =
        NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding width).encode state)))
    (state : Frame.Raw) (clean : Frame.CleanPool state)
    (control : state.1.1.1.control = false) (disabled : state.2.1 = false) :
    (Transport.program same body).applyNormalized environment (Native.ket state) =
      Native.ket state := by
  cases same
  simpa only [Transport.state_refl] using
    (Transport.program_apply rfl body environment state state
      (actual state clean control disabled))

/-- Every original inactive state, including zero and arbitrary finite history, is retained. -/
lemma program_apply_disabled (environment : OracleModel.empty.Interpretation)
    (state : Frame.Raw) (clean : Frame.CleanPool state)
    (control : state.1.1.1.control = false) (disabled : state.2.1 = false) :
    program.applyNormalized environment (Native.ket state) = Native.ket state := by
  apply transport_disabled modulus_size _ environment _ state clean control disabled
  intro original pool originalControl originalDisabled
  have address := congrArg Prod.fst pool
  have cleanPrefix := congrArg (fun value => value.2.1) pool
  have borrow := congrArg (fun value => value.2.2) pool
  exact ControlledResident.program_apply_disabled modulus modulus_nontrivial environment
    original cleanPrefix address borrow originalControl originalDisabled

private lemma transport_dagger {width : Nat} (same : width = 256)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding width).width).toQuantum) :
    (Transport.program same body).dagger (AlgorithmGate.oracleFreeAdjoints .empty) =
      Transport.program same (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)) := by
  cases same
  rfl

/-- Cleanup runs the literal adjoint of this same complete physical program. -/
lemma dagger_result (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : Frame.Controls) (selected : flags.1 = true) :
    (program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
        (Native.ket (result input positive bounded numerator pool flags)) =
      Native.ket (initial input numerator pool flags) := by
  rw [program, transport_dagger]
  exact Transport.program_apply modulus_size _ environment _ _
    (ControlledResident.dagger_result modulus modulus_nontrivial environment input numerator
      coprime positive bounded pool addressZero prefixZero borrowZero flags selected)

lemma initial_value (input numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : Frame.Controls) :
    Frame.work2 (initial input numerator pool flags) =
      Fin.cast (congrArg (fun size => 2 ^ size) modulus_size) input := by
  rw [initial, Transport.state_value, ControlledResident.initial_value]

lemma result_value (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : Frame.Controls) :
    Frame.work2 (result input positive bounded numerator pool flags) =
      Fin.cast (congrArg (fun size => 2 ^ size) modulus_size)
        (NumberTheory.SharedEEA.InverseOutput.word modulus input.val positive bounded) := by
  rw [result, Transport.state_value, ControlledResident.result_value]

private lemma transport_work1 {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) :
    Frame.work1 (Transport.state same state) =
      Fin.cast (congrArg (fun size => 2 ^ size) same) (ControlledResident.work1 state) := by
  cases same
  rfl

/-- The same original Work1 payload is available to the actual multiplication consumer as zero. -/
lemma result_work1_zero (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : Frame.Controls) :
    Frame.work1 (result input positive bounded numerator pool flags) = Horner.zeroWord := by
  rw [result, transport_work1, ControlledResident.result_work1_zero modulus input coprime]
  apply Fin.ext
  change (0 : Fin (2 ^ modulus.size)).val = 0
  exact Fin.val_zero _

lemma result_numerator (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : Frame.Controls) :
    Frame.numerator (result input positive bounded numerator pool flags) =
      Fin.cast (congrArg (fun size => 2 ^ size) modulus_size) numerator := by
  rw [result, Transport.state_numerator, ControlledResident.result_numerator]

lemma result_flags (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : Frame.Controls) :
    (result input positive bounded numerator pool flags).2 = flags := by
  rw [result, Transport.state_flags, ControlledResident.result_flags]

private lemma transport_clean_pool {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) (clean : state.1.1.2 = (0, (0, false))) :
    Frame.CleanPool (Transport.state same state) := by
  cases same
  exact clean

lemma result_clean_pool (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : Frame.Controls)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0)
    (borrowZero : pool.2.2 = false) :
    Frame.CleanPool (result input positive bounded numerator pool flags) := by
  apply transport_clean_pool modulus_size
  exact Prod.ext addressZero (Prod.ext prefixZero borrowZero)

/-- The complete original state and its external Reference correlations are retained. -/
lemma program_reference (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (input numerator : Index → Fin (2 ^ modulus.size))
    (coprime : ∀ index, Nat.Coprime (input index).val modulus)
    (positive : ∀ index, 0 < (input index).val)
    (bounded : ∀ index, (input index).val < modulus) (pool : Index → Pool modulus.size)
    (addressZero : ∀ index, (pool index).1 = 0)
    (prefixZero : ∀ index, (pool index).2.1 = 0)
    (borrowZero : ∀ index, (pool index).2.2 = false)
    (flags : Index → Frame.Controls) (selected : ∀ index, (flags index).1 = true)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (Native.referenceOperator program environment Reference)
        (Native.referenceVector
          (fun index => initial (input index) (numerator index) (pool index) (flags index))
          reference amplitude) =
      Native.referenceVector
        (fun index => result (input index) (positive index) (bounded index) (numerator index)
          (pool index) (flags index)) reference amplitude :=
  Native.coherent_of_basis _ environment _ _
    (fun index => program_initial_active environment (input index) (numerator index)
      (coprime index) (positive index) (bounded index) (pool index) (addressZero index)
      (prefixZero index) (borrowZero index) (flags index) (selected index)) reference amplitude

lemma program_eventTrace : program.eventTrace =
    (ControlledParallel.program modulus modulus_nontrivial).eventTrace :=
  (Transport.program_eventTrace modulus_size _).trans
    (ControlledResident.program_eventTrace modulus modulus_nontrivial)

lemma program_quantumTime : program.evaluatedEventDepth Resource.Event.quantumDuration =
    (ControlledParallel.program modulus modulus_nontrivial).evaluatedEventDepth
      Resource.Event.quantumDuration :=
  (Transport.program_quantumTime modulus_size _).trans
    (ControlledResident.program_quantumTime modulus modulus_nontrivial)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion
