/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Frame
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Forward.Execution

/-!
# Actual controlled same-port inversion on the complete original point frame

One supplied control selects the entire proved forward. The numerator,
normal selector, arbitrary borrowed W, complete small history and scan
pool are retained on their actual original wires. Every Work2 source
address of the same program is placed in the resident numerical order.
No whole-width instruction list or fixed-modulus trajectory is unfolded.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResident

noncomputable section

def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding modulus.size).width).toQuantum :=
  (ControlledResidentFrame.layout modulus.size).place
    (UnitaryCircuit.onBinaryPrefix (ControlledResidentFrame.savedEncoding modulus.size).width
      (ControlledParallel.program modulus nontrivial))

def initial (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    ControlledResidentFrame.Data modulus.size :=
  ControlledResidentFrame.reassemble modulus.size
    (((InitialPortProgram.inputFrame modulus input, pool), (flags.1, flags.2.2)),
      (numerator, flags.2.1))

def result (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) : ControlledResidentFrame.Data modulus.size :=
  ControlledResidentFrame.reassemble modulus.size
    (((SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool),
      (flags.1, flags.2.2)), (numerator, flags.2.1))

/-- Exact complete active forward, preserving both saved systems and all original small history. -/
lemma program_initial_active (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input numerator : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : ControlledResidentFrame.Flags) (selected : flags.1 = true) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode
            (initial modulus input numerator pool flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode
          (result modulus input positive bounded numerator pool flags))) := by
  have actual := ControlledParallel.program_initial_active_direct modulus nontrivial environment
    input coprime positive bounded pool addressZero prefixZero borrowZero
    (flags.1, flags.2.2) selected
  have retained := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (ControlledFrame.encoding modulus.size) (ControlledResidentFrame.savedEncoding modulus.size)
    (ControlledParallel.program modulus nontrivial) _ _ (numerator, flags.2.1) actual
  have placed := (ControlledResidentFrame.layout modulus.size).place_ket_of_eq _ _ _ retained
  simpa only [program, initial, result, ControlledResidentFrame.layout_reassemble] using placed

/-- The inactive physical program preserves every original source label, including zero. -/
lemma program_apply_disabled (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (state : ControlledResidentFrame.Data modulus.size)
    (prefixZero : state.1.1.2.2.1 = 0) (addressZero : state.1.1.2.1 = 0)
    (borrowZero : state.1.1.2.2.2 = false) (control : state.1.1.1.control = false)
    (disabled : state.2.1 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode state)) := by
  let source : ControlledFrame.Data modulus.size :=
    ((OutputOrientation.grouping modulus.size state.1.1.1, state.1.1.2),
      (state.2.1, state.2.2.2))
  have originalControl :
      (OutputOrientation.grouping modulus.size state.1.1.1).control = false :=
    (OutputOrientation.grouping_retained modulus.size state.1.1.1).2.2.2.2.2.2.trans control
  have actual := ControlledParallel.program_apply_disabled_direct modulus nontrivial environment
    source prefixZero addressZero borrowZero originalControl disabled
  have retained := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (ControlledFrame.encoding modulus.size) (ControlledResidentFrame.savedEncoding modulus.size)
    (ControlledParallel.program modulus nontrivial) _ _
    (state.1.2, state.2.2.1) actual
  have placed := (ControlledResidentFrame.layout modulus.size).place_ket_of_eq _ _ _ retained
  have assembled : ControlledResidentFrame.reassemble modulus.size
      (source, (state.1.2, state.2.2.1)) = state := by
    simp only [ControlledResidentFrame.reassemble, source, Equiv.symm_apply_apply]
  simpa only [program, ControlledResidentFrame.layout_reassemble, assembled] using placed

/-- The literal adjoint of this same physical program restores all original fields and words. -/
lemma dagger_result (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input numerator : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : ControlledResidentFrame.Flags) (selected : flags.1 = true) :
    ((program modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((ControlledResidentFrame.encoding modulus.size).encode
              (result modulus input positive bounded numerator pool flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode
          (initial modulus input numerator pool flags))) := by
  have actual := program_initial_active modulus nontrivial environment input numerator coprime
    positive bounded pool addressZero prefixZero borrowZero flags selected
  exact (congrArg (fun state => ((program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment state)
    actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (program modulus nontrivial)
      ((program modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
      (by
        rw [UnitaryCircuit.dagger_matrix,
          Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
            environment]
        exact Unitary.star_eq_inv _) _)

/-- Numerical input really is the original resident payload, with the same full orientation. -/
lemma initial_value (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    ControlledResidentFrame.value (initial modulus input numerator pool flags) = input := by
  apply Fin.ext
  exact (ControlledResidentFrame.reassemble_value _ _).trans
    (Nat.mod_eq_of_lt input.isLt)

/-- Actual returned payload is the independent same-port finite-word modular inverse. -/
lemma result_value (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    ControlledResidentFrame.value (result modulus input positive bounded numerator pool flags) =
      NumberTheory.SharedEEA.InverseOutput.word modulus input.val positive bounded := by
  apply Fin.ext
  exact (ControlledResidentFrame.reassemble_value _ _).trans (by
    rw [SharedEEA.InPlaceForward.result_value,
      Nat.mod_eq_of_lt (NumberTheory.SharedEEA.InverseOutput.word
        modulus input.val positive bounded).isLt])

/-- Every original large work bit remains available as actual zero workspace. -/
lemma result_large_bit (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags)
    (index : Fin modulus.size) :
    (result modulus input positive bounded numerator pool flags).1.1.1.firstWord.getMsbD
      index.val = false :=
  SharedEEA.InPlaceForward.result_large_bit modulus input.val coprime positive bounded index

/-- Literal physical placement and retaining Y/N preserve the complete original native trace. -/
lemma program_eventTrace (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventTrace =
      (ControlledParallel.program modulus nontrivial).eventTrace :=
  ((ControlledResidentFrame.layout modulus.size).place_eventTrace _).trans
    (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace _ _)

/-- The actual child dependency schedule survives both full physical operations unchanged. -/
lemma program_quantumTime (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
      (ControlledParallel.program modulus nontrivial).evaluatedEventDepth
        Resource.Event.quantumDuration :=
  ((ControlledResidentFrame.layout modulus.size).place_evaluatedEventDepth _ _).trans
    (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth _ _ _)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResident
