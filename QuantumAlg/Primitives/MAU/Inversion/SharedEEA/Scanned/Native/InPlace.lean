/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Corrected
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Forward

/-!
# Actual scanned same-port forward EEA with its large workspace returned to zero

The original fixed constant load precedes the new corrected scanned
loop. The original actual output reversal and fixed constant unloading
put the inverse on the same input port and return the original large
Work1 port to zero. All small forward history and the complete scan pool
remain available for the actual native adjoint. No output bank is added.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.InPlaceForward

noncomputable section

/-- Actual fixed input load, new corrected native forward, and paid original output-port word. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  (UnitaryCircuit.onBinaryPrefix (poolEncoding modulus.size).width
    (InitialPortProgram.program modulus)).seq
      ((CorrectedSchedule.program modulus nontrivial).seq
        (UnitaryCircuit.onBinaryPrefix (poolEncoding modulus.size).width
          (OutputPortProgram.program modulus)))

/-- The actual same-port endpoint retains all source history and the same initialized pool. -/
lemma program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding modulus.size).encode (InitialPortProgram.inputFrame modulus input, pool)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding modulus.size).encode
          (SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool))) := by
  have firstActual := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (SharedEEA.encoding modulus.size) (poolEncoding modulus.size)
    (InitialPortProgram.program modulus)
    (InitialPortProgram.inputFrame modulus input) (InitialFrame.initial modulus input) pool
    (InitialPortProgram.program_initial (environment := environment) modulus input)
  have secondActual := CorrectedSchedule.program_initial modulus nontrivial environment input
    coprime positive bounded pool addressZero prefixZero borrowZero
  have thirdActual := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (SharedEEA.encoding modulus.size) (poolEncoding modulus.size)
    (OutputPortProgram.program modulus)
    (SharedEEA.CorrectedSchedule.result modulus input.val positive bounded)
    (SharedEEA.InPlaceForward.result modulus input.val positive bounded) pool
    ((OutputPortProgram.program_realizes (environment := environment) modulus).apply_encoded_ket
      (SharedEEA.CorrectedSchedule.result modulus input.val positive bounded))
  exact UnitaryCircuit.applyNormalized_seq_of_eq firstActual
    (UnitaryCircuit.applyNormalized_seq_of_eq secondActual thirdActual)

/-- The actual same-forward native adjoint recovers the complete original input and pool frame. -/
lemma dagger_result (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    ((program modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((encoding modulus.size).encode
              (SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding modulus.size).encode (InitialPortProgram.inputFrame modulus input, pool))) := by
  have actual := program_initial modulus nontrivial environment input coprime positive bounded
    pool addressZero prefixZero borrowZero
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

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.InPlaceForward
