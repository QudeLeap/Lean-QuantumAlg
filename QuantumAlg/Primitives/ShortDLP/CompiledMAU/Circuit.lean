/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Semantics
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution

/-!
# Actual short-DLP member using the new shared multiplication core

The source Hadamard and two-QFT organization is unchanged. Its middle
segment is the actual pair of new exponentiations, with one shared power
and zero auxiliary word. The final state and terminal PMF agree exactly
with the existing independent short-DLP Born analysis.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Complete short-DLP circuit with the sealed oracle leaf replaced by the two
actual selected-unit modular-exponentiation programs on their shared workspace. -/
def compiledCircuit (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (totalQubits (registerParameters m ell width))).toQuantum :=
  UnitaryCircuit.seq (preparationCircuit (registerParameters m ell width))
    (UnitaryCircuit.seq (compiledGroupActionProgram m ell width N g x)
      (readoutCircuit (registerParameters m ell width)))

/-- The declared and compiled stages use the same actual inverse-Fourier operator. -/
lemma readoutCircuit_binaryMatrix_eq_declared
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) :
    (readoutCircuit params).binaryMatrix environment =
      (DeclaredStage.readout N params).binaryMatrix (declaredInterpretation encoding) := by
  rw [readoutCircuit, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    DeclaredStage.readoutPair_sourceMatrix, DeclaredStage.readout_binaryMatrix]

-- Keep composition abstract so kernel conversion never unfolds the large arithmetic word.
private lemma three_stage_action {gates : GateModel} {oracles declaredOracles : OracleModel}
    {bits : Nat}
    (environment : oracles.Interpretation)
    (declaredEnvironment : declaredOracles.Interpretation)
    (preparation group readout : UnitaryCircuit gates oracles
      (QuantumSignature.qubits bits).canonicalPlacement.layout)
    (declaredReadout declared : UnitaryCircuit gates declaredOracles
      (QuantumSignature.qubits bits).canonicalPlacement.layout)
    (input declaredInput graph : HilbertVector (Qubits bits))
    (groupAction : group.applyBinaryVec environment
      (preparation.applyBinaryVec environment input) = graph)
    (readoutMatrix : readout.binaryMatrix environment =
      declaredReadout.binaryMatrix declaredEnvironment)
    (declaredAction : declared.applyBinaryVec declaredEnvironment declaredInput =
      declaredReadout.applyBinaryVec declaredEnvironment graph) :
    (preparation.seq (group.seq readout)).applyBinaryVec environment input =
      declared.applyBinaryVec declaredEnvironment declaredInput := by
  rw [UnitaryCircuit.applyBinaryVec_seq, UnitaryCircuit.applyBinaryVec_seq, groupAction]
  exact (congrArg (fun operator : UnitaryOperator (Qubits bits) => operator.applyVec graph)
    readoutMatrix).trans declaredAction.symm

/-- On the respective physical clean initial states, the actual compiled
circuit and the idealized permutation circuit produce the same final vector.
This equality transfers the complete Born analysis to the base-gate circuit. -/
lemma compiledCircuit_apply_input_eq_ideal
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (compiledCircuit m ell width N g x).applyBinaryVec environment
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (tripleIndex (registerParameters m ell width) 0 0
            (cleanUnitLabel width N 1)) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) =
      (DeclaredStage.circuit N (registerParameters m ell width) g x).applyBinaryVec
        (declaredInterpretation (unitEncoding width N hNgtOne hN))
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (prodEquiv
            ((0 : Fin (2 ^ (firstBits (registerParameters m ell width) + ell))),
              (0 : Fin (2 ^ workspaceBits width)))) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) :=
  three_stage_action (gates := AlgorithmGate.model) (oracles := .empty)
    (declaredOracles := declaredModel N (registerParameters m ell width))
    (bits := totalQubits (registerParameters m ell width)) environment
    (declaredInterpretation (unitEncoding width N hNgtOne hN))
    (preparationCircuit (registerParameters m ell width))
    (compiledGroupActionProgram m ell width N g x)
    (readoutCircuit (registerParameters m ell width))
    (DeclaredStage.readout N (registerParameters m ell width))
    (DeclaredStage.circuit N (registerParameters m ell width) g x)
    (NormalizedVector.ket (R := Qubits (totalQubits (registerParameters m ell width)))
      (tripleIndex (registerParameters m ell width) 0 0 (cleanUnitLabel width N 1))).vec
    (NormalizedVector.ket (R := Qubits (totalQubits (registerParameters m ell width)))
      (prodEquiv
        ((0 : Fin (2 ^ (firstBits (registerParameters m ell width) + ell))),
          (0 : Fin (2 ^ workspaceBits width))))).vec
    (BornProbability.postOracleVec (params := registerParameters m ell width)
      (unitEncoding width N hNgtOne hN) g x)
    (compiledGroupActionProgram_apply_preparation m ell width N g x hNgtOne hN)
    (readoutCircuit_binaryMatrix_eq_declared (params := registerParameters m ell width)
        (unitEncoding width N hNgtOne hN))
    (BornProbability.declared_circuit_apply_zeroVec (params := registerParameters m ell width)
      (unitEncoding width N hNgtOne hN) g x)

/-- Every terminal basis amplitude of the actual base-gate circuit is exactly
the amplitude already analyzed by the short-DLP Born development. -/
lemma compiledCircuit_amplitude
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width)
    (j : Fin (2 ^ firstBits (registerParameters m ell width)))
    (k : Fin (2 ^ ell))
    (y : Fin (2 ^ workspaceBits width)) :
    (compiledCircuit m ell width N g x).applyBinaryVec environment
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (tripleIndex (registerParameters m ell width) 0 0
            (cleanUnitLabel width N 1)) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width))))
        (tripleEquiv (registerParameters m ell width) ((j, k), y)) =
      BornProbability.circuitAmplitude
        (unitEncoding width N hNgtOne hN) g x j k y := by
  rw [compiledCircuit_apply_input_eq_ideal
    m ell width N g x hNgtOne hN]
  have hamplitude := BornProbability.declaredCircuit_amplitude
    (unitEncoding width N hNgtOne hN) g x j k y
  change
    (DeclaredStage.circuit N (registerParameters m ell width) g x).applyBinaryVec
        (declaredInterpretation (unitEncoding width N hNgtOne hN))
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (prodEquiv
            ((0 : Fin (2 ^ (firstBits (registerParameters m ell width) + ell))),
              (0 : Fin (2 ^ workspaceBits width)))) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width))))
        (tripleEquiv (registerParameters m ell width) ((j, k), y)) =
      BornProbability.circuitAmplitude
        (unitEncoding width N hNgtOne hN) g x j k y at hamplitude
  exact hamplitude

/-- Physical clean-unit input state for the actual two-word workspace. -/
def inputState (m ell width N : Nat) :
    QubitLayout.State (layout (registerParameters m ell width)) where
  state := PureState.ofNormalized
    (NormalizedVector.ket
      (R := Qubits
        (totalQubits (registerParameters m ell width)))
      (tripleIndex (registerParameters m ell width) 0 0
        (cleanUnitLabel width N 1)))
    (layout (registerParameters m ell width)).systemIdx
  system_idx_eq := rfl

/-- Normalized state produced by the complete actual base-gate circuit. -/
def evolvedState (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    QubitLayout.State (layout (registerParameters m ell width)) where
  state := PureState.ofNormalized
    (((compiledCircuit m ell width N g x).binaryMatrix OracleModel.emptyInterpretation).apply
      (NormalizedVector.ket
        (R := Qubits
          (totalQubits (registerParameters m ell width)))
        (tripleIndex (registerParameters m ell width) 0 0
          (cleanUnitLabel width N 1))))
    (layout (registerParameters m ell width)).systemIdx
  system_idx_eq := rfl

/-- The actual compiled state and the state used by the existing Born proof
are mathematically identical; only their physical construction differs. -/
lemma evolvedState_normalized_eq_ideal
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (evolvedState m ell width N g x).normalized =
      (BornProbability.evolvedState (params := registerParameters m ell width)
        (unitEncoding width N hNgtOne hN) g x).normalized := by
  apply NormalizedVector.ext
  intro output
  have hvector := congrArg (fun state => state output)
    (compiledCircuit_apply_input_eq_ideal (environment := OracleModel.emptyInterpretation)
      m ell width N g x hNgtOne hN)
  change
    (compiledCircuit m ell width N g x).applyBinaryVec OracleModel.emptyInterpretation
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (tripleIndex (registerParameters m ell width) 0 0
            (cleanUnitLabel width N 1)) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) output =
      (DeclaredStage.circuit N (registerParameters m ell width) g x).applyBinaryVec
        (declaredInterpretation (unitEncoding width N hNgtOne hN))
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (prodEquiv
            ((0 : Fin (2 ^ (firstBits (registerParameters m ell width) + ell))),
              (0 : Fin (2 ^ workspaceBits width)))) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) output
    at hvector
  exact hvector

/-- Terminal outcome probabilities of the actual base-gate circuit equal the
probabilities already derived from the explicit Fourier amplitudes. -/
lemma outcomePMF_eq_ideal
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (measurement (registerParameters m ell width)).outcomePMF
        (evolvedState m ell width N g x) =
      (measurement (registerParameters m ell width)).outcomePMF
        (BornProbability.evolvedState
          (unitEncoding width N hNgtOne hN) g x) := by
  apply PMF.ext
  intro outcome
  simp only [TerminalZMeasure.outcomePMF_apply]
  rw [evolvedState_normalized_eq_ideal
    m ell width N g x hNgtOne hN]

end

end QuantumAlg.ShortDLP.CompiledMAU
