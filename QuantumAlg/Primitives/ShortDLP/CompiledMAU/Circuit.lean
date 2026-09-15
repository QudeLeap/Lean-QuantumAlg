/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Semantics

/-!
# Actual short-DLP member using the new shared multiplication core

The source Hadamard and two-QFT organization is unchanged. Its middle
segment is the actual pair of new exponentiations, with one shared power
and zero auxiliary word. The final state and terminal PMF agree exactly
with the existing independent short-DLP Born analysis.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Complete short-DLP circuit with the sealed oracle leaf replaced by the two
actual selected-unit modular-exponentiation programs on their shared workspace. -/
def compiledCircuit (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    UnitaryCircuit
      (Qubits (totalQubits (registerParameters m ell width))) :=
  UnitaryCircuit.seq (preparationCircuit (registerParameters m ell width))
    (UnitaryCircuit.seq (compiledGroupActionProgram m ell width N g x)
      (readoutCircuit (registerParameters m ell width)))

/-- Preparation and readout cover the canonical register, while the actual
selected-unit group action stays inside it; hence the complete member advertises exactly
the canonical flat physical layout. -/
@[simp] theorem compiledCircuit_physical_idx
    (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).physical_idx =
      List.range (totalQubits (registerParameters m ell width)) := by
  change
    UnitaryCircuit.unionPhysicalIdx
        (preparationCircuit (registerParameters m ell width)).physical_idx
        (UnitaryCircuit.unionPhysicalIdx
          (compiledGroupActionProgram m ell width N g x).physical_idx
          (readoutCircuit (registerParameters m ell width)).physical_idx) =
      List.range (totalQubits (registerParameters m ell width))
  rw [preparationCircuit_physical_idx, readoutCircuit_physical_idx]
  have hgroup :
      (compiledGroupActionProgram m ell width N g x).physical_idx ⊆
        List.range (totalQubits (registerParameters m ell width)) := by
    simpa only [totalQubits, registerParameters] using
      compiledGroupActionProgram_physical_idx_subset
        m ell width N g x
  rw [UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _ hgroup]
  exact UnitaryCircuit.unionPhysicalIdx_self _

/-- On the respective physical clean initial states, the actual compiled
circuit and the idealized permutation circuit produce the same final vector.
This equality transfers the complete Born analysis to the base-gate circuit. -/
theorem compiledCircuit_apply_input_eq_ideal
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (compiledCircuit m ell width N g x).applyVec
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (tripleIndex (registerParameters m ell width) 0 0
            (cleanUnitLabel width N 1)) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) =
      (circuit (unitEncoding width N hNgtOne hN) g x).applyVec
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          0 :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) := by
  simp only [compiledCircuit, circuit, UnitaryCircuit.applyVec_seq]
  rw [BornProbability.oracle_apply_preparation]
  congr 1
  exact compiledGroupActionProgram_apply_preparation
    m ell width N g x hNgtOne hN

/-- Every terminal basis amplitude of the actual base-gate circuit is exactly
the amplitude already analyzed by the short-DLP Born development. -/
theorem compiledCircuit_amplitude
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width)
    (j : Fin (2 ^ firstBits (registerParameters m ell width)))
    (k : Fin (2 ^ ell))
    (y : Fin (2 ^ workspaceBits width)) :
    (compiledCircuit m ell width N g x).applyVec
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
  have hamplitude := BornProbability.shortDLPCircuit_amplitude
    (unitEncoding width N hNgtOne hN) g x j k y
  change
    (circuit (unitEncoding width N hNgtOne hN) g x).applyVec
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          0 :
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
    ((compiledCircuit m ell width N g x).applyNormalized
      (NormalizedVector.ket
        (R := Qubits
          (totalQubits (registerParameters m ell width)))
        (tripleIndex (registerParameters m ell width) 0 0
          (cleanUnitLabel width N 1))))
    (layout (registerParameters m ell width)).systemIdx
  system_idx_eq := rfl

/-- The actual compiled state and the state used by the existing Born proof
are mathematically identical; only their physical construction differs. -/
theorem evolvedState_normalized_eq_ideal
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (evolvedState m ell width N g x).normalized =
      (BornProbability.evolvedState
        (unitEncoding width N hNgtOne hN) g x).normalized := by
  apply NormalizedVector.ext
  intro output
  have hvector := congrArg (fun state => state output)
    (compiledCircuit_apply_input_eq_ideal
      m ell width N g x hNgtOne hN)
  change
    (compiledCircuit m ell width N g x).applyVec
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          (tripleIndex (registerParameters m ell width) 0 0
            (cleanUnitLabel width N 1)) :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) output =
      (circuit (unitEncoding width N hNgtOne hN) g x).applyVec
        (NormalizedVector.ket
          (R := Qubits
            (totalQubits (registerParameters m ell width)))
          0 :
          HilbertVector
            (Qubits
              (totalQubits (registerParameters m ell width)))) output
    at hvector
  exact hvector

/-- Terminal outcome probabilities of the actual base-gate circuit equal the
probabilities already derived from the explicit Fourier amplitudes. -/
theorem outcomePMF_eq_ideal
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
