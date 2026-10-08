/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage
import all QuantumAlg.Primitives.QFT.Native.Inverse.Macros
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Gates.Hadamard.Layer

/-!
# Source construction statistics of the actual declared short-DLP member

Inverse-QFT macro names are retained in the native construction. Preparation
has no such names: its actual Hadamard layer is counted by its single-qubit
instructions. The combined observations are descriptive source statistics,
with explicit equations relating them to the actual native gate coordinates.
-/

namespace QuantumAlg.ShortDLP.DeclaredStage

noncomputable section

variable {N : Nat} {params : RegisterParameters}
  (encoding : UnitEncoding N params.workspaceBits)

/-- All actual preparation single-qubit instructions are the constructed Hadamard layer. -/
def preparationHadamardCount : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model (oracle encoding))
    (.gate .singleQubit) (prepare encoding).eventCost

/-- Combine the actual untagged preparation with existing readout construction names. -/
def sourceMacroCount (name : String) : Nat :=
  (if "hadamard" = name then preparationHadamardCount encoding else 0) +
    (readout encoding).macroCount name

/-- The constructed preparation contains one actual Hadamard per exponent wire. -/
theorem declaredStage_preparationHadamardCount :
    preparationHadamardCount encoding = firstBits params + params.ell := by
  have cost := congrArg
    (ResourcePool.count (model := .quantum AlgorithmGate.model (oracle encoding))
      (.gate .singleQubit))
    (Gate.HadamardLayer.hadamardLayer_circuit_eventCost
      (oracle encoding) (firstBits params + params.ell))
  rw [preparationHadamardCount, prepare,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
  exact cost.trans (by simp [ResourcePool.count_nsmul, ResourcePool.count_singleton])

private theorem preparationCnotCount :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracle encoding))
      (.gate .cnot) (prepare encoding).eventCost = 0 := by
  have cost := congrArg
    (ResourcePool.count (model := .quantum AlgorithmGate.model (oracle encoding))
      (.gate .cnot))
    (Gate.HadamardLayer.hadamardLayer_circuit_eventCost
      (oracle encoding) (firstBits params + params.ell))
  rw [prepare, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
  exact cost.trans (by simp [ResourcePool.count_nsmul, ResourcePool.count_singleton])

/-- The retained readout macro names belong to the two actual generated inverse words. -/
theorem declaredStage_readout_macroCount (name : String) :
    (readout encoding).macroCount name =
      (firstBits params + params.ell) * (if "hadamard" = name then 1 else 0) +
        ((firstBits params).choose 2 + params.ell.choose 2) *
          (if "controlled-phase" = name then 1 else 0) +
        (firstBits params / 2 + params.ell / 2) * (if "swap" = name then 1 else 0) := by
  change List.count name
    ((QuantumFourierTransform.Native.inverseCircuit (oracle encoding)
      (firstBits params)).sequence.macroTrace ++
      ((QuantumFourierTransform.Native.inverseCircuit (oracle encoding) params.ell).relabel
        (UnitaryCircuit.binarySuffixShift (firstBits params))).sequence.macroTrace) = _
  rw [List.count_append]
  change (QuantumFourierTransform.Native.inverseCircuit (oracle encoding)
    (firstBits params)).macroCount name +
    ((QuantumFourierTransform.Native.inverseCircuit (oracle encoding) params.ell).relabel
      (UnitaryCircuit.binarySuffixShift (firstBits params))).macroCount name = _
  rw [UnitaryCircuit.relabel_macroCount,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_macro_count,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_macro_count]
  ring

/-- Original source counts describe the actual preparation and the actual inverse-QFT word. -/
theorem declaredStage_sourceMacroCount (name : String) :
    sourceMacroCount encoding name =
      (2 * (firstBits params + params.ell)) * (if "hadamard" = name then 1 else 0) +
        ((firstBits params).choose 2 + params.ell.choose 2) *
          (if "controlled-phase" = name then 1 else 0) +
        (firstBits params / 2 + params.ell / 2) * (if "swap" = name then 1 else 0) := by
  rw [sourceMacroCount, declaredStage_preparationHadamardCount, declaredStage_readout_macroCount]
  split_ifs <;> ring

/-- The actual native readout has exactly the expanded one-qubit and CNOT coordinates. -/
theorem declaredStage_readout_nativeCount
    (event : Resource.Event (.quantum AlgorithmGate.model (oracle encoding))) :
    ResourcePool.count event (readout encoding).eventCost =
      (firstBits params + params.ell +
        3 * ((firstBits params).choose 2 + params.ell.choose 2)) *
          (if .gate .singleQubit = event then 1 else 0) +
      (2 * ((firstBits params).choose 2 + params.ell.choose 2) +
        3 * (firstBits params / 2 + params.ell / 2)) *
          (if .gate .cnot = event then 1 else 0) := by
  rw [readout, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    readoutPair, UnitaryCircuit.parallel_eventCost, ResourcePool.count_add,
    UnitaryCircuit.relabel_eventCost,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count]
  ring

/-- Expanding the observed Hadamards and rotations gives the actual native one-qubit count. -/
theorem declaredStage_singleQubit_eq_sourceMacros (g x : (ZMod N)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracle encoding))
      (.gate .singleQubit) (circuit encoding g x).eventCost =
      sourceMacroCount encoding "hadamard" +
        3 * sourceMacroCount encoding "controlled-phase" := by
  rw [circuit_eventCost, ResourcePool.count_add, ResourcePool.count_add,
    declaredStage_readout_nativeCount, declaredStage_sourceMacroCount,
    declaredStage_sourceMacroCount]
  have prepared := declaredStage_preparationHadamardCount encoding
  change ResourcePool.count (model := .quantum AlgorithmGate.model (oracle encoding))
    (.gate .singleQubit) (prepare encoding).eventCost = _ at prepared
  rw [prepared]
  simp
  ring

/-- The controlled-phase and SWAP constructions expand to their actual native CNOT count. -/
theorem declaredStage_cnot_eq_sourceMacros (g x : (ZMod N)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (oracle encoding))
      (.gate .cnot) (circuit encoding g x).eventCost =
      2 * sourceMacroCount encoding "controlled-phase" + 3 * sourceMacroCount encoding "swap" := by
  rw [circuit_eventCost, ResourcePool.count_add, ResourcePool.count_add,
    declaredStage_readout_nativeCount, declaredStage_sourceMacroCount,
    declaredStage_sourceMacroCount, preparationCnotCount]
  simp

end

end QuantumAlg.ShortDLP.DeclaredStage
