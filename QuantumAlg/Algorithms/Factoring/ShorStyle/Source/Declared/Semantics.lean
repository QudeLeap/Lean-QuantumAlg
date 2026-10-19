/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Circuit
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Distribution
import all QuantumAlg.Algorithms.OrderFinding.Native.Matrix
import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Distribution
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix

/-!
# Exact XOR action and Born law of the fixed Shor query family

The declared operator acts on arbitrary target words. The full native member
has exactly the existing order-finding matrix, so its original Born law and
sample-dependent joint distribution can be reused without new arithmetic
assumptions or an independent probability transition.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource

noncomputable section

variable {N width : Nat} (bounds : RegisterBounds N width) (phaseBits : Nat)

/-- Physical placement retains the operator owned by the selected declaration. -/
lemma oracleLayer_matrix (gates : GateModel) (base : Fin (2 ^ width)) :
    (oracleLayer width phaseBits gates base).matrix (interpretation bounds phaseBits) =
      UnitaryOperator.reindex
        (QuantumSignature.qubitsIndexEquiv (phaseBits + width)).symm
        (OrderFinding.modExpOracle (bounds.access phaseBits base)) := by
  rw [oracleLayer, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  apply Subtype.ext
  rfl

/-- Binary coordinates expose exactly the mathematical modular-exponentiation oracle. -/
lemma oracleLayer_binaryMatrix (gates : GateModel) (base : Fin (2 ^ width)) :
    (oracleLayer width phaseBits gates base).binaryMatrix (interpretation bounds phaseBits) =
      OrderFinding.modExpOracle (bounds.access phaseBits base) := by
  rw [UnitaryCircuit.binaryMatrix, oracleLayer_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (phaseBits + width)).symm
    (OrderFinding.modExpOracle (bounds.access phaseBits base))

/-- Every basis target is XOR-updated by the actual power modulo the declared modulus. -/
lemma oracleLayer_apply_ket (gates : GateModel) (base : Fin (2 ^ width))
    (exponent : Fin (2 ^ phaseBits)) (target : Fin (2 ^ width)) :
    ((oracleLayer width phaseBits gates base).binaryMatrix (interpretation bounds phaseBits)).apply
        (NormalizedVector.ket (prodEquiv (exponent, target))) =
      NormalizedVector.ket (prodEquiv (exponent,
        OrderFinding.modExpOracleTarget (bounds.access phaseBits base) exponent target)) := by
  rw [oracleLayer_binaryMatrix]
  exact OrderFinding.modExpOracle_apply_ket (bounds.access phaseBits base) exponent target

/-- The native Hadamards retain the identity on the complete target register. -/
lemma initialLayer_binaryMatrix :
    (initialLayer width phaseBits).binaryMatrix (interpretation bounds phaseBits) =
      (WalshHadamard.hadamardLayerOperator phaseBits).tensor
        (1 : UnitaryOperator (Qubits width)) := by
  rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  exact congrArg (fun operator : UnitaryOperator (Qubits phaseBits) =>
    operator.tensor (1 : UnitaryOperator (Qubits width)))
      (WalshHadamard.Native.native_binary_matrix (model width phaseBits) phaseBits
        (interpretation bounds phaseBits))

/-- The generated inverse QFT has its exact prefix action for every target state. -/
lemma readoutLayer_binaryMatrix :
    (readoutLayer width phaseBits).binaryMatrix (interpretation bounds phaseBits) =
      (star (QFTOperator phaseBits)).tensor (1 : UnitaryOperator (Qubits width)) := by
  rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply congrArg (fun operator : UnitaryOperator (Qubits phaseBits) =>
    operator.tensor (1 : UnitaryOperator (Qubits width)))
  change QuantumFourierTransform.Native.onBinaryLabels
    (QuantumFourierTransform.Native.inverseCircuit (model width phaseBits) phaseBits)
      (interpretation bounds phaseBits) =
      star (QFTOperator phaseBits)
  exact QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
    (model width phaseBits) phaseBits (interpretation bounds phaseBits)

/-- The complete physical member has the exact three-stage source operator. -/
lemma circuit_binaryMatrix (base : Fin (2 ^ width)) :
    (circuit width phaseBits base).binaryMatrix (interpretation bounds phaseBits) =
      (star (QFTOperator phaseBits)).tensor (1 : UnitaryOperator (Qubits width)) *
        (OrderFinding.modExpOracle (bounds.access phaseBits base) *
          (WalshHadamard.hadamardLayerOperator phaseBits).tensor
            (1 : UnitaryOperator (Qubits width))) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    initialLayer_binaryMatrix, oracleLayer_binaryMatrix, readoutLayer_binaryMatrix]

/-- Selecting a base in one fixed model preserves the established source matrix. -/
lemma circuit_binaryMatrix_eq_native (base : Fin (2 ^ width)) :
    (circuit width phaseBits base).binaryMatrix (interpretation bounds phaseBits) =
      (OrderFinding.Native.circuit phaseBits width).binaryMatrix
        (OrderFinding.Native.interpretation (bounds.access phaseBits base)) := by
  rw [circuit_binaryMatrix, OrderFinding.Native.circuit_binaryMatrix]

/-- The original all-zero source state evolved by this actual selected member. -/
def evolvedState (base : Fin (2 ^ width)) :
    QubitLayout.State (OrderFinding.Native.sourceLayout phaseBits width) :=
  { state := PureState.ofNormalized
      (((circuit width phaseBits base).binaryMatrix (interpretation bounds phaseBits)).apply
        (OrderFinding.Native.zeroInput phaseBits width))
      (OrderFinding.Native.sourceLayout phaseBits width).systemIdx
    system_idx_eq := rfl }

/-- The entire normalized phase-target state agrees with the existing Born source. -/
lemma evolvedState_eq_native (base : Fin (2 ^ width)) :
    evolvedState bounds phaseBits base =
      OrderFinding.Native.evolvedState (bounds.access phaseBits base) := by
  unfold evolvedState OrderFinding.Native.evolvedState OrderFinding.Native.evolvedVector
  rw [circuit_binaryMatrix_eq_native]

/-- The actual phase-prefix Born law of the selected declared member. -/
def outcomePMF (base : Fin (2 ^ width)) : PMF (TerminalZMeasure.Outcome phaseBits) :=
  (OrderFinding.Native.measurement phaseBits width).outcomePMF
    (evolvedState bounds phaseBits base)

/-- The old source Born theorem applies to the complete new physical member. -/
lemma outcomePMF_eq_native (base : Fin (2 ^ width)) :
    outcomePMF bounds phaseBits base =
      OrderFinding.Native.sourceOutcomePMF (bounds.access phaseBits base) := by
  rw [outcomePMF, evolvedState_eq_native]
  rfl

/-- Original Shor inputs supply precisely the declared register conditions. -/
lemma sourceBounds {N : Nat} (input : Input N) : RegisterBounds N (modulusBits N) where
  modulus_pos := input.modulus_pos
  register_fits := input.register_fits

/-- Read the sampler's original stored base without imposing a unit-only query domain. -/
def sampleBase {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) : Fin (2 ^ modulusBits N) :=
  ⟨(parameterValue input sample).first.toNat,
    (parameterValue input sample).first.toNat_lt⟩

/-- The fixed-family member selected by the original sample has its original conditional law. -/
lemma sample_outcomePMF_eq {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    outcomePMF (sourceBounds input) (Canonical.phaseBits N) (sampleBase input sample) =
      sourceSampleOutcomePMF input sample := by
  rw [outcomePMF_eq_native]
  rfl

/-- Uniform sampling keeps the original correlation between the base and its Born outcome. -/
lemma sampled_outcomePMF_eq {N : Nat} (input : Input N) :
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).bind (fun sample =>
      (outcomePMF (sourceBounds input) (Canonical.phaseBits N) (sampleBase input sample)).map
        fun measurement => (⟨sample, measurement⟩ : SourceOutcome N)) =
      sourceOutcomePMF input := by
  simp only [sample_outcomePMF_eq, sourceOutcomePMF]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource
