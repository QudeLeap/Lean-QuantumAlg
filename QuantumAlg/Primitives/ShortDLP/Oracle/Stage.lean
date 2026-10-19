/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Oracle.Declared
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix

/-!
# Model-owned short-DLP quantum stage

The two exponent registers receive actual parallel Hadamards. One query from
the fixed group-operation declaration follows. The two inverse QFTs run on
disjoint original exponent registers in parallel while the group workspace
remains resident.
-/

namespace QuantumAlg.ShortDLP.DeclaredStage

noncomputable section

private abbrev oracle (N : Nat) (params : RegisterParameters) : OracleModel :=
  declaredModel N params

private abbrev layout (params : RegisterParameters) :
    QuantumLayout (totalQubits params) :=
  (QuantumSignature.qubits (totalQubits params)).canonicalPlacement.layout

/-- Both actual exponent registers are prepared in parallel; workspace is untouched. -/
def prepare (N : Nat) (params : RegisterParameters) :
    UnitaryCircuit AlgorithmGate.model (oracle N params) (layout params) :=
  (Gate.HadamardLayer.circuit (oracle N params)
    (firstBits params + params.ell)).onBinaryPrefix params.workspaceBits

/-- Preparation uses one parallel dependency layer for nonempty exponent storage. -/
lemma prepare_unitDepth (N : Nat) (params : RegisterParameters) :
    (prepare N params).evaluatedEventDepth (fun _ => 1) =
      if firstBits params + params.ell = 0 then 0 else 1 := by
  rw [prepare, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth _ _

private lemma readout_disjoint (first second : Nat) :
    Disjoint
      (UnitaryCircuit.binaryPrefixEmbedding first second).selection
      (UnitaryCircuit.binarySuffixEmbedding first second).selection := by
  apply Finset.disjoint_left.mpr
  intro wire inFirst inSecond
  obtain ⟨a, _, equalFirst⟩ := Finset.mem_map.mp inFirst
  obtain ⟨b, _, equalSecond⟩ := Finset.mem_map.mp inSecond
  have firstBound := a.isLt
  have same := congrArg Fin.val (equalFirst.trans equalSecond.symm)
  change a.val < first at firstBound
  change a.val = first + b.val at same
  omega

/-- Both inverse QFT words operate in parallel on disjoint original exponent wires. -/
def readoutPair (oracles : OracleModel) (params : RegisterParameters) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (firstBits params + params.ell)).canonicalPlacement.layout :=
  UnitaryCircuit.parallel
    (QuantumFourierTransform.Native.inverseCircuit oracles (firstBits params))
    ((QuantumFourierTransform.Native.inverseCircuit oracles params.ell).relabel
      (UnitaryCircuit.binarySuffixShift (firstBits params)))
    (UnitaryCircuit.binaryPrefixEmbedding (firstBits params) params.ell)
    (UnitaryCircuit.binarySuffixEmbedding (firstBits params) params.ell)
    (readout_disjoint (firstBits params) params.ell)

/-- The group workspace remains resident through both parallel inverse QFTs. -/
def readout (N : Nat) (params : RegisterParameters) :
    UnitaryCircuit AlgorithmGate.model (oracle N params) (layout params) :=
  (readoutPair (oracle N params) params).onBinaryPrefix params.workspaceBits

/-- Readout depth is the maximum of the two native inverse-QFT depths. -/
lemma readout_unitDepth (N : Nat) (params : RegisterParameters) :
    (readout N params).evaluatedEventDepth (fun _ => 1) =
      max
        ((QuantumFourierTransform.Native.inverseCircuit (oracle N params)
          (firstBits params)).evaluatedEventDepth (fun _ => 1))
        ((QuantumFourierTransform.Native.inverseCircuit (oracle N params)
          params.ell).evaluatedEventDepth (fun _ => 1)) := by
  simp only [readout, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth,
    readoutPair, UnitaryCircuit.evaluatedEventDepth_parallel,
    UnitaryCircuit.relabel_evaluatedEventDepth]

/-- The actual prepare, declared-query, parallel-readout construction. -/
def circuit (N : Nat) (params : RegisterParameters) (g x : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model (oracle N params) (layout params) :=
  (prepare N params).seq
    ((declaredCircuit AlgorithmGate.model N params g x).seq (readout N params))

/-- The actual stage has the source permutation between its real preparation
and inverse-Fourier readout, all in the same binary coordinates. -/
lemma circuit_binaryMatrix {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) (g x : (ZMod N)ˣ) :
    ((circuit N params g x).binaryMatrix (declaredInterpretation encoding)) =
      ((readout N params).binaryMatrix (declaredInterpretation encoding)) *
        oracleOperator encoding g x * ((prepare N params).binaryMatrix (declaredInterpretation
          encoding)) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    declaredCircuit_binaryMatrix]

/-- The complete event ledger includes the single declared group query. -/
lemma circuit_eventCost (N : Nat) (params : RegisterParameters) (g x : (ZMod N)ˣ) :
    (circuit N params g x).eventCost =
      (prepare N params).eventCost +
        (ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (oracle N params))
          (.oracle .groupOperation) + (readout N params).eventCost) := by
  rw [circuit, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, declaredCircuit_eventCost]

/-- Preparation and both inverse Fourier words have no oracle instruction:
the complete stage makes exactly its one model-owned group query. -/
lemma circuit_groupQueryCount (N : Nat) (params : RegisterParameters) (g x : (ZMod N)ˣ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (oracle N params))
      (.oracle .groupOperation)
      (circuit N params g x).eventCost = 1 := by
  have preparationCount :
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (oracle N params))
        (.oracle .groupOperation)
        (prepare N params).eventCost = 0 := by
    have cost := congrArg
      (ResourcePool.count
        (model := .quantum AlgorithmGate.model (oracle N params))
        (.oracle .groupOperation))
      (Gate.HadamardLayer.hadamardLayer_circuit_eventCost
        (oracle N params) (firstBits params + params.ell))
    rw [prepare, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
    exact cost.trans (by simp [ResourcePool.count_nsmul, ResourcePool.count_singleton])
  have readoutCount :
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (oracle N params))
        (.oracle .groupOperation)
        (readout N params).eventCost = 0 := by
    rw [readout, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
      readoutPair, UnitaryCircuit.parallel_eventCost,
      ResourcePool.count_add, UnitaryCircuit.relabel_eventCost,
      QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count,
      QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count]
    simp
  rw [circuit_eventCost, ResourcePool.count_add, ResourcePool.count_add,
    preparationCount, readoutCount]
  simp [ResourcePool.count_singleton]

/-- One query separates the parallel preparation and parallel inverse readout. -/
lemma circuit_unitDepth (N : Nat) (params : RegisterParameters) (g x : (ZMod N)ˣ) :
    (circuit N params g x).evaluatedEventDepth (fun _ => 1) =
      (if firstBits params + params.ell = 0 then 0 else 1) + 1 +
        max
          ((QuantumFourierTransform.Native.inverseCircuit (oracle N params)
            (firstBits params)).evaluatedEventDepth (fun _ => 1))
          ((QuantumFourierTransform.Native.inverseCircuit (oracle N params)
            params.ell).evaluatedEventDepth (fun _ => 1)) := by
  rw [circuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, prepare_unitDepth,
    declaredCircuit_unitDepth, readout_unitDepth]
  omega

end

end QuantumAlg.ShortDLP.DeclaredStage
