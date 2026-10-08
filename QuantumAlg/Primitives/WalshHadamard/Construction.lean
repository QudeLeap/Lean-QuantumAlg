/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Native
public import QuantumAlg.Components.Oracle.Xor.Model
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Components.Oracle.Xor.Model
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Actual Hadamard-XOR-Hadamard execution

The first layer acts on every input and target qubit. The single declared XOR
query is followed by a Hadamard layer on the input only. Every gate and query
belongs to this same physical circuit [dW19, qcnotes.tex:1149-1173].
-/

namespace QuantumAlg.WalshHadamard.Native

noncomputable section

open Gate.HadamardLayer

/-- Actual final input-register Hadamards with the original target qubit untouched. -/
public def finalLayer (oracles : OracleModel) (width : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (layout (width + 1)) :=
  ((Gate.HadamardLayer.circuit oracles width).tensor
    (UnitaryCircuit.identity AlgorithmGate.model oracles (lastLayout width))
    (hadamardLayer_layout_disjoint width)).castLayout (hadamardLayer_layout_append width)

/-- The complete actual three-stage native circuit, with exactly the declared XOR access. -/
public def queryPipeline {width : Nat} (function : Fin (2 ^ width) → Bool) :
    UnitaryCircuit AlgorithmGate.model (XorOracle.model function) (layout (width + 1)) :=
  ((Gate.HadamardLayer.circuit (XorOracle.model function) (width + 1)).seq
    (XorOracle.circuit AlgorithmGate.model function)).seq
      (finalLayer (XorOracle.model function) width)

/-- Leaving the final target untouched adds no native instruction. -/
public theorem walshNative_finalLayer_eventCost (oracles : OracleModel) (width : Nat) :
    (finalLayer oracles width).eventCost = width •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [finalLayer, UnitaryCircuit.castLayout_eventCost,
    UnitaryCircuit.tensor_native_eventCost, UnitaryCircuit.identity_eventCost, add_zero,
    hadamardLayer_circuit_eventCost]

/-- The final layer retains the input's parallel depth, including the empty input. -/
public theorem walshNative_finalLayer_unit_depth (oracles : OracleModel) (width : Nat) :
    (finalLayer oracles width).evaluatedEventDepth (fun _ => 1) =
      if width = 0 then 0 else 1 := by
  rw [finalLayer, UnitaryCircuit.castLayout_evaluatedEventDepth,
    UnitaryCircuit.tensor_native_evaluatedEventDepth]
  change max ((Gate.HadamardLayer.circuit oracles width).evaluatedEventDepth (fun _ => 1)) 0 = _
  rw [max_eq_left (Nat.zero_le _), hadamardLayer_circuit_unit_depth]

/-- The full pipeline records the actual two Hadamard layers and its one XOR query. -/
public theorem walshNative_queryPipeline_eventCost {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    (queryPipeline function).eventCost =
      ((width + 1) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (XorOracle.model function)) (.gate .singleQubit) +
        ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (XorOracle.model function)) (.oracle .xor)) +
      width • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (XorOracle.model function))
          (.gate .singleQubit) := by
  rw [queryPipeline, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    hadamardLayer_circuit_eventCost, XorOracle.xorOracle_native_eventCost,
    walshNative_finalLayer_eventCost]

/-- Unit query duration gives two layers on an empty input and three otherwise. -/
public theorem walshNative_queryPipeline_unit_depth {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    (queryPipeline function).evaluatedEventDepth (fun _ => 1) =
      if width = 0 then 2 else 3 := by
  change (UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
    (Gate.HadamardLayer.circuit (XorOracle.model function) (width + 1)) +
    (XorOracle.circuit AlgorithmGate.model function).evaluatedEventDepth (fun _ => 1)) +
    (finalLayer (XorOracle.model function) width).evaluatedEventDepth (fun _ => 1) = _
  rw [hadamardLayer_circuit_unit_depth,
    XorOracle.xorOracle_native_unit_depth, walshNative_finalLayer_unit_depth]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
  split <;> rfl

end

end QuantumAlg.WalshHadamard.Native
