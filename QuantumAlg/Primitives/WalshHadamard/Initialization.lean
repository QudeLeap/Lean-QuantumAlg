/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Construction
import all QuantumAlg.Primitives.WalshHadamard.Construction
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# The actual target flip after zero preparation

The only preparation instruction supplies zero on each fresh system. The
original target state |1> therefore requires its own native X before the
Hadamard-query-Hadamard word [dW19, qcnotes.tex:1193,1245]. The definitions
here describe the unitary part after allocation and zero preparation;
measurement and classical storage remain in the complete readout execution.
-/

namespace QuantumAlg.WalshHadamard.Native

noncomputable section

open Gate.HadamardLayer

/-- Flip the original final target wire with one actual native X operation. -/
public def targetFlip (oracles : OracleModel) (width : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (layout (width + 1)) :=
  Gate.singleQubitAt (layout (width + 1)) oracles Gate.XOp (Fin.last width) rfl

/-- The actual unitary word accepts the all-zero state produced by fixed preparation. -/
public def zeroInputProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model (XorOracle.model width) (layout (width + 1)) :=
  (targetFlip (XorOracle.model width) width).seq (queryPipeline width)

/-- The nonzero target is paid for by one additional native one-qubit instruction. -/
public lemma walshNative_targetFlip_eventCost (oracles : OracleModel) (width : Nat) :
    (targetFlip oracles width).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rfl

/-- The explicit target flip has one dependency step. -/
public lemma walshNative_targetFlip_unit_depth (oracles : OracleModel) (width : Nat) :
    (targetFlip oracles width).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

/-- Both Hadamard layers and the target flip contribute their actual native events. -/
public lemma walshNative_zeroInputProgram_eventCost (width : Nat) :
    (zeroInputProgram width).eventCost =
      (2 * width + 2) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (XorOracle.model width)) (.gate .singleQubit) +
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (XorOracle.model width)) (.oracle .xor) := by
  rw [zeroInputProgram, UnitaryCircuit.seq_eventCost,
    walshNative_targetFlip_eventCost, walshNative_queryPipeline_eventCost]
  rw [show 2 * width + 2 = (width + 1) + width + 1 by omega]
  simp only [add_nsmul, one_nsmul]
  abel

/-- Post-preparation unitary depth includes the target flip, also at zero query width. -/
public lemma walshNative_zeroInputProgram_unit_depth (width : Nat) :
    (zeroInputProgram width).evaluatedEventDepth (fun _ => 1) =
      if width = 0 then 3 else 4 := by
  change (targetFlip (XorOracle.model width) width).evaluatedEventDepth (fun _ => 1) +
    (queryPipeline width).evaluatedEventDepth (fun _ => 1) = _
  rw [walshNative_targetFlip_unit_depth, walshNative_queryPipeline_unit_depth]
  split <;> rfl

end

end QuantumAlg.WalshHadamard.Native
