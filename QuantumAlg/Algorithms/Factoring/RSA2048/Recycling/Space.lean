/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Space
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Simultaneous space of the actual recycled RSA-2048 run

The fixed-width source facts determine the same independent generic allowance.
All seven source pairs, 112 packed outcomes and seven factors are allocated
before the single quantum bank. Recovery scratch dominates the other three
chronological scratch scopes. No old full-bank execution theorem is reused.
-/

namespace QuantumAlg.Factoring.RSA2048.Recycling

noncomputable section

open Execution
open EkeraHastadStyle.Canonical

/-- Seven complete batches use one control and the two 2,048-bit arithmetic words. -/
def qubitBound : Nat := 4_097

/-- Complete preallocation, reusable measurement cells and actual recovery scratch. -/
def classicalBitBound : Nat := 1_053_148_338_921

/-- The fixed independent pool keeps every native space coordinate. -/
def additionalSpace : SpacePool .quantum
  | .classicalBits => classicalBitBound
  | .quantumSystems dimension => if dimension = 2 then qubitBound else 0

/-- The one-bank quantum formula specializes for every original exact-width key. -/
lemma model_qubitBound_eq {N : Nat} (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Recycling.Program.qubitLimit N NativeRSA2048.rounds = qubitBound := by
  change 1 + 2 * arithmeticBits N = qubitBound
  rw [NativeRSA2048.model_arithmeticBits_eq model]
  norm_num [qubitBound, NativeRSA2048.modulusBits, NativeRSA2048.primeBits]

/-- The simultaneous classical formula specializes without normalizing an actual path. -/
lemma model_classicalBitBound_eq {N : Nat} (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Recycling.Program.classicalBitLimit N NativeRSA2048.rounds = classicalBitBound := by
  rw [NativeRSA2048.rounds, RSA.Recycling.Program.classicalBitLimit,
    RSA.Recycling.ClassicalFrame.classicalBits,
    NativeRSA2048.model_modulusBits_eq model,
    NativeRSA2048.model_measurementBits_eq model,
    NativeRSA2048.model_arithmeticBits_eq model,
    NativeRSA2048.model_allocationBits_eq model]
  norm_num [classicalBitBound, NativeRSA2048.modulusBits, NativeRSA2048.primeBits]

/-- Every native coordinate of the generic independent allowance equals the fixed pool. -/
lemma model_additionalSpace_eq {N : Nat} (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Recycling.Program.spaceLimit N NativeRSA2048.rounds = additionalSpace := by
  funext axis
  cases axis with
  | classicalBits =>
      exact (RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_classicalBits
        N NativeRSA2048.rounds).trans (model_classicalBitBound_eq model)
  | quantumSystems dimension =>
      by_cases same : dimension = 2
      · subst dimension
        exact (RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_qubits
          N NativeRSA2048.rounds).trans (model_qubitBound_eq model)
      · change RSA.Recycling.Program.liveSpace N 7 (.quantumSystems dimension) +
          RSA.Recycling.Program.temporarySpace N (.quantumSystems dimension) =
            if dimension = 2 then qubitBound else 0
        rw [if_neg same]
        rw [RSA.Recycling.Program.temporarySpace_quantum]
        simp only [RSA.Recycling.Program.liveSpace, Pi.add_apply,
          RSA.Recycling.ClassicalFrame.rsaRecyclingFrame_frameSpace_eq,
          SpacePool.ofShape, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add,
          RSA.Recycling.Program.readoutSpace, add_zero]
        change (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout
          (arithmeticBits N)).toQuantumLayout.dimensionCount dimension = 0
        rw [QubitLayout.toQuantumLayout_dimensionCount, if_neg (Ne.symm same)]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every actual seven-batch path obeys the fixed resident classical capacity. -/
lemma run_resident_classicalBits_le (model : NativeRSA2048.FixedWidthModel N)
    (input : Input N)
    (path : (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.Path) :
    (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.peakResidentSpace
      path .classicalBits ≤ base.residentSpace .classicalBits + classicalBitBound := by
  simpa only [model_classicalBitBound_eq model] using
    RSA.Recycling.Program.rsaRecyclingParent_run_resident_classicalBits_le
      base noQuantum input NativeRSA2048.rounds path

/-- Auxiliary storage has its own caller contribution and the same independent allowance. -/
lemma run_auxiliary_classicalBits_le (model : NativeRSA2048.FixedWidthModel N)
    (input : Input N)
    (path : (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.Path) :
    (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.peakAuxiliarySpace
      path .classicalBits ≤ base.auxiliarySpace .classicalBits + classicalBitBound := by
  simpa only [model_classicalBitBound_eq model] using
    RSA.Recycling.Program.rsaRecyclingParent_run_auxiliary_classicalBits_le
      base noQuantum input NativeRSA2048.rounds path

/-- The same actual path uses at most 4,097 added qubits for every original fixed-width key. -/
lemma run_resident_qubits_le (model : NativeRSA2048.FixedWidthModel N) (input : Input N)
    (path : (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.Path) :
    (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.peakResidentSpace
      path (.quantumSystems 2) ≤ base.residentSpace (.quantumSystems 2) + qubitBound := by
  simpa only [model_qubitBound_eq model] using
    RSA.Recycling.Program.rsaRecyclingParent_run_resident_qubits_le
      base noQuantum input NativeRSA2048.rounds path

end

end QuantumAlg.Factoring.RSA2048.Recycling
