/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Resources
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Space
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Simultaneous space of the actual measured RSA-2048 run

The fixed-width source facts determine the same independent generic allowance.
All four source pairs, 80 packed outcomes and four factors are allocated
before the single quantum bank. Recovery scratch dominates the other three
chronological scratch scopes. No old full-bank execution theorem is reused.
-/

namespace QuantumAlg.Factoring.RSA2048.Measured

noncomputable section

attribute [local instance] RSA.Configuration.rsa2048

private lemma rsaMeasured2048_configuredAdditional_eq : RSA.Configuration.additionalMembers = 18
    := rfl

open Execution
open EkeraHastadStyle.Canonical

/-- Four complete batches use two 2,048-bit words, one control and three helpers. -/
def qubitBound : Nat := 4_100

/-- Complete preallocation, reusable measurement cells and actual recovery scratch. -/
def classicalBitBound : Nat := 1_053_148_158_593

/-- The fixed independent pool keeps every native space coordinate. -/
def additionalSpace : SpacePool .quantum
  | .classicalBits => classicalBitBound
  | .quantumSystems dimension => if dimension = 2 then qubitBound else 0

/-- The one-bank quantum formula specializes for every original exact-width key. -/
lemma rsaMeasured2048_model_qubitBound_eq {N : Nat} (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Measured.Program.qubitLimit N RSA.Configuration.rsa2048Batches = qubitBound := by
  change 2 * arithmeticBits N + 4 = qubitBound
  rw [NativeRSA2048.model_arithmeticBits_eq model]
  norm_num [qubitBound, NativeRSA2048.modulusBits, NativeRSA2048.primeBits]

/-- The simultaneous classical formula specializes without normalizing an actual path. -/
lemma rsaMeasured2048_model_classicalBitBound_eq {N : Nat} (model :
    NativeRSA2048.FixedWidthModel N) :
    RSA.Measured.Program.classicalBitLimit N RSA.Configuration.rsa2048Batches =
      classicalBitBound := by
  rw [RSA.Configuration.rsa2048Batches, RSA.Measured.Program.classicalBitLimit,
    RSA.Recycling.ClassicalFrame.classicalBits,
    NativeRSA2048.model_modulusBits_eq model,
    NativeRSA2048.model_measurementBits_eq model,
    NativeRSA2048.model_arithmeticBits_eq model,
    NativeRSA2048.model_allocationBits_eq model]
  norm_num [RSA.membersPerBatch, rsaMeasured2048_configuredAdditional_eq, RSA.Configuration.rsa2048,
    classicalBitBound,
    NativeRSA2048.modulusBits, NativeRSA2048.primeBits]

/-- Every native coordinate of the generic independent allowance equals the fixed pool. -/
lemma rsaMeasured2048_model_additionalSpace_eq {N : Nat} (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Measured.Program.spaceLimit N RSA.Configuration.rsa2048Batches = additionalSpace := by
  funext axis
  cases axis with
  | classicalBits =>
      exact (RSA.Measured.Program.rsaMeasuredParent_spaceLimit_classicalBits
        N RSA.Configuration.rsa2048Batches).trans (rsaMeasured2048_model_classicalBitBound_eq model)
  | quantumSystems dimension =>
      by_cases same : dimension = 2
      · subst dimension
        exact (RSA.Measured.Program.rsaMeasuredParent_spaceLimit_qubits
          N RSA.Configuration.rsa2048Batches).trans (rsaMeasured2048_model_qubitBound_eq model)
      · change RSA.Measured.Program.liveSpace N 4 (.quantumSystems dimension) +
          RSA.Measured.Program.temporarySpace N (.quantumSystems dimension) =
            if dimension = 2 then qubitBound else 0
        rw [if_neg same]
        rw [RSA.Measured.Program.temporarySpace_quantum]
        simp only [RSA.Measured.Program.liveSpace, Pi.add_apply,
          RSA.Recycling.ClassicalFrame.rsaRecyclingFrame_frameSpace_eq,
          SpacePool.ofShape, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add,
          RSA.Measured.Program.readoutSpace, add_zero]
        change (MAU.Multiplication.Gidney.Measured.Physical.qubits
          (arithmeticBits N)).toQuantumLayout.dimensionCount dimension = 0
        rw [QubitLayout.toQuantumLayout_dimensionCount, if_neg (Ne.symm same)]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every actual four-batch path obeys the fixed resident classical capacity. -/
lemma rsaMeasured2048_run_resident_classicalBits_le (model : NativeRSA2048.FixedWidthModel N)
    (input : Input N)
    (path : (RSA.Measured.Program.run base noQuantum N input
      RSA.Configuration.rsa2048Batches).code.Path) :
    (RSA.Measured.Program.run base noQuantum N input
      RSA.Configuration.rsa2048Batches).code.peakResidentSpace
      path .classicalBits ≤ base.residentSpace .classicalBits + classicalBitBound := by
  simpa only [rsaMeasured2048_model_classicalBitBound_eq model] using
    RSA.Measured.Program.rsaMeasuredParent_run_resident_classicalBits_le
      base noQuantum input RSA.Configuration.rsa2048Batches path

/-- Auxiliary storage has its own caller contribution and the same independent allowance. -/
lemma rsaMeasured2048_run_auxiliary_classicalBits_le (model : NativeRSA2048.FixedWidthModel N)
    (input : Input N)
    (path : (RSA.Measured.Program.run base noQuantum N input
      RSA.Configuration.rsa2048Batches).code.Path) :
    (RSA.Measured.Program.run base noQuantum N input
      RSA.Configuration.rsa2048Batches).code.peakAuxiliarySpace
      path .classicalBits ≤ base.auxiliarySpace .classicalBits + classicalBitBound := by
  simpa only [rsaMeasured2048_model_classicalBitBound_eq model] using
    RSA.Measured.Program.rsaMeasuredParent_run_auxiliary_classicalBits_le
      base noQuantum input RSA.Configuration.rsa2048Batches path

/-- The same actual path uses at most 4,100 added qubits for every original fixed-width key. -/
lemma rsaMeasured2048_run_resident_qubits_le (model : NativeRSA2048.FixedWidthModel N) (input :
    Input N)
    (path : (RSA.Measured.Program.run base noQuantum N input
      RSA.Configuration.rsa2048Batches).code.Path) :
    (RSA.Measured.Program.run base noQuantum N input
      RSA.Configuration.rsa2048Batches).code.peakResidentSpace
      path (.quantumSystems 2) ≤ base.residentSpace (.quantumSystems 2) + qubitBound := by
  simpa only [rsaMeasured2048_model_qubitBound_eq model] using
    RSA.Measured.Program.rsaMeasuredParent_run_resident_qubits_le
      base noQuantum input RSA.Configuration.rsa2048Batches path

end

end QuantumAlg.Factoring.RSA2048.Measured
