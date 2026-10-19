/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA2048
public import QuantumAlg.Algorithms.Factoring.RSA.Results
public import QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.KeyAverage
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted

import all QuantumAlg.Algorithms.Factoring.RSA2048
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Calibration
import all QuantumAlg.Algorithms.Factoring.RSA.Results
import all QuantumAlg.Algorithms.Factoring.RSA2048.Recycling.Contract
import all QuantumAlg.Algorithms.Factoring.RSA2048.Recycling.Resources
import all QuantumAlg.Algorithms.Factoring.RSA2048.Recycling.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Endpoint
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.KeyAverage
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Util.RSA.GeneratorOrder
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Execution.Trace
import Mathlib.Tactic.NormNum

/-!
# Same-run single-control RSA-2048 resources and ordered-key success

The actual modulus-only algorithm executes seven batches and 112 measured
members on one recycled control and the original arithmetic bank. Its entire
native event allowance includes preparation, paid packing, measured reset,
reload, complete recovery and final selection. Each resource theorem applies
to every original exact-width key, including exceptional keys.

The conditional complete contract and the original ordered-key average both
observe this same new execution. Key-dependent arbitrary caller states and
external references remain admitted. Averaging retains the per-key seventh
failure power. The fixed seven-batch guarantee is distinct from the generic
one-percent calibration, whose count is ten.

The reduction is [EH17, source.tex:878-966], and sampling and reconstruction
are [E23, arxiv-v5.tex:218-299,329-355]. Measured Fourier reuse is
[GN96, 9511007.tex:100-114,246-266]. Native resource ceilings are implementation
refinements of these mathematical constructions.
-/

namespace QuantumAlg.Factoring.RSA2048

open EkeraHastadStyle EkeraHastadStyle.Canonical

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Every original legal key supplies a specification witness for the same public program. -/
public def factorWitness {N : Nat} (key : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum N).Witness := key

/-- Every legal specification witness admits every normalized caller and interpretation. -/
public lemma source_valid {N : Nat} (key : NativeRSA2048.FixedKeyModel N)
    {Reference : Register}
    (original : Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    (problem base noQuantum N).valid environment (factorWitness base noQuantum key)
      original.caller.localState := by
  trivial

/-- The actual program prepares its own bank without an additional caller premise. -/
public lemma source_initialized {N : Nat} (key : NativeRSA2048.FixedKeyModel N)
    {Reference : Register}
    (original : Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    (problem base noQuantum N).initialization environment (factorWitness base noQuantum key)
      original.localState := by
  trivial

/-- The actual seven-batch candidate receives only the original public-modulus input. -/
@[expose] public def algorithm {N : Nat} (specification : Canonical.Input N) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (RSA.Recycling.Program.outputContext base noQuantum N NativeRSA2048.rounds)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  RSA.algorithmAtCount base noQuantum specification NativeRSA2048.rounds

/-- This named candidate satisfies the independent complete fixed-width problem. -/
public lemma algorithm_solves {N : Nat} (specification : Canonical.Input N) :
    Algorithm.Solves (algorithm base noQuantum specification)
      (problem base noQuantum N) :=
  complete_correct base noQuantum specification

/-- The original conditional seven-batch floor is itself at least ninety-nine percent. -/
public lemma problem_successLB_ge_99
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {N : Nat}
      (model : NativeRSA2048.FixedKeyModel N) :
    ENNReal.ofReal ((99 : Real) / 100) ≤ ((problem base noQuantum N).successLB environment
      (factorWitness base noQuantum model)).value :=
  Recycling.model_successFloor_ge_99 base noQuantum environment model

/-- Independent simultaneous space includes one recycled control and all retained classical data. -/
@[expose] public def additionalSpace : SpacePool .quantum
  | .classicalBits => 1_053_148_338_921
  | .quantumSystems dimension => if dimension = 2 then 4_097 else 0

/-- The resident budget exposes the fixed new classical allowance. -/
public lemma problem_resident_classicalBits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum N).resources.resident .classicalBits =
      base.residentSpace .classicalBits + 1_053_148_338_921 := by
  exact congrArg (fun bits => base.residentSpace .classicalBits + bits)
    ((RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_classicalBits N
      NativeRSA2048.rounds).trans (Recycling.model_classicalBitBound_eq model.widthModel))

/-- Auxiliary storage keeps its separate caller contribution and the same actual allowance. -/
public lemma problem_auxiliary_classicalBits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum N).resources.auxiliary .classicalBits =
      base.auxiliarySpace .classicalBits + 1_053_148_338_921 := by
  exact congrArg (fun bits => base.auxiliarySpace .classicalBits + bits)
    ((RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_classicalBits N
      NativeRSA2048.rounds).trans (Recycling.model_classicalBitBound_eq model.widthModel))

include noQuantum in
private lemma caller_qubits_zero : base.residentSpace (.quantumSystems 2) = 0 := by
  rw [RuntimeCtx.residentSpace_quantumSystems]
  simp only [QuantumLayout.dimensionCount, QuantumLayout.dimensions, RuntimeCtx.systemCount,
    noQuantum, List.length_nil, List.ofFn_zero, List.count_nil]

/-- With the required quantum-empty caller, the independent resident allowance is 4,097 qubits. -/
public lemma problem_resident_qubits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum N).resources.resident (.quantumSystems 2) = 4_097 := by
  have scalar : RSA.Recycling.Program.spaceLimit N NativeRSA2048.rounds
      (.quantumSystems 2) = 4_097 :=
    (RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_qubits N NativeRSA2048.rounds).trans
      (Recycling.model_qubitBound_eq model.widthModel)
  change base.residentSpace (.quantumSystems 2) +
    RSA.Recycling.Program.spaceLimit N NativeRSA2048.rounds (.quantumSystems 2) = _
  rw [scalar, caller_qubits_zero base noQuantum, Nat.zero_add]

/-- The auxiliary quantum budget retains its own caller contribution. -/
public lemma problem_auxiliary_qubits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum N).resources.auxiliary (.quantumSystems 2) =
      base.auxiliarySpace (.quantumSystems 2) + 4_097 := by
  exact congrArg (fun qubits => base.auxiliarySpace (.quantumSystems 2) + qubits)
    ((RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_qubits N NativeRSA2048.rounds).trans
      (Recycling.model_qubitBound_eq model.widthModel))

/-- The independent time formula is bounded by the fixed complete quantum-time ceiling. -/
public lemma problem_quantumTimeLimit {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum N).quantumTimeLimit ≤ 117_480_458_204_112_193 :=
  Recycling.model_quantumTimeLimit_le model.widthModel

/-- The total native-event allowance counts an independent parameter pool, not an actual trace. -/
public def eventCountBound (N : Nat) : Nat :=
  (RSA.Recycling.Program.eventBudget N NativeRSA2048.rounds).card

/-- Every complete actual path is bounded by that independent native-event cardinality. -/
public lemma algorithm_eventCount_le {N : Nat} (_model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) :
    ((algorithm base noQuantum specification).run.code.eventTrace path).length ≤
      eventCountBound N := by
  have bounded := Multiset.card_le_card
    (RSA.Recycling.Program.rsaRecyclingParent_run_pool_le
      base noQuantum N specification NativeRSA2048.rounds path)
  exact bounded

/-- Fixed ceilings for all native gate coordinates of the new complete program. -/
@[expose] public def gateCountBound : AlgorithmGate.Coordinate → Nat
  | .toffoli => 117_064_166_104_596_480
  | .cnot => 416_291_951_738_880
  | .singleQubit => 148_235_585

/-- The independent fixed problem specializes the same generic native resource allowances. -/
public lemma problem_gateCountLimit {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate coordinate) (problem base noQuantum N).resources.events ≤
        gateCountBound coordinate :=
  Recycling.model_gateCountLimit_le model coordinate

/-- Every native gate coordinate belongs to the same actual complete path. -/
public lemma algorithm_gateCount_le {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate coordinate) ((algorithm base noQuantum specification).run.code.resourcePool path) ≤
        gateCountBound coordinate :=
  Recycling.run_gateCount_le base noQuantum model specification path coordinate

/-- Quantum time covers preparation and every member, reset and reload of the complete run. -/
public lemma algorithm_quantumTime_le {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) :
    (algorithm base noQuantum specification).quantumTime path ≤ 117_480_458_204_112_193 :=
  Recycling.run_quantumTime_le base noQuantum model specification path

/-- Literal classical operations retain their independent fixed ceiling on the same path. -/
public lemma algorithm_classicalOperation_le {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm base noQuantum specification).run.code.resourcePool path) ≤
        15_343_042_058_108_937_824 :=
  Recycling.run_classicalOperation_le base noQuantum model specification path

/-- Independent complete space, quantum-time, native-event and classical-operation allowances. -/
@[expose] public def ResourceBounds {N : Nat} (specification : Canonical.Input N) : Prop :=
  ∀ path : (algorithm base noQuantum specification).run.code.Path,
    (algorithm base noQuantum specification).run.code.peakResidentSpace path ≤
        base.residentSpace + additionalSpace ∧
    (algorithm base noQuantum specification).run.code.peakAuxiliarySpace path ≤
        base.auxiliarySpace + additionalSpace ∧
    (algorithm base noQuantum specification).quantumTime path ≤ 117_480_458_204_112_193 ∧
    ((algorithm base noQuantum specification).run.code.eventTrace path).length ≤
        eventCountBound N ∧
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm base noQuantum specification).run.code.resourcePool path) ≤
        15_343_042_058_108_937_824

/-- Every original exact-width key, including exceptional keys, satisfies the same path bounds. -/
public lemma algorithm_resourceBounds {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N) : ResourceBounds base noQuantum specification := by
  intro path
  have space : RSA.Recycling.Program.spaceLimit N NativeRSA2048.rounds = additionalSpace :=
    Recycling.model_additionalSpace_eq model
  have resident := RSA.Recycling.Program.rsaRecyclingParent_run_resident_le
    base noQuantum N specification NativeRSA2048.rounds path
  have auxiliary := RSA.Recycling.Program.rsaRecyclingParent_run_auxiliary_le
    base noQuantum N specification NativeRSA2048.rounds path
  rw [space] at resident auxiliary
  exact ⟨resident, auxiliary, algorithm_quantumTime_le base noQuantum model specification path,
    algorithm_eventCount_le base noQuantum model specification path,
    algorithm_classicalOperation_le base noQuantum model specification path⟩

/-- Fixed independent ceilings retain the caller's resident and auxiliary classical capacities. -/
@[expose] public def coordinateLimits : RSA.CoordinateLimits where
  qubits := 4_097
  toffoli := 117_064_166_104_596_480
  cnot := 416_291_951_738_880
  singleQubit := 148_235_585
  quantumTime := 117_480_458_204_112_193
  residentClassicalBits := base.residentSpace .classicalBits + 1_053_148_338_921
  auxiliaryClassicalBits := base.auxiliarySpace .classicalBits + 1_053_148_338_921
  classicalOperations := 15_343_042_058_108_937_824

/-- The shared arbitrary-count observation contract specializes to the fixed seven batches. -/
public abbrev SevenCoordinateBounds {N : Nat} (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) : Prop :=
  RSA.SevenCoordinateBoundsAtCount base noQuantum specification NativeRSA2048.rounds
    (coordinateLimits base) path

/-- All seven coordinates constrain one actual path for every original fixed-width key. -/
public lemma algorithm_sevenCoordinates {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) :
    SevenCoordinateBounds base noQuantum specification path := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · have actual := Recycling.run_resident_qubits_le base noQuantum model specification path
    rw [caller_qubits_zero base noQuantum, Nat.zero_add] at actual
    exact actual
  · exact algorithm_gateCount_le base noQuantum model specification path .toffoli
  · exact algorithm_gateCount_le base noQuantum model specification path .cnot
  · exact algorithm_gateCount_le base noQuantum model specification path .singleQubit
  · exact algorithm_quantumTime_le base noQuantum model specification path
  · exact Recycling.run_resident_classicalBits_le base noQuantum model specification path
  · exact Recycling.run_auxiliary_classicalBits_le base noQuantum model specification path
  · exact algorithm_classicalOperation_le base noQuantum model specification path

/-- With an empty caller, both complete classical capacities fit in 132 decimal gigabytes. -/
public lemma algorithm_classicalMemory_emptyBase_le_132GB {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) (specification : Canonical.Input N)
    (path : (algorithm (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires specification).run.code.Path) :
    (algorithm (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires specification).run.code.peakResidentSpace
        path .classicalBits ≤ 132 * 8 * 10 ^ 9 ∧
    (algorithm (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires specification).run.code.peakAuxiliarySpace
        path .classicalBits ≤ 132 * 8 * 10 ^ 9 := by
  rcases algorithm_sevenCoordinates (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires model specification path with
    ⟨_, _, _, _, _, ⟨resident, auxiliary⟩, _⟩
  constructor
  · calc
      _ ≤ (RuntimeCtx.empty : RuntimeCtx .quantum).residentSpace .classicalBits +
          1_053_148_338_921 := resident
      _ ≤ 132 * 8 * 10 ^ 9 := by norm_num [RuntimeCtx.residentSpace_empty]
  · calc
      _ ≤ (RuntimeCtx.empty : RuntimeCtx .quantum).auxiliarySpace .classicalBits +
          1_053_148_338_921 := auxiliary
      _ ≤ 132 * 8 * 10 ^ 9 := by norm_num [RuntimeCtx.auxiliarySpace_empty]

/-- Original ordered keys are followed by the actual new seven-batch run at each public modulus. -/
public def keygenOutput {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    PMF (Nat × Nat × Option Nat) :=
  RSA.Recycling.Program.KeyAverage.keygenOutputDistribution (environment := environment)
    base noQuantum NativeRSA2048.primeBits
    NativeRSA2048.keygenNonempty NativeRSA2048.rounds inputs

private lemma keygenOutput_eq {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    keygenOutput (environment := environment) base noQuantum inputs =
      RSA.Recycling.Program.KeyAverage.keygenOutputDistribution (environment := environment)
        base noQuantum
        NativeRSA2048.primeBits NativeRSA2048.keygenNonempty NativeRSA2048.rounds inputs := rfl

/-- The actual original-key average reaches ninety-nine percent for every input/reference family. -/
public lemma success_ge_99 {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      (keygenOutput (environment := environment) base noQuantum inputs).toOuterMeasure
        RSA.Recycling.Program.KeyAverage.successEvent := by
  have massEq (count : Nat) :
      RSA.Recycling.Program.KeyAverage.successMass (environment := environment)
        base noQuantum NativeRSA2048.primeBits
          NativeRSA2048.keygenNonempty count inputs =
        (RSA.Recycling.Program.KeyAverage.keygenOutputDistribution (environment := environment)
          base noQuantum
          NativeRSA2048.primeBits NativeRSA2048.keygenNonempty count inputs).toOuterMeasure
            RSA.Recycling.Program.KeyAverage.successEvent := by as_aux_lemma => rfl
  have effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤
      NativeRSA2048.primeBits := by
    norm_num [QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits, NativeRSA2048.primeBits]
  have averaged := RSA.Recycling.Program.KeyAverage.success_ge_rounds (environment := environment)
    base noQuantum NativeRSA2048.primeBits NativeRSA2048.keygenNonempty
      NativeRSA2048.rounds inputs effective
  have calibrated := NativeRSA2048.Calibration.combinedSuccess_seven_ge_99
  have bitsEq : (1024 : Nat) = NativeRSA2048.primeBits := rfl
  have roundsEq : (7 : Nat) = NativeRSA2048.rounds := rfl
  rw [bitsEq, roundsEq] at calibrated
  have lower := calibrated.trans averaged
  rw [keygenOutput_eq, ← massEq]
  exact lower

/-- The complete fixed-width key-average contract admits every normalized input/reference family. -/
@[expose] public def KeyGenerationSuccess : Prop :=
  ∀ (Reference : Register)
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput ClassicalOracleModel.empty base Reference),
      ENNReal.ofReal ((99 : Real) / 100) ≤
        (keygenOutput (environment := environment) base noQuantum inputs).toOuterMeasure
          RSA.Recycling.Program.KeyAverage.successEvent

/-- Fixed seven-batch success belongs to the actual new run throughout the original key average. -/
public lemma keyGenerationSuccess : KeyGenerationSuccess (environment := environment)
  base noQuantum :=
  fun _ inputs => success_ge_99 (environment := environment) base noQuantum inputs

/-- Every supported populated output is one of its own generated primes,
including exceptional keys. -/
public lemma keygenOutput_some_sound {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput ClassicalOracleModel.empty base Reference) {p q factor : Nat}
    (member : (p, q, some factor) ∈ (keygenOutput (environment := environment)
      base noQuantum inputs).support) :
    factor = p ∨ factor = q := by
  rw [keygenOutput, RSA.Recycling.Program.KeyAverage.keygenOutputDistribution,
    PMF.mem_support_bind_iff] at member
  rcases member with ⟨pair, _pairMember, outputMember⟩
  rw [PMF.mem_support_map_iff] at outputMember
  rcases outputMember with ⟨output, outputMember, outputEq⟩
  have leftEq : pair.p = p := congrArg Prod.fst outputEq
  have restEq : (pair.q, NativeRetrySelection.decodeFactor output) = (q, some factor) :=
    congrArg Prod.snd outputEq
  have rightEq : pair.q = q := congrArg Prod.fst restEq
  have factorEq : NativeRetrySelection.decodeFactor output = some factor :=
    congrArg Prod.snd restEq
  subst p
  subst q
  cases output with
  | optionNone => cases factorEq
  | optionSome word =>
      have valueEq : word.toNat = factor := Option.some.inj factorEq
      have sound := RSA.Recycling.Program.rsaRecyclingParent_run_some_sound
        base noQuantum (inputOfKeyPair pair) NativeRSA2048.rounds (inputs pair) word outputMember
      have declared := (semiprimeOfKeyPair pair).nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      rw [valueEq] at declared
      exact declared

end

end QuantumAlg.Factoring.RSA2048
