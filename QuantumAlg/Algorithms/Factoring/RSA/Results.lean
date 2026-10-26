/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA
public import QuantumAlg.Algorithms.Factoring.RSA.ScalarBounds
import all QuantumAlg.Algorithms.Factoring.RSA

public import QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events.Comparison
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events.General
public import QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.KeyAverage
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted

import all QuantumAlg.Algorithms.Factoring.RSA.ScalarBounds
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.KeyAverage
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Context
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Endpoint
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.QuantumTime
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

/-!
# Same-run RSA coordinates and ordered-key guarantees

The implementation receives the public modulus and real failure target.
The factors, same-width encoding and original exceptional-key condition are
proof-side data. Each batch executes the actual residue sampler, configured
compiled arithmetic members and complete lattice recovery. Later batches
reuse the measured quantum bank; actual retained selection returns the first
factor. Separate theorems establish the complete conditional execution contract and
the original eventual guarantee over uniform ordered keys.

The RSA reduction is [EH17, source.tex:878-966]. The quantum construction
and measurement law are [E23, arxiv-v5.tex:218-299]; lattice post-processing
starts at [E23, arxiv-v5.tex:329-355]. The compiled native event and storage
bounds are proved implementation refinements of this mathematical route.
-/

namespace QuantumAlg.Factoring.RSA

open EkeraHastadStyle EkeraHastadStyle.Canonical ShortDLP.CompiledMAU

noncomputable section

variable [configuration : Configuration]

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Every original legal key supplies a specification witness for the same public program. -/
public def factorWitness {N : Nat} (η : Real) (key : GoodKeyModel N) :
    (problem base noQuantum N η).Witness := key

/-- Every legal specification witness admits every normalized caller and interpretation. -/
public lemma source_valid {N : Nat} (η : Real) (key : GoodKeyModel N)
    {Reference : Register}
    (original : Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    (problem base noQuantum N η).valid environment (factorWitness base noQuantum η key)
      original.caller.localState := by
  trivial

/-- The actual program prepares its own bank without an additional caller premise. -/
public lemma source_initialized {N : Nat} (η : Real) (key : GoodKeyModel N)
    {Reference : Register}
    (original : Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    (problem base noQuantum N η).initialization environment (factorWitness base noQuantum η key)
      original.localState := by
  trivial

/-- The same actual algorithm at any specified finite batch count. -/
public def algorithmAtCount {N : Nat} (specification : Canonical.Input N) (count : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (Measured.Program.outputContext base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  Measured.Program.algorithm base noQuantum specification count

/-- Calibration specializes the same arbitrary-count algorithm on the original input. -/
@[expose] public def algorithm {N : Nat} (specification : Canonical.Input N)
    (η : Real) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (Measured.Program.outputContext base noQuantum N
        (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  algorithmAtCount base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount η)

/-- The named public candidate satisfies every state, probability and native resource gate. -/
public lemma algorithm_solves {N : Nat} (specification : Canonical.Input N)
    (η : Real) (etaPositive : 0 < η) (_etaLessOne : η < 1) :
    Algorithm.Solves (algorithm base noQuantum specification η)
      (problem base noQuantum N η) :=
  realTarget_solves base noQuantum specification η etaPositive

/-- The public resident classical budget exposes the independent finite-count scalar formula. -/
public lemma problem_resident_classicalBits (N : Nat)
    (η : Real) :
    (problem base noQuantum N η).resources.resident .classicalBits =
      base.residentSpace .classicalBits +
        classicalBitBoundAtCount N
          (NativeFiniteRetry.Calibration.retryCount η) := by
  exact congrArg (fun bits => base.residentSpace .classicalBits + bits)
    (Measured.Program.rsaMeasuredParent_spaceLimit_classicalBits N
      (NativeFiniteRetry.Calibration.retryCount η))

/-- The public auxiliary classical budget retains the same independent temporary allowance. -/
public lemma problem_auxiliary_classicalBits (N : Nat)
    (η : Real) :
    (problem base noQuantum N η).resources.auxiliary .classicalBits =
      base.auxiliarySpace .classicalBits +
        classicalBitBoundAtCount N
          (NativeFiniteRetry.Calibration.retryCount η) := by
  exact congrArg (fun bits => base.auxiliarySpace .classicalBits + bits)
    (Measured.Program.rsaMeasuredParent_spaceLimit_classicalBits N
      (NativeFiniteRetry.Calibration.retryCount η))

/-- The public resident quantum budget charges one bank at every positive calibrated count. -/
public lemma problem_resident_qubits (N : Nat)
    (η : Real) :
    (problem base noQuantum N η).resources.resident (.quantumSystems 2) =
      base.residentSpace (.quantumSystems 2) +
        qubitBoundAtCount N (NativeFiniteRetry.Calibration.retryCount η) := by
  exact congrArg (fun qubits => base.residentSpace (.quantumSystems 2) + qubits)
    (Measured.Program.rsaMeasuredParent_spaceLimit_qubits N
      (NativeFiniteRetry.Calibration.retryCount η))

/-- The public auxiliary quantum coordinate is the same one-bank independent allowance. -/
public lemma problem_auxiliary_qubits (N : Nat)
    (η : Real) :
    (problem base noQuantum N η).resources.auxiliary (.quantumSystems 2) =
      base.auxiliarySpace (.quantumSystems 2) +
        qubitBoundAtCount N (NativeFiniteRetry.Calibration.retryCount η) := by
  exact congrArg (fun qubits => base.auxiliarySpace (.quantumSystems 2) + qubits)
    (Measured.Program.rsaMeasuredParent_spaceLimit_qubits N
      (NativeFiniteRetry.Calibration.retryCount η))

/-- Independent scalar ceilings for the seven observed resource coordinates.
Resident and auxiliary classical storage retain separate bounds. -/
public structure CoordinateLimits where
  /-- Peak resident two-level quantum systems, including the caller. -/
  qubits : Nat
  /-- Total Toffoli gates on the complete execution path. -/
  toffoli : Nat
  /-- Total CNOT gates on the complete execution path. -/
  cnot : Nat
  /-- Total single-qubit gates on the complete execution path. -/
  singleQubit : Nat
  /-- Quantum computation time of the complete actual execution. -/
  quantumTime : Nat
  /-- Peak resident classical bits, including the caller. -/
  residentClassicalBits : Nat
  /-- Peak auxiliary classical bits, including the caller. -/
  auxiliaryClassicalBits : Nat
  /-- Total literal classical operations on the complete execution path. -/
  classicalOperations : Nat

/-- The tight key-domain problem pool fits the independent full-input observation ceiling. -/
private lemma problem_eventBudget_le_general (N : Nat) (η : Real) :
    (problem base noQuantum N η).resources.events ≤
      Measured.Program.generalEventBudget N (NativeFiniteRetry.Calibration.retryCount η) :=
  Measured.Program.rsaMeasured_eventBudget_le_general N
    (NativeFiniteRetry.Calibration.retryCount η)

/-- General full-input ceilings, including the caller and even or small-width moduli.
The independent tight-key budgets remain the problem/scalar contract allowances. -/
public def coordinateLimitsAtCount (N count : Nat) : CoordinateLimits where
  qubits := base.residentSpace (.quantumSystems 2) + Measured.Program.qubitLimit N count
  toffoli := Measured.Program.generalGateCountLimit N count .toffoli
  cnot := Measured.Program.generalGateCountLimit N count .cnot
  singleQubit := Measured.Program.generalGateCountLimit N count .singleQubit
  quantumTime := Measured.Program.generalQuantumTimeLimit N count
  residentClassicalBits := base.residentSpace .classicalBits +
    Measured.Program.classicalBitLimit N count
  auxiliaryClassicalBits := base.auxiliarySpace .classicalBits +
    Measured.Program.classicalBitLimit N count
  classicalOperations := Measured.Program.generalClassicalOperationLimit N count

/-- Each tight problem gate allowance fits the corresponding full-input observation ceiling. -/
public lemma problem_gateCount_le_coordinateLimits (N : Nat) (η : Real)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate coordinate) (problem base noQuantum N η).resources.events ≤
      match coordinate with
      | .toffoli => (coordinateLimitsAtCount base N
          (NativeFiniteRetry.Calibration.retryCount η)).toffoli
      | .cnot => (coordinateLimitsAtCount base N
          (NativeFiniteRetry.Calibration.retryCount η)).cnot
      | .singleQubit => (coordinateLimitsAtCount base N
          (NativeFiniteRetry.Calibration.retryCount η)).singleQubit := by
  have bounded := ResourcePool.le_iff_count.mp
    (problem_eventBudget_le_general base noQuantum N η) (.gate coordinate)
  cases coordinate <;> exact bounded

/-- Seven bounds on one actual complete execution path.
Generic and fixed ceilings instantiate this same observation contract. -/
public structure SevenCoordinateBoundsAtCount {N : Nat}
    (specification : Canonical.Input N) (count : Nat)
    (limits : CoordinateLimits)
    (path : (algorithmAtCount base noQuantum specification count).run.code.Path) : Prop where
  qubits :
    (algorithmAtCount base noQuantum specification count).run.code.peakResidentSpace
      path (.quantumSystems 2) ≤
        limits.qubits
  toffoli :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .toffoli)
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.toffoli
  cnot :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .cnot)
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.cnot
  singleQubit :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .singleQubit)
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.singleQubit
  quantumTime :
    (algorithmAtCount base noQuantum specification count).quantumTime path ≤ limits.quantumTime
  classicalBits :
    ((algorithmAtCount base noQuantum specification count).run.code.peakResidentSpace
      path .classicalBits ≤ limits.residentClassicalBits) ∧
    (algorithmAtCount base noQuantum specification count).run.code.peakAuxiliarySpace
      path .classicalBits ≤ limits.auxiliaryClassicalBits
  classicalOperations :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.classicalOperations

/-- All original modulus inputs and all finite counts satisfy every coordinate. -/
public lemma algorithmAtCount_sevenCoordinates {N : Nat}
    (specification : Canonical.Input N) (count : Nat)
    (path : (algorithmAtCount base noQuantum specification count).run.code.Path) :
    SevenCoordinateBoundsAtCount base noQuantum specification count
      (coordinateLimitsAtCount base N count) path := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact Measured.Program.rsaMeasuredParent_run_resident_qubits_le
      base noQuantum specification count path
  · exact Measured.Program.rsaMeasuredGeneral_run_gateCount_le
      base noQuantum N specification count path .toffoli
  · exact Measured.Program.rsaMeasuredGeneral_run_gateCount_le
      base noQuantum N specification count path .cnot
  · exact Measured.Program.rsaMeasuredGeneral_run_gateCount_le
      base noQuantum N specification count path .singleQubit
  · exact Measured.Program.rsaMeasuredGeneral_run_quantumTime_le
      base noQuantum N specification count path
  · exact Measured.Program.rsaMeasuredParent_run_resident_classicalBits_le
      base noQuantum specification count path
  · exact Measured.Program.rsaMeasuredParent_run_auxiliary_classicalBits_le
      base noQuantum specification count path
  · exact Measured.Program.rsaMeasuredGeneral_run_classicalOperation_le
      base noQuantum N specification count path

/-- Calibration specializes the arbitrary-count contract without duplicating its fields. -/
public abbrev SevenCoordinateBounds {N : Nat} (specification : Canonical.Input N)
    (η : Real)
    (path : (algorithm base noQuantum specification η).run.code.Path) : Prop :=
  SevenCoordinateBoundsAtCount base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount η)
    (coordinateLimitsAtCount base N (NativeFiniteRetry.Calibration.retryCount η)) path

/-- Every path of the public finite RSA algorithm obeys the same seven bounds. -/
public lemma algorithm_sevenCoordinates {N : Nat} (specification : Canonical.Input N)
    (η : Real)
    (path : (algorithm base noQuantum specification η).run.code.Path) :
    SevenCoordinateBounds base noQuantum specification η path :=
  algorithmAtCount_sevenCoordinates base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount η) path

/-- Original ordered-key averaging observes the same actual single-control algorithm.
The input family admits arbitrary correlations between the key and the initial reference. -/
public def keygenOutput (bitWidth : Nat)
    (nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
    (η : Real) {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth →
      Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    PMF (Nat × Nat × Option Nat) :=
  Measured.Program.KeyAverage.keygenOutputDistribution (environment := environment)
    base noQuantum bitWidth nonempty
    (NativeFiniteRetry.Calibration.retryCount η) inputs

/-- The public average is the proved key average of the same new physical execution. -/
lemma keygenOutput_eq (bitWidth : Nat)
    (nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
    (η : Real) {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth →
      Execution.OracleInput ClassicalOracleModel.empty base Reference) :
    keygenOutput (environment := environment) base noQuantum bitWidth nonempty η inputs =
      Measured.Program.KeyAverage.keygenOutputDistribution (environment := environment)
        base noQuantum bitWidth nonempty
        (NativeFiniteRetry.Calibration.retryCount η) inputs := rfl

/-- The full target retains original ordered keys and the actual new public algorithm. -/
@[expose] public def AsymptoticKeygenSuccess (η : Real) : Prop :=
  ∀ᶠ bitWidth in Filter.atTop,
    ∀ nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth),
      QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
      ∀ (Reference : Register)
        (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth →
          Execution.OracleInput ClassicalOracleModel.empty base Reference),
        ENNReal.ofReal (1 - η) ≤
          (keygenOutput (environment := environment)
            base noQuantum bitWidth nonempty η inputs).toOuterMeasure
            Measured.Program.KeyAverage.successEvent

/-- The original eventual full target holds for the actual single-control key average. -/
public lemma asymptoticKeygenSuccess (η : Real)
    (etaPositive : 0 < η) (_etaLessOne : η < 1) :
    AsymptoticKeygenSuccess (environment := environment) base noQuantum η := by
  filter_upwards
    [Measured.Program.KeyAverage.rsaMeasuredKeyAverage_eventually_success_ge_target
      (environment := environment) base noQuantum η etaPositive] with bitWidth success
  intro nonempty effective Reference inputs
  rw [keygenOutput_eq]
  exact success nonempty effective Reference inputs

end

end QuantumAlg.Factoring.RSA
