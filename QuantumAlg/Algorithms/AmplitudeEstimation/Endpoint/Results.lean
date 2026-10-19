/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.AmplitudeEstimation.Endpoint
import all QuantumAlg.Algorithms.AmplitudeEstimation.Endpoint
import all QuantumAlg.Algorithms.AmplitudeEstimation.Endpoint.Execution

public import QuantumAlg.Algorithms.AmplitudeEstimation.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Components.Oracle.AmplitudeAmplification
public import QuantumAlg.Core.Base.Accounting.Weighted
public import Mathlib.Data.Nat.Choose.Basic
public import QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Distribution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Restoration
import all QuantumAlg.Algorithms.AmplitudeEstimation.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Space
import all QuantumAlg.Algorithms.AmplitudeEstimation.Specification
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.Real.PeriodicSinSq

/-!
# Complete native prepared-state amplitude estimation

The original source model and selected precision determine one actual
prepare, source-query, Z-write, and packing circuit. Complete Output retains
all of its phase/source systems and classical cells. Its own block masses
prove the original additive-error guarantee for every external reference,
while its actual paths satisfy independent native resource and depth bounds.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The complete estimation contract uses the original real failure target. -/
public lemma aeProblem_successLB_value {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η) (environment : (model n).Environment) :
    ((problem n eps η nonnegative).successLB environment E).value = ENNReal.ofReal (1 - η) := by
  rfl

/-- The runtime input admits the original precision and failure domain. -/
public lemma problem_valid_iff {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η) (environment : (model n).Environment)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem n eps η nonnegative).valid environment E state ↔
      environment.quantum = AmplitudeAmplificationSource.interpretation
        E.source.preparation E.source.good true true ∧ 0 < eps ∧ eps ≤ 1 ∧ 0 < η ∧ η ≤ 1 := Iff.rfl

/-- The returned phase bits obey precisely the original sine-squared additive-error test. -/
public lemma problem_accepts_bits_iff {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η) (environment : (model n).Environment)
    (initial : Execution.Store pre)
    (outcome : Fin (selectedPhaseQubits eps η) → Bool) :
    (problem n eps η nonnegative).accepts environment E initial (.bits outcome) ↔
      |Real.sin (Real.pi *
        ((TerminalZMeasure.fullRegisterIndex outcome).val /
          (2 : Real) ^ selectedPhaseQubits eps η)) ^ 2 - targetProbability E.source| ≤ eps :=
  Iff.rfl

/-- All native gates are actual elementary occurrences, including the exact controlled S0 sign. -/
public lemma algorithm_gateCount (n : Nat)
    (eps η : Real) (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((algorithm n eps η).run.code.resourcePool path) =
      2 * selectedPhaseQubits eps η +
        (2 ^ selectedPhaseQubits eps η - 1) * ZeroReflection.controlledElementaryGateCount n +
        5 * (selectedPhaseQubits eps η).choose 2 + 3 * (selectedPhaseQubits eps η / 2) :=
  code_gateCount n (selectedPhaseQubits eps η) path

/-- The complete AE run's exact native single-qubit gate multiplicity. -/
public lemma aeAlgorithm_singleQubitCount (n : Nat)
    (eps η : Real) (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .singleQubit)
      ((algorithm n eps η).run.code.resourcePool path) =
        2 * selectedPhaseQubits eps η +
          (2 ^ selectedPhaseQubits eps η - 1) *
            ZeroReflection.controlledElementarySingleQubitCount n +
          3 * (selectedPhaseQubits eps η).choose 2 :=
  aeCode_singleQubitCount n (selectedPhaseQubits eps η) path

/-- The complete AE run's exact native CNOT gate multiplicity. -/
public lemma aeAlgorithm_cnotCount (n : Nat)
    (eps η : Real) (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .cnot)
      ((algorithm n eps η).run.code.resourcePool path) =
        (2 ^ selectedPhaseQubits eps η - 1) *
            ZeroReflection.controlledElementaryCNOTCount n +
          2 * (selectedPhaseQubits eps η).choose 2 +
          3 * (selectedPhaseQubits eps η / 2) :=
  aeCode_cnotCount n (selectedPhaseQubits eps η) path

/-- The complete AE run's exact native Toffoli gate multiplicity. -/
public lemma aeAlgorithm_toffoliCount (n : Nat)
    (eps η : Real) (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .toffoli)
      ((algorithm n eps η).run.code.resourcePool path) =
        (2 ^ selectedPhaseQubits eps η - 1) *
          ZeroReflection.controlledElementaryToffoliCount n :=
  aeCode_toffoliCount n (selectedPhaseQubits eps η) path

/-- Actual ordinary U calls include the initial preparation before all ladder repetitions. -/
public lemma algorithm_preparationCount (n : Nat)
    (eps η : Real) (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n) (.oracle .preparation)
      ((algorithm n eps η).run.code.resourcePool path) =
        (2 ^ selectedPhaseQubits eps η - 1) + 1 :=
  code_preparationCount n (selectedPhaseQubits eps η) path

/-- Actual U-dagger calls remain ordinary inverse queries in every controlled ladder repetition. -/
public lemma algorithm_inversePreparationCount (n : Nat)
    (eps η : Real) (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n) (.oracle .inversePreparation)
      ((algorithm n eps η).run.code.resourcePool path) =
        2 ^ selectedPhaseQubits eps η - 1 :=
  code_inversePreparationCount n (selectedPhaseQubits eps η) path

/-- Each actual ladder repetition uses the declared controlled good-state reflection once. -/
public lemma algorithm_controlledGoodReflectionCount (n : Nat) (eps η : Real)
    (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n) (.oracle .controlledGoodReflection)
      ((algorithm n eps η).run.code.resourcePool path) =
        2 ^ selectedPhaseQubits eps η - 1 :=
  code_controlledGoodReflectionCount n (selectedPhaseQubits eps η) path

/-- The complete execution measures each selected phase wire exactly once. -/
public lemma algorithm_measurementCount (n : Nat) (eps η : Real)
    (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n) (.measurement (2 : ℕ+))
      ((algorithm n eps η).run.code.resourcePool path) =
        selectedPhaseQubits eps η :=
  code_measurementCount n (selectedPhaseQubits eps η) path

/-- The measured phase bits are packed by one actual classical operation. -/
public lemma algorithm_packCount (n : Nat) (eps η : Real)
    (path : (algorithm n eps η).run.code.Path) :
    ResourcePool.count (model := model n)
      (.classicalOperation (.nominalEncoding (.packFiniteBits (selectedPhaseQubits eps η))))
      ((algorithm n eps η).run.code.resourcePool path) = 1 :=
  code_packCount n (selectedPhaseQubits eps η) path

/-- Admitted precision and failure parameters use no qubits beyond source and phase registers. -/
public lemma aeAlgorithm_quantumSpace (n : Nat)
    {eps η : Real} (heps : 0 < eps) (heps_le : eps ≤ 1)
    (heta : 0 < η) (heta_le : η ≤ 1)
    (path : (algorithm n eps η).run.code.Path) :
    (algorithm n eps η).run.code.peakResidentSpace path (.quantumSystems 2) ≤
        n + ⌈Real.logb 2 (Real.pi / (eps * η))⌉₊ ∧
      (algorithm n eps η).run.code.peakAuxiliarySpace path (.quantumSystems 2) ≤
        n + ⌈Real.logb 2 (Real.pi / (eps * η))⌉₊ := by
  have resident := code_residentSpace n (selectedPhaseQubits eps η) path (.quantumSystems 2)
  have auxiliary := code_auxiliarySpace n (selectedPhaseQubits eps η) path (.quantumSystems 2)
  have empty := Elementary.selected_helperWidth_eq_zero n heps heps_le heta heta_le
  have budget : spaceBudget (selectedPhaseQubits eps η) n (.quantumSystems 2) =
      n + ⌈Real.logb 2 (Real.pi / (eps * η))⌉₊ := by
    change selectedPhaseQubits eps η +
      (Elementary.helperWidth (selectedPhaseQubits eps η) n + n) = _
    rw [empty, Nat.zero_add, selectedPhaseQubits_eq_logCeiling heps heta]
    exact Nat.add_comm _ _
  exact ⟨resident.trans_eq budget, auxiliary.trans_eq budget⟩

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public lemma algorithm_solves (n : Nat)
    (eps η : Real) (nonnegative : 0 ≤ η) :
    Algorithm.Solves (algorithm n eps η) (problem n eps η nonnegative) :=
  complete_correct n eps η nonnegative

/-- The public run retains every actual phase, source, work and classical output cell. -/
public lemma algorithm_output_listing (n : Nat) (eps η : Real) :
    (algorithm n eps η).run.output.listing =
      (post (selectedPhaseQubits eps η) n).keys :=
  run_output_listing n (selectedPhaseQubits eps η)

end

end QuantumAlg.AmplitudeEstimation
