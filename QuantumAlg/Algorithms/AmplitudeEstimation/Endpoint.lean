/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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

/-- The runtime input admits the original precision and failure domain. -/
public theorem problem_valid_iff {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem E eps η nonnegative).valid state ↔
      0 < eps ∧ eps ≤ 1 ∧ 0 < η ∧ η ≤ 1 := Iff.rfl

/-- The returned phase bits obey precisely the original sine-squared additive-error test. -/
public theorem problem_accepts_bits_iff {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η) (initial : Execution.Store pre)
    (outcome : Fin (selectedPhaseQubits eps η) → Bool) :
    (problem E eps η nonnegative).accepts initial (.bits outcome) ↔
      |Real.sin (Real.pi *
        ((TerminalZMeasure.fullRegisterIndex outcome).val /
          (2 : Real) ^ selectedPhaseQubits eps η)) ^ 2 - targetProbability E.source| ≤ eps :=
  Iff.rfl

/-- The public selected-width execution, including actual preparation and complete live Output. -/
public def algorithm {n : Nat} (E : GeneralAmplitudeEstimationInput n) (eps η : Real) :
    Algorithm (model E) pre (post (selectedPhaseQubits eps η) n)
      (.bits (selectedPhaseQubits eps η)) where
  run := run E (selectedPhaseQubits eps η)

/-- All native gates are actual elementary occurrences, including the exact controlled S0 sign. -/
public theorem algorithm_gateCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((algorithm E eps η).run.code.resourcePool path) =
      2 * selectedPhaseQubits eps η +
        (2 ^ selectedPhaseQubits eps η - 1) * ZeroReflection.controlledElementaryGateCount n +
        5 * (selectedPhaseQubits eps η).choose 2 + 3 * (selectedPhaseQubits eps η / 2) :=
  code_gateCount E (selectedPhaseQubits eps η) path

/-- The complete AE run's exact native single-qubit gate multiplicity. -/
public theorem aeAlgorithm_singleQubitCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E) (.gate .singleQubit)
      ((algorithm E eps η).run.code.resourcePool path) =
        2 * selectedPhaseQubits eps η +
          (2 ^ selectedPhaseQubits eps η - 1) *
            ZeroReflection.controlledElementarySingleQubitCount n +
          3 * (selectedPhaseQubits eps η).choose 2 :=
  aeCode_singleQubitCount E (selectedPhaseQubits eps η) path

/-- The complete AE run's exact native CNOT gate multiplicity. -/
public theorem aeAlgorithm_cnotCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E) (.gate .cnot)
      ((algorithm E eps η).run.code.resourcePool path) =
        (2 ^ selectedPhaseQubits eps η - 1) *
            ZeroReflection.controlledElementaryCNOTCount n +
          2 * (selectedPhaseQubits eps η).choose 2 +
          3 * (selectedPhaseQubits eps η / 2) :=
  aeCode_cnotCount E (selectedPhaseQubits eps η) path

/-- The complete AE run's exact native Toffoli gate multiplicity. -/
public theorem aeAlgorithm_toffoliCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E) (.gate .toffoli)
      ((algorithm E eps η).run.code.resourcePool path) =
        (2 ^ selectedPhaseQubits eps η - 1) *
          ZeroReflection.controlledElementaryToffoliCount n :=
  aeCode_toffoliCount E (selectedPhaseQubits eps η) path

/-- Actual ordinary U calls include the initial preparation before all ladder repetitions. -/
public theorem algorithm_preparationCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E) (.oracle .preparation)
      ((algorithm E eps η).run.code.resourcePool path) =
        (2 ^ selectedPhaseQubits eps η - 1) + 1 :=
  code_preparationCount E (selectedPhaseQubits eps η) path

/-- Actual U-dagger calls remain ordinary inverse queries in every controlled ladder repetition. -/
public theorem algorithm_inversePreparationCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E) (.oracle .inversePreparation)
      ((algorithm E eps η).run.code.resourcePool path) =
        2 ^ selectedPhaseQubits eps η - 1 :=
  code_inversePreparationCount E (selectedPhaseQubits eps η) path

/-- Each actual ladder repetition uses the declared controlled good-state reflection once. -/
public theorem algorithm_controlledGoodReflectionCount {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (eps η : Real)
    (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E) (.oracle .controlledGoodReflection)
      ((algorithm E eps η).run.code.resourcePool path) =
        2 ^ selectedPhaseQubits eps η - 1 :=
  code_controlledGoodReflectionCount E (selectedPhaseQubits eps η) path

/-- The complete execution measures each selected phase wire exactly once. -/
public theorem algorithm_measurementCount {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (eps η : Real)
    (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E) (.measurement (2 : ℕ+))
      ((algorithm E eps η).run.code.resourcePool path) =
        selectedPhaseQubits eps η :=
  code_measurementCount E (selectedPhaseQubits eps η) path

/-- The measured phase bits are packed by one actual classical operation. -/
public theorem algorithm_packCount {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (eps η : Real)
    (path : (algorithm E eps η).run.code.Path) :
    ResourcePool.count (model := model E)
      (.classicalOperation (.nominalEncoding (.packFiniteBits (selectedPhaseQubits eps η))))
      ((algorithm E eps η).run.code.resourcePool path) = 1 :=
  code_packCount E (selectedPhaseQubits eps η) path

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public theorem algorithm_solves {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η) :
    Algorithm.Solves (algorithm E eps η) (problem E eps η nonnegative) := by
  constructor
  · intro Reference input promised _initialized
    exact actual_success E eps η
      (selectedPhaseQubits_pos promised.1 promised.2.1 promised.2.2.1 promised.2.2.2)
      promised.1 promised.2.1 promised.2.2.1 promised.2.2.2 input
  · intro _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _promised _initialized
    have restored := code_borrowedRestored E (selectedPhaseQubits eps η)
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code E (selectedPhaseQubits eps η)).BorrowedRestored _ input.state
      ((code E (selectedPhaseQubits eps η)).execute _
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed _)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events E (selectedPhaseQubits eps η) path)
  · intro _Reference _input _promised _initialized path _supported
    exact code_residentSpace E (selectedPhaseQubits eps η) path
  · intro _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace E (selectedPhaseQubits eps η) path
  · intro _Reference _input _promised _initialized path _supported
    exact code_depth E (selectedPhaseQubits eps η) path


/-- The original prepared-state amplitude-estimation problem is solved by the actual native
execution, with complete storage, joint reference preservation, and independent budgets. -/
public theorem main {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η) :
    ∃ candidate : Algorithm (model E) pre (post (selectedPhaseQubits eps η) n)
        (.bits (selectedPhaseQubits eps η)),
      Algorithm.Solves candidate (problem E eps η nonnegative) :=
  ⟨algorithm E eps η, algorithm_solves E eps η nonnegative⟩

end

end QuantumAlg.AmplitudeEstimation
