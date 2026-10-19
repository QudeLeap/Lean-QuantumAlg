/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Execution

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Cycle
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Ambient
public import QuantumAlg.Util.Real.LogCeiling
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Cycle
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Encoding
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Scalar
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun

import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Preservation

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Specification
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Scalar
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Bounds
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Resources
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale
import all QuantumAlg.Components.Classical.ConstantWord.Trace
import all QuantumAlg.Components.Classical.Word.Split.Resources
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Depth
import all QuantumAlg.Components.Classical.Modular.Reduce.Native.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Selection.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Bounds
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Classification
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Magnitude
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Finalization
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Correction.Resources
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Depth

/-!
# Finite-cyclic discrete logarithms with one actual binary quantum bank

The complete execution uses the minimal binary group representation, retains
its classical samples and physically resets the reused bank after every sample.
All displayed native resources and complete-run quantum-time bounds belong
to this same execution, including every positive order and arbitrary external
references [Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- All original source witnesses and input states satisfy the new environment boundary. -/
public lemma binaryEndpoint_problem_source_valid (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P)
    (state : ExecutionState (Execution.Store Reusable.pre) Reusable.pre.register) :
    (problem P).valid (Reusable.sourceEnvironment P) secret state := rfl


/-- The independent endpoint contract exposes its acceptance relation without
making the complete specification structure reducible to every consumer. -/
public lemma binaryEndpoint_problem_accepts (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) (initial : Execution.Store Reusable.pre)
    (output : CShape.Value (.option (.unsignedWord (OrderPreparation.width P)))) :
    (problem P).accepts environment secret initial output = accepts secret initial output := rfl

/-- The endpoint contract uses the fixed source success threshold. -/
public lemma binaryEndpoint_problem_success_value (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) :
    ((problem P).successLB environment secret).value = ENNReal.ofReal ((2 : Real) / 3) := rfl

/-- No separate final-state promise is needed beyond success and borrowed restoration. -/
public lemma binaryEndpoint_problem_states (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) : (problem P).states environment secret = [] := rfl

/-- The endpoint event limit is the independently stated complete-run budget. -/
public lemma binaryEndpoint_problem_event_budget (P : KnownOrderProblem G) :
    (problem P).resources.events = eventBudget P := rfl

/-- The endpoint resident-space limit is the independently stated complete-run budget. -/
public lemma binaryEndpoint_problem_resident_budget (P : KnownOrderProblem G) :
    (problem P).resources.resident = residentBudget P := rfl

/-- The endpoint auxiliary-space limit is the independently stated complete-run budget. -/
public lemma binaryEndpoint_problem_auxiliary_budget (P : KnownOrderProblem G) :
    (problem P).resources.auxiliary = auxiliaryBudget P := rfl

/-- The endpoint quantum-time limit is the independent complete-run unit-event allowance. -/
public lemma binaryEndpoint_problem_quantumTimeLimit (P : KnownOrderProblem G) :
    (problem P).quantumTimeLimit = quantumTimeLimit P := rfl

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The complete execution solves the independent all-order contract. -/
public lemma binaryEndpoint_algorithm_solves (P : KnownOrderProblem G) :
    Algorithm.Solves (algorithm P) (problem P) :=
  complete_correct P

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
/-- The exact implemented binary widths are the real logarithmic ceilings. -/
public lemma binaryEndpoint_widths_eq_logCeil (P : KnownOrderProblem G) :
    Binary.groupWidth P = ⌈Real.logb 2 (P.order : Real)⌉₊ ∧
      OrderPreparation.width P = ⌈Real.logb 2 (12 * (P.order : Real))⌉₊ := by
  constructor
  · have positive : (0 : Real) < P.order := by exact_mod_cast P.order_pos
    simpa only [Binary.groupWidth, Nat.ceil_natCast, Nat.cast_ofNat] using
      RealLog.clog_ceil_eq_natCeil_logb (by norm_num : 1 < 2) positive
  · have positive : (0 : Real) < (12 * P.order : Nat) := by
      exact_mod_cast Nat.mul_pos (by norm_num : 0 < 12) P.order_pos
    have exactWidth :=
      RealLog.clog_ceil_eq_natCeil_logb (by norm_num : 1 < 2) positive
    rw [Nat.ceil_natCast] at exactWidth
    simpa only [OrderPreparation.width, orderWidth, oversampledOrder,
      fourierOversamplingFactor, Nat.cast_mul, Nat.cast_ofNat] using exactWidth

/-- Actual complete-run quantum time is bounded by the independent unit-event
allowance, which also counts preparation, measurement and classical work. -/
public lemma binaryEndpoint_quantumTime_le (P : KnownOrderProblem G)
    (path : (algorithm P).run.code.Path) :
    (algorithm P).quantumTime path ≤ quantumTimeLimit P :=
  (Circuit.quantumTime_le_unitDepth _ _).trans (binaryEndpoint_code_depth_le P path)

/-- All displayed coordinates constrain one actual path of the full solver. -/
@[expose] public def BinaryResourceBounds (P : KnownOrderProblem G)
    (path : (algorithm P).run.code.Path) : Prop :=
  SpacePool.count (.quantumSystems 2) ((algorithm P).run.code.peakResidentSpace path) ≤
      2 * OrderPreparation.width P + Binary.groupWidth P ∧
    ResourcePool.count (model := Reusable.model P) (.oracle .ux)
      ((algorithm P).run.code.resourcePool path) ≤ sampleCount P ∧
    ResourcePool.count (model := Reusable.model P) (.gate .cnot)
      ((algorithm P).run.code.resourcePool path) ≤ sampleCount P *
        (2 * (OrderPreparation.width P) ^ 2 + 4 * OrderPreparation.width P +
          6 * (OrderPreparation.width P / 2)) ∧
    ResourcePool.count (model := Reusable.model P) (.gate .singleQubit)
      ((algorithm P).run.code.resourcePool path) ≤ sampleCount P *
        (3 * (OrderPreparation.width P) ^ 2 + 23 * OrderPreparation.width P +
          Binary.groupWidth P) ∧
    (algorithm P).quantumTime path ≤ quantumTimeLimit P ∧
    ResourcePool.count
      (OrderRecovery.Native.groupOperationEvent (oracles := Binary.Oracle.model P) P)
      ((algorithm P).run.code.resourcePool path) ≤
        2 * sampleCount P * OrderPreparation.width P

/-- The complete actual output distribution returns the bounded logarithm word
with probability at least two thirds for every empty-interface input. -/
public lemma binaryEndpoint_output_probability (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (algorithm P).outputDistribution (Reusable.sourceEnvironment P) input
        (.optionSome (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  change _ ≤ (run P).outputDistribution (Reusable.sourceEnvironment P) input _
  exact binaryEndpoint_run_success P secret input


/-- Correctness, reference-aware execution contracts and every displayed native
resource bound hold for the same solver and the same complete execution.
The secret occurs only in the mathematical specification, never in the code. -/
public lemma binaryEndpoint_completeContract (P : KnownOrderProblem G) :
    Algorithm.Solves (algorithm P) (problem P) ∧
      Binary.groupWidth P = ⌈Real.logb 2 (P.order : Real)⌉₊ ∧
      OrderPreparation.width P = ⌈Real.logb 2 (12 * (P.order : Real))⌉₊ ∧
      sampleCount P = Nat.ceil
        (Real.log ((1 : Real) / 3) /
          Real.log (1 - ((P.order : Real) * Nat.totient P.order) /
            2 ^ (2 * OrderPreparation.width P + 2))) ∧
      ∀ path, BinaryResourceBounds P path := by
  obtain ⟨groupWidth, exponentWidth⟩ := binaryEndpoint_widths_eq_logCeil P
  refine ⟨binaryEndpoint_algorithm_solves P, groupWidth, exponentWidth,
    Binary.sampleCount_eq_closedForm P, ?_⟩
  intro path
  obtain ⟨cnot, single, queries⟩ := code_nativeCounts_le_width P path
  exact ⟨code_qubits_le P path, queries, cnot, single,
    binaryEndpoint_quantumTime_le P path, code_groupOperations_le_width P path⟩
end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

/-! Closed complete-run time ceilings for the independent problem.
The unit-event allowance conservatively bounds canonical quantum time. -/

open ClassicalRoutines
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
open ClassicalRoutines.NumberTheory.Checked.Native
open ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
open ClassicalRoutines.NumberTheory.XGCD.Native
open ClassicalRoutines.Modular.NativePower
open QuantumAlg.FiniteCyclicDLP

private lemma loader_unit_le {model : ExecutionModel} [BitWord.Selected model]
    (width : Nat) (bits : List Bool) :
    ((ConstantWord.loaderTrace model width bits).map (fun _ => 1)).sum ≤ 2 * bits.length := by
  induction bits with
  | nil => simp [ConstantWord.loaderTrace]
  | cons bit bits ih =>
      cases bit <;> simp_all [ConstantWord.loaderTrace, Nat.mul_add] <;> omega

private lemma preparation_unit_le {model : ExecutionModel} [BitWord.Selected model]
    {width : Nat} (spec : ClassicalAlgorithms.Modular.ModulusSpec width) :
    preparationDepthLimit (model := model) spec (fun _ => 1) ≤ 8 * width + 15 := by
  have load := loader_unit_le (model := model) (width + 1)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))
  simp only [List.length_ofFn] at load
  simp only [preparationDepthLimit, Word.Split.splitTrace, Word.Split.shiftTrace,
    preparationSeedEvents, Word.PowerOfTwo.shiftTrace, scaleBodyEvents,
    List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, List.map_replicate, List.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one, max_self]
  omega

private lemma inverse_unit_le {model : ExecutionModel} [BitWord.Selected model]
    {width : Nat} (spec : ClassicalAlgorithms.Modular.ModulusSpec width) :
    checkedInverseDepthLimit (model := model) spec (fun _ => 1) ≤ 30 * width + 70 := by
  have load := loader_unit_le (model := model) (width + 1)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))
  simp only [List.length_ofFn] at load
  rw [checkedInverseDepthLimit, xgcdNativeRawDepthLimit_unit]
  simp only [checkedSelectionDepthLimit, checkedDecisionEvents, signedReductionDepthLimit,
    signClassificationEvents, signedMagnitudeEvents, finalCorrectionEvents,
    negativeCorrectionEvents, ClassicalRoutines.Modular.Reduce.Native.reductionEvents,
    List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, if_true]
  norm_num at *
  omega

private lemma exposure_unit_le {model : ExecutionModel} [BitWord.Selected model]
    {width : Nat} (spec : ClassicalAlgorithms.Modular.ModulusSpec width) :
    singleExposureDepthLimit (model := model) spec (fun _ => 1) ≤ 38 * width + 96 := by
  have prepared := preparation_unit_le (model := model) spec
  have inverted := inverse_unit_le (model := model) spec
  simp only [singleExposureDepthLimit, checkedExposureDepthLimit, selectedExposureDepthLimit,
    multiplyDepth, exposureCopyEvents, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

universe u
variable {G : Type u} [Group G] [Fintype G]

private lemma attempt_unit_le (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P)) :
    QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native.attemptDepthLimit
      (oracles := Binary.Oracle.model P) P spec
      (fun _ => 1) ≤ 40 * OrderPreparation.width P + 100 := by
  have raw := exposure_unit_le
    (model := QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native.recoveryModel P
      (Binary.Oracle.model P)) spec
  simp only [QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native.attemptDepthLimit,
    QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native.acceptanceEvents,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private lemma recovery_unit_le (P : KnownOrderProblem G) :
    BinaryEndpoint.recoveryDepthLimit P (fun _ => 1) ≤
      BinaryEndpoint.sampleCount P * (40 * OrderPreparation.width P + 104) + 2 := by
  unfold BinaryEndpoint.recoveryDepthLimit
  split_ifs with trivial
  · change 1 + 1 ≤ _
    omega
  · have one := attempt_unit_le P (BinaryEndpoint.recoverySpec P trivial)
    change BinaryEndpoint.sampleCount P *
      (QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native.attemptDepthLimit
        (oracles := Binary.Oracle.model P) P (BinaryEndpoint.recoverySpec P trivial)
        (fun _ => 1) + 4) + 1 ≤ _
    have bound : QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native.attemptDepthLimit
        (oracles := Binary.Oracle.model P) P (BinaryEndpoint.recoverySpec P trivial)
        (fun _ => 1) + 4 ≤ 40 * OrderPreparation.width P + 104 := by omega
    have multiplied := Nat.mul_le_mul_left (BinaryEndpoint.sampleCount P) bound
    omega

/-- A closed independent ceiling for complete-run quantum time. -/
@[expose] public def binaryEndpointQuantumTimeCeiling (n t count : Nat) : Nat :=
  3 + count * (5 * t.choose 2 + 57 * t + 2 * n + 109)

/-- This bounds the existing independent time limit for every positive group order,
including the explicit order-one branch. No new condition on count is introduced. -/
public lemma binaryEndpoint_problem_quantumTimeLimit_le (P : KnownOrderProblem G) :
    (BinaryEndpoint.problem P).quantumTimeLimit ≤
      binaryEndpointQuantumTimeCeiling (Binary.groupWidth P) (OrderPreparation.width P)
        (BinaryEndpoint.sampleCount P) := by
  have prepared := (OrderPreparation.orderPreparation_scalarBounds P
    (OrderExecution.canonicalExpansion P)).2.2
  have recovered := recovery_unit_le P
  have round : Reusable.roundUnitDepth P (OrderExecution.canonicalExpansion P) ≤
      5 * (OrderPreparation.width P).choose 2 + 17 * OrderPreparation.width P +
        2 * Binary.groupWidth P + 5 := by
    simp only [Reusable.roundUnitDepth, Reusable.bankWidth, Reusable.sampleWidth]
    split_ifs <;> omega
  have repeated := Nat.mul_le_mul_left (BinaryEndpoint.sampleCount P) round
  change 1 + BinaryEndpoint.sampleCount P *
    Reusable.roundUnitDepth P (OrderExecution.canonicalExpansion P) +
      BinaryEndpoint.recoveryDepthLimit P (fun _ => 1) ≤ _
  unfold binaryEndpointQuantumTimeCeiling
  nlinarith

/-- The zero-round ceiling retains the original prefix allowance. -/
public lemma binaryEndpointQuantumTimeCeiling_zero_count (n t : Nat) :
    binaryEndpointQuantumTimeCeiling n t 0 = 3 := by
  simp [binaryEndpointQuantumTimeCeiling]

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
