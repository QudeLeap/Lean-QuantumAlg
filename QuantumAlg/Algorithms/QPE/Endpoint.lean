/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Specification
public import QuantumAlg.Algorithms.QPE.Construction
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Measure.Distribution
public import Mathlib.Analysis.Normed.Group.AddCircle
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.WindowProbability
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Distribution
import all QuantumAlg.Algorithms.QPE.Restoration
import all QuantumAlg.Algorithms.QPE.Resources
import all QuantumAlg.Algorithms.QPE.Space
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete native quantum phase estimation

The supplied borrowed eigenstate, internally prepared phase word, actual
controlled-power ladder, individual Z writes and stored bit packing belong
to one execution. Its own probabilities establish the original phase-window
bound, while complete Output and unconditional joint borrowed restoration
retain every live physical system and its reference correlations.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Public validity is exactly positive precision and the original local eigenstate matrix. -/
public theorem problem_valid_iff {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (state : ExecutionState (Execution.Store (pre t n)) (pre t n).register) :
    (problem P t).valid state ↔ 0 < t ∧
      ∀ row column, state.quantumMarginal.matrix row column =
        P.eigenstate (inputBasisEquiv t n row) *
          star (P.eigenstate (inputBasisEquiv t n column)) := Iff.rfl

/-- The actual stored bits are accepted precisely at the original circular phase precision. -/
public theorem problem_accepts_bits_iff {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (initial : Execution.Store (pre t n)) (outcome : Fin t → Bool) :
    (problem P t).accepts initial (.bits outcome) ↔
      ‖((P.phase - (TerminalZMeasure.fullRegisterIndex outcome).val / (2 : Real) ^ t : Real) :
        UnitAddCircle)‖ ≤ 1 / (2 : Real) ^ t := by
  change SuccessfulOutcome P t outcome ↔ _
  obtain ⟨index, rfl⟩ := (qpeOutcome_bijective t).surjective outcome
  rw [qpeOutcome_fullRegisterIndex]
  constructor
  · rintro ⟨other, same, close⟩
    have indices := qpeOutcome_injective t same
    subst other
    exact close
  · intro close
    exact ⟨index, rfl, close⟩

/-- The complete public execution prepares, measures and returns its actual retained phase bits. -/
public def algorithm {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    Algorithm (model P) (pre t n) (post t n) (.bits t) where
  run := run P t

/-- Every actual path contains exactly the controlled source calls of the power ladder. -/
public theorem algorithm_controlledUnitaryCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (algorithm P t).run.code.Path) :
    ResourcePool.count (model := model P) (.oracle UnitarySource.Coordinate.controlled)
      ((algorithm P t).run.code.resourcePool path) = 2 ^ t - 1 :=
  code_controlledUnitaryCount P t path

/-- Every actual QPE path has the inverse-Fourier expansion's exact native one-qubit count. -/
public theorem qpeAlgorithm_singleQubitCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (algorithm P t).run.code.Path) :
    ResourcePool.count (model := model P) (.gate .singleQubit)
      ((algorithm P t).run.code.resourcePool path) = 2 * t + 3 * t.choose 2 :=
  qpeCode_singleQubitCount P t path

/-- Every actual QPE path has the inverse-Fourier expansion's exact native CNOT count. -/
public theorem qpeAlgorithm_cnotCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (algorithm P t).run.code.Path) :
    ResourcePool.count (model := model P) (.gate .cnot)
      ((algorithm P t).run.code.resourcePool path) = 2 * t.choose 2 + 3 * (t / 2) :=
  qpeCode_cnotCount P t path

/-- The actual phase-estimation circuit uses no native Toffoli gate. -/
public theorem qpeAlgorithm_toffoliCount {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) (path : (algorithm P t).run.code.Path) :
    ResourcePool.count (model := model P) (.gate .toffoli)
      ((algorithm P t).run.code.resourcePool path) = 0 :=
  qpeCode_toffoliCount P t path

/-- Complete Output lists every actual live entry, including the borrowed source and phase word. -/
public theorem algorithm_output_listing {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    (algorithm P t).run.output.listing = (post t n).keys :=
  run_output_listing P t

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public theorem algorithm_solves {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    Algorithm.Solves (algorithm P t) (problem P t) := by
  constructor
  · intro Reference input promised _initialized
    exact actual_success P t input promised.2
  · intro _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input promised _initialized
    have promisedState : inputPromise P t
        (input.state.mapClassical
          (fun value => (value.1, (value.2, value.1)))).quantumMarginal.marginalLeft := by
      have localPromise := promised.2
      rw [Execution.Input.localState_quantumMarginal,
        Execution.OracleInput.oracleInput_caller_quantumMarginal] at localPromise
      simpa only [ExecutionState.mapClassical_quantumMarginal] using localPromise
    have restored := code_borrowedRestored P t
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))) promisedState
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code P t).BorrowedRestored Reference input.state
      ((code P t).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events P t path)
  · intro _Reference _input _promised _initialized path _supported
    exact code_residentSpace P t path
  · intro _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace P t path
  · intro _Reference _input _promised _initialized path _supported
    exact code_depth P t path


/-- The original borrowed-eigenstate phase-estimation problem is solved by the same actual
execution with complete output, joint borrowed restoration and independent native budgets. -/
public theorem main {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    ∃ candidate : Algorithm (model P) (pre t n) (post t n) (.bits t),
      Algorithm.Solves candidate (problem P t) :=
  ⟨algorithm P t, algorithm_solves P t⟩

end

end QuantumAlg.QuantumPhaseEstimation
