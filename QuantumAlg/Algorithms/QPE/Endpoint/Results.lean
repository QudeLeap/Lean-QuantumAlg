/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Endpoint
import all QuantumAlg.Algorithms.QPE.Endpoint
import all QuantumAlg.Algorithms.QPE.Endpoint.Execution

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

/-- The complete phase-estimation contract retains the explicit Fourier success constant. -/
public lemma qpeProblem_successLB_value (n t : Nat) (environment : (model n).Environment)
    (P : (problem n t).Witness) :
    ((problem n t).successLB environment P).value = ENNReal.ofReal (4 / Real.pi ^ 2) := by
  rfl

/-- The auxiliary quantum budget consists of precisely the owned phase-register width. -/
public lemma qpeProblem_quantumAuxiliary (n t : Nat) :
    (problem n t).resources.auxiliary (.quantumSystems 2) = t := by
  change (if (2 : ℕ+) = 2 then t else 0) = t
  exact if_pos rfl

/-- Public validity identifies the source interpretation and the original eigenstate promise. -/
public lemma problem_valid_iff {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (environment : (model n).Environment)
    (state : ExecutionState (Execution.Store (pre t n)) (pre t n).register) :
    (problem n t).valid environment P state ↔
      environment.quantum = UnitarySource.interpretation P.unitary true ∧ 0 < t ∧
      ∀ row column, state.quantumMarginal.matrix row column =
        P.eigenstate.vec (inputBasisEquiv t n row) *
          star (P.eigenstate.vec (inputBasisEquiv t n column)) := Iff.rfl

/-- The actual stored bits are accepted precisely at the original circular phase precision. -/
public lemma problem_accepts_bits_iff {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (environment : (model n).Environment)
    (initial : Execution.Store (pre t n)) (outcome : Fin t → Bool) :
    (problem n t).accepts environment P initial (.bits outcome) ↔
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

/-- Every actual path contains exactly the controlled source calls of the power ladder. -/
public lemma algorithm_controlledUnitaryCount (n : Nat)
    (t : Nat) (path : (algorithm n t).run.code.Path) :
    ResourcePool.count (model := model n) (.oracle UnitarySource.Coordinate.controlled)
      ((algorithm n t).run.code.resourcePool path) = 2 ^ t - 1 :=
  code_controlledUnitaryCount n t path

/-- Every actual QPE path has the inverse-Fourier expansion's exact native one-qubit count. -/
public lemma qpeAlgorithm_singleQubitCount (n : Nat)
    (t : Nat) (path : (algorithm n t).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .singleQubit)
      ((algorithm n t).run.code.resourcePool path) = 2 * t + 3 * t.choose 2 :=
  qpeCode_singleQubitCount n t path

/-- Every actual QPE path has the inverse-Fourier expansion's exact native CNOT count. -/
public lemma qpeAlgorithm_cnotCount (n : Nat)
    (t : Nat) (path : (algorithm n t).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .cnot)
      ((algorithm n t).run.code.resourcePool path) = 2 * t.choose 2 + 3 * (t / 2) :=
  qpeCode_cnotCount n t path

/-- The actual phase-estimation circuit uses no native Toffoli gate. -/
public lemma qpeAlgorithm_toffoliCount (n : Nat)
    (t : Nat) (path : (algorithm n t).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .toffoli)
      ((algorithm n t).run.code.resourcePool path) = 0 :=
  qpeCode_toffoliCount n t path

/-- Complete Output lists every actual live entry, including the borrowed source and phase word. -/
public lemma algorithm_output_listing (n : Nat) (t : Nat) :
    (algorithm n t).run.output.listing = (post t n).keys :=
  run_output_listing n t

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public lemma algorithm_solves (n : Nat) (t : Nat) :
    Algorithm.Solves (algorithm n t) (problem n t) :=
  complete_correct n t

end

end QuantumAlg.QuantumPhaseEstimation
