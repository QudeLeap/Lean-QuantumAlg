/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Specification
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Success
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# The original finite-cyclic problem solved by one actual execution

The algorithm contains only the original complete Endpoint.run. Its actual
output law, borrowed-reference restoration and independent resources discharge
the same problem's separate obligations without caller correctness promises.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint.Final

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

private theorem output_atom_eq_relational {kind : ProblemKind}
    {pre post : RuntimeCtx kind} {shape : CShape} (run : AlgorithmRun pre post shape)
    {Reference : Register} (input : Execution.Input pre Reference) (value : shape.Value) :
    run.outputDistribution input value =
      (run.relationalDistribution input).toOuterMeasure {pair | pair.2 = value} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  rfl

/-- Local validity supplies the same original target at every positive full-reference block. -/
theorem valid_originalTarget (P : KnownOrderProblem G) (A : Access P)
    {Reference : Register} (input : Execution.Input (pre P) Reference)
    (valid : Specification.inputDomain P A input.localState) :
    ∀ store, 0 < (input.state.block store).mass →
      store.read (targetRef P) = targetValue A := by
  intro store positive
  have localPositive : 0 < (input.localState.block store).mass := by
    rw [Execution.Input.localState_block_mass]
    exact positive
  rw [valid store localPositive]
  exact inputStore_target A

/-- The candidate executes the same complete sampler, retained result and recovery tail. -/
def algorithm (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    Algorithm .quantum (pre P) (outputContext P)
      (.option (.unsignedWord (orderWidth P))) where
  run := Endpoint.run P B A

/-- The candidate satisfies the independent resource contract on all of its actual paths. -/
theorem algorithm_resources (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    Specification.ClosedResourceContract P B A (algorithm P B A).run.code :=
  Specification.finiteCyclic_closedResourceContract P B A

/-- The same complete output lists every original and retained context entry. -/
theorem algorithm_output_listing (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    (algorithm P B A).run.output.listing = (outputContext P).keys :=
  finiteCyclic_run_output_listing P B A

/-- The actual execution restores the borrowed target with all joint reference correlations. -/
theorem algorithm_restoresBorrowed (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} (input : Execution.Input (pre P) Reference) :
    (algorithm P B A).run.RestoresBorrowed input :=
  Circuit.borrowedRestored_of_noBorrowedQuantum _ (input_noBorrowedQuantum P) Reference
    (input.state.mapClassical (fun store => (store, store)))

/-- The relational accepted event is exactly the original secret output atom of the same run. -/
theorem algorithm_accepted_probability (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P)
    {Reference : Register} (input : Execution.Input (pre P) Reference) :
    ((algorithm P B A).relationalDistribution input).toOuterMeasure
        {pair | (Specification.specification P secret B A).accepts pair.1 pair.2} =
      (Endpoint.run P B A).outputDistribution input
        (.optionSome (CShape.wordOfNat (orderWidth P) secret.secret.val)) :=
  (output_atom_eq_relational (Endpoint.run P B A) input _).symm

/-- The same actual execution meets the original exact-answer and complete resource contract. -/
theorem algorithm_solves (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P) :
    Algorithm.Solves (algorithm P B A) (Specification.specification P secret B A) where
  success := by
    intro Reference input valid
    change ENNReal.ofReal ((2 : Real) / 3) ≤
      ((algorithm P B A).relationalDistribution input).toOuterMeasure
        {pair | (Specification.specification P secret B A).accepts pair.1 pair.2}
    rw [algorithm_accepted_probability]
    exact finiteCyclic_run_success P B A secret input (valid_originalTarget P A input valid)
  states := by
    intro _Reference _input _valid _requirement present
    exact False.elim (List.not_mem_nil present)
  borrowed := by
    intro Reference input _valid
    exact algorithm_restoresBorrowed P B A input
  events := by
    intro _Reference _input _valid path _supported
    exact (algorithm_resources P B A).events path
  resident := by
    intro _Reference _input _valid path _supported
    exact (algorithm_resources P B A).resident path
  auxiliary := by
    intro _Reference _input _valid path _supported
    exact (algorithm_resources P B A).auxiliary path
  depth := by
    intro _Reference _input _valid path _supported
    exact (algorithm_resources P B A).depth path

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint.Final
