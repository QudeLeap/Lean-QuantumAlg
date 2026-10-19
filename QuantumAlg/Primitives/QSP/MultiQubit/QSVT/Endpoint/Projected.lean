/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Projected
import all QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Projected

/-!
# Complete projected singular-value transformation

Pure polynomial synthesis specifies the complete balanced target independently.
The granted source and projector queries realize that target on every joint
input, with the source polynomial block and exact occurrence counts proved in
the supporting construction [GSLW19, BlockHam.tex:747-887].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected
noncomputable section

/-- **Input.** One supplied owned phase qubit and the original N signal qubits.
**Output.** The full mathematical balanced unitary selected by polynomial phase synthesis.
**Resource budget.** Independent degree-indexed source/projector query and rotation
budget, N+1 live qubits, and abstract depth at most 4 L+1.
**Success.** Exact full joint-state action with every external reference retained.
**Source.** Projected real singular-value transformation [GSLW19, BlockHam.tex:851]. -/
@[expose]
public def problem (N : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    Problem (.quantum AlgorithmGate.model (ProjectedSignal.model N))
      (UnitaryExecution.Owned.context (UnitaryExecution.Owned.Binary.layout (1 + N)))
      (UnitaryExecution.Owned.context (UnitaryExecution.Owned.Binary.layout (1 + N))) .unit where
  Witness := UnitaryOperator (Qubits N) × OrthogonalProjector N × OrthogonalProjector N
  valid := fun environment witness _ =>
    environment.quantum = ProjectedSignal.interpretation witness.1 witness.2.1 witness.2.2
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ witness => [StateRequirement.unitary
    (UnitaryExecution.Owned.target (UnitaryExecution.Owned.Binary.physicalTarget
      (Execution.Selected.projectedTarget witness.1 witness.2.1 witness.2.2 source)))]
  resources :=
    { events := Execution.projectedBudget N L
      resident := SpacePool.ofQuantumLayout (UnitaryExecution.Owned.Binary.layout (1 + N))
      auxiliary := SpacePool.ofQuantumLayout (UnitaryExecution.Owned.Binary.layout (1 + N)) }
  quantumTimeLimit := 4 * L + 1

private lemma word_solves (N : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P)
    (word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model N)
      (UnitaryExecution.Owned.Binary.layout (1 + N)))
    (matrix : ∀ (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N),
      word.binaryMatrix (ProjectedSignal.interpretation U left right) =
        Execution.Selected.projectedTarget U left right source)
    (cost : word.eventCost = Execution.projectedBudget N L)
    (depth : word.evaluatedEventDepth (fun _ => 1) ≤ 4 * L + 1) :
    Algorithm.Solves (UnitaryExecution.Owned.Binary.algorithm word) (problem N source) := by
  have actual := UnitaryExecution.Owned.Binary.main (fun environment
    => word.binaryMatrix environment)
    (Execution.projectedBudget N L) (4 * L + 1) word (fun _ => rfl) (le_of_eq cost) depth
  constructor
  · intro environment witness Reference input _valid _initialized
    exact actual.success environment () Reference input trivial trivial
  · intro environment witness Reference input valid _initialized requirement present
    apply actual.states environment () Reference input trivial trivial requirement
    change requirement ∈ [StateRequirement.unitary (UnitaryExecution.Owned.target
      (UnitaryExecution.Owned.Binary.physicalTarget (word.binaryMatrix environment.quantum)))]
    change environment.quantum =
      ProjectedSignal.interpretation witness.1 witness.2.1 witness.2.2 at valid
    rw [valid, matrix]
    exact present
  · intro environment witness Reference input _valid _initialized
    exact actual.borrowed environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.events environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.resident environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.auxiliary environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.time environment () Reference input trivial trivial

/-- Public polynomial data fixes one exact execution for every admitted source interpretation. -/
public theorem main (N : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ candidate : Algorithm _ _ _ .unit, candidate.Solves (problem N source) := by
  obtain ⟨word, semantic, cost, depth⟩ :=
    Execution.Selected.exists_projected_target_execution N source
  refine ⟨UnitaryExecution.Owned.Binary.algorithm word, ?_⟩
  exact word_solves N source word (fun U left right => (semantic U left right).1) cost depth

end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected
