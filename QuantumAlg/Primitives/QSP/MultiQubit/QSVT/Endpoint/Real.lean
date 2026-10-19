/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Real
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Real
import all QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Real

/-!
# Complete matching-parity Hermitian polynomial transformation

The full target is determined by pure phase synthesis, mathematical boundary
Hadamards and ancilla reassociation. The original polynomial block and all native
coordinate bounds remain independent construction theorems
[GSLW19, BlockHam.tex:851].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianRealParity
noncomputable section

/-- **Input.** A supplied owned register of m+1 block ancillas and n system qubits.
**Output.** The full mathematical unitary selected from the real polynomial phase certificate.
**Resource budget.** Degree/width native budget, m+n+1 live qubits, and
15 ((40 m+4) L+2) abstract depth, including source queries.
**Success.** Exact action on arbitrary joint inputs and external references.
**Source.** Real matching-parity transformation [GSLW19, BlockHam.tex:851]. -/
@[expose]
public def problem (m n : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    Problem (.quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
      (UnitaryExecution.Owned.context (UnitaryExecution.Owned.Binary.layout ((1 + m) + n)))
      (UnitaryExecution.Owned.context (UnitaryExecution.Owned.Binary.layout ((1 + m) + n))) .unit
        where
  Witness := UnitaryOperator (Qubits (m + n)) × HilbertOperator (Qubits n)
  valid := fun environment witness _ =>
    environment.quantum = UnitarySource.interpretation witness.1 false true false ∧
      ExactBlockEncoding m n witness.1 witness.2 ∧ witness.2.IsHermitian
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ witness => [StateRequirement.unitary
    (UnitaryExecution.Owned.target (UnitaryExecution.Owned.Binary.physicalTarget
      (Execution.Selected.realTarget witness.1 source)))]
  resources :=
    { events := Execution.realBudget m n L
      resident := SpacePool.ofQuantumLayout (UnitaryExecution.Owned.Binary.layout ((1 + m) + n))
      auxiliary := SpacePool.ofQuantumLayout (UnitaryExecution.Owned.Binary.layout ((1 + m) + n)) }
  quantumTimeLimit := 15 * ((40 * m + 4) * L + 2)

private lemma word_solves (m n : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P)
    (word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) false true false)
      (UnitaryExecution.Owned.Binary.layout ((1 + m) + n)))
    (matrix : ∀ (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n)),
      ExactBlockEncoding m n U A → A.IsHermitian →
      word.binaryMatrix (UnitarySource.interpretation U false true false) =
        Execution.Selected.realTarget U source)
    (cost : word.eventCost = Execution.realBudget m n L)
    (depth : word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 4) * L + 2)) :
    Algorithm.Solves (UnitaryExecution.Owned.Binary.algorithm word) (problem m n source) := by
  have actual := UnitaryExecution.Owned.Binary.main (fun environment
    => word.binaryMatrix environment)
    (Execution.realBudget m n L) (15 * ((40 * m + 4) * L + 2)) word (fun _
      => rfl) (le_of_eq cost) depth
  constructor
  · intro environment witness Reference input _valid _initialized
    exact actual.success environment () Reference input trivial trivial
  · intro environment witness Reference input valid _initialized requirement present
    apply actual.states environment () Reference input trivial trivial requirement
    change requirement ∈ [StateRequirement.unitary (UnitaryExecution.Owned.target
      (UnitaryExecution.Owned.Binary.physicalTarget (word.binaryMatrix environment.quantum)))]
    change environment.quantum = UnitarySource.interpretation witness.1 false true false ∧
      ExactBlockEncoding m n witness.1 witness.2 ∧ witness.2.IsHermitian at valid
    rw [valid.1, matrix witness.1 witness.2 valid.2.1 valid.2.2]
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
public theorem main (m n : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ candidate : Algorithm _ _ _ .unit, candidate.Solves (problem m n source) := by
  obtain ⟨word, semantic, cost, depth, _, _⟩ :=
    Execution.Selected.exists_real_target_execution m n source
  refine ⟨UnitaryExecution.Owned.Binary.algorithm word, ?_⟩
  exact word_solves m n source word
    (fun U A encoding hermitian => (semantic U A encoding hermitian).1) cost depth


end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianRealParity
