/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Complex
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Complex
import all QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Complex

/-!
# Complete complex Hermitian polynomial transformation

Mathematical synthesis fixes the four phase branches and their full unitary
before execution. The width is m+1 at degree zero and m+3 otherwise. The original
normalization-four block and native coordinate bounds remain independent
construction theorems [GSLW19, BlockHam.tex:1938].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianComplex
noncomputable section

/-- **Input.** The supplied owned source/system register and one or three transformation ancillas.
**Output.** The independently selected full four-branch mathematical unitary.
**Resource budget.** Degree/width native budget, m+n+(if L=0 then 1 else 3) live qubits,
and 15 ((40 m+21) L+20) abstract depth, including source queries.
**Success.** Exact action on arbitrary joint inputs and external references.
**Source.** Complex polynomial transformation [GSLW19, BlockHam.tex:1938]. -/
@[expose]
public def problem (m n : Nat) {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    Problem (.quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (UnitaryExecution.Owned.context (UnitaryExecution.Owned.Binary.layout
        (Execution.Selected.complexAncillas m L + n)))
      (UnitaryExecution.Owned.context (UnitaryExecution.Owned.Binary.layout
        (Execution.Selected.complexAncillas m L + n))) .unit where
  Witness := UnitaryOperator (Qubits (m + n)) × HilbertOperator (Qubits n)
  valid := fun environment witness _ =>
    environment.quantum = UnitarySource.interpretation witness.1 true true false ∧
      ExactBlockEncoding m n witness.1 witness.2 ∧ witness.2.IsHermitian
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ witness => [StateRequirement.unitary
    (UnitaryExecution.Owned.target (UnitaryExecution.Owned.Binary.physicalTarget
      (Execution.Selected.complexTarget witness.1 P degree bounded)))]
  resources :=
    { events := Execution.complexBudget m n L
      resident := SpacePool.ofQuantumLayout (UnitaryExecution.Owned.Binary.layout
        (Execution.Selected.complexAncillas m L + n))
      auxiliary := SpacePool.ofQuantumLayout (UnitaryExecution.Owned.Binary.layout
        (Execution.Selected.complexAncillas m L + n)) }
  quantumTimeLimit := 15 * ((40 * m + 21) * L + 20)

private lemma word_solves (m n : Nat) {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1)
    (word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false)
      (UnitaryExecution.Owned.Binary.layout (Execution.Selected.complexAncillas m L + n)))
    (matrix : ∀ (U : UnitaryOperator (Qubits (m + n))),
      word.binaryMatrix (UnitarySource.interpretation U true true false) =
        Execution.Selected.complexTarget U P degree bounded)
    (cost : word.eventCost = Execution.complexBudget m n L)
    (depth : word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 21) * L + 20)) :
    Algorithm.Solves (UnitaryExecution.Owned.Binary.algorithm word) (problem m n P degree bounded)
      := by
  have actual := UnitaryExecution.Owned.Binary.main (fun environment
    => word.binaryMatrix environment)
    (Execution.complexBudget m n L) (15 * ((40 * m + 21) * L + 20)) word (fun _
      => rfl) (le_of_eq cost) depth
  constructor
  · intro environment witness Reference input _valid _initialized
    exact actual.success environment () Reference input trivial trivial
  · intro environment witness Reference input valid _initialized requirement present
    apply actual.states environment () Reference input trivial trivial requirement
    change requirement ∈ [StateRequirement.unitary (UnitaryExecution.Owned.target
      (UnitaryExecution.Owned.Binary.physicalTarget (word.binaryMatrix environment.quantum)))]
    change environment.quantum = UnitarySource.interpretation witness.1 true true false ∧
      ExactBlockEncoding m n witness.1 witness.2 ∧ witness.2.IsHermitian at valid
    rw [valid.1, matrix witness.1]
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
public theorem main (m n : Nat) {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ candidate : Algorithm _ _ _ .unit, candidate.Solves (problem m n P degree bounded) := by
  obtain ⟨word, semantic, cost, depth, _, _⟩ :=
    Execution.Selected.exists_complex_target_execution m n P degree bounded
  refine ⟨UnitaryExecution.Owned.Binary.algorithm word, ?_⟩
  exact word_solves m n P degree bounded word semantic cost depth



end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianComplex
