/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Execution.Selected
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Execution.Context
public import QuantumAlg.Core.Execution.Time
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Execution.Selected
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Execution.Context
import all QuantumAlg.Core.Execution.Supplied.Qubits
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Signal
import all QuantumAlg.Core.Algorithm.Unitary.Endpoint
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Components.Oracle.QPP

/-!
# Complete QPP execution and exact source counts

The same phase-selected native word supplies its full joint-state action,
projected polynomial block, exact controlled-query and rotation counts, and
complete quantum time. Equal-wire placement retains every native instruction
[WZYW23, arxiv_v3.tex:598-618,635-666].
-/

namespace QuantumAlg.QSP.MultiQubit.QPP.Execution
noncomputable section

/-- The actual source word has the independently specified entire event pool. -/
public lemma qpp_word_events {L : Nat} (n : Nat)
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    (word n source).eventCost = events n L := by
  rw [word, Native.circuit_eventCost, (phases source).length_eq]
  simp only [events, show 2 * (2 * L) + 3 = 4 * L + 3 by omega]

/-- The original exact controlled-query and rotation counts concern this same source word. -/
public lemma qpp_word_exact_counts {L : Nat} (n : Nat)
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    HasExactResourceCounts n (2 * L) (word n source).eventCost := by
  simpa only [word, HasExactResourceCounts, (phases source).length_eq] using
    Native.circuit_counts n (phases source).φ (phases source).θ₀
      (phases source).φ₀ (phases source).ps

private lemma step_time (n : Nat)
    (index : Nat) (angles : ℝ × ℝ) :
    (Native.step n index angles).evaluatedEventDepth Resource.Event.quantumDuration = 3 := by
  by_cases even : index % 2 = 0
  · simp only [Native.step, Native.oracle, if_pos even,
      UnitaryCircuit.evaluatedEventDepth_seq]
    rfl
  · simp only [Native.step, Native.oracle, if_neg even,
      UnitaryCircuit.evaluatedEventDepth_seq]
    rfl

private lemma fold_time (n : Nat)
    (schedule : List ((ℝ × ℝ) × Nat))
    (start : UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (Native.layout n)) :
    (schedule.foldl (fun accumulated item => (Native.step n item.2 item.1).seq accumulated)
      start).evaluatedEventDepth Resource.Event.quantumDuration =
        3 * schedule.length + start.evaluatedEventDepth Resource.Event.quantumDuration := by
  induction schedule generalizing start with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.zero_add]
  | cons item rest ih =>
      rw [List.foldl_cons, ih, UnitaryCircuit.evaluatedEventDepth_seq, step_time,
        List.length_cons]
      omega

/-- All native rotations and queries count in the complete sequential quantum time. -/
public lemma qpp_word_quantumTime {L : Nat} (n : Nat)
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    (word n source).evaluatedEventDepth Resource.Event.quantumDuration = 6 * L + 3 := by
  rw [word, Native.circuit, fold_time, List.length_zipIdx, (phases source).length_eq]
  change 3 * (2 * L) + 3 = 6 * L + 3
  omega

/-- The same native instructions placed on one owned ancilla and the supplied input. -/
public def program {L : Nat} (n : Nat)
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (context n).quantumLayout :=
  QuantumAlg.Execution.unitaryOfEqualWires (Native.layout n) (context n).quantumLayout
    (context_wires n) (word n source)

private lemma program_matrix {n L : Nat} (U : UnitaryOperator (Qubits n))
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    ((program n source).matrix (QPPOracle.interpretation U))
      = physicalTarget (target U source) := by
  rw [program, QuantumAlg.Execution.unitaryOfEqualWires_matrix, physicalTarget,
    ← qpp_word_target U source]
  congr 1
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (1 + n)) ((word n source).matrix (QPPOracle.interpretation
      U))).symm

/-- One actual execution retaining both the data interface and the signal ancilla. -/
public def algorithm {L : Nat} (n : Nat)
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    Algorithm (.quantum AlgorithmGate.model (QPPOracle.model n)) (context n) (context n) .unit :=
  UnitaryExecution.algorithm (program n source)

/-- The complete native execution satisfies the independently specified full-state problem. -/
lemma qpp_complete_execution (n : Nat) {L : Nat}
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    (algorithm n source).Solves
      (UnitaryExecution.problem (fun environment => (program n source).matrix environment)
        (resources n L) (6 * L + 3)) := by
  apply UnitaryExecution.main _ _ _ (program n source) (fun _ => rfl) rfl rfl
  · exact le_of_eq (qpp_word_events n source)
  · apply le_of_eq
    rw [context_resident]
    funext axis
    cases axis <;> rfl
  · apply le_of_eq
    rw [context_auxiliary]
    funext axis
    cases axis <;> rfl
  · exact le_of_eq (qpp_word_quantumTime n source)

/-- The original source theorem, retaining exact phase and resources of the selected circuit. -/
public lemma qpp_source_circuit {n L : Nat} (U : UnitaryOperator (Qubits n))
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    projectedBlock 1 n (((word n source).binaryMatrix (QPPOracle.interpretation U)) :
      HilbertOperator (Qubits (1 + n))) =
        unitaryLaurentPolynomial L U coeff ∧
      HasExactResourceCounts n (2 * L) (word n source).eventCost :=
  ⟨qpp_word_projectedBlock U source, qpp_word_exact_counts n source⟩

/-- Every path of the same complete run has the source's exact native multiplicities. -/
public lemma qpp_execution_exact_counts {L : Nat} (n : Nat)
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff)
    (path : (algorithm n source).run.code.Path) :
    HasExactResourceCounts n (2 * L) ((algorithm n source).run.code.resourcePool path) := by
  change HasExactResourceCounts n (2 * L) (ResourcePool.ofList (program n source).eventTrace)
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact qpp_word_exact_counts n source

/-- Complete execution time is charged to the same path, including every rotation and query. -/
public lemma qpp_execution_quantumTime {L : Nat} (n : Nat)
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff)
    (path : (algorithm n source).run.code.Path) :
    (algorithm n source).run.code.quantumTime path = 6 * L + 3 :=
  qpp_word_quantumTime n source

end
end QuantumAlg.QSP.MultiQubit.QPP.Execution
