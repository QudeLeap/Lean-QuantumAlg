/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Gates.GlobalPhase
import all QuantumAlg.Components.Gates.GlobalPhase
public import QuantumAlg.Primitives.Trotter.PauliRotation.Cost
import all QuantumAlg.Primitives.Trotter.PauliRotation.Cost
public import QuantumAlg.Primitives.Trotter.PauliRotation.Rotation
import all QuantumAlg.Primitives.Trotter.PauliRotation.Rotation
import all QuantumAlg.Primitives.Trotter.PauliRotation.Basis
import all QuantumAlg.Primitives.Trotter.PauliRotation.Parity
import all QuantumAlg.Primitives.Trotter.PauliRotation.Tensor
import all QuantumAlg.Primitives.Trotter.Native
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.Pauli.Letter
import all QuantumAlg.Components.Gates

/-!
# Exact native circuits for Pauli-string rotations

For nonempty support, basis changes and a CNOT parity fan-in implement
`exp (-i θ P)` exactly [WBA11, h2.arxiv2.tex:384-412]. The last support
wire is the target, including for gapped support. The fan-in is equivalent to
the displayed parity chain; no routing or synthesis claim is made.

Empty support executes a one-qubit scalar instruction with the explicit
scalar phase `exp (-i θ)`, which must be retained before coherent control
[WBA11, h2.arxiv2.tex:835]. Native counts are derived from the same circuit.
-/

namespace QuantumAlg.Trotter

open PauliRotation

noncomputable section

/-- Pure mathematical identity-string phase, including the zero-width register. -/
public lemma pauli_identity_evolution {n : ℕ} (P : PauliString n) (θ : ℝ)
    (h : P.support = ∅) : timeEvolution P.hamiltonian θ = globalPhaseOp θ := by
  have hletters : ∀ j, P j = .i := by
    intro j
    by_contra hj
    have hm : j ∈ P.support := by simp [PauliString.support, hj]
    simp [h] at hm
  have hP : P.op = 1 := by
    rw [← tensorOp_pauli]
    simp only [hletters, PauliLetter.op]
    exact tensorOp_one n
  apply Subtype.ext
  rw [pauli_evolution, hP, globalPhaseOp_coe]
  change cosine θ • (1 : HilbertOperator (Qubits n)) + sine θ • 1 =
    Complex.exp (-(Complex.I * (θ : ℂ))) • 1
  rw [← add_smul]
  congr 1
  simp only [cosine, sine, Complex.cosh, Complex.sinh]
  ring

/-- The retained scalar instruction occupies the first actual input qubit. -/
private def scalarPhase {n : ℕ} [NeZero n] (θ : ℝ) : NativeCircuit n :=
  globalPhaseAt (QubitLayout.canonical n) .empty θ (0 : Fin n)

private lemma scalarPhase_matrix (n : ℕ) [NeZero n] (θ : ℝ) :
    (scalarPhase (n := n) θ).binaryOperator = globalPhaseOp θ := by
  have same : (scalarPhase (n := n) θ).matrix OracleModel.emptyInterpretation =
      (globalPhaseOp θ : UnitaryOperator (nativeLayout n).register) :=
    globalPhaseAt_matrix (QubitLayout.canonical n) .empty θ (0 : Fin n)
      OracleModel.emptyInterpretation
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n)
    ((scalarPhase (n := n) θ).matrix OracleModel.emptyInterpretation) = _
  rw [same]
  apply Subtype.ext
  ext i j
  simp [UnitaryOperator.coe_reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    globalPhaseOp_coe, Matrix.one_apply]

private lemma scalarPhase_eventCost (n : ℕ) [NeZero n] (θ : ℝ) :
    (scalarPhase (n := n) θ).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) :=
  globalPhaseAt_eventCost (QubitLayout.canonical n) .empty θ (0 : Fin n)

/-- Exact Pauli rotation; empty support applies scalar phase on the first real qubit. -/
public def expPauli {n : ℕ} [NeZero n] (P : PauliString n) (θ : ℝ) : NativeCircuit n :=
  if h : P.support.Nonempty then
    (inputLayer P).seq ((central P (P.support.max' h) θ).seq (outputLayer P))
  else scalarPhase θ

/-- Exact matrix equality for every angle and support, with the full identity phase. -/
public lemma expPauli_matrix {n : ℕ} [NeZero n] (P : PauliString n) (θ : ℝ) :
    (expPauli P θ).binaryOperator = timeEvolution P.hamiltonian θ := by
  by_cases h : P.support.Nonempty
  · apply Subtype.ext
    simp only [expPauli, dif_pos h, NativeCircuit.binaryOperator_seq]
    change ((outputLayer P).binaryOperator : HilbertOperator (Qubits n)) *
      ((central P (P.support.max' h) θ).binaryOperator : HilbertOperator (Qubits n)) *
      ((inputLayer P).binaryOperator : HilbertOperator (Qubits n)) = _
    rw [central_matrix P _ (Finset.max'_mem _ h), pauli_evolution]
    have hinverse : ((outputLayer P).binaryOperator : HilbertOperator (Qubits n)) *
        ((inputLayer P).binaryOperator : HilbertOperator (Qubits n)) = 1 :=
      congrArg (fun U : UnitaryOperator (Qubits n) => (U : HilbertOperator (Qubits n)))
        (layers_inverse P)
    have hconj : ((outputLayer P).binaryOperator : HilbertOperator (Qubits n)) *
        ((zString P).op : HilbertOperator (Qubits n)) *
        ((inputLayer P).binaryOperator : HilbertOperator (Qubits n)) = P.op :=
      congrArg (fun U : UnitaryOperator (Qubits n) => (U : HilbertOperator (Qubits n)))
        (layers_conjugates P)
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, mul_one, hinverse, hconj]
  · rw [pauli_identity_evolution P θ (Finset.not_nonempty_iff_eq_empty.mp h)]
    simp only [expPauli, dif_neg h, scalarPhase_matrix]

/-- Exact native pool of this circuit: two parity passes, one rotation, and
literal H/S basis changes, counted in the actual default gate coordinates. -/
public lemma expPauli_eventCost {n : ℕ} [NeZero n] (P : PauliString n) (θ : ℝ) :
    (expPauli P θ).eventCost =
      if P.support.Nonempty then
        (2 * (P.weight - 1)) •
          ({.gate .cnot} : ResourcePool (.quantum AlgorithmGate.model .empty)) +
        {.gate .singleQubit} +
        (2 * (pauliLetterCount P .x + pauliLetterCount P .y)) •
          {.gate .singleQubit} +
        (4 * pauliLetterCount P .y) • {.gate .singleQubit}
      else {.gate .singleQubit} := by
  by_cases h : P.support.Nonempty
  · simp only [expPauli, dif_pos h, if_pos h, UnitaryCircuit.seq_eventCost]
    rw [central_eventCost P _ (Finset.max'_mem _ h)]
    have hlayers := layers_eventCost P
    calc
      _ = (central P (P.support.max' h) θ).eventCost +
          ((inputLayer P).eventCost + (outputLayer P).eventCost) := by
        rw [central_eventCost P _ (Finset.max'_mem _ h)]
        abel
      _ = _ := by
        rw [hlayers, central_eventCost P _ (Finset.max'_mem _ h)]
        abel
  · simp [expPauli, h, scalarPhase_eventCost, ResourcePool.singleton]

/-- Exact default-model CNOT count, including identity strings. -/
public lemma expPauli_cnot_count {n : ℕ} [NeZero n] (P : PauliString n) (θ : ℝ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (expPauli P θ).eventCost =
        if P.support.Nonempty then 2 * (P.weight - 1) else 0 := by
  rw [expPauli_eventCost]
  split <;> simp [ResourcePool.count]

/-- Literal H, S, rotation and scalar instructions in the default one-qubit coordinate. -/
public lemma expPauli_singleQubit_count {n : ℕ} [NeZero n] (P : PauliString n) (θ : ℝ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (expPauli P θ).eventCost =
        if P.support.Nonempty then
          1 + 2 * pauliLetterCount P .x + 6 * pauliLetterCount P .y else 1 := by
  rw [expPauli_eventCost]
  split <;> simp [ResourcePool.count]
  omega

/-- A closed-form unit-event-depth ceiling, including the empty-support case.
This serial upper bound does not assume nearest-neighbor routing. -/
public lemma expPauli_eventDepth_le {n : ℕ} [NeZero n] (P : PauliString n) (θ : ℝ) :
    (expPauli P θ).evaluatedEventDepth (fun _ => 1) ≤
      if P.support.Nonempty then
        2 * (P.weight - 1) + 1 +
          2 * (pauliLetterCount P .x + pauliLetterCount P .y) +
          4 * pauliLetterCount P .y
      else 1 := by
  have hb := DepthExpr.depthEval_le_costEval
    (fun _ : Resource.Event (.quantum AlgorithmGate.model .empty) => 1) (expPauli P θ).eventDepth
  rw [DepthExpr.costEval_eq_weightedCount] at hb
  change (expPauli P θ).evaluatedEventDepth (fun _ => 1) ≤
    ResourcePool.weightedCount (fun _ => 1) (expPauli P θ).resourcesFromEventDepth at hb
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost, expPauli_eventCost] at hb
  split at hb <;> simpa [ResourcePool.weightedCount, *] using hb

end
end QuantumAlg.Trotter
