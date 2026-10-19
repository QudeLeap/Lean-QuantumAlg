/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.SingleQubit.Singleton
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Native reflection-convention QSP words

The source product has d signal factors and d+1 processing rotations
[Lin22, hermfunc.tex:1103-1138]. Each factor is implemented by its actual
one-qubit operator in the default native model. The supplied qubit remains
live and arbitrary, including at degree zero; no oracle access is assumed.
-/

namespace QuantumAlg.ReflectionBasedQuantumSignalProcessing

noncomputable section

/-- The default native model for the explicit one-qubit signal formula. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- The single supplied physical qubit. -/
public abbrev layout := (QuantumSignature.qubits 1).canonicalPlacement.layout

/-- Independent native ledger of the fully expanded degree-d word. -/
public def eventBudget (d : Nat) : ResourcePool model :=
  (2 * d + 1) • ResourcePool.singleton (model := model) (.gate .singleQubit)

private def one (name : String) (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model .empty layout :=
  .macroCall name (Gate.singleQubitAt layout .empty operator (0 : Fin 1) rfl)

private lemma one_matrix (name : String) (operator : UnitaryOperator (Qubits 1))
    (environment : OracleModel.empty.Interpretation) :
    ((one name operator).binaryMatrix environment) = operator := by
  exact Gate.singleQubitAt_singleton_binaryMatrix .empty operator

private def step (x φ : Real) (hx : x ∈ Set.Icc (-1 : Real) 1) :
    UnitaryCircuit AlgorithmGate.model .empty layout :=
  (one "processing-rotation" (rotZOp φ)).seq (one "qsp-signal" (qspSignalOOp x hx))

/-- The actual source-order word, without preparation or allocation. -/
public def circuit (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    UnitaryCircuit AlgorithmGate.model .empty layout :=
  φs.foldl (fun accumulated φ => (step x φ hx).seq accumulated)
    (one "processing-rotation" (rotZOp φ₀))

/-- The independent certified algebraic source product. -/
public def operator (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) : UnitaryOperator (Qubits 1) :=
  qspOUnitary φ₀ φs x hx

private lemma fold_matrix (phases : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1)
    (start : UnitaryCircuit AlgorithmGate.model .empty layout)
      (environment : OracleModel.empty.Interpretation) :
    ((phases.foldl (fun accumulated φ
      => (step x φ hx).seq accumulated) start).binaryMatrix environment) =
      phases.foldl (fun accumulated φ => accumulated * (qspSignalOOp x hx * rotZOp φ))
        (start.binaryMatrix environment) := by
  induction phases generalizing start with
  | nil => rfl
  | cons φ tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, step, one_matrix]

lemma circuit_matrix (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) (environment : OracleModel.empty.Interpretation) :
    ((circuit φ₀ φs x hx).binaryMatrix environment) = operator φ₀ φs x hx := by
  rw [circuit, fold_matrix, one_matrix]
  rfl

private lemma fold_events (phases : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1)
    (start : UnitaryCircuit AlgorithmGate.model .empty layout) :
    (phases.foldl (fun accumulated φ => (step x φ hx).seq accumulated) start).eventCost =
      (2 * phases.length) • ResourcePool.singleton (model := model) (.gate .singleQubit) +
        start.eventCost := by
  induction phases generalizing start with
  | nil => simp
  | cons φ tail ih =>
      simp only [List.foldl_cons, List.length_cons, ih, UnitaryCircuit.seq_eventCost]
      simp only [step, UnitaryCircuit.seq_eventCost, one,
        UnitaryCircuit.macroCall_eventCost, Gate.singleQubitAt_eventCost]
      rw [Nat.mul_add, add_nsmul]
      simp only [Nat.mul_one, two_nsmul]
      ac_rfl

lemma circuit_events (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    (circuit φ₀ φs x hx).eventCost = eventBudget φs.length := by
  rw [circuit, fold_events]
  simp [one, eventBudget, add_nsmul]

private lemma one_macro (name focus : String) (operator : UnitaryOperator (Qubits 1)) :
    (one name operator).macroCount focus = if name = focus then 1 else 0 := by
  rw [one, UnitaryCircuit.macroCount_macroCall]
  rfl

private lemma fold_macro (phases : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1)
    (start : UnitaryCircuit AlgorithmGate.model .empty layout) (focus : String) :
    (phases.foldl (fun accumulated φ => (step x φ hx).seq accumulated) start).macroCount focus =
      phases.length * ((if "processing-rotation" = focus then 1 else 0) +
        (if "qsp-signal" = focus then 1 else 0)) + start.macroCount focus := by
  induction phases generalizing start with
  | nil => simp
  | cons φ tail ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [UnitaryCircuit.macroCount_seq, step, one_macro, Nat.add_mul, Nat.one_mul]
      omega

/-- Source factors are descriptive observations of this same expanded native word. -/
public lemma circuit_macro_counts (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    (circuit φ₀ φs x hx).macroCount "qsp-signal" = φs.length ∧
      (circuit φ₀ φs x hx).macroCount "processing-rotation" = φs.length + 1 := by
  simp [circuit, fold_macro, one_macro]

private lemma fold_depth (phases : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1)
    (start : UnitaryCircuit AlgorithmGate.model .empty layout) :
    (phases.foldl (fun accumulated φ => (step x φ hx).seq accumulated) start).evaluatedEventDepth
        (fun _ => 1) = 2 * phases.length + start.evaluatedEventDepth (fun _ => 1) := by
  induction phases generalizing start with
  | nil => simp
  | cons φ tail ih =>
      simp only [List.foldl_cons, List.length_cons, ih,
        UnitaryCircuit.evaluatedEventDepth_seq]
      change 2 * tail.length + (2 + _) = _
      omega

lemma circuit_depth (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    (circuit φ₀ φs x hx).evaluatedEventDepth (fun _ => 1) = 2 * φs.length + 1 :=
  fold_depth φs x hx _

end

end QuantumAlg.ReflectionBasedQuantumSignalProcessing
