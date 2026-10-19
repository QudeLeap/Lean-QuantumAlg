/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.ProjectedSignal.Circuit
public import QuantumAlg.Components.Oracle.ProjectedSignal.Source
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Components.Oracle.ProjectedSignal.Circuit
import all QuantumAlg.Components.Oracle.ProjectedSignal.Source
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Actual alternating projected-signal execution

The source-aligned word alternates U and its explicitly granted inverse, with
projector phase gadgets on the same phase ancilla
[GSLW19, BlockHam.tex:738-745,883-890]. Ordinary source queries are never converted
into controlled queries. Each phase gadget retains its two actual projector calls.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Native

noncomputable section

variable {width : Nat} (U : UnitaryOperator (Qubits width))
  (left right : OrthogonalProjector width) (allowControlled : Bool)

private def eventPool
    (event : Resource.Event
      (.quantum AlgorithmGate.model (ProjectedSignal.model width allowControlled))) :
    ResourcePool
      (.quantum AlgorithmGate.model (ProjectedSignal.model width allowControlled)) :=
  ResourcePool.singleton event

/-- One source query acts on the suffix, preserving the complete phase ancilla. -/
def signal (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model width allowControlled)
      (ProjectorPhase.layout width) :=
  UnitaryCircuit.onBinarySuffix 1
    (ProjectedSignal.Source.circuit AlgorithmGate.model width allowControlled inverse)

/-- The source suffix query has its original operator and identity on the phase ancilla. -/
lemma signal_matrix (inverse : Bool) :
    ((signal (width := width) allowControlled inverse).binaryMatrix
      (ProjectedSignal.interpretation U left right allowControlled)) =
      (1 : UnitaryOperator (Qubits 1)).tensor (if inverse then U⁻¹ else U) := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    ProjectedSignal.Source.circuit_matrix]

/-- The source suffix query retains exactly one ordinary or inverse coordinate. -/
lemma signal_events (inverse : Bool) :
    (signal (width := width) allowControlled inverse).eventCost =
      eventPool (width := width) allowControlled
        (.oracle (.source (if inverse then .inverse else .ordinary))) := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost,
    ProjectedSignal.Source.circuit_events]
  rfl

/-- Suffix placement preserves the source query's single abstract step. -/
lemma signal_depth (inverse : Bool) :
    (signal (width := width) allowControlled inverse).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth,
    ProjectedSignal.Source.circuit_depth]

/-- The actual two-projector-query phase gadget at one source phase slot. -/
def phase (useRight : Bool) (φ : ℝ) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model width allowControlled)
      (ProjectorPhase.layout width) :=
  ProjectorPhase.circuit
    (ProjectedSignal.Circuit.projectorFlip AlgorithmGate.model width
      allowControlled useRight)
    (2 * φ)

/-- One projected phase uses its two declared calls and one actual native rotation. -/
lemma phase_events (useRight : Bool) (φ : ℝ) :
    (phase (width := width) allowControlled useRight φ).eventCost =
      2 • eventPool (width := width) allowControlled
        (.oracle (if useRight then .rightNot else .leftNot)) +
      eventPool (width := width) allowControlled (.gate .singleQubit) := by
  rw [phase, ProjectorPhase.circuit_events, ProjectedSignal.Circuit.projectorFlip_events]
  simp only [eventPool, two_nsmul]
  ac_rfl

/-- The two projector calls and rotation occupy three sequential abstract steps. -/
lemma phase_depth (useRight : Bool) (φ : ℝ) :
    (phase (width := width) allowControlled useRight φ).evaluatedEventDepth (fun _ => 1) = 3 := by
  rw [phase, ProjectorPhase.circuit_depth, ProjectedSignal.Circuit.projectorFlip_depth]

/-- The same source-order phase list constructs every actual source and projector occurrence. -/
def circuit : List ℝ →
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model width allowControlled)
      (ProjectorPhase.layout width)
  | [] => .identity _ _ _
  | φ :: phases =>
      let even := decide ((phases.length + 1) % 2 = 0)
      ((circuit phases).seq
        (signal (width := width) allowControlled even)).seq
        (phase (width := width) allowControlled even φ)

/-- Independent closed-form query and native budgets for a source word of length L. -/
def budget (L : Nat) :
    ResourcePool
      (.quantum AlgorithmGate.model (ProjectedSignal.model width allowControlled)) :=
  ((L + 1) / 2) • eventPool (width := width) allowControlled (.oracle (.source .ordinary)) +
    (L / 2) • eventPool (width := width) allowControlled (.oracle (.source .inverse)) +
    (2 * ((L + 1) / 2)) • eventPool (width := width) allowControlled (.oracle .leftNot) +
    (2 * (L / 2)) • eventPool (width := width) allowControlled (.oracle .rightNot) +
    L • eventPool (width := width) allowControlled (.gate .singleQubit)

private lemma budget_succ (L : Nat) :
    budget (width := width) allowControlled (L + 1) =
      (budget (width := width) allowControlled L +
        eventPool (width := width) allowControlled (.oracle (.source
          (if decide ((L + 1) % 2 = 0) then .inverse else .ordinary)))) +
      (2 • eventPool (width := width) allowControlled (.oracle
          (if decide ((L + 1) % 2 = 0) then .rightNot else .leftNot)) +
        eventPool (width := width) allowControlled (.gate .singleQubit)) := by
  by_cases even : (L + 1) % 2 = 0
  · have upper : (L + 1 + 1) / 2 = (L + 1) / 2 := by omega
    have lower : (L + 1) / 2 = L / 2 + 1 := by omega
    simp only [budget, upper, lower, even, decide_true, ↓reduceIte,
      Nat.mul_add, Nat.mul_one, add_nsmul, one_nsmul]
    ac_rfl
  · have upper : (L + 1 + 1) / 2 = (L + 1) / 2 + 1 := by omega
    have lower : (L + 1) / 2 = L / 2 := by omega
    simp only [budget, upper, lower, even, decide_false, Bool.false_eq_true, ↓reduceIte,
      Nat.mul_add, Nat.mul_one, add_nsmul, one_nsmul]
    ac_rfl

/-- All query coordinates and native rotations are derived from the same executed word. -/
lemma circuit_events (phases : List ℝ) :
    (circuit (width := width) allowControlled phases).eventCost =
      budget (width := width) allowControlled phases.length := by
  induction phases with
  | nil => simp [circuit, budget]
  | cons φ phases ih =>
      simp only [circuit, UnitaryCircuit.seq_eventCost, ih, signal_events, phase_events,
        List.length_cons]
      exact (budget_succ (width := width) allowControlled phases.length).symm

/-- The exact full dependency depth includes all source, projector and native phase steps. -/
lemma circuit_depth (phases : List ℝ) :
    (circuit (width := width) allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      4 * phases.length := by
  induction phases with
  | nil => rfl
  | cons φ phases ih =>
      simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq, ih, signal_depth, phase_depth,
        List.length_cons]
      omega

end

end QuantumAlg.QSP.MultiQubit.QSVT.Native
