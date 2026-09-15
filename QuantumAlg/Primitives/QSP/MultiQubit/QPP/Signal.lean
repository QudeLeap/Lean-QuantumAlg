/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
import all QuantumAlg.Components.Oracle.Common
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Pair
import all QuantumAlg.Primitives.QSP.SingleQubit.Fourier
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# QPP alternating circuits

YZZYZ and alternating controlled-unitary QPP words, typed circuits, and exact
strict-event resource accounting.  Every public resource fact is read from the same
`UnitaryCircuit` whose matrix supplies the semantic statement.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open NormalizedVector Module.End

noncomputable section

variable {n : ℕ}
variable {U : UnitaryOperator (Qubits n)}

private theorem qpp_phaseGateOnZeroOp_applyVec_eq_smul_rotZStdOp
    (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOnZeroOp (-θ)).applyVec ψ =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ).applyVec ψ := by
  change (phaseGateOnZero (-θ)).applyVec ψ =
    Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
      (rotZStd θ).applyVec ψ
  exact phaseGateOnZero_applyVec_eq_smul_rotZStd θ ψ

private theorem qpp_phaseGateOp_applyVec_eq_smul_rotZStdOp
    (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOp θ).applyVec ψ =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ).applyVec ψ := by
  change (phaseGate θ).applyVec ψ =
    Complex.exp ((θ / 2 : ℝ) * Complex.I) •
      (rotZStd θ).applyVec ψ
  exact phaseGate_applyVec_eq_smul_rotZStd θ ψ

/-- Re-annotate the semantic unitary as one canonical local oracle call.  The
matrix is unchanged; only placement and resource metadata are normalized. -/
def qppOracleGate (U : UnitaryOperator (Qubits n)) : UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf (qppOracleLeaf U) (by
    simpa only [qppOracleLeaf, qppOracleLeafAt,
      UnitaryLeaf.subroutine_systemIdx] using
      (List.nodup_range : (List.range n).Nodup))

@[simp]
theorem qppOracleGate_matrix (U : UnitaryOperator (Qubits n)) :
    (qppOracleGate U).matrix = U :=
  rfl

@[simp]
theorem qppOracleGate_dagger_matrix (U : UnitaryOperator (Qubits n)) :
    (qppOracleGate U).dagger.matrix = U.dagger := by
  apply Subtype.ext
  simp [UnitaryOperator.coe_dagger]

@[simp] theorem qppOracleGate_applyVec (U : UnitaryOperator (Qubits n))
    (ψ : HilbertVector (Qubits n)) :
    (qppOracleGate U).matrix.applyVec ψ = U.applyVec ψ := rfl

/-- The one-control QPP query coordinate used by both controlled conventions. -/
def qppControlledOracleEvent (n : ℕ) : Resource.Event .quantum :=
  (qppOracleEvent n).controlForDimension 2

/-- Count the one-controlled query coordinate used by a QPP word. -/
def qppControlledOracleQueryCount (n : ℕ)
    (resources : ResourcePool .quantum) : ℕ :=
  ResourcePool.count (qppControlledOracleEvent n) resources



/-- Literal Y-rotation event advertised by the shared gate component. -/
def qppRotationYEvent : Resource.Event .quantum :=
  .gate (.declared "QuantumAlg.Components.Gate" "rotation-y")

/-- Literal Z-rotation event advertised by the shared gate component. -/
def qppRotationZEvent : Resource.Event .quantum :=
  .gate (.declared "QuantumAlg.Components.Gate" "rotation-z")

theorem qppOracleEvent_eq (n : ℕ) :
    qppOracleEvent n = .quantumSubroutine (qppOracleLabel n).quantum :=
  rfl

theorem qppControlledOracleEvent_eq (n : ℕ) :
    qppControlledOracleEvent n =
      .quantumSubroutine
        { base := qppOracleLabel n, controlDimensions := [2] } :=
  rfl

theorem qppRotationYEvent_eq :
    qppRotationYEvent =
      .gate (.declared "QuantumAlg.Components.Gate" "rotation-y") :=
  rfl

theorem qppRotationZEvent_eq :
    qppRotationZEvent =
      .gate (.declared "QuantumAlg.Components.Gate" "rotation-z") :=
  rfl

@[simp] theorem qppOracleEvent_ne_controlled (n : ℕ) :
    qppOracleEvent n ≠ qppControlledOracleEvent n := by
  intro equality
  have controlDimensionsEqual := congrArg
    (fun event : Resource.Event .quantum =>
      match event with
      | .quantumSubroutine label => label.controlDimensions
      | _ => []) equality
  simp [qppOracleEvent, qppControlledOracleEvent,
    Resource.Event.controlForDimension, Resource.Event.controlForDimensions,
    Resource.QuantumSubroutineLabel.controlForDimensions] at controlDimensionsEqual

@[simp] theorem qppOracleEvent_ne_rotationY (n : ℕ) :
    qppOracleEvent n ≠ qppRotationYEvent := by
  simp [qppOracleEvent, qppRotationYEvent]

@[simp] theorem qppOracleEvent_ne_rotationZ (n : ℕ) :
    qppOracleEvent n ≠ qppRotationZEvent := by
  simp [qppOracleEvent, qppRotationZEvent]

@[simp] theorem qppControlledOracleEvent_ne_rotationY (n : ℕ) :
    qppControlledOracleEvent n ≠ qppRotationYEvent := by
  simp [qppControlledOracleEvent, qppOracleEvent, qppRotationYEvent]

@[simp] theorem qppControlledOracleEvent_ne_rotationZ (n : ℕ) :
    qppControlledOracleEvent n ≠ qppRotationZEvent := by
  simp [qppControlledOracleEvent, qppOracleEvent, qppRotationZEvent]

@[simp] theorem qppRotationYEvent_ne_rotationZ :
    qppRotationYEvent ≠ qppRotationZEvent := by
  intro equality
  have namesEqual := congrArg
    (fun event : Resource.Event .quantum =>
      match event with
      | .gate label => label.name
      | _ => "") equality
  simp [qppRotationYEvent, qppRotationZEvent,
    Resource.GateLabel.declared] at namesEqual

@[simp] theorem qppOracleLeaf_event {n : ℕ}
    (U : UnitaryOperator (Qubits n)) :
    (qppOracleLeaf U).event = qppOracleEvent n :=
  rfl

theorem rotYLeaf_event_eq_qppRotationYEvent (θ : ℝ) :
    (rotYLeaf θ).event = qppRotationYEvent :=
  rfl

theorem rotZStdLeaf_event_eq_qppRotationZEvent (φ : ℝ) :
    (rotZStdLeaf φ).event = qppRotationZEvent :=
  rfl

attribute [local simp] ResourcePool.count_singleton_of_ne

/-- Count the source-advertised one-qubit `Y`/`Z` processing rotations. -/
def qppRotationCount (resources : ResourcePool .quantum) : ℕ :=
  ResourcePool.count qppRotationYEvent resources +
    ResourcePool.count qppRotationZEvent resources

@[simp] theorem qppControlledOracleQueryCount_add (n : ℕ)
    (left right : ResourcePool .quantum) :
    qppControlledOracleQueryCount n (left + right) =
      qppControlledOracleQueryCount n left +
        qppControlledOracleQueryCount n right := by
  simp [qppControlledOracleQueryCount]



@[simp] theorem qppRotationCount_add
    (left right : ResourcePool .quantum) :
    qppRotationCount (left + right) =
      qppRotationCount left + qppRotationCount right := by
  simp [qppRotationCount]
  omega

/-- Exact source-level QPP resource statement for a schedule of `steps`
controlled oracle uses. -/
public def QPP.HasExactResourceCounts (n steps : ℕ)
    (resources : ResourcePool .quantum) : Prop :=
  qppControlledOracleQueryCount n resources = steps ∧
    qppRotationCount resources = 2 * steps + 3

/-! ### Circuit construction helpers -/

/-- Fold typed circuit atoms in the execution order whose matrix semantics
realizes an algebraic left-to-right product. -/
private theorem circuitAlgebraicFold_matrix {R : Register} {α : Type}
    (schedule : List α) (start : UnitaryCircuit R) (step : α → UnitaryCircuit R) :
    (schedule.foldl (fun accumulated item => UnitaryCircuit.seq (step item) accumulated)
        start).matrix =
      schedule.foldl
        (fun accumulated item => accumulated * (step item).matrix)
        start.matrix := by
  induction schedule generalizing start with
  | nil => rfl
  | cons item tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rfl



/-- Coercing a fold of certified operators exposes the corresponding raw
matrix fold without introducing a parallel proof payload. -/
private theorem unitaryFold_coe {R : Register} {α : Type}
    (schedule : List α) (start : UnitaryOperator R)
    (step : α → UnitaryOperator R) :
    ((schedule.foldl (fun accumulated item => accumulated * step item) start :
      UnitaryOperator R) : HilbertOperator R) =
      schedule.foldl
        (fun accumulated item => accumulated * (step item : HilbertOperator R))
        (start : HilbertOperator R) := by
  induction schedule generalizing start with
  | nil => rfl
  | cons item tail ih =>
      simp only [List.foldl_cons]
      simpa using ih (start * step item)

/-- Lift one one-qubit processing gate to the leading QPP ancilla while using
canonical local placement for the whole register. -/
def qppLiftProcessingGate (n : ℕ) (G : UnitaryCircuit (Qubits 1))
    (hG : G.physical_idx = [0]) : UnitaryCircuit (Qubits (1 + n)) :=
  let rest := UnitaryCircuit.identity (Qubits n) (List.range' 1 n) List.nodup_range'
  UnitaryCircuit.tensorQubits G rest
    { left_nodup := G.physical_idx_nodup
      right_nodup := rest.physical_idx_nodup
      disjoint := by
        rw [hG]
        change [0].Disjoint (List.range' 1 n)
        simp }

/-- The two trainable one-qubit rotations in one QPP step. -/
def qppProcessingPairGate (p : ℝ × ℝ) : UnitaryCircuit (Qubits 1) :=
  UnitaryCircuit.seq (rotZStd p.2) (rotY p.1)

@[simp]
theorem qppProcessingPairGate_physical_idx (p : ℝ × ℝ) :
    (qppProcessingPairGate p).physical_idx = [0] :=
  rfl

@[simp]
theorem qppProcessingPairGate_matrix (p : ℝ × ℝ) :
    ((qppProcessingPairGate p).matrix : HilbertOperator (Qubits 1)) =
      (rotYOp p.1 : HilbertOperator (Qubits 1)) *
        (rotZStdOp p.2 : HilbertOperator (Qubits 1)) :=
  rfl

@[simp]
theorem qppLiftProcessingGate_matrix (n : ℕ) (G : UnitaryCircuit (Qubits 1))
    (hG : G.physical_idx = [0]) :
    ((qppLiftProcessingGate n G hG).matrix :
      HilbertOperator (Qubits (1 + n))) =
      HilbertOperator.tensor (G.matrix : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits n)) := by
  simp [qppLiftProcessingGate]

/-- A direct controlled QPP oracle in canonical local placement. -/
def qppControlledOracleGate (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (Qubits (1 + n)) :=
  let body := UnitaryCircuit.shiftPhysicalIdx 1 (qppOracleGate U)
  UnitaryCircuit.controlQubitsAt [0] body
    { left_nodup := by simp
      right_nodup := body.physical_idx_nodup
      disjoint := by simp [body, UnitaryCircuit.shiftPhysicalIdx] }
    (1 : Fin 2)

@[simp]
theorem qppControlledOracleGate_matrix (U : UnitaryOperator (Qubits n)) :
    (qppControlledOracleGate U).matrix = UnitaryOperator.controlledQubits U := by
  simp [qppControlledOracleGate, UnitaryOperator.controlledQubits]

/-- The alternating controlled-`U†`/controlled-`U` oracle atom. -/
def qppAlternatingOracleGate (U : UnitaryOperator (Qubits n)) (j : ℕ) :
    UnitaryCircuit (Qubits (1 + n)) :=
  let oracle := if j % 2 = 0 then (qppOracleGate U).dagger else qppOracleGate U
  let body := UnitaryCircuit.shiftPhysicalIdx 1 oracle
  let activation : Fin 2 := if j % 2 = 0 then 0 else 1
  UnitaryCircuit.controlQubitsAt [0] body
    { left_nodup := by simp
      right_nodup := body.physical_idx_nodup
      disjoint := by simp [body, oracle, UnitaryCircuit.shiftPhysicalIdx] }
    activation

theorem qppAlternatingOracleGate_matrix_of_even
    (U : UnitaryOperator (Qubits n)) {j : ℕ} (hj : j % 2 = 0) :
    (qppAlternatingOracleGate U j).matrix =
      UnitaryOperator.controlledQubitsOnZero U.dagger := by
  simp [qppAlternatingOracleGate, hj,
    UnitaryOperator.controlledQubitsOnZero]

theorem qppAlternatingOracleGate_matrix_of_odd
    (U : UnitaryOperator (Qubits n)) {j : ℕ} (hj : j % 2 ≠ 0) :
    (qppAlternatingOracleGate U j).matrix =
      UnitaryOperator.controlledQubits U := by
  simp [qppAlternatingOracleGate, hj, UnitaryOperator.controlledQubits]



/-- Direct and daggered signal circuits each carry the literal uncontrolled
query coordinate once. -/
theorem qppOracleEvent_counts (U : UnitaryOperator (Qubits n)) :
    ResourcePool.count (qppOracleEvent n) (qppOracleGate U).eventCost = 1 ∧
      ResourcePool.count (qppOracleEvent n)
        (qppOracleGate U).dagger.eventCost = 1 := by
  simp [qppOracleGate, qppOracleLeaf, qppOracleLeafAt, qppOracleEvent,
    ResourcePool.count, ResourcePool.singleton]

/-- Both QPP control conventions carry the literal one-control query
coordinate once. -/
theorem qppControlledOracleEvent_counts (U : UnitaryOperator (Qubits n)) :
    qppControlledOracleQueryCount n
        (qppControlledOracleGate U).eventCost = 1 ∧
      qppControlledOracleQueryCount n
        (qppAlternatingOracleGate U 0).eventCost = 1 := by
  simp [qppControlledOracleQueryCount, qppControlledOracleGate,
    qppAlternatingOracleGate, qppOracleGate, qppOracleLeaf,
    qppOracleLeafAt, qppControlledOracleEvent, qppOracleEvent,
    ResourcePool.count, ResourcePool.singleton,
    ResourcePool.controlForDimension, ResourcePool.controlForDimensions,
    Resource.Event.controlForDimension, Resource.Event.controlForDimensions,
    Resource.QuantumSubroutineLabel.controlForDimensions]

/-- Three front rotations of a QPP word, lifted to the ancilla. -/
def qppAlternatingInitialGate (n : ℕ) (φ θ₀ φ₀ : ℝ) :
    UnitaryCircuit (Qubits (1 + n)) :=
  qppLiftProcessingGate n (qspYZZYZInitialCircuit φ θ₀ φ₀)
    (qspYZZYZInitialCircuit_physical_idx φ θ₀ φ₀)

/-- Initial typed circuit for either QPP convention. -/
def qppAlternatingInitialCircuit (n : ℕ) (φ θ₀ φ₀ : ℝ) :
    UnitaryCircuit (Qubits (1 + n)) :=
  qppAlternatingInitialGate n φ θ₀ φ₀

/-- One direct-controlled YZZYZ QPP step. -/
def qppYZZYZStepCircuit (U : UnitaryOperator (Qubits n)) (p : ℝ × ℝ) :
    UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.seq
    (qppLiftProcessingGate n (qppProcessingPairGate p)
      (qppProcessingPairGate_physical_idx p))
    (qppControlledOracleGate U)

@[simp]
theorem qppYZZYZStepCircuit_matrix (U : UnitaryOperator (Qubits n))
    (p : ℝ × ℝ) :
    (qppYZZYZStepCircuit U p).matrix =
      UnitaryOperator.controlledQubits U *
        (rotYOp p.1 * rotZStdOp p.2).tensor
          (1 : UnitaryOperator (Qubits n)) := by
  apply Subtype.ext
  simp [qppYZZYZStepCircuit]

/-- One typed source-aligned alternating QPP step. -/
def qppAlternatingStepCircuit (U : UnitaryOperator (Qubits n)) (j : ℕ)
    (p : ℝ × ℝ) : UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.seq
    (qppLiftProcessingGate n (qppProcessingPairGate p)
      (qppProcessingPairGate_physical_idx p))
    (qppAlternatingOracleGate U j)

/-- The metadata-free unitary derived from the same typed step circuit. -/
def qppAlternatingStepGate (U : UnitaryOperator (Qubits n)) (j : ℕ)
    (p : ℝ × ℝ) : UnitaryOperator (Qubits (1 + n)) :=
  (qppAlternatingStepCircuit U j p).matrix

/-- Operator semantics of the lifted initial processing gate. -/
@[simp] theorem qppAlternatingInitialGate_operator
    (n : ℕ) (φ θ₀ φ₀ : ℝ) :
    ((qppAlternatingInitialGate n φ θ₀ φ₀).matrix :
      HilbertOperator (Qubits (1 + n))) =
      HilbertOperator.tensor
        ((qspYZZYZInitialCircuit φ θ₀ φ₀).matrix : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits n)) := by
  simp [qppAlternatingInitialGate]

/-- Operator semantics of one typed alternating QPP step. -/
@[simp] theorem qppAlternatingStepGate_operator
    (U : UnitaryOperator (Qubits n)) (j : ℕ) (p : ℝ × ℝ) :
    (qppAlternatingStepGate U j p : HilbertOperator (Qubits (1 + n))) =
      ((qppAlternatingOracleGate U j).matrix : HilbertOperator (Qubits (1 + n))) *
        ((qppLiftProcessingGate n (qppProcessingPairGate p)
          (qppProcessingPairGate_physical_idx p)).matrix :
          HilbertOperator (Qubits (1 + n))) := rfl

/-! ### Direct YZZYZ QPP and eigenspace decomposition -/

/-- The mathematical YZZYZ QPP word.  Its typed realization below carries all
execution and resource metadata. -/
def qppYZZYZ (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : UnitaryOperator (Qubits (1 + n)) :=
  ps.foldl
    (fun W p =>
      W * (UnitaryOperator.controlledQubits U *
        (rotYOp p.1 * rotZStdOp p.2).tensor
          (1 : UnitaryOperator (Qubits n))))
    ((rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀)).tensor
      (1 : UnitaryOperator (Qubits n)))

@[simp] theorem qppYZZYZ_nil (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    qppYZZYZ U φ θ₀ φ₀ [] =
      (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀)).tensor
        (1 : UnitaryOperator (Qubits n)) := rfl

theorem qppYZZYZ_concat (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    qppYZZYZ U φ θ₀ φ₀ (ps ++ [p]) =
      qppYZZYZ U φ θ₀ φ₀ ps *
        (UnitaryOperator.controlledQubits U *
          (rotYOp p.1 * rotZStdOp p.2).tensor
            (1 : UnitaryOperator (Qubits n))) := by
  simp [qppYZZYZ, List.foldl_append]

/-- Typed circuit whose matrix is the YZZYZ QPP word. -/
def qppYZZYZCircuit (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : UnitaryCircuit (Qubits (1 + n)) :=
  ps.foldl
    (fun accumulated p => UnitaryCircuit.seq (qppYZZYZStepCircuit U p) accumulated)
    (qppAlternatingInitialCircuit n φ θ₀ φ₀)

@[simp] theorem qppYZZYZCircuit_matrix (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    (qppYZZYZCircuit U φ θ₀ φ₀ ps).matrix = qppYZZYZ U φ θ₀ φ₀ ps := by
  induction ps using List.reverseRecOn with
  | nil =>
      apply Subtype.ext
      simp [qppYZZYZCircuit, qppYZZYZ, qppAlternatingInitialCircuit,
        qppAlternatingInitialGate]
  | append_singleton ps p ih =>
      rw [show qppYZZYZCircuit U φ θ₀ φ₀ (ps ++ [p]) =
          UnitaryCircuit.seq (qppYZZYZStepCircuit U p)
            (qppYZZYZCircuit U φ θ₀ φ₀ ps) by
        simp [qppYZZYZCircuit, List.foldl_append]]
      apply Subtype.ext
      change
        ((qppYZZYZCircuit U φ θ₀ φ₀ ps).matrix :
            HilbertOperator (Qubits (1 + n))) *
          ((qppYZZYZStepCircuit U p).matrix :
            HilbertOperator (Qubits (1 + n))) =
        (qppYZZYZ U φ θ₀ φ₀ (ps ++ [p]) :
          HilbertOperator (Qubits (1 + n)))
      rw [ih, qppYZZYZStepCircuit_matrix, qppYZZYZ_concat]
      rfl

/-- Eigenspace decomposition of direct-controlled YZZYZ QPP. -/
theorem QPP.eigenstate_decomposition (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (ψ : HilbertVector (Qubits 1)) :
    (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ ps.length •
          HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ)
        (u : HilbertVector (Qubits n)) := by
  induction ps using List.reverseRecOn generalizing ψ with
  | nil =>
      rw [qppYZZYZ_nil, qspYZZYZ_nil, List.length_nil, pow_zero, one_smul,
        UnitaryOperator.tensor_applyVec_tensor, UnitaryOperator.one_applyVec]
      change HilbertVector.tensor
          (HilbertOperator.applyVec
            ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
              ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
                (rotZStdOp φ₀ : HilbertOperator (Qubits 1)))) ψ)
          (u : HilbertVector (Qubits n)) =
        HilbertVector.tensor
          (HilbertOperator.applyVec
            ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
              ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
                (rotZStdOp φ₀ : HilbertOperator (Qubits 1)))) ψ)
          (u : HilbertVector (Qubits n))
      rfl
  | append_singleton ps p ih =>
      rw [qppYZZYZ_concat, UnitaryOperator.mul_applyVec,
        UnitaryOperator.mul_applyVec, UnitaryOperator.tensor_applyVec_tensor,
        UnitaryOperator.one_applyVec]
      have hsignal :
          (UnitaryOperator.controlledQubits U).applyVec
              (HilbertVector.tensor
                ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ)
                (u : HilbertVector (Qubits n))) =
            HilbertVector.tensor
              (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
                (rotZStdOp θ).applyVec
                  ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ))
              (u : HilbertVector (Qubits n)) := by
        exact QPP.eigenstate_reductionVec U u θ hu
          ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ)
      rw [hsignal, ih, qspYZZYZ_concat, List.length_append,
        List.length_singleton]
      congr 1
      change
        (Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ ps.length •
            HilbertOperator.applyVec
              (qspYZZYZ φ θ₀ φ₀ ps θ : HilbertOperator (Qubits 1))
              (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
                HilbertOperator.applyVec
                  (rotZStdOp θ : HilbertOperator (Qubits 1))
                  (HilbertOperator.applyVec
                    ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                      (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)) =
          (Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ (ps.length + 1) •
            HilbertOperator.applyVec
              ((qspYZZYZ φ θ₀ φ₀ ps θ : HilbertOperator (Qubits 1)) *
                ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
                  ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                    (rotZStdOp p.2 : HilbertOperator (Qubits 1))))) ψ
      rw [HilbertOperator.applyVec_smul, smul_smul, ← pow_succ,
        ← HilbertOperator.mul_applyVec, ← HilbertOperator.mul_applyVec, mul_assoc]

/-- Every admissible single-qubit QSP transform is realized on an eigenspace. -/
theorem QPP.realizes_target (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n))
    (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧
      ∀ ψ : NormalizedVector (Qubits 1),
        (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
            (HilbertVector.tensor (ψ : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L •
              HilbertOperator.applyVec (qspMatYZ L A B θ)
                (ψ : HilbertVector (Qubits 1)))
            (u : HilbertVector (Qubits n)) := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ :=
    (TrigonometricQuantumSignalProcessing.main L A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, fun ψ => ?_⟩
  rw [QPP.eigenstate_decomposition U u θ hu, hlen]
  have happly := congrArg
    (fun M : HilbertOperator (Qubits 1) =>
      HilbertOperator.applyVec M (ψ : HilbertVector (Qubits 1))) (hmat θ)
  exact congrArg
    (fun v : HilbertVector (Qubits 1) =>
      HilbertVector.tensor
        ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L • v)
        (u : HilbertVector (Qubits n))) happly

/-! ### Exact resources of the typed words -/

private theorem qppCircuitFold_resourceCounts {R : Register} {α : Type}
    (n : ℕ) (schedule : List α) (start : UnitaryCircuit R)
    (step : α → UnitaryCircuit R) (queries rotations : ℕ)
    (hstartQueries : qppControlledOracleQueryCount n start.eventCost = queries)
    (hstartRotations : qppRotationCount start.eventCost = rotations)
    (hstepQueries : ∀ item,
      qppControlledOracleQueryCount n (step item).eventCost = 1)
    (hstepRotations : ∀ item, qppRotationCount (step item).eventCost = 2) :
    qppControlledOracleQueryCount n
        (schedule.foldl
          (fun accumulated item => UnitaryCircuit.seq (step item) accumulated) start).eventCost =
        queries + schedule.length ∧
      qppRotationCount
        (schedule.foldl
          (fun accumulated item => UnitaryCircuit.seq (step item) accumulated) start).eventCost =
        rotations + 2 * schedule.length := by
  induction schedule generalizing start queries rotations with
  | nil => simpa using And.intro hstartQueries hstartRotations
  | cons item tail ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hq : qppControlledOracleQueryCount n
          (UnitaryCircuit.seq (step item) start).eventCost = queries + 1 := by
        simp [hstepQueries item, hstartQueries, Nat.add_comm]
      have hr : qppRotationCount
          (UnitaryCircuit.seq (step item) start).eventCost = rotations + 2 := by
        simp [hstepRotations item, hstartRotations, Nat.add_comm]
      have hrest := ih (UnitaryCircuit.seq (step item) start) (queries + 1)
        (rotations + 2) hq hr
      constructor <;> omega

private theorem qppInitialCircuit_counts (n : ℕ) (φ θ₀ φ₀ : ℝ) :
    qppControlledOracleQueryCount n
        (qppAlternatingInitialCircuit n φ θ₀ φ₀).eventCost = 0 ∧
      qppRotationCount (qppAlternatingInitialCircuit n φ θ₀ φ₀).eventCost = 3 := by
  simp [qppAlternatingInitialCircuit, qppAlternatingInitialGate,
    qppLiftProcessingGate, qspYZZYZInitialCircuit,
    qppControlledOracleQueryCount,
    qppRotationCount, qppControlledOracleEvent, qppOracleEvent,
    qppRotationYEvent, qppRotationZEvent,
    ResourcePool.count, ResourcePool.singleton, Resource.GateLabel.declared]

private theorem qppYZZYZStepCircuit_counts (U : UnitaryOperator (Qubits n))
    (p : ℝ × ℝ) :
    qppControlledOracleQueryCount n
        (qppYZZYZStepCircuit U p).eventCost = 1 ∧
      qppRotationCount (qppYZZYZStepCircuit U p).eventCost = 2 := by
  simp [qppYZZYZStepCircuit, qppControlledOracleGate, qppOracleGate,
    qppLiftProcessingGate, qppProcessingPairGate,
    qppControlledOracleQueryCount,
    qppRotationCount, qppControlledOracleEvent, qppOracleEvent,
    qppRotationYEvent, qppRotationZEvent,
    qppOracleLeaf, qppOracleLeafAt,
    ResourcePool.count, ResourcePool.singleton, Resource.GateLabel.declared,
    ResourcePool.controlForDimension, ResourcePool.controlForDimensions,
    Resource.Event.controlForDimension, Resource.Event.controlForDimensions,
    Resource.QuantumSubroutineLabel.controlForDimensions]

/-- Exact query and rotation multiplicities derived from the direct YZZYZ
circuit itself. -/
theorem qppYZZYZCircuit_resources_exact (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    QPP.HasExactResourceCounts n ps.length
      (qppYZZYZCircuit U φ θ₀ φ₀ ps).eventCost := by
  rcases qppInitialCircuit_counts n φ θ₀ φ₀ with ⟨hq, hr⟩
  have h := qppCircuitFold_resourceCounts n ps
    (qppAlternatingInitialCircuit n φ θ₀ φ₀)
    (qppYZZYZStepCircuit U) 0 3 hq hr
    (fun p => (qppYZZYZStepCircuit_counts U p).1)
    (fun p => (qppYZZYZStepCircuit_counts U p).2)
  refine ⟨?_, ?_⟩
  · simpa [qppYZZYZCircuit] using h.1
  · simpa [qppYZZYZCircuit] using (show 3 + 2 * ps.length =
      2 * ps.length + 3 by omega ▸ h.2)

/-- The direct YZZYZ correctness theorem paired with resources from the same
typed circuit. -/
theorem qpp_realizes_target_with_resources (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧
      (∀ ψ : NormalizedVector (Qubits 1),
        (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
            (HilbertVector.tensor (ψ : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L •
              HilbertOperator.applyVec (qspMatYZ L A B θ)
                (ψ : HilbertVector (Qubits 1)))
            (u : HilbertVector (Qubits n))) ∧
      QPP.HasExactResourceCounts n L
        (qppYZZYZCircuit U φ θ₀ φ₀ ps).eventCost := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hcorrect⟩ :=
    QPP.realizes_target U u θ hu L A B h
  refine ⟨φ, θ₀, φ₀, ps, hlen, hcorrect, ?_⟩
  simpa [hlen] using qppYZZYZCircuit_resources_exact U φ θ₀ φ₀ ps

/-! ### Alternating source convention -/

/-- Typed circuit for the alternating controlled-`U†` / controlled-`U` word. -/
def qppAlternatingControlledCircuit (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : UnitaryCircuit (Qubits (1 + n)) :=
  ps.zipIdx.foldl
    (fun accumulated jp =>
      UnitaryCircuit.seq (qppAlternatingStepCircuit U jp.2 jp.1) accumulated)
    (qppAlternatingInitialCircuit n φ θ₀ φ₀)

/-- The empty alternating schedule evaluates the typed initial circuit. -/
@[simp] theorem qppAlternatingControlledCircuit_nil_matrix
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    (qppAlternatingControlledCircuit U φ θ₀ φ₀ []).matrix =
      (qppAlternatingInitialGate n φ θ₀ φ₀).matrix := rfl

private theorem qppAlternatingStepCircuit_counts (U : UnitaryOperator (Qubits n))
    (j : ℕ) (p : ℝ × ℝ) :
    qppControlledOracleQueryCount n
        (qppAlternatingStepCircuit U j p).eventCost = 1 ∧
      qppRotationCount (qppAlternatingStepCircuit U j p).eventCost = 2 := by
  by_cases hj : j % 2 = 0 <;>
    simp [qppAlternatingStepCircuit, qppAlternatingOracleGate, hj,
      qppOracleGate, qppLiftProcessingGate, qppProcessingPairGate,
      qppControlledOracleQueryCount, qppControlledOracleEvent, qppOracleEvent,
      qppRotationCount, qppRotationYEvent, qppRotationZEvent,
      qppOracleLeaf, qppOracleLeafAt,
      ResourcePool.count, ResourcePool.singleton, Resource.GateLabel.declared,
      ResourcePool.controlForDimension, ResourcePool.controlForDimensions,
      Resource.Event.controlForDimension, Resource.Event.controlForDimensions,
      Resource.QuantumSubroutineLabel.controlForDimensions]

/-- Exact pooled query and rotation multiplicities from the alternating circuit
itself. -/
theorem qppAlternatingControlledCircuit_resources_exact
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    QPP.HasExactResourceCounts n ps.length
      (qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).eventCost := by
  rcases qppInitialCircuit_counts n φ θ₀ φ₀ with ⟨hq, hr⟩
  have h := qppCircuitFold_resourceCounts n ps.zipIdx
    (qppAlternatingInitialCircuit n φ θ₀ φ₀)
    (fun jp => qppAlternatingStepCircuit U jp.2 jp.1) 0 3 hq hr
    (fun jp => (qppAlternatingStepCircuit_counts U jp.2 jp.1).1)
    (fun jp => (qppAlternatingStepCircuit_counts U jp.2 jp.1).2)
  have hr := h.2
  rw [List.length_zipIdx] at hr
  refine ⟨?_, ?_⟩
  · simpa [qppAlternatingControlledCircuit, List.length_zipIdx] using h.1
  · simpa [qppAlternatingControlledCircuit, List.length_zipIdx] using
      (show 3 + 2 * ps.length = 2 * ps.length + 3 by omega ▸ hr)

/-! ### Alternating eigenspace semantics -/

/-- One source-aligned alternating step reduces to the corresponding one-qubit
phase signal on an eigenstate. -/
theorem QPP.qppAlternatingStep_eigenstate_reductionVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (j : ℕ) (p : ℝ × ℝ) (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingStepGate U j p).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        (HilbertOperator.applyVec
          (if j % 2 = 0 then
            (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1))
          else (phaseGateOp θ : HilbertOperator (Qubits 1)))
          (HilbertOperator.applyVec
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ))
        (u : HilbertVector (Qubits n)) := by
  change UnitaryCircuit.applyVec (qppAlternatingStepCircuit U j p)
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) = _
  rw [qppAlternatingStepCircuit, UnitaryCircuit.applyVec_seq]
  change (qppAlternatingOracleGate U j).matrix.applyVec
      ((qppLiftProcessingGate n (qppProcessingPairGate p)
        (qppProcessingPairGate_physical_idx p)).matrix.applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n)))) = _
  have hprocessing :
      (qppLiftProcessingGate n (qppProcessingPairGate p)
        (qppProcessingPairGate_physical_idx p)).matrix.applyVec
          (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
        HilbertVector.tensor
          (HilbertOperator.applyVec
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)
          (u : HilbertVector (Qubits n)) := by
    change HilbertOperator.applyVec
        ((qppLiftProcessingGate n (qppProcessingPairGate p)
          (qppProcessingPairGate_physical_idx p)).matrix :
          HilbertOperator (Qubits (1 + n)))
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) = _
    rw [qppLiftProcessingGate_matrix, qppProcessingPairGate_matrix,
      HilbertOperator.tensor_applyVec_tensor, HilbertOperator.one_applyVec]
  rw [hprocessing]
  by_cases hj : j % 2 = 0
  · rw [if_pos hj]
    change (qppAlternatingOracleGate U j).matrix.applyVec
        (HilbertVector.tensor
          (HilbertOperator.applyVec
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)
          (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        ((phaseGateOnZeroOp (-θ)).applyVec
          (HilbertOperator.applyVec
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ))
        (u : HilbertVector (Qubits n))
    rw [qppAlternatingOracleGate_matrix_of_even U hj]
    exact
      QPP.controlledOnZero_conjTranspose_apply_eigenstate_phaseVec
        U u θ hu
        (HilbertOperator.applyVec
          ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
            (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)
  · rw [if_neg hj]
    change (qppAlternatingOracleGate U j).matrix.applyVec
        (HilbertVector.tensor
          (HilbertOperator.applyVec
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)
          (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        ((phaseGateOp θ).applyVec
          (HilbertOperator.applyVec
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ))
        (u : HilbertVector (Qubits n))
    rw [qppAlternatingOracleGate_matrix_of_odd U hj]
    exact controlled_apply_eigenstate_phaseVec U u θ hu
        (HilbertOperator.applyVec
          ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
            (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)

/-- The one-qubit signal step induced on an eigenspace. -/
def qppAlternatingSignalStep (θ : ℝ) (j : ℕ) (p : ℝ × ℝ) :
    UnitaryOperator (Qubits 1) :=
  (if j % 2 = 0 then
      phaseGateOnZeroOp (-θ)
    else phaseGateOp θ) *
    (rotYOp p.1 * rotZStdOp p.2)

/-- Global phase of the `j`-th alternating signal block. -/
def qppAlternatingStepScalar (θ : ℝ) (j : ℕ) : ℂ :=
  if j % 2 = 0 then Complex.exp (-(θ / 2 : ℝ) * Complex.I)
  else Complex.exp ((θ / 2 : ℝ) * Complex.I)

/-- Product of alternating-step global phases, beginning at `start`. -/
def qppAlternatingSignalScalarFrom (θ : ℝ) (start : ℕ) :
    List (ℝ × ℝ) → ℂ
  | [] => 1
  | _ :: rest => qppAlternatingStepScalar θ start *
      qppAlternatingSignalScalarFrom θ (start + 1) rest

/-- Total global phase of a zero-based alternating signal sequence. -/
def qppAlternatingSignalScalar (θ : ℝ) (ps : List (ℝ × ℝ)) : ℂ :=
  qppAlternatingSignalScalarFrom θ 0 ps

theorem QPP.qppAlternatingSignalStep_applyVec_eq_scalar_yzzyz_step
    (θ : ℝ) (j : ℕ) (p : ℝ × ℝ) (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingSignalStep θ j p).applyVec ψ =
      qppAlternatingStepScalar θ j •
        HilbertOperator.applyVec
          ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1)))) ψ := by
  rw [qppAlternatingSignalStep, UnitaryOperator.mul_applyVec]
  by_cases hj : j % 2 = 0
  · rw [if_pos hj, qppAlternatingStepScalar, if_pos hj]
    change (phaseGateOnZeroOp (-θ)).applyVec
        ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ * (rotYOp p.1 * rotZStdOp p.2)).applyVec ψ
    have hnegHalf :
        Complex.exp (((-θ) / 2 : ℝ) * Complex.I) =
          Complex.exp (-(θ / 2 : ℝ) * Complex.I) := by
      congr 1
      push_cast
      ring_nf
    calc
      _ = Complex.exp (((-θ) / 2 : ℝ) * Complex.I) •
          (rotZStdOp θ).applyVec
            ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) := by
        rw [hnegHalf]
        exact qpp_phaseGateOnZeroOp_applyVec_eq_smul_rotZStdOp θ _
      _ = Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
          (rotZStdOp θ).applyVec
            ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) := by rw [hnegHalf]
      _ = _ := congrArg
        (fun v : HilbertVector (Qubits 1) =>
          Complex.exp (-(θ / 2 : ℝ) * Complex.I) • v)
        (UnitaryOperator.mul_applyVec (rotZStdOp θ)
          (rotYOp p.1 * rotZStdOp p.2) ψ).symm
  · rw [if_neg hj, qppAlternatingStepScalar, if_neg hj]
    change (phaseGateOp θ).applyVec
        ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ * (rotYOp p.1 * rotZStdOp p.2)).applyVec ψ
    calc
      _ = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
          (rotZStdOp θ).applyVec
            ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) :=
        qpp_phaseGateOp_applyVec_eq_smul_rotZStdOp θ _
      _ = _ := congrArg
        (fun v : HilbertVector (Qubits 1) =>
          Complex.exp ((θ / 2 : ℝ) * Complex.I) • v)
        (UnitaryOperator.mul_applyVec (rotZStdOp θ)
          (rotYOp p.1 * rotZStdOp p.2) ψ).symm

/-- Alternating one-qubit signal word on one eigenphase. -/
def qppAlternatingSignalGate (θ φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : UnitaryOperator (Qubits 1) :=
  ps.zipIdx.foldl
    (fun W jp => W * qppAlternatingSignalStep θ jp.2 jp.1)
    (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀))

theorem qppAlternatingSignalGate_eq_foldlIdx
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    qppAlternatingSignalGate θ φ θ₀ φ₀ ps =
      ps.foldlIdx (fun j W p => W * qppAlternatingSignalStep θ j p)
        (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀)) 0 := by
  rw [qppAlternatingSignalGate, List.foldlIdx_eq_foldl_zipIdx]

@[simp]
theorem coe_qppAlternatingSignalGate (θ φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps :
      HilbertOperator (Qubits 1)) =
      ps.zipIdx.foldl
        (fun W jp => W *
          (qppAlternatingSignalStep θ jp.2 jp.1 :
            HilbertOperator (Qubits 1)))
        ((rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀) :
          UnitaryOperator (Qubits 1)) : HilbertOperator (Qubits 1)) := by
  exact unitaryFold_coe ps.zipIdx
    (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀))
    (fun jp => qppAlternatingSignalStep θ jp.2 jp.1)

theorem QPP.qppAlternatingSignal_fold_applyVec_eq_scalar_yzzyz_fold
    (θ : ℝ) (ps : List (ℝ × ℝ)) (start : ℕ)
    (W Q : HilbertOperator (Qubits 1)) (c : ℂ)
    (hW : ∀ ψ : HilbertVector (Qubits 1),
      HilbertOperator.applyVec W ψ = c • HilbertOperator.applyVec Q ψ)
    (ψ : HilbertVector (Qubits 1)) :
    HilbertOperator.applyVec
        (ps.foldlIdx
          (fun j W p => W *
            (qppAlternatingSignalStep θ j p : HilbertOperator (Qubits 1)))
          W start) ψ =
      (c * qppAlternatingSignalScalarFrom θ start ps) •
        HilbertOperator.applyVec
          (ps.foldl
            (fun Q p => Q *
              ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
                ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                  (rotZStdOp p.2 : HilbertOperator (Qubits 1))))) Q) ψ := by
  induction ps generalizing start W Q c ψ with
  | nil => simpa [qppAlternatingSignalScalarFrom] using hW ψ
  | cons p ps ih =>
      simp only [List.foldlIdx_cons, List.foldl_cons,
        qppAlternatingSignalScalarFrom]
      have hnext := ih (start + 1)
        (W * (qppAlternatingSignalStep θ start p :
          HilbertOperator (Qubits 1)))
        (Q * ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
          ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
            (rotZStdOp p.2 : HilbertOperator (Qubits 1)))))
        (c * qppAlternatingStepScalar θ start)
        (by
          intro ψ'
          rw [HilbertOperator.mul_applyVec]
          change HilbertOperator.applyVec W
            ((qppAlternatingSignalStep θ start p).applyVec ψ') = _
          rw [QPP.qppAlternatingSignalStep_applyVec_eq_scalar_yzzyz_step,
            HilbertOperator.applyVec_smul, hW, HilbertOperator.mul_applyVec]
          rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
            HilbertOperator.mul_applyVec]
          simp only [smul_smul]
          rw [mul_comm (qppAlternatingStepScalar θ start) c]
          exact congrArg
            (fun v : HilbertVector (Qubits 1) =>
              (c * qppAlternatingStepScalar θ start) •
                HilbertOperator.applyVec Q
                  (HilbertOperator.applyVec
                    (rotZStdOp θ : HilbertOperator (Qubits 1)) v))
            (HilbertOperator.mul_applyVec
              (rotYOp p.1 : HilbertOperator (Qubits 1))
              (rotZStdOp p.2 : HilbertOperator (Qubits 1)) ψ').symm) ψ
      simpa [mul_assoc] using hnext

theorem qppAlternatingStepScalar_mul_succ (θ : ℝ) (j : ℕ) :
    qppAlternatingStepScalar θ j * qppAlternatingStepScalar θ (j + 1) = 1 := by
  unfold qppAlternatingStepScalar
  by_cases hj : j % 2 = 0
  · have hj1 : (j + 1) % 2 ≠ 0 := by omega
    rw [if_pos hj, if_neg hj1, ← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero]
  · have hj1 : (j + 1) % 2 = 0 := by omega
    rw [if_neg hj, if_pos hj1, ← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero]

theorem qppAlternatingSignalScalarFrom_eq_if_length_mod
    (θ : ℝ) (ps : List (ℝ × ℝ)) (start : ℕ) :
    qppAlternatingSignalScalarFrom θ start ps =
      if ps.length % 2 = 0 then 1 else qppAlternatingStepScalar θ start := by
  induction ps generalizing start with
  | nil => simp [qppAlternatingSignalScalarFrom]
  | cons p rest ih =>
      rw [qppAlternatingSignalScalarFrom, ih (start + 1)]
      by_cases hrest : rest.length % 2 = 0
      · have htotal : (rest.length + 1) % 2 ≠ 0 := by omega
        simp [hrest, htotal]
      · have htotal : (rest.length + 1) % 2 = 0 := by omega
        simp [hrest, htotal, qppAlternatingStepScalar_mul_succ θ start]

theorem qppAlternatingSignalScalar_eq_one_of_even_length
    (θ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ}
    (h : ps.length = 2 * L) : qppAlternatingSignalScalar θ ps = 1 := by
  have hmod : ps.length % 2 = 0 := by rw [h]; omega
  simp [qppAlternatingSignalScalar,
    qppAlternatingSignalScalarFrom_eq_if_length_mod θ ps 0, hmod]

theorem QPP.qppAlternatingSignalGate_applyVec_eq_scalar_yzzyz
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ =
      qppAlternatingSignalScalar θ ps •
        HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ := by
  have h := QPP.qppAlternatingSignal_fold_applyVec_eq_scalar_yzzyz_fold
    θ ps 0
    ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
      ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
        (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))
    ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
      ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
        (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))
    (1 : ℂ) (by intro ψ'; simp) ψ
  change HilbertOperator.applyVec
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps : HilbertOperator (Qubits 1)) ψ = _
  rw [List.foldlIdx_eq_foldl_zipIdx] at h
  rw [coe_qppAlternatingSignalGate]
  change HilbertOperator.applyVec
      (ps.zipIdx.foldl
        (fun W jp => W *
          (qppAlternatingSignalStep θ jp.2 jp.1 : HilbertOperator (Qubits 1)))
        ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
          ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
            (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))) ψ =
    qppAlternatingSignalScalar θ ps •
      HilbertOperator.applyVec
        (ps.foldl
          (fun Q p => Q *
            ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
              ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                (rotZStdOp p.2 : HilbertOperator (Qubits 1)))))
          ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
            ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
              (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))) ψ
  simpa only [qppAlternatingSignalScalar, one_mul] using h

theorem QPP.qppAlternatingSignalGate_applyVec_eq_yzzyz_of_even_length
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ}
    (hps : ps.length = 2 * L) (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ =
      HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ := by
  rw [QPP.qppAlternatingSignalGate_applyVec_eq_scalar_yzzyz]
  rw [qppAlternatingSignalScalar_eq_one_of_even_length θ ps hps]
  simp

private theorem qppAlternatingControlledCircuit_algebraic_matrix
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    (qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix =
      ps.zipIdx.foldl
        (fun W jp => W *
          qppAlternatingStepGate U jp.2 jp.1)
        (qppAlternatingInitialGate n φ θ₀ φ₀).matrix := by
  rw [qppAlternatingControlledCircuit, circuitAlgebraicFold_matrix]
  rfl

/-- Source-aligned eigenspace decomposition of the alternating circuit. -/
theorem QPP.qppAlternating_eigenstate_decompositionVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (ψ : HilbertVector (Qubits 1)) :
    HilbertOperator.applyVec
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
          HilbertOperator (Qubits (1 + n)))
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        ((qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ)
        (u : HilbertVector (Qubits n)) := by
  let schedule := ps.zipIdx
  let initialSignal : HilbertOperator (Qubits 1) :=
    (rotZStdOp φ : HilbertOperator (Qubits 1)) *
      ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
        (rotZStdOp φ₀ : HilbertOperator (Qubits 1)))
  let initialGate : HilbertOperator (Qubits (1 + n)) :=
    qppAlternatingInitialGate n φ θ₀ φ₀
  have hfold : ∀ (schedule : List ((ℝ × ℝ) × ℕ))
      (W : HilbertOperator (Qubits (1 + n)))
      (S : HilbertOperator (Qubits 1)),
      (∀ ψ : HilbertVector (Qubits 1),
        HilbertOperator.applyVec W
            (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor (HilbertOperator.applyVec S ψ)
            (u : HilbertVector (Qubits n))) →
      ∀ ψ : HilbertVector (Qubits 1),
        HilbertOperator.applyVec
            (schedule.foldl
              (fun W jp => W *
                (qppAlternatingStepGate U jp.2 jp.1 :
                  HilbertOperator (Qubits (1 + n)))) W)
            (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            (HilbertOperator.applyVec
              (schedule.foldl
                (fun S jp => S *
                  (qppAlternatingSignalStep θ jp.2 jp.1 :
                    HilbertOperator (Qubits 1))) S) ψ)
            (u : HilbertVector (Qubits n)) := by
    intro schedule
    induction schedule with
    | nil => intro W S hbase ψ; exact hbase ψ
    | cons jp rest ih =>
        intro W S hbase ψ
        apply ih
        intro ψ'
        rw [HilbertOperator.mul_applyVec]
        have hstep := QPP.qppAlternatingStep_eigenstate_reductionVec
          U u θ hu jp.2 jp.1 ψ'
        change HilbertOperator.applyVec
            (qppAlternatingStepGate U jp.2 jp.1 :
              HilbertOperator (Qubits (1 + n)))
            (HilbertVector.tensor ψ' (u : HilbertVector (Qubits n))) = _ at hstep
        rw [show HilbertOperator.applyVec
            (qppAlternatingStepGate U jp.2 jp.1 :
              HilbertOperator (Qubits (1 + n)))
              (HilbertVector.tensor ψ' (u : HilbertVector (Qubits n))) =
            HilbertVector.tensor
              (HilbertOperator.applyVec
                (qppAlternatingSignalStep θ jp.2 jp.1 :
                  HilbertOperator (Qubits 1)) ψ')
              (u : HilbertVector (Qubits n)) by
          by_cases hj : jp.2 % 2 = 0
          · calc
              _ = HilbertVector.tensor
                    (HilbertOperator.applyVec
                      (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1))
                      (HilbertOperator.applyVec
                        ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                          (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ'))
                    (u : HilbertVector (Qubits n)) := by
                      simpa only [if_pos hj] using hstep
                _ = _ := by
                      rw [qppAlternatingSignalStep, if_pos hj]
                      exact congrArg
                        (fun v : HilbertVector (Qubits 1) =>
                          HilbertVector.tensor v (u : HilbertVector (Qubits n)))
                        (HilbertOperator.mul_applyVec
                          (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1))
                          ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                            (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ').symm
          · calc
              _ = HilbertVector.tensor
                    (HilbertOperator.applyVec
                      (phaseGateOp θ : HilbertOperator (Qubits 1))
                      (HilbertOperator.applyVec
                        ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                          (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ'))
                    (u : HilbertVector (Qubits n)) := by
                      simpa only [if_neg hj] using hstep
                _ = _ := by
                      rw [qppAlternatingSignalStep, if_neg hj]
                      exact congrArg
                        (fun v : HilbertVector (Qubits 1) =>
                          HilbertVector.tensor v (u : HilbertVector (Qubits n)))
                        (HilbertOperator.mul_applyVec
                          (phaseGateOp θ : HilbertOperator (Qubits 1))
                          ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                            (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ').symm]
        rw [hbase, HilbertOperator.mul_applyVec]
  have hbase : ∀ ψ : HilbertVector (Qubits 1),
      HilbertOperator.applyVec initialGate
          (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
        HilbertVector.tensor (HilbertOperator.applyVec initialSignal ψ)
          (u : HilbertVector (Qubits n)) := by
    intro ψ
    dsimp [initialGate, initialSignal]
    rw [qppAlternatingInitialGate_operator,
      qspYZZYZInitialCircuit_matrix,
      HilbertOperator.tensor_applyVec_tensor,
      HilbertOperator.one_applyVec]
  change HilbertOperator.applyVec
      ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
        HilbertOperator (Qubits (1 + n)))
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
    HilbertVector.tensor
      (HilbertOperator.applyVec
        (qppAlternatingSignalGate θ φ θ₀ φ₀ ps :
          HilbertOperator (Qubits 1)) ψ)
      (u : HilbertVector (Qubits n))
  rw [qppAlternatingControlledCircuit_algebraic_matrix]
  rw [unitaryFold_coe, coe_qppAlternatingSignalGate]
  let controlledFold : HilbertOperator (Qubits (1 + n)) :=
    ps.zipIdx.foldl
      (fun W jp => W *
        (qppAlternatingStepGate U jp.2 jp.1 :
          HilbertOperator (Qubits (1 + n))))
      ((qppAlternatingInitialGate n φ θ₀ φ₀).matrix :
        HilbertOperator (Qubits (1 + n)))
  let signalFold : HilbertOperator (Qubits 1) :=
    ps.zipIdx.foldl
      (fun S jp => S *
        (qppAlternatingSignalStep θ jp.2 jp.1 : HilbertOperator (Qubits 1)))
      ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
        ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
          (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))
  change HilbertOperator.applyVec controlledFold
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
    HilbertVector.tensor (HilbertOperator.applyVec signalFold ψ)
      (u : HilbertVector (Qubits n))
  have h := hfold schedule initialGate initialSignal hbase ψ
  change HilbertOperator.applyVec controlledFold
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
    HilbertVector.tensor (HilbertOperator.applyVec signalFold ψ)
      (u : HilbertVector (Qubits n)) at h
  exact h

theorem QPP.qppAlternating_eigenstate_decomposition_evenVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ}
    (hps : ps.length = 2 * L) (ψ : HilbertVector (Qubits 1)) :
    HilbertOperator.applyVec
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
          HilbertOperator (Qubits (1 + n)))
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        (HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ)
        (u : HilbertVector (Qubits n)) := by
  rw [QPP.qppAlternating_eigenstate_decompositionVec U u θ hu]
  rw [QPP.qppAlternatingSignalGate_applyVec_eq_yzzyz_of_even_length
    θ φ θ₀ φ₀ ps hps]

theorem QPP.alternating_realizes_target_on_eigenstate
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair (2 * L) A B) :
    ∃ φ θ₀ φ₀ : ℝ, ∃ ps : List (ℝ × ℝ), ps.length = 2 * L ∧
      ∀ ψ : NormalizedVector (Qubits 1),
        HilbertOperator.applyVec
            ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
              HilbertOperator (Qubits (1 + n)))
            (HilbertVector.tensor (ψ : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            (HilbertOperator.applyVec (qspMatYZ (2 * L) A B θ)
              (ψ : HilbertVector (Qubits 1)))
            (u : HilbertVector (Qubits n)) := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ :=
    (TrigonometricQuantumSignalProcessing.main (2 * L) A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, fun ψ => ?_⟩
  rw [QPP.qppAlternating_eigenstate_decomposition_evenVec
    U u θ hu φ θ₀ φ₀ ps hlen]
  exact congrArg
    (fun v : HilbertVector (Qubits 1) =>
      HilbertVector.tensor v (u : HilbertVector (Qubits n)))
    (congrArg
      (fun M : HilbertOperator (Qubits 1) =>
        HilbertOperator.applyVec M (ψ : HilbertVector (Qubits 1))) (hmat θ))

namespace QPP.Signal

/-- Namespace-local view of the resource-carrying alternating QPP circuit. -/
abbrev qppAlternatingControlledCircuit (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : UnitaryCircuit (Qubits (1 + n)) :=
  QuantumAlg.QSP.MultiQubit.qppAlternatingControlledCircuit U φ θ₀ φ₀ ps

theorem alternating_realizes_target_on_eigenstate
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair (2 * L) A B) :
    ∃ φ θ₀ φ₀ : ℝ, ∃ ps : List (ℝ × ℝ), ps.length = 2 * L ∧
      ∀ ψ : NormalizedVector (Qubits 1),
        HilbertOperator.applyVec
            ((QuantumAlg.QSP.MultiQubit.qppAlternatingControlledCircuit
              U φ θ₀ φ₀ ps).matrix :
              HilbertOperator (Qubits (1 + n)))
            (HilbertVector.tensor (ψ : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            (HilbertOperator.applyVec (qspMatYZ (2 * L) A B θ)
              (ψ : HilbertVector (Qubits 1)))
            (u : HilbertVector (Qubits n)) :=
  QuantumAlg.QSP.MultiQubit.QPP.alternating_realizes_target_on_eigenstate
    U u θ hu L A B h

end QPP.Signal

end

end QSP.MultiQubit

end QuantumAlg

end
