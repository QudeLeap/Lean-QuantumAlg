/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Gates
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
public import QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Core.Algorithm.QuantumState
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Util.Complex
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Util.PMF
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import Mathlib.Algebra.Group.Defs

/-!
# Canonical quantum access for finite-cyclic discrete logarithms

The finite-cyclic DLP experiment owns one explicit three-register circuit.
Callers supply the two normalized range preparations and the encoded group
oracle as certified unitaries.  Their opaque subroutine events, the inverse-QFT
readout, and the terminal Z descriptor are all derived from this one stored
construction.  No classical recovery or legacy resource projection is part of
this quantum foundation.
-/

section

namespace QuantumAlg

open NormalizedVector

noncomputable section

namespace FiniteCyclicDLP
namespace Canonical

universe u

variable {G : Type u} [Group G]

/-- Three equal-width registers: two Fourier exponents and one encoded group
workspace. -/
public abbrev totalQubits (P : KnownOrderProblem G) : Nat :=
  orderWidth P + orderWidth P + orderWidth P

/-- Flatten the two exponent labels and the group-workspace label into the
canonical big-endian qubit basis. -/
public def tripleIndex {n : Nat}
    (left right workspace : Fin (2 ^ n)) : Fin (2 ^ (n + n + n)) :=
  prodEquiv (prodEquiv (left, right), workspace)

/-- Caller-provided realization of the exact finite range-uniform state
preparation.  The action equation fixes its zero column without assigning an
independent cost or depth. -/
structure UniformPreparationAccess (P : KnownOrderProblem G) where
  /-- Unitary applied independently to each exponent register. -/
  operator : UnitaryOperator (Qubits (orderWidth P))
  /-- Its all-zero column is the source range-uniform state. -/
  apply_zero :
    operator.apply (NormalizedVector.ket (R := Qubits (orderWidth P)) 0) =
      rangeUniformState P.order (orderWidth P) P.order_pos
        (order_le_fourierModulus P)

/-- Caller-provided encoded group oracle for
`|a,b,y⟩ ↦ |a,b,y g^a x^{-b}⟩`. -/
public structure UxAccess (P : KnownOrderProblem G) where
  /-- Fixed-width basis encoding of the ambient group elements. -/
  encode : G → Fin (2 ^ orderWidth P)
  /-- Encoded group basis vectors are distinct. -/
  encode_injective : Function.Injective encode
  /-- The certified black-box oracle unitary. -/
  operator : UnitaryOperator (Qubits (totalQubits P))
  /-- Source-faithful action on every encoded group basis state. -/
  basisAction :
    ∀ (left right : Fin (2 ^ orderWidth P)) (workspace : G),
      operator.apply
          (NormalizedVector.ket (R := Qubits (totalQubits P))
            (tripleIndex left right (encode workspace))) =
        NormalizedVector.ket (R := Qubits (totalQubits P))
          (tripleIndex left right
            (encode (workspace *
              P.toSourceScope.oracleMultiplier left.val right.val)))

/-- All caller-supplied quantum access required by the canonical experiment. -/
structure Access (P : KnownOrderProblem G) where
  /-- The reusable exact finite range preparation. -/
  uniform : UniformPreparationAccess P
  /-- The encoded DLP oracle. -/
  ux : UxAccess P

/-- Strict coordinate for one caller-supplied `U_unif` call. -/
def uniformPreparationSubroutineLabel (P : KnownOrderProblem G) :
    Resource.SubroutineLabel :=
  { family := "finite-cyclic-dlp"
    name := "U_unif"
    parameters := [P.order, orderWidth P] }

/-- Strict coordinate for one caller-supplied `U_x` call. -/
def uxSubroutineLabel (P : KnownOrderProblem G) : Resource.SubroutineLabel :=
  { family := "finite-cyclic-dlp"
    name := "U_x"
    parameters := [P.order, orderWidth P] }

/-- Event derived from the `U_unif` opaque-subroutine coordinate. -/
def uniformPreparationEvent (P : KnownOrderProblem G) :
    Resource.Event .quantum :=
  .quantumSubroutine (uniformPreparationSubroutineLabel P).quantum

/-- Event derived from the `U_x` opaque-subroutine coordinate. -/
def uxEvent (P : KnownOrderProblem G) : Resource.Event .quantum :=
  .quantumSubroutine (uxSubroutineLabel P).quantum

/-- Circuit-depth interpretation used by the public endpoint.  Gates and
opaque quantum subroutines take one layer; preparation, terminal measurement,
and classical post-processing remain fully counted events but contribute no
layers to the advertised maximal circuit depth. -/
def circuitDepthAssignment : Resource.Event .quantum → Nat
  | .gate _ => 1
  | .quantumSubroutine _ => 1
  | .preparation _ => 0
  | .measurement _ => 0
  | .classicalOperation _ => 0
  | .classicalSubroutine _ => 0

theorem uniformPreparationEvent_ne_uxEvent (P : KnownOrderProblem G) :
    uniformPreparationEvent P ≠ uxEvent P := by
  intro equality
  have labels := Resource.Event.quantumSubroutine.inj equality
  have bases := congrArg Resource.QuantumSubroutineLabel.base labels
  have names := congrArg Resource.SubroutineLabel.name bases
  simp [uniformPreparationSubroutineLabel, uxSubroutineLabel] at names

namespace EndpointDeclarations

/-- One caller-supplied range preparation at an actual exponent-register
placement. -/
def uniformPreparationLeafAt {P : KnownOrderProblem G} (A : Access P)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits (orderWidth P)) :=
  UnitaryLeaf.subroutine (uniformPreparationSubroutineLabel P)
    systemIdx A.uniform.operator

/-- One caller-supplied encoded DLP oracle at an actual full-register
placement. -/
def uxLeafAt {P : KnownOrderProblem G} (A : Access P)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits (totalQubits P)) :=
  UnitaryLeaf.subroutine (uxSubroutineLabel P) systemIdx A.ux.operator

end EndpointDeclarations

/-- The first `U_unif` instance, before it is paired with its shifted copy. -/
def uniformPreparationLeaf {P : KnownOrderProblem G} (A : Access P) :
    UnitaryLeaf (Qubits (orderWidth P)) :=
  EndpointDeclarations.uniformPreparationLeafAt A (List.range (orderWidth P))

/-- A one-register typed circuit for one opaque `U_unif` occurrence. -/
def uniformPreparationCircuit {P : KnownOrderProblem G} (A : Access P) :
    UnitaryCircuit (Qubits (orderWidth P)) :=
  UnitaryCircuit.ofLeaf (uniformPreparationLeaf A) List.nodup_range

@[simp] theorem uniformPreparationCircuit_physical_idx
    {P : KnownOrderProblem G} (A : Access P) :
    (uniformPreparationCircuit A).physical_idx = List.range (orderWidth P) :=
  rfl

@[simp] theorem uniformPreparationCircuit_eventCost
    {P : KnownOrderProblem G} (A : Access P) :
    (uniformPreparationCircuit A).eventCost =
      ResourcePool.singleton (uniformPreparationEvent P) :=
  rfl

@[simp] theorem uniformPreparationCircuit_eventDepth
    {P : KnownOrderProblem G} (A : Access P) :
    (uniformPreparationCircuit A).eventDepth =
      .atom (uniformPreparationEvent P) :=
  rfl

/-- Put two copies of an `n`-qubit circuit on consecutive physical intervals.
Their tensor construction is the actual parallel execution witness. -/
def pairConsecutiveCircuit {n : Nat} (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) : UnitaryCircuit (Qubits (n + n)) := by
  let right := UnitaryCircuit.shiftPhysicalIdx n body
  let layout : PhysicalLayout.DisjointMerge body.physical_idx right.physical_idx :=
    { left_nodup := body.physical_idx_nodup
      right_nodup := right.physical_idx_nodup
      disjoint := by
        rw [hphysical, UnitaryCircuit.shiftPhysicalIdx_physical_idx, hphysical,
          List.disjoint_left]
        intro index hleft hright
        obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hright
        have hleft_lt := List.mem_range.mp hleft
        have hsource_lt := List.mem_range.mp hsource
        omega }
  exact UnitaryCircuit.tensorQubits body right layout

@[simp] theorem pairConsecutiveCircuit_physical_idx {n : Nat}
    (body : UnitaryCircuit (Qubits n)) (hphysical : body.physical_idx = List.range n) :
    (pairConsecutiveCircuit body hphysical).physical_idx = List.range (n + n) := by
  simp only [pairConsecutiveCircuit, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, PhysicalLayout.DisjointMerge.merged_eq_append,
    UnitaryCircuit.shiftPhysicalIdx_physical_idx, hphysical]
  rw [← List.range'_eq_map_range]
  simpa [List.range_eq_range'] using
    (List.range'_append_1 (s := 0) (m := n) (n := n))

@[simp] theorem pairConsecutiveCircuit_eventCost {n : Nat}
    (body : UnitaryCircuit (Qubits n)) (hphysical : body.physical_idx = List.range n) :
    (pairConsecutiveCircuit body hphysical).eventCost =
      body.eventCost + body.eventCost := by
  simp only [pairConsecutiveCircuit, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.shiftPhysicalIdx_eventCost]

@[simp] theorem pairConsecutiveCircuit_eventDepth {n : Nat}
    (body : UnitaryCircuit (Qubits n)) (hphysical : body.physical_idx = List.range n) :
    (pairConsecutiveCircuit body hphysical).eventDepth =
      .tensor body.eventDepth body.eventDepth := by
  simp only [pairConsecutiveCircuit, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    UnitaryCircuit.shiftPhysicalIdx_eventDepth]

/-- Extend a two-exponent-register circuit by an untouched group workspace. -/
def withGroupWorkspace {n : Nat} (body : UnitaryCircuit (Qubits (n + n)))
    (hphysical : body.physical_idx = List.range (n + n)) :
    UnitaryCircuit (Qubits (n + n + n)) :=
  let workspace := UnitaryCircuit.identity (Qubits n) (List.range' (n + n) n)
    List.nodup_range'
  UnitaryCircuit.tensorQubits body workspace
    { left_nodup := body.physical_idx_nodup
      right_nodup := List.nodup_range'
      disjoint := by
        rw [hphysical, List.disjoint_left]
        intro index hleft hright
        have hlt := List.mem_range.mp hleft
        have hle := List.left_le_of_mem_range' hright
        omega }

@[simp] theorem withGroupWorkspace_physical_idx {n : Nat}
    (body : UnitaryCircuit (Qubits (n + n)))
    (hphysical : body.physical_idx = List.range (n + n)) :
    (withGroupWorkspace body hphysical).physical_idx = List.range (n + n + n) := by
  simp only [withGroupWorkspace, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, UnitaryCircuit.identity,
    PhysicalLayout.DisjointMerge.merged_eq_append, hphysical]
  simpa [List.range_eq_range'] using
    (List.range'_append_1 (s := 0) (m := n + n) (n := n))

@[simp] theorem withGroupWorkspace_eventCost {n : Nat}
    (body : UnitaryCircuit (Qubits (n + n)))
    (hphysical : body.physical_idx = List.range (n + n)) :
    (withGroupWorkspace body hphysical).eventCost = body.eventCost := by
  simp only [withGroupWorkspace, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]

@[simp] theorem withGroupWorkspace_eventDepth {n : Nat}
    (body : UnitaryCircuit (Qubits (n + n)))
    (hphysical : body.physical_idx = List.range (n + n)) :
    (withGroupWorkspace body hphysical).eventDepth =
      .tensor body.eventDepth .id := by
  simp only [withGroupWorkspace, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    UnitaryCircuit.identity_eventDepth]

/-- The two concurrent external `U_unif` calls, with the group workspace
untouched. -/
def uniformCircuit {P : KnownOrderProblem G} (A : Access P) :
    UnitaryCircuit (Qubits (totalQubits P)) :=
  withGroupWorkspace
    (pairConsecutiveCircuit (uniformPreparationCircuit A)
      (uniformPreparationCircuit_physical_idx A))
    (pairConsecutiveCircuit_physical_idx (uniformPreparationCircuit A)
      (uniformPreparationCircuit_physical_idx A))

@[simp] theorem uniformCircuit_physical_idx {P : KnownOrderProblem G}
    (A : Access P) :
    (uniformCircuit A).physical_idx = List.range (totalQubits P) := by
  simp [uniformCircuit, totalQubits]

@[simp] theorem uniformCircuit_eventCost {P : KnownOrderProblem G}
    (A : Access P) :
    (uniformCircuit A).eventCost =
      ResourcePool.singleton (uniformPreparationEvent P) +
        ResourcePool.singleton (uniformPreparationEvent P) := by
  rw [uniformCircuit, withGroupWorkspace_eventCost,
    pairConsecutiveCircuit_eventCost, uniformPreparationCircuit_eventCost]

@[simp] theorem uniformCircuit_eventDepth {P : KnownOrderProblem G}
    (A : Access P) :
    (uniformCircuit A).eventDepth =
      .tensor
        (.tensor (.atom (uniformPreparationEvent P))
          (.atom (uniformPreparationEvent P)))
        .id := by
  rw [uniformCircuit, withGroupWorkspace_eventDepth,
    pairConsecutiveCircuit_eventDepth, uniformPreparationCircuit_eventDepth]

/-- The caller-supplied `U_x` as one sealed full-register circuit leaf. -/
def uxCircuit {P : KnownOrderProblem G} (A : Access P) :
    UnitaryCircuit (Qubits (totalQubits P)) :=
  UnitaryCircuit.ofLeaf
    (EndpointDeclarations.uxLeafAt A (List.range (totalQubits P)))
    List.nodup_range

@[simp] theorem uxCircuit_physical_idx {P : KnownOrderProblem G}
    (A : Access P) :
    (uxCircuit A).physical_idx = List.range (totalQubits P) :=
  rfl

@[simp] theorem uxCircuit_eventCost {P : KnownOrderProblem G}
    (A : Access P) :
    (uxCircuit A).eventCost = ResourcePool.singleton (uxEvent P) :=
  rfl

@[simp] theorem uxCircuit_eventDepth {P : KnownOrderProblem G}
    (A : Access P) :
    (uxCircuit A).eventDepth = .atom (uxEvent P) :=
  rfl

/-- Two inverse QFTs in parallel on the exponent registers, with the group
workspace retained untouched. -/
private theorem inverseQFTBody_physical_idx (P : KnownOrderProblem G) :
    (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))).physical_idx =
      List.range (orderWidth P) := by
  simp

def inverseQFTCircuit (P : KnownOrderProblem G) :
    UnitaryCircuit (Qubits (totalQubits P)) :=
  withGroupWorkspace
    (pairConsecutiveCircuit (UnitaryCircuit.dagger (QFTCircuit (orderWidth P)))
      (inverseQFTBody_physical_idx P))
    (pairConsecutiveCircuit_physical_idx
      (UnitaryCircuit.dagger (QFTCircuit (orderWidth P)))
      (inverseQFTBody_physical_idx P))

@[simp] theorem inverseQFTCircuit_physical_idx (P : KnownOrderProblem G) :
    (inverseQFTCircuit P).physical_idx = List.range (totalQubits P) := by
  simp [inverseQFTCircuit, totalQubits]

@[simp] theorem inverseQFTCircuit_eventDepth (P : KnownOrderProblem G) :
    (inverseQFTCircuit P).eventDepth =
      .tensor
        (.tensor (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))).eventDepth
          (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))).eventDepth)
        .id := by
  rw [inverseQFTCircuit, withGroupWorkspace_eventDepth,
    pairConsecutiveCircuit_eventDepth]

/-- The actual all-zero-to-`U_unif`-to-`U_x`-to-inverse-QFT quantum circuit. -/
def quantumCircuit {P : KnownOrderProblem G} (A : Access P) :
    UnitaryCircuit (Qubits (totalQubits P)) :=
  UnitaryCircuit.seq (uniformCircuit A)
    (UnitaryCircuit.seq (uxCircuit A) (inverseQFTCircuit P))

@[simp] theorem quantumCircuit_physical_idx {P : KnownOrderProblem G}
    (A : Access P) :
    (quantumCircuit A).physical_idx = List.range (totalQubits P) := by
  simp only [quantumCircuit, UnitaryCircuit.seq,
    uniformCircuit_physical_idx, uxCircuit_physical_idx,
    inverseQFTCircuit_physical_idx, UnitaryCircuit.unionPhysicalIdx_self]

@[simp] theorem quantumCircuit_eventCost {P : KnownOrderProblem G}
    (A : Access P) :
    (quantumCircuit A).eventCost =
      (uniformCircuit A).eventCost +
        ((uxCircuit A).eventCost + (inverseQFTCircuit P).eventCost) :=
  rfl

@[simp] theorem quantumCircuit_eventDepth {P : KnownOrderProblem G}
    (A : Access P) :
    (quantumCircuit A).eventDepth =
      .seq (uniformCircuit A).eventDepth
        (.seq (uxCircuit A).eventDepth (inverseQFTCircuit P).eventDepth) :=
  rfl

/-- Exact maximal depth of the real `U_unif`; `U_x`; parallel inverse-QFT
circuit.  Preparation, terminal measurement, and typed classical recovery are
separate strict events and therefore do not alter this circuit-only quantity. -/
theorem quantumCircuit_evaluatedEventDepth {P : KnownOrderProblem G}
    (A : Access P) :
    (quantumCircuit A).evaluatedEventDepth circuitDepthAssignment =
      2 + orderWidth P + orderWidth P * (orderWidth P - 1) / 2 +
        orderWidth P / 2 := by
  have qftDepth :
      (QFTCircuit (orderWidth P)).evaluatedEventDepth circuitDepthAssignment =
        orderWidth P + orderWidth P * (orderWidth P - 1) / 2 +
          orderWidth P / 2 := by
    exact QFTCircuit_evaluatedEventDepth (orderWidth P) circuitDepthAssignment
      rfl rfl rfl
  have qftDaggerDepth :
      (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))).evaluatedEventDepth
          circuitDepthAssignment =
        orderWidth P + orderWidth P * (orderWidth P - 1) / 2 +
          orderWidth P / 2 := by
    change DepthExpr.depthEval circuitDepthAssignment
      (.inverse (QFTCircuit (orderWidth P)).eventDepth) = _
    simpa only [DepthExpr.depthEval_inverse, UnitaryCircuit.evaluatedEventDepth]
      using qftDepth
  change DepthExpr.depthEval circuitDepthAssignment
    (quantumCircuit A).eventDepth = _
  rw [quantumCircuit_eventDepth, uniformCircuit_eventDepth,
    uxCircuit_eventDepth, inverseQFTCircuit_eventDepth]
  simp only [DepthExpr.depthEval_seq, DepthExpr.depthEval_tensor,
    DepthExpr.depthEval_atom, DepthExpr.depthEval_id]
  rw [show DepthExpr.depthEval circuitDepthAssignment
      (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))).eventDepth = _ from
    qftDaggerDepth]
  simp only [uniformPreparationEvent, uxEvent, circuitDepthAssignment,
    Nat.max_zero, Nat.max_self]
  omega

/-- Canonical logical placement for the three-register experiment. -/
def layout (P : KnownOrderProblem G) : QubitLayout (totalQubits P) where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ equality => Fin.ext equality

@[simp] theorem layout_systemIdx (P : KnownOrderProblem G) :
    (layout P).systemIdx = List.range (totalQubits P) := by
  simp [layout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- The sole initial preparation is the computational-basis state with both
exponents zero and the workspace at the encoded group identity. -/
def inputPreparation {P : KnownOrderProblem G} (A : Access P) :
    KnownPreparation (totalQubits P) :=
  KnownPreparation.basis
    (tripleIndex (0 : Fin (2 ^ orderWidth P))
      (0 : Fin (2 ^ orderWidth P)) (A.ux.encode 1))

@[simp] theorem inputPreparation_normalized {P : KnownOrderProblem G}
    (A : Access P) :
    (inputPreparation A).normalized =
      NormalizedVector.ket (R := Qubits (totalQubits P))
        (tripleIndex (0 : Fin (2 ^ orderWidth P))
          (0 : Fin (2 ^ orderWidth P)) (A.ux.encode 1)) :=
  rfl

/-- Terminally measure the two exponent registers in their logical order. -/
def terminalMeasurement (P : KnownOrderProblem G) :
    TerminalZMeasure (layout P) (orderWidth P + orderWidth P) :=
  zMeasureAt (layout P)
    (fun index => ⟨index.val, by unfold totalQubits; omega⟩)
    (fun _ _ equality => Fin.ext (Fin.mk.inj equality))

/-- The full strict event pool of one terminal quantum attempt. -/
def attemptEventCost {P : KnownOrderProblem G} (A : Access P) :
    ResourcePool .quantum :=
  (inputPreparation A).eventCost +
    ((quantumCircuit A).eventCost + (terminalMeasurement P).eventCost)

/-- The strict critical-path expression derived from the same preparation,
circuit, and terminal-measurement objects. -/
def attemptEventDepth {P : KnownOrderProblem G} (A : Access P) :
    DepthExpr (Resource.Event .quantum) :=
  .seq (inputPreparation A).eventDepth
    (.seq (quantumCircuit A).eventDepth (terminalMeasurement P).eventDepth)

/-- Preparation and terminal measurement remain present in the strict event
ledger but contribute no layers to the public circuit-only depth projection. -/
theorem attemptEventDepth_evaluated {P : KnownOrderProblem G}
    (A : Access P) :
    DepthExpr.depthEval circuitDepthAssignment (attemptEventDepth A) =
      2 + orderWidth P + orderWidth P * (orderWidth P - 1) / 2 +
        orderWidth P / 2 := by
  have preparationDepth :
      DepthExpr.depthEval circuitDepthAssignment
          (inputPreparation A).eventDepth = 0 := by
    rcases KnownPreparation.event_eq_preparation (inputPreparation A) with
      ⟨label, eventEq⟩
    change circuitDepthAssignment (inputPreparation A).event = 0
    rw [eventEq]
    rfl
  have measurementDepth :
      DepthExpr.depthEval circuitDepthAssignment
          (terminalMeasurement P).eventDepth = 0 := by
    unfold TerminalZMeasure.eventDepth TerminalZMeasure.eventTrace
    have foldZero : ∀ count,
        DepthExpr.depthEval circuitDepthAssignment
          (List.foldr
            (fun current tail =>
              DepthExpr.tensor (DepthExpr.atom current) tail)
            DepthExpr.id
            (List.replicate count
              (.measurement (terminalMeasurement P).eventLabel))) = 0 := by
      intro count
      induction count with
      | zero => rfl
      | succ count countZero =>
          simp only [List.replicate_succ, List.foldr_cons,
            DepthExpr.depthEval_tensor, DepthExpr.depthEval_atom,
            circuitDepthAssignment, countZero, Nat.max_self]
    exact foldZero (orderWidth P + orderWidth P)
  unfold attemptEventDepth
  simp only [DepthExpr.depthEval_seq]
  rw [preparationDepth, measurementDepth]
  have circuitDepth := quantumCircuit_evaluatedEventDepth A
  change DepthExpr.depthEval circuitDepthAssignment
    (quantumCircuit A).eventDepth = _ at circuitDepth
  rw [circuitDepth]
  omega

theorem attemptEventDepth_coherent {P : KnownOrderProblem G} (A : Access P) :
    DepthExpr.costEval (fun event => ResourcePool.singleton event)
        (attemptEventDepth A) = attemptEventCost A := by
  change ResourcePool.singleton (inputPreparation A).event +
      ((quantumCircuit A).resourcesFromEventDepth +
        DepthExpr.costEval (fun event => ResourcePool.singleton event)
          (terminalMeasurement P).eventDepth) =
    (inputPreparation A).eventCost +
      ((quantumCircuit A).eventCost + (terminalMeasurement P).eventCost)
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    TerminalZMeasure.resourcesFromEventDepth_eq_eventCost]
  rfl

theorem terminalMeasurement_eventCount (P : KnownOrderProblem G) :
    ResourcePool.count (terminalMeasurement P).event
        (terminalMeasurement P).eventCost = orderWidth P + orderWidth P := by
  exact TerminalZMeasure.count_eventCost (terminalMeasurement P)

end Canonical
end FiniteCyclicDLP

end

end QuantumAlg

end
