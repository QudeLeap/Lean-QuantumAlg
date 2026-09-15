/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
public import QuantumAlg.Core.Base
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Exponents
import all QuantumAlg.Core.Algorithm.QuantumState
import all QuantumAlg.Core.Measure

/-!
# Original opaque elliptic-curve group action and unitary sampling spine

The public oracle keeps its intrinsic identity-inclusive point encoding and
its original action on every encoded basis point. Both exponent preparations,
one opaque query and both inverse Fourier transforms are the original unitary
circuits. The terminal descriptor selects the same leading exponent wires;
actual allocation, measurement, repetition and recovery are separate programs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The fixed intrinsic basis label of two exponents and one actual curve
point. -/
public def basisIndex (I : ECDLPInstance E)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (workspace : GroupPoint E) : Fin (2 ^ Layout.totalQubits I) :=
  (Layout.fullEncoding I).encode ((left, right), workspace)

/-- Opaque `U_{P,Q}` access on the intrinsic identity-inclusive point layout.
No encoding or width is supplied by the caller. -/
public structure Access (I : ECDLPInstance E) where
  /-- The certified black-box group-action unitary. -/
  operator : UnitaryOperator (Qubits (Layout.totalQubits I))
  /-- Source-faithful action on every canonical point-register basis state. -/
  basisAction :
    ∀ (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
      (workspace : GroupPoint E),
      operator.apply
          (NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
            (basisIndex I left right workspace)) =
        NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
          (basisIndex I left right
            (workspace *
              (problem I).toSourceScope.oracleMultiplier left.val right.val))

/-- Strict family coordinate for the sole opaque ECDLP group action. -/
def uPQSubroutineLabel (I : ECDLPInstance E) : Resource.SubroutineLabel :=
  { family := "elliptic-curve-dlp"
    name := "U_{P,Q}"
    parameters :=
      [p, I.subgroupOrder, FiniteCyclicDLP.orderWidth (problem I),
        Layout.pointWidth E] }

/-- Counted query event for one opaque `U_{P,Q}` invocation. -/
def uPQEvent (I : ECDLPInstance E) : Resource.Event .quantum :=
  .quantumSubroutine (uPQSubroutineLabel I).quantum

/-- Extend the two exponent registers by the untouched intrinsic point
register. -/
def extendWithPoint (I : ECDLPInstance E)
    (body : UnitaryCircuit (Qubits
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))))
    (physical : body.physical_idx = List.range
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))) :
    UnitaryCircuit (Qubits (Layout.totalQubits I)) :=
  let point := UnitaryCircuit.identity (Qubits (Layout.pointWidth E))
    (List.range'
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))
      (Layout.pointWidth E)) List.nodup_range'
  UnitaryCircuit.tensorQubits body point
    { left_nodup := body.physical_idx_nodup
      right_nodup := List.nodup_range'
      disjoint := by
        rw [physical, List.disjoint_left]
        intro index inExponent inPoint
        have indexLt := List.mem_range.mp inExponent
        have exponentLe := List.left_le_of_mem_range' inPoint
        exact (Nat.not_lt_of_ge exponentLe) indexLt }

@[simp] theorem extendWithPoint_physical_idx (I : ECDLPInstance E)
    (body : UnitaryCircuit (Qubits
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))))
    (physical : body.physical_idx = List.range
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))) :
    (extendWithPoint I body physical).physical_idx =
      List.range (Layout.totalQubits I) := by
  simp only [extendWithPoint, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, UnitaryCircuit.identity,
    PhysicalLayout.DisjointMerge.merged_eq_append, physical]
  simpa [Layout.totalQubits, List.range_eq_range'] using
    (List.range'_append_1
      (s := 0)
      (m := FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))
      (n := Layout.pointWidth E))

@[simp] theorem extendWithPoint_eventCost (I : ECDLPInstance E)
    (body : UnitaryCircuit (Qubits
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))))
    (physical : body.physical_idx = List.range
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))) :
    (extendWithPoint I body physical).eventCost = body.eventCost := by
  simp only [extendWithPoint, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]

/-- Extending by the untouched point register preserves symbolic depth. -/
@[simp] theorem extendWithPoint_eventDepth (I : ECDLPInstance E)
    (body : UnitaryCircuit (Qubits
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))))
    (physical : body.physical_idx = List.range
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))) :
    (extendWithPoint I body physical).eventDepth =
      .tensor body.eventDepth .id := by
  simp only [extendWithPoint, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    UnitaryCircuit.identity_eventDepth]

/-- Actual pair of exact finite-range preparation circuits, leaving the point
register at identity. -/
def preparationCircuit (I : ECDLPInstance E) :
    UnitaryCircuit (Qubits (Layout.totalQubits I)) :=
  extendWithPoint I
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit (problem I))
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit_physical_idx
      (problem I))

@[simp] theorem preparationCircuit_physical_idx (I : ECDLPInstance E) :
    (preparationCircuit I).physical_idx = List.range (Layout.totalQubits I) :=
  extendWithPoint_physical_idx I _ _

namespace EndpointDeclarations

/-- Declare one opaque `U_{P,Q}` family member at a caller-supplied physical
placement. -/
def uPQLeafAt (I : ECDLPInstance E) (A : Access I)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits (Layout.totalQubits I)) :=
  UnitaryLeaf.subroutine (uPQSubroutineLabel I) systemIdx A.operator

end EndpointDeclarations

/-- One opaque `U_{P,Q}` occurrence on the complete intrinsic layout. -/
def uPQCircuit (I : ECDLPInstance E) (A : Access I) :
    UnitaryCircuit (Qubits (Layout.totalQubits I)) :=
  UnitaryCircuit.ofLeaf
    (EndpointDeclarations.uPQLeafAt I A
      (List.range (Layout.totalQubits I)))
    List.nodup_range

@[simp] theorem uPQCircuit_physical_idx (I : ECDLPInstance E) (A : Access I) :
    (uPQCircuit I A).physical_idx = List.range (Layout.totalQubits I) :=
  rfl

@[simp] theorem uPQCircuit_eventCost (I : ECDLPInstance E) (A : Access I) :
    (uPQCircuit I A).eventCost = ResourcePool.singleton (uPQEvent I) :=
  rfl

/-- Actual pair of inverse-QFT circuits on the exponent registers. -/
def inverseQFTCircuit (I : ECDLPInstance E) :
    UnitaryCircuit (Qubits (Layout.totalQubits I)) :=
  extendWithPoint I
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit (problem I))
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit_physical_idx
      (problem I))

@[simp] theorem inverseQFTCircuit_physical_idx (I : ECDLPInstance E) :
    (inverseQFTCircuit I).physical_idx = List.range (Layout.totalQubits I) :=
  extendWithPoint_physical_idx I _ _

/-- The real quantum circuit for one ECDLP Fourier experiment. -/
def quantumCircuit (I : ECDLPInstance E) (A : Access I) :
    UnitaryCircuit (Qubits (Layout.totalQubits I)) :=
  UnitaryCircuit.seq (preparationCircuit I)
    (UnitaryCircuit.seq (uPQCircuit I A) (inverseQFTCircuit I))

@[simp] theorem quantumCircuit_physical_idx (I : ECDLPInstance E)
    (A : Access I) :
    (quantumCircuit I A).physical_idx = List.range (Layout.totalQubits I) := by
  simp only [quantumCircuit, UnitaryCircuit.seq, preparationCircuit_physical_idx,
    uPQCircuit_physical_idx, inverseQFTCircuit_physical_idx,
    UnitaryCircuit.unionPhysicalIdx_self]

/-- Canonical physical placement of the complete intrinsic layout. -/
def qubitLayout (I : ECDLPInstance E) : QubitLayout (Layout.totalQubits I) where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ equality => Fin.ext equality

@[simp] theorem qubitLayout_systemIdx (I : ECDLPInstance E) :
    (qubitLayout I).systemIdx = List.range (Layout.totalQubits I) := by
  simp [qubitLayout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Initial basis state with zero exponents and the actual curve identity. -/
def inputPreparation (I : ECDLPInstance E) :
    KnownPreparation (Layout.totalQubits I) :=
  KnownPreparation.basis
    (basisIndex I
      (0 : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
      (0 : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I))) 1)

/-- Terminally measure the two leading exponent registers only. -/
def terminalMeasurement (I : ECDLPInstance E) :
    TerminalZMeasure (qubitLayout I)
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I)) :=
  zMeasureAt (qubitLayout I)
    (fun index => ⟨index.val, by
      unfold Layout.totalQubits
      omega⟩)
    (fun _ _ equality => Fin.ext (Fin.mk.inj equality))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
