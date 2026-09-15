/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Algorithm.QuantumState
import all QuantumAlg.Core.Measure
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Exponents

/-!
# Concrete finite-cyclic DLP unitary experiment

The original encoding, clean group action, range preparation and inverse
Fourier readout share one actual unitary circuit. Its terminal measurement
descriptor is independent of any allocation or repetition wrapper. Opaque
group actions retain their own counted query; the optional absence-of-query
certificate applies only when a gate implementation provides it.
-/

namespace QuantumAlg.FiniteCyclicDLP

open NormalizedVector

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- A concrete clean-tail realization of the finite-cyclic DLP group action.

The two leading registers hold Fourier exponents.  `Tail` contains the group
workspace together with every implementation work bit, and `cleanTail`
selects the clean representation for each semantic group value. -/
structure ConcreteCircuitAccess (P : KnownOrderProblem G) where
  /-- Carrier of the group workspace and every implementation work bit. -/
  Tail : Type
  /-- Faithful binary encoding of the complete implementation tail. -/
  tailEncoding : BinaryLabelEncoding Tail
  /-- Canonical clean implementation state for one semantic group value. -/
  cleanTail : G → Tail
  /-- The clean encoding distinguishes all semantic group values. -/
  cleanTail_injective : Function.Injective cleanTail
  /-- The actual exponent-controlled circuit, including all arithmetic work. -/
  oracleCircuit : UnitaryCircuit
    (Qubits (orderWidth P + orderWidth P + tailEncoding.width))
  /-- The actual circuit addresses exactly the two exponent registers and the
  complete implementation tail. -/
  oracleCircuit_physical_idx :
    oracleCircuit.physical_idx =
      List.range (orderWidth P + orderWidth P + tailEncoding.width)
  /-- The stored circuit realizes the group action on every canonical clean
  input and returns all implementation work to canonical clean form. -/
  realizesClean :
    ∀ leftExponent rightExponent workspace,
      oracleCircuit.applyNormalized
          (NormalizedVector.ket
            ((BinaryLabelEncoding.prod
              (BinaryLabelEncoding.prod
                (BinaryLabelEncoding.finIdentity (orderWidth P))
                (BinaryLabelEncoding.finIdentity (orderWidth P)))
              tailEncoding).encode
              ((leftExponent, rightExponent), cleanTail workspace))) =
        NormalizedVector.ket
          ((BinaryLabelEncoding.prod
            (BinaryLabelEncoding.prod
              (BinaryLabelEncoding.finIdentity (orderWidth P))
              (BinaryLabelEncoding.finIdentity (orderWidth P)))
            tailEncoding).encode
            ((leftExponent, rightExponent),
              cleanTail
                (workspace *
                  P.toSourceScope.oracleMultiplier
                    leftExponent.val rightExponent.val)))


namespace ConcreteCircuitAccess

variable {P : KnownOrderProblem G}

/-- Additional provenance certificate for a gate-level implementation whose
oracle circuit contains no opaque quantum-subroutine leaf.  This is deliberately
separate from `ConcreteCircuitAccess`: counted-oracle endpoints use the same
real-layout circuit spine without satisfying this gate-compiled condition. -/
class OracleCircuitQuantumSubroutineFree (A : ConcreteCircuitAccess P) : Prop where
  count_zero : ∀ label : Resource.QuantumSubroutineLabel,
    ResourcePool.count (.quantumSubroutine label) A.oracleCircuit.eventCost = 0

/-- The two leading exponent registers in canonical big-endian order. -/
abbrev exponentEncoding (P : KnownOrderProblem G) :
    BinaryLabelEncoding
      (Fin (2 ^ orderWidth P) × Fin (2 ^ orderWidth P)) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.finIdentity (orderWidth P))
    (BinaryLabelEncoding.finIdentity (orderWidth P))

/-- The full logical width of the concrete experiment. -/
abbrev totalQubits (A : ConcreteCircuitAccess P) : Nat :=
  orderWidth P + orderWidth P + A.tailEncoding.width

/-- The common binary encoding of both exponent registers and the clean tail. -/
abbrev encoding (A : ConcreteCircuitAccess P) :
    BinaryLabelEncoding
      ((Fin (2 ^ orderWidth P) × Fin (2 ^ orderWidth P)) × A.Tail) :=
  BinaryLabelEncoding.prod (exponentEncoding P) A.tailEncoding

/-- One canonical encoded state of the two exponent registers and group
workspace. -/
def cleanState (A : ConcreteCircuitAccess P)
    (leftExponent rightExponent : Fin (2 ^ orderWidth P))
    (workspace : G) :
    (Fin (2 ^ orderWidth P) × Fin (2 ^ orderWidth P)) × A.Tail :=
  ((leftExponent, rightExponent), A.cleanTail workspace)

/-- The stored implementation circuit realizes its clean group-action
contract. -/
theorem oracleCircuit_apply_clean (A : ConcreteCircuitAccess P)
    (leftExponent rightExponent : Fin (2 ^ orderWidth P))
    (workspace : G) :
    A.oracleCircuit.applyNormalized
        (NormalizedVector.ket
          (A.encoding.encode
            (A.cleanState leftExponent rightExponent workspace))) =
      NormalizedVector.ket
        (A.encoding.encode
          (A.cleanState leftExponent rightExponent
            (workspace *
              P.toSourceScope.oracleMultiplier
                leftExponent.val rightExponent.val))) :=
  A.realizesClean leftExponent rightExponent workspace

/-- Every opaque-subroutine event count of the stored implementation is zero. -/
theorem oracleCircuit_quantumSubroutine_count_zero
    (A : ConcreteCircuitAccess P) [OracleCircuitQuantumSubroutineFree A]
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label) A.oracleCircuit.eventCost = 0 :=
  OracleCircuitQuantumSubroutineFree.count_zero label

/-- Extend an exponent-register circuit by an untouched complete tail. -/
def extendWithTail {n : Nat} (A : ConcreteCircuitAccess P)
    (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) :
    UnitaryCircuit (Qubits (n + A.tailEncoding.width)) :=
  let tail := UnitaryCircuit.identity (Qubits A.tailEncoding.width)
    (List.range' n A.tailEncoding.width) List.nodup_range'
  UnitaryCircuit.tensorQubits body tail
    { left_nodup := body.physical_idx_nodup
      right_nodup := List.nodup_range'
      disjoint := by
        rw [hphysical, List.disjoint_left]
        intro index hleft hright
        have hlt := List.mem_range.mp hleft
        have hle := List.left_le_of_mem_range' hright
        omega }

@[simp] theorem extendWithTail_physical_idx {n : Nat}
    (A : ConcreteCircuitAccess P) (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) :
    (A.extendWithTail body hphysical).physical_idx =
      List.range (n + A.tailEncoding.width) := by
  simp only [extendWithTail, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, UnitaryCircuit.identity,
    PhysicalLayout.DisjointMerge.merged_eq_append, hphysical]
  simpa [List.range_eq_range'] using
    (List.range'_append_1 (s := 0) (m := n)
      (n := A.tailEncoding.width))

/-- Tensoring with the untouched implementation tail preserves the body event
pool exactly. -/
@[simp] theorem extendWithTail_eventCost {n : Nat}
    (A : ConcreteCircuitAccess P) (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) :
    (A.extendWithTail body hphysical).eventCost = body.eventCost := by
  simp only [extendWithTail, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]

/-- Tensoring with an untouched implementation tail preserves symbolic depth. -/
@[simp] theorem extendWithTail_eventDepth {n : Nat}
    (A : ConcreteCircuitAccess P) (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) :
    (A.extendWithTail body hphysical).eventDepth =
      .tensor body.eventDepth .id := by
  simp only [extendWithTail, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    UnitaryCircuit.identity_eventDepth]

/-- Two exact exponent preparations with the implementation tail untouched. -/
def preparationCircuit (A : ConcreteCircuitAccess P) :
    UnitaryCircuit (Qubits A.totalQubits) :=
  A.extendWithTail (exponentPreparationCircuit P)
    (exponentPreparationCircuit_physical_idx P)

@[simp] theorem preparationCircuit_physical_idx (A : ConcreteCircuitAccess P) :
    A.preparationCircuit.physical_idx = List.range A.totalQubits := by
  change
    (A.extendWithTail (exponentPreparationCircuit P)
        (exponentPreparationCircuit_physical_idx P)).physical_idx =
      List.range
        (orderWidth P + orderWidth P + A.tailEncoding.width)
  exact A.extendWithTail_physical_idx (exponentPreparationCircuit P)
    (exponentPreparationCircuit_physical_idx P)

/-- Two inverse-QFT readouts with the implementation tail untouched. -/
def readoutCircuit (A : ConcreteCircuitAccess P) :
    UnitaryCircuit (Qubits A.totalQubits) :=
  A.extendWithTail (exponentReadoutCircuit P)
    (exponentReadoutCircuit_physical_idx P)

@[simp] theorem readoutCircuit_physical_idx (A : ConcreteCircuitAccess P) :
    A.readoutCircuit.physical_idx = List.range A.totalQubits := by
  change
    (A.extendWithTail (exponentReadoutCircuit P)
        (exponentReadoutCircuit_physical_idx P)).physical_idx =
      List.range
        (orderWidth P + orderWidth P + A.tailEncoding.width)
  exact A.extendWithTail_physical_idx (exponentReadoutCircuit P)
    (exponentReadoutCircuit_physical_idx P)

/-- One full concrete finite-cyclic DLP circuit: prepare the exponents,
execute the stored group-action circuit, then read out both exponents. -/
def fullCircuit (A : ConcreteCircuitAccess P) : UnitaryCircuit (Qubits A.totalQubits) :=
  UnitaryCircuit.seq A.preparationCircuit
    (UnitaryCircuit.seq A.oracleCircuit A.readoutCircuit)

/-- Strict event resources projected from the one full concrete circuit. -/
def eventCost (A : ConcreteCircuitAccess P) : ResourcePool .quantum :=
  A.fullCircuit.eventCost

/-- Strict event critical path projected from the one full concrete circuit. -/
def eventDepth (A : ConcreteCircuitAccess P) :
    DepthExpr (Resource.Event .quantum) :=
  A.fullCircuit.eventDepth

/-- The actual full-circuit physical footprint. -/
def physicalIdx (A : ConcreteCircuitAccess P) : List Nat :=
  A.fullCircuit.physical_idx

@[simp] theorem fullCircuit_eventCost (A : ConcreteCircuitAccess P) :
    A.fullCircuit.eventCost =
      A.preparationCircuit.eventCost +
        (A.oracleCircuit.eventCost + A.readoutCircuit.eventCost) :=
  rfl

@[simp] theorem fullCircuit_eventDepth (A : ConcreteCircuitAccess P) :
    A.fullCircuit.eventDepth =
      .seq A.preparationCircuit.eventDepth
        (.seq A.oracleCircuit.eventDepth A.readoutCircuit.eventDepth) :=
  rfl

/-- Canonical full-register layout for the stored concrete circuit. -/
def layout (A : ConcreteCircuitAccess P) : QubitLayout A.totalQubits where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ equality => Fin.ext equality

@[simp] theorem layout_systemIdx (A : ConcreteCircuitAccess P) :
    A.layout.systemIdx = List.range A.totalQubits := by
  simp [layout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

@[simp] theorem fullCircuit_physical_idx (A : ConcreteCircuitAccess P) :
    A.fullCircuit.physical_idx = A.layout.systemIdx := by
  rw [layout_systemIdx]
  change
    UnitaryCircuit.unionPhysicalIdx A.preparationCircuit.physical_idx
      (UnitaryCircuit.unionPhysicalIdx A.oracleCircuit.physical_idx
        A.readoutCircuit.physical_idx) =
      List.range A.totalQubits
  rw [preparationCircuit_physical_idx, A.oracleCircuit_physical_idx,
    readoutCircuit_physical_idx, UnitaryCircuit.unionPhysicalIdx_self,
    UnitaryCircuit.unionPhysicalIdx_self]

@[simp] theorem physicalIdx_eq_layout (A : ConcreteCircuitAccess P) :
    A.physicalIdx = A.layout.systemIdx :=
  A.fullCircuit_physical_idx

/-- The canonical all-zero exponent state with the group identity in its
clean tail encoding. -/
def preparation (A : ConcreteCircuitAccess P) : KnownPreparation A.totalQubits :=
  KnownPreparation.basis (A.encoding.encode (A.cleanState 0 0 1))

/-- Terminally measure the two leading exponent registers only. -/
def measurement (A : ConcreteCircuitAccess P) :
    TerminalZMeasure A.layout (orderWidth P + orderWidth P) :=
  zMeasureAt A.layout
    (fun index =>
      ⟨index.val, by
        have hindex := index.isLt
        change
          index.val <
            orderWidth P + orderWidth P + A.tailEncoding.width
        omega⟩)
    (fun _ _ equality => Fin.ext (Fin.mk.inj equality))

/-- The oversampled exponent-register width is positive, including for an
order-one group. -/
theorem orderWidth_pos (P : KnownOrderProblem G) : 0 < orderWidth P := by
  unfold orderWidth oversampledOrder fourierOversamplingFactor
  apply Nat.clog_pos
  · norm_num
  · have := P.order_pos
    omega

theorem eventCost_from_fullCircuit (A : ConcreteCircuitAccess P) :
    A.eventCost = A.fullCircuit.eventCost := rfl

theorem eventDepth_from_fullCircuit (A : ConcreteCircuitAccess P) :
    A.eventDepth = A.fullCircuit.eventDepth := rfl

end ConcreteCircuitAccess

end

end QuantumAlg.FiniteCyclicDLP
