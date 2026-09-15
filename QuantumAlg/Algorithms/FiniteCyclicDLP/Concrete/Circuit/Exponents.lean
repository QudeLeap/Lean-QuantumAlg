/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Primitives.QFT.Construction

/-!
# Original exponent preparation and readout circuits

The two original range preparations and inverse Fourier transforms occupy
consecutive physical intervals. Their complete circuit bodies, exact event
pools and symbolic depths are independent of the classical recovery layer.
-/

namespace QuantumAlg.FiniteCyclicDLP.ConcreteCircuitAccess

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Put two copies of an `n`-qubit circuit on consecutive physical intervals.
The certified tensor construction is the actual parallel execution witness. -/
def pairConsecutiveCircuit {n : Nat} (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) :
    UnitaryCircuit (Qubits (n + n)) := by
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

/-- Parallel placement of two identical circuit copies adds their exact event
pools. -/
@[simp] theorem pairConsecutiveCircuit_eventCost {n : Nat}
    (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) :
    (pairConsecutiveCircuit body hphysical).eventCost =
      body.eventCost + body.eventCost := by
  simp only [pairConsecutiveCircuit, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.shiftPhysicalIdx_eventCost]

/-- Parallel placement of two identical circuit copies takes the maximum of
their two symbolic depths. -/
@[simp] theorem pairConsecutiveCircuit_eventDepth {n : Nat}
    (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n) :
    (pairConsecutiveCircuit body hphysical).eventDepth =
      .tensor body.eventDepth body.eventDepth := by
  simp only [pairConsecutiveCircuit, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    UnitaryCircuit.shiftPhysicalIdx_eventDepth]

/-- Two parallel exact range-uniform exponent preparations before the tail is
attached. -/
private theorem rangePreparationCircuit_physical_idx
    (P : KnownOrderProblem G) :
    (rangePreparationCircuit P).physical_idx = List.range (orderWidth P) :=
  rfl

def exponentPreparationCircuit (P : KnownOrderProblem G) :
    UnitaryCircuit (Qubits (orderWidth P + orderWidth P)) :=
  pairConsecutiveCircuit (rangePreparationCircuit P)
    (rangePreparationCircuit_physical_idx P)

@[simp] theorem exponentPreparationCircuit_physical_idx
    (P : KnownOrderProblem G) :
    (exponentPreparationCircuit P).physical_idx =
      List.range (orderWidth P + orderWidth P) :=
  pairConsecutiveCircuit_physical_idx (rangePreparationCircuit P)
    (rangePreparationCircuit_physical_idx P)

private theorem inverseQFTBody_physical_idx (P : KnownOrderProblem G) :
    (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))).physical_idx =
      List.range (orderWidth P) := by
  simp

/-- Two inverse-QFT exponent readouts before the tail is attached. -/
def exponentReadoutCircuit (P : KnownOrderProblem G) :
    UnitaryCircuit (Qubits (orderWidth P + orderWidth P)) :=
  pairConsecutiveCircuit (UnitaryCircuit.dagger (QFTCircuit (orderWidth P)))
    (inverseQFTBody_physical_idx P)

@[simp] theorem exponentReadoutCircuit_physical_idx
    (P : KnownOrderProblem G) :
    (exponentReadoutCircuit P).physical_idx =
      List.range (orderWidth P + orderWidth P) :=
  pairConsecutiveCircuit_physical_idx
    (UnitaryCircuit.dagger (QFTCircuit (orderWidth P)))
    (inverseQFTBody_physical_idx P)

end

end QuantumAlg.FiniteCyclicDLP.ConcreteCircuitAccess
