/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical.Labels
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Storage
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Context

/-!
# Actual measured-arithmetic bank and disjoint retained output storage

One original control, both full arithmetic words, two adder helpers and one
flag are allocated together. The retained exponent outputs have their own
physical cells. The separate width-minus-two vent bank is reused across
arithmetic stages; actual chronological outcome history remains in the
execution paths [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

include noQuantum in
private lemma allocationDisjoint (width : Nat) :
    List.Disjoint (Physical.qubits width).toQuantum.identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- Sole actual quantum allocation, containing exactly the complete measured arithmetic frame. -/
def bankContext (width : Nat) : RuntimeCtx .quantum :=
  base.addOwnedLayout base.canonicalFreshKey (Physical.qubits width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width)

/-- Distinct actual storage for all retained outputs and the reused physical vent results. -/
def context (m ell width : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum width) 2 (resultBits m ell + (width - 2))

/-- No quantum system is added or removed by either real classical cell bank. -/
lemma context_wires (m ell width : Nat) :
    (Physical.qubits width).toQuantum.wires =
      (context base noQuantum m ell width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  unfold context
  rw [MeasurementCells.context_quantumWires]
  change (Physical.qubits width).toQuantum.wires =
    (Physical.qubits width).toQuantum.wires ++ base.quantumWires
  rw [noQuantum, List.append_nil]

/-- The actual stage carrier contains the original control, two words and exactly three helpers. -/
lemma systemCount_eq (m ell width : Nat) :
    (context base noQuantum m ell width).systemCount = 2 * width + 4 := by
  have same := congrArg List.length (context_wires base noQuantum m ell width)
  simp only [QuantumLayout.wires_length] at same
  exact same.symm

/-- Each retained output or reused vent result occupies its original addressed real binary cell. -/
def cells (m ell width : Nat) (index : Fin (resultBits m ell + (width - 2))) :
    CWriteRef (context base noQuantum m ell width) (.finite 2) :=
  MeasurementCells.reference (bankContext base noQuantum width) 2
    (resultBits m ell + (width - 2)) index

lemma cells_distinct (m ell width : Nat) :
    Function.Injective (fun index => (cells base noQuantum m ell width index).key) :=
  MeasurementCells.reference_key_injective (bankContext base noQuantum width) 2
    (resultBits m ell + (width - 2))

/-- Retained exponent outcomes occupy the first original output block. -/
def resultCell (m ell width : Nat) (index : Fin (resultBits m ell)) :
    CWriteRef (context base noQuantum m ell width) (.finite 2) :=
  cells base noQuantum m ell width (Fin.castAdd (width - 2) index)

/-- Arithmetic vents overwrite only their separate reusable original bank. -/
def ventCell (m ell width : Nat) (index : Fin (width - 2)) :
    CWriteRef (context base noQuantum m ell width) (.finite 2) :=
  cells base noQuantum m ell width (Fin.natAdd (resultBits m ell) index)

/-- The complete arithmetic record bank is physically distinct, without restricting old Stores. -/
def recordBank (m ell width : Nat) :
    MAU.Addition.Gidney.Measured.RecordBank
      (context base noQuantum m ell width) (width - 2) where
  output := ventCell base noQuantum m ell width
  distinct := by
    intro first second same
    have indices := cells_distinct base noQuantum m ell width same
    apply Fin.ext
    have values : resultBits m ell + first.val = resultBits m ell + second.val :=
      congrArg Fin.val indices
    omega

/-- Arithmetic vents cannot overwrite a retained chronological exponent output. -/
lemma vent_result_distinct (m ell width : Nat) (vent : Fin (width - 2))
    (result : Fin (resultBits m ell)) :
    (ventCell base noQuantum m ell width vent).key ≠
      (resultCell base noQuantum m ell width result).key := by
  intro same
  have indices := cells_distinct base noQuantum m ell width same
  have values : resultBits m ell + vent.val = result.val := congrArg Fin.val indices
  have bound := result.isLt
  omega

/-- Actual cell capacities include the new reused vent bank in addition to retained outputs. -/
lemma context_resident (m ell width : Nat) :
    (context base noQuantum m ell width).residentSpace =
      (resultBits m ell + (width - 2)) • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Physical.qubits width).toQuantum + base.residentSpace) := by
  rw [context, MeasurementCells.context_residentSpace]
  rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
