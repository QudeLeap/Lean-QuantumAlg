/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Extend an actual canonical circuit by an idle physical suffix

The supplied program keeps every original wire identity. The suffix occupies
the following physical positions and contributes identity on its complete
state, including arbitrary correlations. Tensor syntax records those actual
systems; it does not allocate, initialize or release them.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Tensor an actual circuit with identity on the following physical positions. -/
def idleSuffix {width : Nat} (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat) :
    UnitaryCircuit (Qubits (width + suffix)) :=
  tensorQubits program
    (identity (Qubits suffix) (List.range' width suffix) List.nodup_range')
    { left_nodup := program.physical_idx_nodup
      right_nodup := List.nodup_range'
      disjoint := by
        rw [List.disjoint_left]
        intro wire inProgram inSuffix
        have before := List.mem_range.mp (contained inProgram)
        have after := List.left_le_of_mem_range' inSuffix
        omega }

/-- The complete operator includes the true identity factor on every suffix state. -/
theorem idleSuffix_matrix {width : Nat} (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat) :
    (program.idleSuffix contained suffix).matrix =
      UnitaryOperator.tensor program.matrix (1 : UnitaryOperator (Qubits suffix)) := rfl

/-- The actual suffix wires follow the unchanged original program positions. -/
theorem idleSuffix_physical_idx {width : Nat} (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat) :
    (program.idleSuffix contained suffix).physical_idx =
      program.physical_idx ++ List.range' width suffix := rfl

/-- Every original or suffix position lies in the actual enlarged register. -/
theorem idleSuffix_physical_idx_subset_range {width : Nat}
    (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat) :
    (program.idleSuffix contained suffix).physical_idx ⊆ List.range (width + suffix) := by
  intro wire present
  rw [idleSuffix_physical_idx] at present
  apply List.mem_range.mpr
  rcases List.mem_append.mp present with inProgram | inSuffix
  · have before := List.mem_range.mp (contained inProgram)
    omega
  · obtain ⟨index, bounded, same⟩ := List.mem_range'.mp inSuffix
    omega

/-- Canonical input order extends to canonical full-register order. -/
theorem idleSuffix_physical_idx_eq_range {width : Nat}
    (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat)
    (ordered : program.physical_idx = List.range width) :
    (program.idleSuffix contained suffix).physical_idx = List.range (width + suffix) := by
  rw [idleSuffix_physical_idx, ordered]
  simpa only [List.range_eq_range', Nat.zero_add] using
    (List.range'_append_1 (s := 0) (m := width) (n := suffix))

/-- Identity on the suffix adds no occurrence to the actual event trace. -/
theorem idleSuffix_eventTrace {width : Nat} (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat) :
    (program.idleSuffix contained suffix).eventTrace = program.eventTrace := by
  simp only [idleSuffix, tensorQubits_eventTrace, identity_eventTrace, List.append_nil]

/-- Native event multiplicities are those of the actual source program. -/
theorem idleSuffix_eventCost {width : Nat} (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat) :
    (program.idleSuffix contained suffix).eventCost = program.eventCost := by
  simp only [idleSuffix, tensorQubits_eventCost, identity_eventCost, add_zero]

/-- Parallel identity on the suffix adds no depth for any native event weights. -/
theorem idleSuffix_evaluatedEventDepth {width : Nat} (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) (suffix : Nat)
    (weight : Resource.Event .quantum → Nat) :
    (program.idleSuffix contained suffix).evaluatedEventDepth weight =
      program.evaluatedEventDepth weight := by
  simp only [evaluatedEventDepth, idleSuffix, tensorQubits_eventDepth, identity_eventDepth,
    DepthExpr.depthEval, Nat.max_zero]

end

end QuantumAlg.UnitaryCircuit
