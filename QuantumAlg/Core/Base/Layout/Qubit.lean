/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.Linter.Style

/-!
# Typed qubit layouts

`QubitLayout n` is the base-layer placement witness for exactly `n` logical
qubits.  It records an injective physical index for each logical qubit; it does
not claim fault-tolerant expansion, routing overhead, or a compiled physical
footprint.
-/

section

namespace QuantumAlg
-- Declaration-scoped exception: retain the shared physical_idx placement coordinate spelling.
set_option linter.style.nameCheck false
/-- An injective physical placement for a fixed number of logical qubits. -/
public structure QubitLayout (qubitCount : Nat) where
  /-- Physical system occupied by each logical qubit. -/
  physical_idx : Fin qubitCount → Nat
  /-- Distinct logical qubits occupy distinct physical systems. -/
  physical_idx_injective : Function.Injective physical_idx
set_option linter.style.nameCheck true

-- Intentional coordinate spelling shared with the pure-circuit placement API.
attribute [nolint defsWithUnderscore] QubitLayout.physical_idx

/-- A sealed injective selection of logical positions from one complete qubit
layout width.

The descriptor records only logical positions. Physical placement remains the
responsibility of the `QubitLayout` to which a consumer applies the selection.
The selected width may be smaller than the complete width, so terminal
measurement can retain partial readout while still consuming the complete live
frame. -/
public structure QubitSelection (totalQubits selectedQubits : Nat) where
  private mk ::
  /-- Selected logical positions, in canonical result order. -/
  logical_idx : Fin selectedQubits → Fin totalQubits
  /-- No logical position can be selected twice. -/
  logical_idx_injective : Function.Injective logical_idx

attribute [nolint defsWithUnderscore] QubitSelection.logical_idx

namespace QubitSelection

/-- Seal one logical selection from its actual injective position map. -/
public def ofLogicalIdx {totalQubits selectedQubits : Nat}
    (logicalIdx : Fin selectedQubits → Fin totalQubits)
    (logicalIdxInjective : Function.Injective logicalIdx) :
    QubitSelection totalQubits selectedQubits where
  logical_idx := logicalIdx
  logical_idx_injective := logicalIdxInjective

end QubitSelection

namespace QubitLayout

/-- Build a typed qubit layout from an actual duplicate-free list of physical
systems.  The logical-qubit count is the list length; no separate count can be
claimed by the caller. -/
def ofSystemIdx (systemIdx : List Nat) (systemIdxNodup : systemIdx.Nodup) :
    QubitLayout systemIdx.length where
  physical_idx := systemIdx.get
  physical_idx_injective := systemIdxNodup.injective_get

/-- List view of a typed layout, ordered by logical-qubit index. -/
public def systemIdx {qubitCount : Nat} (layout : QubitLayout qubitCount) : List Nat :=
  List.ofFn layout.physical_idx

@[simp] theorem systemIdx_ofSystemIdx (physicalIdx : List Nat)
    (physicalIdxNodup : physicalIdx.Nodup) :
    (ofSystemIdx physicalIdx physicalIdxNodup).systemIdx = physicalIdx :=
  List.ofFn_get physicalIdx

@[simp] theorem systemIdx_length {qubitCount : Nat}
    (layout : QubitLayout qubitCount) :
    layout.systemIdx.length = qubitCount := by
  simp [systemIdx]

public theorem systemIdx_nodup {qubitCount : Nat}
    (layout : QubitLayout qubitCount) :
    layout.systemIdx.Nodup := by
  exact List.nodup_ofFn.mpr layout.physical_idx_injective

/-- Append two actually disjoint typed layouts in logical-index order. -/
def append {leftCount rightCount : Nat}
    (left : QubitLayout leftCount) (right : QubitLayout rightCount)
    (disjoint : List.Disjoint left.systemIdx right.systemIdx) :
    QubitLayout (leftCount + rightCount) where
  physical_idx := Fin.append left.physical_idx right.physical_idx
  physical_idx_injective := by
    apply List.nodup_ofFn.mp
    rw [List.ofFn_fin_append]
    exact left.systemIdx_nodup.append right.systemIdx_nodup disjoint

@[simp] theorem systemIdx_append {leftCount rightCount : Nat}
    (left : QubitLayout leftCount) (right : QubitLayout rightCount)
    (disjoint : List.Disjoint left.systemIdx right.systemIdx) :
    (append left right disjoint).systemIdx =
      left.systemIdx ++ right.systemIdx := by
  simp [systemIdx, append, List.ofFn_fin_append]

end QubitLayout

end QuantumAlg

end
