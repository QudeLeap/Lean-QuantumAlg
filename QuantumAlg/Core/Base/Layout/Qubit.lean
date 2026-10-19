/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Signature
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

/-- Canonical placement of a qubit word on physical systems zero through
`qubitCount - 1`. -/
@[expose]
public def canonical (qubitCount : Nat) : QubitLayout qubitCount where
  physical_idx := Fin.val
  physical_idx_injective := Fin.val_injective

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

/-- The canonical layout lists every physical qubit in increasing order. -/
@[simp] public lemma canonical_systemIdx (qubitCount : Nat) :
    (canonical qubitCount).systemIdx = List.range qubitCount := by
  change List.ofFn (fun index : Fin qubitCount => index.val) = List.range qubitCount
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

@[simp] lemma systemIdx_ofSystemIdx (physicalIdx : List Nat)
    (physicalIdxNodup : physicalIdx.Nodup) :
    (ofSystemIdx physicalIdx physicalIdxNodup).systemIdx = physicalIdx :=
  List.ofFn_get physicalIdx

@[simp] lemma systemIdx_length {qubitCount : Nat}
    (layout : QubitLayout qubitCount) :
    layout.systemIdx.length = qubitCount := by
  simp [systemIdx]

public lemma systemIdx_nodup {qubitCount : Nat}
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

@[simp] lemma systemIdx_append {leftCount rightCount : Nat}
    (left : QubitLayout leftCount) (right : QubitLayout rightCount)
    (disjoint : List.Disjoint left.systemIdx right.systemIdx) :
    (append left right disjoint).systemIdx =
      left.systemIdx ++ right.systemIdx := by
  simp [systemIdx, append, List.ofFn_fin_append]

/-- The same addressed qubits as a dimension-certified physical layout. -/
@[expose, implicit_reducible]
public def toQuantum {qubitCount : Nat} (layout : QubitLayout qubitCount) :
    QuantumLayout qubitCount :=
  ((QuantumSignature.qubits qubitCount).place layout.physical_idx
    layout.physical_idx_injective).layout

/-- The physical conversion retains each actual qubit identity and dimension. -/
@[simp] public lemma toQuantum_wire {qubitCount : Nat} (layout : QubitLayout qubitCount)
    (index : Fin qubitCount) :
    layout.toQuantum.wire index = ⟨layout.physical_idx index, 2⟩ := rfl

/-- Fixed big-endian coordinates relate physical qubits to binary word labels. -/
public def basisEquiv {qubitCount : Nat} (layout : QubitLayout qubitCount) :
    layout.toQuantum.register.Index ≃ (Qubits qubitCount).Index :=
  QuantumSignature.qubitsIndexEquiv qubitCount

end QubitLayout

end QuantumAlg

end
