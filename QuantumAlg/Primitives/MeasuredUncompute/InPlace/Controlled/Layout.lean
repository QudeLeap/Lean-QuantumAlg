/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Framing
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.OperatorAgreement
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws
import all QuantumAlg.Core.Execution.Local.Framing.State
import all QuantumAlg.Core.Execution.Owned.Qubits

/-!
# One actual owned control beside the measured arithmetic frame

The original X/Y/A wires, complete EEA history and retained finite result
cells keep their identities. A separate supplied owned control occupies the
next physical address. The complete runtime basis follows those actual wire
records, so coherent control is not a classical store value or an uncharged
external reference. The three-field-register arithmetic is the existing
measured sequence [LYL+26, sec_point_add/sec_point_add.tex:24-36,52-121].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open Execution MAU.Inversion.SharedEEA ContextUnion

/-- The original complete three-word native width, including all EEA history. -/
@[reducible] def frameWidth (width : Nat) : Nat := (OutputCopy.encoding width).width

/-- The new owned control follows every original native wire. -/
def controlWire (width : Nat) : Nat := frameWidth width

private theorem original_bounded (width : Nat) (wire : Nat)
    (present : wire ∈ (NumeratorMeasurement.context width).physicalIdx) :
    wire < frameWidth width := by
  rw [NumeratorMeasurement.context_physical, InverseRuntimeFrame.after_physical] at present
  rcases List.mem_append.mp present with auxiliary | supplied
  · change wire ∈ List.ofFn (InputPreparation.auxiliaryPhysicalIndex width) at auxiliary
    obtain ⟨index, same⟩ := List.mem_ofFn.mp auxiliary
    have bound := (InputAssembly.auxiliaryPosition width index).isLt
    change InputPreparation.auxiliaryPhysicalIndex width index < (encoding width).width at bound
    rw [← same]
    change InputPreparation.auxiliaryPhysicalIndex width index < (encoding width).width + width
    omega
  · change wire ∈ List.ofFn
      (fun index : Fin (width + width) => InversePreparation.physicalIndex width index.val)
        at supplied
    obtain ⟨index, same⟩ := List.mem_ofFn.mp supplied
    have bound := index.isLt
    rw [← same]
    change InversePreparation.physicalIndex width index.val < (encoding width).width + width
    unfold InversePreparation.physicalIndex
    have complete := InputPreparation.complete_width width
    unfold InputPreparation.auxiliaryWidth InputPreparation.suffixWidth at complete
    split <;> omega

/-- The supplied control is one actual dimension-two system. -/
def controlQubitLayout (width : Nat) : QubitLayout 1 where
  physical_idx _ := controlWire width
  physical_idx_injective := fun _ _ _ => Subsingleton.elim _ _

def controlLayout (width : Nat) : QuantumLayout 1 :=
  (controlQubitLayout width).toQuantumLayout

/-- Its storage identity is fresh for all retained measurement cells. -/
def controlKey (width : Nat) : StorageKey :=
  (NumeratorMeasurement.context width).canonicalFreshKey

/-- A genuinely supplied owned control, without an initialization promise. -/
def controlContext (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout (controlKey width) (controlLayout width) (by exact
    List.not_mem_nil)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

theorem controlContext_physical (width : Nat) :
    (controlContext width).physicalIdx = [controlWire width] := by
  change ((controlLayout width).wires ++ []).map QuantumWire.identity = _
  simp only [List.append_nil, QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun _ : Fin 1 => controlWire width) = _
  simp

theorem control_disjoint (width : Nat) :
    RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context width) (controlContext width) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint (NumeratorMeasurement.context width).keys [controlKey width]
    apply List.disjoint_left.mpr
    intro key present singleton
    have same := List.mem_singleton.mp singleton
    rw [same] at present
    exact (NumeratorMeasurement.context width).canonicalFreshKey_fresh present
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [controlContext_physical]
    apply List.disjoint_left.mpr
    intro wire present singleton
    have same := List.mem_singleton.mp singleton
    rw [same] at present
    have bound := original_bounded width (controlWire width) present
    exact (Nat.lt_irrefl (frameWidth width)) bound

/-- The already allocated measured body and its physically charged quantum control. -/
@[reducible] def context (width : Nat) : RuntimeCtx .quantum :=
  (NumeratorMeasurement.context width).disjointUnion (controlContext width)
    (control_disjoint width)

theorem context_physical (width : Nat) :
    (context width).physicalIdx =
      (NumeratorMeasurement.context width).physicalIdx ++ [controlWire width] := by
  rw [context, RuntimeCtx.physicalIdx_disjointUnion, controlContext_physical]

private theorem control_wires (width : Nat) :
    (controlLayout width).wires = (controlContext width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (controlLayout width).wires = (controlLayout width).wires ++ []
  exact (List.append_nil _).symm

/-- The real owned control has the canonical finite one-bit basis. -/
def controlBasis (width : Nat) : (controlContext width).register.Index ≃ Fin 2 :=
  (basisOfEqualWires (controlLayout width) (controlContext width).quantumLayout
    (control_wires width)).symm.trans (controlQubitLayout width).binaryIndexEquiv

/-- Exact binary assembly: the leading logical control is the appended physical control. -/
def basis (width : Nat) : (context width).register.Index ≃ Fin (2 ^ (1 + frameWidth width)) :=
  (unionBasisEquiv (NumeratorMeasurement.context width) (controlContext width)
    (control_disjoint width)).trans
      ((Equiv.prodCongr (NumeratorMeasurement.frameBasis width) (controlBasis width)).trans
        ((Equiv.prodComm _ _).trans (prodEquiv (m := 1) (n := frameWidth width))))

/-- Native basis labels retain every real control, arithmetic and history coordinate. -/
def label (width : Nat) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    (context width).register.Index :=
  (unionBasisEquiv (NumeratorMeasurement.context width) (controlContext width)
    (control_disjoint width)).symm (original, (controlBasis width).symm control)

theorem basis_label (width : Nat) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    basis width (label width control original) =
      prodEquiv (control, NumeratorMeasurement.frameBasis width original) := by
  change (prodEquiv (m := 1) (n := frameWidth width))
    (controlBasis width ((unionBasisEquiv _ _ (control_disjoint width))
      ((unionBasisEquiv _ _ (control_disjoint width)).symm
        (original, (controlBasis width).symm control))).2,
     NumeratorMeasurement.frameBasis width
      ((unionBasisEquiv _ _ (control_disjoint width))
        ((unionBasisEquiv _ _ (control_disjoint width)).symm
          (original, (controlBasis width).symm control))).1) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The original actual finite-result read survives the union unchanged. -/
def resultInput (width : Nat) : CInputRef (context width) (.fixedVector width (.finite 2)) :=
  inputLeft (control_disjoint width) (NumeratorMeasurement.input width)

/-- Every retained classical cell belongs to the original source store. -/
theorem resultInput_read (width : Nat) (store : Store (context width)) :
    store.read (resultInput width) =
      ((storeEquiv (control_disjoint width) store).1).read (NumeratorMeasurement.input width) := by
  obtain ⟨⟨first, second⟩, rfl⟩ := (storeEquiv (control_disjoint width)).symm.surjective store
  rw [Equiv.apply_symm_apply]
  exact contextUnion_read_join_left (control_disjoint width) first second _

/-- Every native address and the real control occurs in the complete actual context. -/
theorem native_contained (width : Nat) :
    List.range (1 + frameWidth width) ⊆ (context width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  rw [context_physical]
  by_cases original : wire < frameWidth width
  · apply List.mem_append_left
    rw [NumeratorMeasurement.context_physical]
    exact InverseRuntimeFrame.range_contained width (List.mem_range.mpr original)
  · apply List.mem_append_right
    have same : wire = controlWire width := by unfold controlWire; omega
    exact List.mem_singleton.mpr same

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
