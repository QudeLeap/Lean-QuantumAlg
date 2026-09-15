/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Mathematics
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Layout
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Ports

/-!
# Actual measured affine point-addition boundary

The supplied coherent control activates ordinary affine addition by one fixed
classical point. Only the active input excludes that point and its inverse.
The exceptional second multiplier is handled internally, without imposing a
reverse-addition domain [LYL+26, sec_point_add/sec_point_add.tex:24-36,119-123].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

/-- The original affine domain restricts the active control sector alone. -/
def affineAllowed {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (control : Bool) (P Q : AffinePoint E) : Prop :=
  control = true → P ≠ Q ∧ P ≠ AffinePoint.negate Q

/-- The first preserved operand is the original coordinate difference. -/
def firstDifference {p : Nat} (x xQ : ZMod p) : ZMod p := x - xQ

/-- Canonical field slope; no inverse of the numerator or slope is taken. -/
def slope {p : Nat} [Fact p.Prime] (x y xQ yQ : ZMod p) : ZMod p :=
  (y - yQ) / firstDifference x xQ

/-- The second preserved operand becomes the fixed x coordinate minus the result's x. -/
def secondDifference {p : Nat} [Fact p.Prime] (x y xQ yQ : ZMod p) : ZMod p :=
  firstDifference x xQ + 3 * xQ - slope x y xQ yQ ^ 2

/-- A total classical constant; the reachable exceptional arm supplies its domain internally. -/
def exceptionalSlope {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : ZMod p :=
  (doubleY E (AffinePoint.negate Q) - Q.y) /
    (doubleX E (AffinePoint.negate Q) - Q.x)

/-- Only a nonzero preserved multiplier activates the second measured arithmetic call. -/
def normalControl {p : Nat} (control : Bool) (difference : ZMod p) : Bool :=
  control && decide (difference ≠ 0)

/-- Independent field output, with a reversible constant subtraction on the exceptional arm. -/
def fieldOutput {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Bool) (x y : ZMod p) : ZMod p × ZMod p :=
  if control then
    let value := slope x y Q.x Q.y
    let difference := secondDifference x y Q.x Q.y
    (Q.x - difference,
      (if difference = 0 then value - exceptionalSlope E Q else difference * value) - Q.y)
  else (x, y)

open Execution ContextUnion MeasuredUncompute

/-- The complete original field frame and both real quantum control bits. -/
abbrev Raw (width : Nat) := (ProductPlacement.Frame width × Bool) × Bool

/-- Logical bits follow their original physical frame order, then C and then N. -/
def encoding (width : Nat) : BinaryLabelEncoding (Raw width) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    BinaryLabelEncoding.bool

/-- The only new qubit follows the frozen arithmetic body's supplied control. -/
def selectorWire (width : Nat) : Nat := InPlaceControlled.frameWidth width + 1

def selectorQubitLayout (width : Nat) : QubitLayout 1 where
  physical_idx _ := selectorWire width
  physical_idx_injective := fun _ _ _ => Subsingleton.elim _ _

def selectorLayout (width : Nat) : QuantumLayout 1 :=
  (selectorQubitLayout width).toQuantumLayout

/-- The internal selector owns a real key distinct from every original outcome and control. -/
def selectorKey (width : Nat) : StorageKey := (InPlaceControlled.context width).canonicalFreshKey

/-- This body receives the allocated selector; its enclosing preparation establishes zero. -/
def selectorContext (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout (selectorKey width) (selectorLayout width)
    (by exact List.not_mem_nil)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

theorem selectorContext_physical (width : Nat) :
    (selectorContext width).physicalIdx = [selectorWire width] := by
  change ((selectorLayout width).wires ++ []).map QuantumWire.identity = _
  simp only [List.append_nil, QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun _ : Fin 1 => selectorWire width) = _
  simp

theorem selector_disjoint (width : Nat) :
    RuntimeCtx.StorageDisjoint (InPlaceControlled.context width) (selectorContext width) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint (InPlaceControlled.context width).keys [selectorKey width]
    apply List.disjoint_left.mpr
    intro key present singleton
    have same := List.mem_singleton.mp singleton
    rw [same] at present
    exact (InPlaceControlled.context width).canonicalFreshKey_fresh present
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [selectorContext_physical]
    apply List.disjoint_left.mpr
    intro wire present singleton
    have same := List.mem_singleton.mp singleton
    rw [same, InPlaceControlled.context_physical] at present
    rcases List.mem_append.mp present with original | control
    · have bound := InPlaceControlled.original_bounded width (selectorWire width) original
      unfold selectorWire at bound
      omega
    · have equal := List.mem_singleton.mp control
      unfold selectorWire InPlaceControlled.controlWire at equal
      omega

/-- Actual storage union keeps all field/history wires and reuses the same n finite cells. -/
@[reducible] def context (width : Nat) : RuntimeCtx .quantum :=
  (InPlaceControlled.context width).disjointUnion (selectorContext width)
    (selector_disjoint width)

theorem context_physical (width : Nat) :
    (context width).physicalIdx =
      (InPlaceControlled.context width).physicalIdx ++ [selectorWire width] := by
  rw [context, RuntimeCtx.physicalIdx_disjointUnion, selectorContext_physical]

private theorem selector_wires (width : Nat) :
    (selectorLayout width).wires = (selectorContext width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (selectorLayout width).wires = (selectorLayout width).wires ++ []
  exact (List.append_nil _).symm

/-- The real owned selector contributes precisely one binary quantum coordinate. -/
def selectorBasis (width : Nat) : (selectorContext width).register.Index ≃ Fin 2 :=
  (basisOfEqualWires (selectorLayout width) (selectorContext width).quantumLayout
    (selector_wires width)).symm.trans (selectorQubitLayout width).binaryIndexEquiv

private def frameControlBasis (width : Nat) :
    (InPlaceControlled.context width).register.Index ≃
      Fin (2 ^ (InPlaceControlled.frameWidth width + 1)) :=
  (unionBasisEquiv (NumeratorMeasurement.context width) (InPlaceControlled.controlContext width)
    (InPlaceControlled.control_disjoint width)).trans
      ((Equiv.prodCongr (NumeratorMeasurement.frameBasis width)
        (InPlaceControlled.controlBasis width)).trans
          (prodEquiv (m := InPlaceControlled.frameWidth width) (n := 1)))

/-- Complete runtime placement reads Frame,C,N in their actual physical bit order. -/
def basis (width : Nat) : (context width).register.Index ≃ Fin (2 ^ (encoding width).width) :=
  (unionBasisEquiv (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width)).trans
      ((Equiv.prodCongr (frameControlBasis width) (selectorBasis width)).trans
        (prodEquiv (m := InPlaceControlled.frameWidth width + 1) (n := 1)))

/-- Full labels retain the old measured body basis and both quantum control values. -/
def label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    (context width).register.Index :=
  (unionBasisEquiv (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width)).symm
      (InPlaceControlled.label width control original, (selectorBasis width).symm selector)

theorem basis_label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    basis width (label width control selector original) =
      prodEquiv (prodEquiv (NumeratorMeasurement.frameBasis width original, control),
        selector) := by
  change prodEquiv (m := InPlaceControlled.frameWidth width + 1) (n := 1)
    (frameControlBasis width
      ((unionBasisEquiv _ _ (selector_disjoint width))
        ((unionBasisEquiv _ _ (selector_disjoint width)).symm
          (InPlaceControlled.label width control original, (selectorBasis width).symm selector))).1,
    selectorBasis width ((unionBasisEquiv _ _ (selector_disjoint width))
      ((unionBasisEquiv _ _ (selector_disjoint width)).symm
        (InPlaceControlled.label width control original,
          (selectorBasis width).symm selector))).2) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change prodEquiv (m := InPlaceControlled.frameWidth width + 1) (n := 1)
    (prodEquiv (m := InPlaceControlled.frameWidth width) (n := 1)
    (NumeratorMeasurement.frameBasis width
      ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width))
        ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width)).symm
          (original, (InPlaceControlled.controlBasis width).symm control))).1,
      InPlaceControlled.controlBasis width
        ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width))
          ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width)).symm
            (original, (InPlaceControlled.controlBasis width).symm control))).2), selector) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The same real finite result cells are read by both measured arithmetic calls. -/
def resultInput (width : Nat) : CInputRef (context width) (.fixedVector width (.finite 2)) :=
  inputLeft (selector_disjoint width) (InPlaceControlled.resultInput width)

/-- Every native physical position is an already resident owned qubit. -/
theorem native_contained (width : Nat) :
    List.range (encoding width).width ⊆ (context width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  rw [context_physical]
  by_cases old : wire < 1 + InPlaceControlled.frameWidth width
  · exact List.mem_append_left _ (InPlaceControlled.native_contained width (List.mem_range.mpr old))
  · have same : wire = selectorWire width := by
      change wire < (InPlaceControlled.frameWidth width + 1) + 1 at bound
      unfold selectorWire
      omega
    exact List.mem_append_right _ (List.mem_singleton.mpr same)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
