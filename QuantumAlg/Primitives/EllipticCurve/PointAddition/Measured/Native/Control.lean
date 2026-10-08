/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Layout
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Product
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement

/-!
# Literal control lists for the affine point-addition frame

The exceptional branch first compiles its negative inner control without the
outer control in the carrier. The outer positive control then expands that
actual list. A complete position-preserving regrouping recovers the original
two-bit prefix. Every borrowed coordinate is restored for arbitrary inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open EncodedBit GateSpec BinaryLabelEncoding

/-- The two coherent sectors used by the concrete affine schedule. -/
inductive OffsetControl where
  | supplied
  | exceptional
  deriving DecidableEq

@[reducible] def controlWidth : OffsetControl → Nat
  | .supplied => 1
  | .exceptional => 2

def activeValue : (control : OffsetControl) → Fin (2 ^ controlWidth control)
  | .supplied => 1
  | .exceptional => 2

private def prefixGrouping {Data : Type} :
    Fin (2 ^ 2) × Data ≃ Fin (2 ^ 1) × (Fin (2 ^ 1) × Data) :=
  (Equiv.prodCongr (prodEquiv (m := 1) (n := 1)).symm (Equiv.refl Data)).trans
    (Equiv.prodAssoc _ _ _)

private def prefixRegrouping {Data : Type} (data : BinaryLabelEncoding Data) :
    FullPlacement (prod (finIdentity 1) (prod (finIdentity 1) data))
      (prod (finIdentity 2) data) :=
  FullPlacement.ofEqualWidth _ _ prefixGrouping (by
    change 1 + (1 + data.width) = 2 + data.width
    omega) (by
      rintro ⟨control, state⟩
      obtain ⟨⟨first, second⟩, rfl⟩ := (prodEquiv (m := 1) (n := 1)).surjective control
      simp only [prefixGrouping, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.prodAssoc_apply]
      apply Fin.ext
      change (data.encode state).val + 2 ^ data.width * second.val +
        2 ^ (1 + data.width) * first.val =
          (data.encode state).val + 2 ^ data.width * (second.val + 2 * first.val)
      rw [pow_add]
      ring)

private theorem prefixBit_wire (index : Fin (finIdentity 1).width) :
    (finIdentityBit 1 index).wire = index := rfl

private def negativePrefixGates {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (source : List (GateSpec data)) :
    List (GateSpec (prod (finIdentity 1) data)) :=
  let control := prodLeftBit (finIdentity 1) data (finIdentityBit 1 0)
  [.x control] ++
    controlRightList (finIdentityBit 1) bits prefixBit_wire bitsWire
      (by change 5 ≤ 1 + data.width; omega) (finIdentityBit 1 0) source ++
    [.x control]

/-- Actual positive or mixed-polarity native expansion of the supplied source list. -/
def prefixControlGates {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl) (source : List (GateSpec data)) :
    List (GateSpec (prod (finIdentity (controlWidth control)) data)) :=
  match control with
  | .supplied =>
      controlRightList (finIdentityBit 1) bits prefixBit_wire bitsWire
        (by change 5 ≤ 1 + data.width; omega) (finIdentityBit 1 0) source
  | .exceptional =>
      (controlRightList (finIdentityBit 1)
        (productBit (finIdentityBit 1) bits) prefixBit_wire
        (productBit_wire (left := finIdentity 1) (right := data)
          (finIdentityBit 1) bits prefixBit_wire bitsWire)
        (by change 5 ≤ 1 + (1 + data.width); omega) (finIdentityBit 1 0)
        (negativePrefixGates data bits bitsWire capacity source)).map
          (prefixRegrouping data).placeGate

private theorem negativePrefixGates_step {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (source : List (GateSpec data)) (state : Fin (2 ^ 1) × Data) :
    stepList (negativePrefixGates data bits bitsWire capacity source) state =
      (state.1, if state.1 = 0 then stepList source state.2 else state.2) := by
  rcases state with ⟨control, state⟩
  simp only [negativePrefixGates, stepList_append, stepList, GateSpec.step, id_eq]
  erw [controlRightList_step]
  fin_cases control <;>
    norm_num [finIdentityBit, ofEquivBit, WireAddress.bitIndex, WireAddress.flipBit, prodLeftBit]

/-- Exact all-label action, including both unchanged prefix controls and every dirty field. -/
theorem pointPrefixControlGates_step {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl) (source : List (GateSpec data))
    (state : Fin (2 ^ controlWidth control) × Data) :
    stepList (prefixControlGates data bits bitsWire capacity control source) state =
      (state.1, if state.1 = activeValue control then stepList source state.2 else state.2) := by
  cases control
  · rw [prefixControlGates]
    erw [controlRightList_step]
    rcases state with ⟨control, state⟩
    fin_cases control <;>
      norm_num [finIdentityBit, ofEquivBit, WireAddress.bitIndex, activeValue, Fin.ext_iff]
  · rw [prefixControlGates, FullPlacement.placeGates_step]
    simp only [FullPlacement.step, prefixRegrouping, FullPlacement.ofEqualWidth_grouping]
    erw [controlRightList_step]
    rcases state with ⟨control, state⟩
    fin_cases control <;>
      norm_num [prefixGrouping, negativePrefixGates_step, activeValue,
        finIdentityBit, ofEquivBit, WireAddress.bitIndex, prodEquiv, finProdFinEquiv,
        Fin.ext_iff, Fin.modNat]

/-- The physical program has exact unit phase on every basis label, with no clean-bit premise. -/
theorem pointPrefixControlGates_realizes {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl) (source : List (GateSpec data))
    (layout : QubitLayout (controlWidth control + data.width)) :
    UnitaryCircuit.Realizes (layout := layout) (prod (finIdentity (controlWidth control)) data)
      (programList layout .empty (prefixControlGates data bits bitsWire capacity control source))
      (fun state =>
        (state.1, if state.1 = activeValue control then stepList source state.2 else state.2)) :=
  realizesList_congrStep layout .empty _
    (pointPrefixControlGates_step data bits bitsWire capacity control source)

/-- Both negative-control X gates themselves undergo the outer native control expansion. -/
theorem pointPrefixControlGates_length_bound {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl) (source : List (GateSpec data)) :
    (prefixControlGates data bits bitsWire capacity control source).length ≤
      match control with
      | .supplied => 4 * source.length
      | .exceptional => 16 * source.length + 8 := by
  cases control
  · exact controlRightList_length_bound (finIdentityBit 1) bits prefixBit_wire bitsWire
      (by change 5 ≤ 1 + data.width; omega) (finIdentityBit 1 0) source
  · have inner := controlRightList_length_bound (finIdentityBit 1) bits prefixBit_wire
      bitsWire (by change 5 ≤ 1 + data.width; omega) (finIdentityBit 1 0) source
    have outer := controlRightList_length_bound (finIdentityBit 1)
      (productBit (finIdentityBit 1) bits) prefixBit_wire
      (productBit_wire (left := finIdentity 1) (right := data)
          (finIdentityBit 1) bits prefixBit_wire bitsWire)
      (by change 5 ≤ 1 + (1 + data.width); omega) (finIdentityBit 1 0)
      (negativePrefixGates data bits bitsWire capacity source)
    simp only [prefixControlGates, List.length_map]
    have negativeLength : (negativePrefixGates data bits bitsWire capacity source).length =
        2 + (controlRightList (finIdentityBit 1) bits prefixBit_wire bitsWire
          (by change 5 ≤ 1 + data.width; omega) (finIdentityBit 1 0) source).length := by
      simp only [negativePrefixGates, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [negativeLength] at outer
    omega

private theorem rightControl_counts {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (leftWire : ∀ index, (leftBits index).wire = index)
    (rightWire : ∀ index, (rightBits index).wire = index)
    (capacity : 5 ≤ left.width + right.width) (control : EncodedBit left)
    (source : List (GateSpec right)) :
    ((controlRightList leftBits rightBits leftWire rightWire capacity control source).map
      xMultiplicity).sum = 0 ∧
    ((controlRightList leftBits rightBits leftWire rightWire capacity control source).map
      cnotMultiplicity).sum = (source.map xMultiplicity).sum ∧
    ((controlRightList leftBits rightBits leftWire rightWire capacity control source).map
      toffoliMultiplicity).sum =
        (source.map cnotMultiplicity).sum + 4 * (source.map toffoliMultiplicity).sum := by
  have counts := controlWithin_native_counts (productBit leftBits rightBits)
    (productBit_wire leftBits rightBits leftWire rightWire) capacity
    (prodLeftBit left right control) (source.map (GateSpec.prodRight left))
    (rightList_disjoint control source)
  have same := map_event_prodRight (oracles := .empty) left source
  have singles := sum_xMultiplicity_eq_of_events_eq .empty same
  have cnots := sum_cnotMultiplicity_eq_of_events_eq .empty same
  have toffolis := sum_toffoliMultiplicity_eq_of_events_eq .empty same
  rw [singles, cnots, toffolis] at counts
  exact counts

/-- Actual ordered primitive events, without replacing them by abstract controlled labels. -/
theorem pointPrefixControlGates_trace {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl) (source : List (GateSpec data))
    (layout : QubitLayout (controlWidth control + data.width)) :
    (programList layout .empty
      (prefixControlGates data bits bitsWire capacity control source)).eventTrace =
        (prefixControlGates data bits bitsWire capacity control source).map (event .empty) :=
  programList_eventTrace layout .empty
    (prefixControlGates data bits bitsWire capacity control source)

/-- Exact cost cardinality charges every emitted gate, including both outer-controlled X gates. -/
theorem pointPrefixControlGates_event_count {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl) (source : List (GateSpec data))
    (layout : QubitLayout (controlWidth control + data.width)) :
    (programList layout .empty
      (prefixControlGates data bits bitsWire capacity control source)).eventCost.card =
        (prefixControlGates data bits bitsWire capacity control source).length :=
  programList_eventCost_card layout .empty
    (prefixControlGates data bits bitsWire capacity control source)

/-- Exact native multiplicities of the positive and mixed-polarity control expansions. -/
theorem pointPrefixControlGates_counts {Data : Type} (data : BinaryLabelEncoding Data)
    (bits : Fin data.width → EncodedBit data) (bitsWire : ∀ index, (bits index).wire = index)
    (capacity : 4 ≤ data.width) (control : OffsetControl) (source : List (GateSpec data)) :
    ((prefixControlGates data bits bitsWire capacity control source).map xMultiplicity).sum = 0 ∧
      ((prefixControlGates data bits bitsWire capacity control source).map cnotMultiplicity).sum =
        (match control with
          | .supplied => (source.map xMultiplicity).sum
          | .exceptional => 2) ∧
      ((prefixControlGates data bits bitsWire capacity control source).map
        toffoliMultiplicity).sum =
        (match control with
          | .supplied => (source.map cnotMultiplicity).sum +
              4 * (source.map toffoliMultiplicity).sum
          | .exceptional => (source.map xMultiplicity).sum +
              4 * (source.map cnotMultiplicity).sum +
                16 * (source.map toffoliMultiplicity).sum) := by
  have inner := rightControl_counts (finIdentity 1) data (finIdentityBit 1) bits
    prefixBit_wire bitsWire (by change 5 ≤ 1 + data.width; omega) (finIdentityBit 1 0) source
  cases control
  · exact inner
  · let negative := negativePrefixGates data bits bitsWire capacity source
    let outer := controlRightList (finIdentityBit 1) (productBit (finIdentityBit 1) bits)
      prefixBit_wire
      (productBit_wire (left := finIdentity 1) (right := data)
        (finIdentityBit 1) bits prefixBit_wire bitsWire)
      (by change 5 ≤ 1 + (1 + data.width); omega) (finIdentityBit 1 0) negative
    have negativeCounts : (negative.map xMultiplicity).sum = 2 ∧
        (negative.map cnotMultiplicity).sum = (source.map xMultiplicity).sum ∧
        (negative.map toffoliMultiplicity).sum =
          (source.map cnotMultiplicity).sum + 4 * (source.map toffoliMultiplicity).sum := by
      simp [negative, negativePrefixGates, inner.1, inner.2.1, inner.2.2]
    have outerCounts := rightControl_counts (finIdentity 1) (prod (finIdentity 1) data)
      (finIdentityBit 1) (productBit (finIdentityBit 1) bits) prefixBit_wire
      (productBit_wire (left := finIdentity 1) (right := data)
        (finIdentityBit 1) bits prefixBit_wire bitsWire)
      (by change 5 ≤ 1 + (1 + data.width); omega) (finIdentityBit 1 0) negative
    change (outer.map xMultiplicity).sum = 0 ∧
      (outer.map cnotMultiplicity).sum = (negative.map xMultiplicity).sum ∧
      (outer.map toffoliMultiplicity).sum =
        (negative.map cnotMultiplicity).sum + 4 * (negative.map toffoliMultiplicity).sum
      at outerCounts
    rw [negativeCounts.1, negativeCounts.2.1, negativeCounts.2.2] at outerCounts
    have same :
        (prefixControlGates data bits bitsWire capacity .exceptional source).map (event .empty) =
          outer.map (event .empty) := by
      change (outer.map (prefixRegrouping data).placeGate).map (event .empty) = _
      simp only [List.map_map, Function.comp_def, FullPlacement.placeGate_event]
    rw [sum_xMultiplicity_eq_of_events_eq .empty same,
      sum_cnotMultiplicity_eq_of_events_eq .empty same,
      sum_toffoliMultiplicity_eq_of_events_eq .empty same]
    exact ⟨outerCounts.1, outerCounts.2.1, outerCounts.2.2.trans (by ring)⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
