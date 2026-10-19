/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Borrowed
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive

/-!
# Native control of a complete arithmetic word in a product register

The control belongs to the left field and the source word acts on the right
field. Gate-local borrowing uses only existing positions of the same product
carrier and restores them before the next source instruction. The original
source word may use every wire of its right field.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Left Right : Type} {left : BinaryLabelEncoding Left}
  {right : BinaryLabelEncoding Right}

/-- All physical bit lenses of two complete fields in their actual product order. -/
def productBit (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (position : Fin (BinaryLabelEncoding.prod left right).width) :
    EncodedBit (BinaryLabelEncoding.prod left right) :=
  if first : position.val < left.width then
    BinaryLabelEncoding.prodLeftBit left right (leftBits ⟨position.val, first⟩)
  else
    BinaryLabelEncoding.prodRightBit left right
      (rightBits ⟨position.val - left.width, by
        have bound : position.val < left.width + right.width := position.isLt
        omega⟩)

/-- The combined lens family covers precisely the original physical coordinates. -/
lemma productBit_wire (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (leftWire : ∀ position, (leftBits position).wire = position)
    (rightWire : ∀ position, (rightBits position).wire = position)
    (position : Fin (BinaryLabelEncoding.prod left right).width) :
    (productBit leftBits rightBits position).wire = position := by
  unfold productBit
  split
  · apply Fin.ext
    simp only [BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire, leftWire]
  · apply Fin.ext
    simp only [BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire, rightWire]
    omega

private lemma rightList_disjoint (control : EncodedBit left) (gates : List (GateSpec right)) :
    ∀ gate, gate ∈ gates.map (prodRight left) →
      bitDisjoint (BinaryLabelEncoding.prodLeftBit left right control) gate := by
  intro gate present
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp present
  exact bitDisjoint_prodRight_leftBit left right control source

/-- Actual native control of a right-field instruction list, with no new physical wire. -/
def controlRightList (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (leftWire : ∀ position, (leftBits position).wire = position)
    (rightWire : ∀ position, (rightBits position).wire = position)
    (capacity : 5 ≤ left.width + right.width) (control : EncodedBit left)
    (gates : List (GateSpec right)) : List (GateSpec (BinaryLabelEncoding.prod left right)) :=
  controlWithin (productBit leftBits rightBits)
    (productBit_wire leftBits rightBits leftWire rightWire) capacity
    (BinaryLabelEncoding.prodLeftBit left right control)
    (gates.map (prodRight left)) (rightList_disjoint control gates)

/-- Both control branches preserve every left-field value and every source-word correlation. -/
lemma controlRightList_step (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (leftWire : ∀ position, (leftBits position).wire = position)
    (rightWire : ∀ position, (rightBits position).wire = position)
    (capacity : 5 ≤ left.width + right.width) (control : EncodedBit left)
    (gates : List (GateSpec right)) (state : Left × Right) :
    stepList (controlRightList leftBits rightBits leftWire rightWire capacity control gates) state =
      (state.1, if control.get state.1 then stepList gates state.2 else state.2) := by
  rw [controlRightList, controlWithin_step, stepList_prodRight]
  change (if control.get state.1 then (state.1, stepList gates state.2) else state) = _
  cases control.get state.1 <;> rfl

/-- The default-model program has the exact coherent conditional action, including phase. -/
lemma controlRightList_realizes (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (leftWire : ∀ position, (leftBits position).wire = position)
    (rightWire : ∀ position, (rightBits position).wire = position)
    (capacity : 5 ≤ left.width + right.width) (control : EncodedBit left)
    (layout : QubitLayout (left.width + right.width)) (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (gates : List (GateSpec right)) :
    UnitaryCircuit.Realizes (layout := layout) (BinaryLabelEncoding.prod left right)
      (programList layout oracles
        (controlRightList leftBits rightBits leftWire rightWire capacity control gates)) environment
      (fun state => (state.1, if control.get state.1 then stepList gates state.2 else state.2)) :=
  realizesList_congrStep layout oracles _
    (controlRightList_step leftBits rightBits leftWire rightWire capacity control gates) environment

/-- The actual controlled arithmetic list uses at most four instructions per source gate. -/
lemma controlRightList_length_bound (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (leftWire : ∀ position, (leftBits position).wire = position)
    (rightWire : ∀ position, (rightBits position).wire = position)
    (capacity : 5 ≤ left.width + right.width) (control : EncodedBit left)
    (gates : List (GateSpec right)) :
    (controlRightList leftBits rightBits leftWire rightWire capacity control gates).length ≤
      4 * gates.length := by
  have bound := controlWithin_length_bound (productBit leftBits rightBits)
    (productBit_wire leftBits rightBits leftWire rightWire) capacity
    (BinaryLabelEncoding.prodLeftBit left right control)
    (gates.map (prodRight left)) (rightList_disjoint control gates)
  simpa only [controlRightList, List.length_map] using bound

/-- Coherent selection converts X to CNOT and expands each Toffoli into four Toffolis. -/
lemma controlRightList_native_counts (leftBits : Fin left.width → EncodedBit left)
    (rightBits : Fin right.width → EncodedBit right)
    (leftWire : ∀ position, (leftBits position).wire = position)
    (rightWire : ∀ position, (rightBits position).wire = position)
    (capacity : 5 ≤ left.width + right.width) (control : EncodedBit left)
    (gates : List (GateSpec right)) :
    ((controlRightList leftBits rightBits leftWire rightWire capacity control gates).map
        xMultiplicity).sum = 0 ∧
      ((controlRightList leftBits rightBits leftWire rightWire capacity control gates).map
        cnotMultiplicity).sum = (gates.map xMultiplicity).sum ∧
      ((controlRightList leftBits rightBits leftWire rightWire capacity control gates).map
        toffoliMultiplicity).sum =
        (gates.map cnotMultiplicity).sum + 4 * (gates.map toffoliMultiplicity).sum := by
  have counts := controlWithin_native_counts (productBit leftBits rightBits)
    (productBit_wire leftBits rightBits leftWire rightWire) capacity
    (BinaryLabelEncoding.prodLeftBit left right control)
    (gates.map (prodRight left)) (rightList_disjoint control gates)
  have same := map_event_prodRight (oracles := .empty) left gates
  simpa only [controlRightList,
    sum_xMultiplicity_eq_of_events_eq .empty same,
    sum_cnotMultiplicity_eq_of_events_eq .empty same,
    sum_toffoliMultiplicity_eq_of_events_eq .empty same] using counts

end

end QuantumAlg.EncodedBit.GateSpec
