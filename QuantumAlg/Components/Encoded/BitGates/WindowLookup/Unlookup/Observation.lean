/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Reference
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber

/-!
# Exact original table graph and retained address observations

Naming or physically resetting result values preserves all supplied low
and high address fields. The original table graph determines those result
values from these protected address fields. Consequently clearing its result
word is injective on that graph; this is the concrete isometry boundary
needed for normalized measurement-unlookup weights.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)

/-- The static table word at the complete original split low/high address. -/
def tableAt
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (state : Data) : Fin (2 ^ resultWidth) :=
  table ((frame.high.stack ⟨0, by omega⟩).get state)
    (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state)
    (frame.low.prefixLabel lowWidth (Nat.le_refl _) state)

/-- Exact basis graph of the original table lookup on the existing physical result word. -/
def Graph
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (state : Data) : Prop :=
  ∀ index, (frame.result.bit index).get state = (frame.tableAt table state).val.testBit index.val

/-- Naming a result outcome retains every original high-address readout. -/
lemma resultSet_highAddress (value : Fin (2 ^ resultWidth)) (index : Fin highRemaining)
    (state : Data) :
    (frame.high.address index).get (resultSetConstant frame.result value state) =
      (frame.high.address index).get state :=
  resultSetConstant_observed frame.result value _
    (fun target => Ne.symm (frame.highAddressResult index target)) state

/-- Naming a result outcome retains every original high-stack readout. -/
lemma resultSet_highStack (value : Fin (2 ^ resultWidth)) (index : Fin (highRemaining + 1))
    (state : Data) :
    (frame.high.stack index).get (resultSetConstant frame.result value state) =
      (frame.high.stack index).get state :=
  resultSetConstant_observed frame.result value _
    (fun target => Ne.symm (frame.highStackResult index target)) state

/-- Naming a result outcome retains every original low-address readout. -/
lemma resultSet_lowAddress (value : Fin (2 ^ resultWidth)) (index : Fin lowWidth) (state : Data) :
    (frame.low.address index).get (resultSetConstant frame.result value state) =
      (frame.low.address index).get state :=
  resultSetConstant_observed frame.result value _
    (fun target => Ne.symm (frame.lowAddressResult index target)) state

/-- The original complete table address is unchanged by naming or clearing any result outcome. -/
lemma tableAt_resultSet
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (value : Fin (2 ^ resultWidth)) (state : Data) :
    frame.tableAt table (resultSetConstant frame.result value state) =
      frame.tableAt table state := by
  unfold tableAt
  rw [frame.resultSet_highStack,
    frame.high.addressLabelAt_congr _ _
      (fun index => frame.resultSet_highAddress value index state),
    frame.low.prefixLabel_congr _ _ _ _ (fun index => frame.resultSet_lowAddress value index state)]

/-- The original physically reused unary target subset is zero after clearing the result word. -/
lemma resultSet_zero_low (state : Data) (index : Fin (2 ^ lowWidth)) :
    (frame.low.target index).get (resultSetConstant frame.result 0 state) = false := by
  have reading : (frame.low.target index).get (resultSetConstant frame.result 0 state) =
      (frame.result.bit (frame.lowResult index)).get (resultSetConstant frame.result 0 state) := by
    rw [← (frame.low.target index).get_eq, frame.lowResultWire]
    exact (frame.result.bit (frame.lowResult index)).get_eq _
  rw [reading, resultSetConstant_get frame.result frame.resultDistinct]
  simp

/-- Clearing or naming result values preserves the original explicit high-prefix zero promise. -/
lemma resultSet_clean (value : Fin (2 ^ resultWidth)) (state : Data)
    (clean : frame.high.CleanFrom 0 state) :
    frame.high.CleanFrom 0 (resultSetConstant frame.result value state) := by
  intro index later
  rw [frame.resultSet_highStack]
  exact clean index later

/-- Clearing the result word is injective on the concrete original lookup graph. -/
lemma resultSet_zero_injective_graph (physical : QubitLayout encoding.width)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (first second : Data) (firstGraph : frame.Graph table first)
    (secondGraph : frame.Graph table second)
    (same : resultSetConstant frame.result 0 first = resultSetConstant frame.result 0 second) :
    first = second := by
  have address : frame.tableAt table first = frame.tableAt table second := by
    rw [← frame.tableAt_resultSet table 0 first, same, frame.tableAt_resultSet]
  apply encoding.encode_injective
  apply physical.basisEquiv.symm.injective
  apply wordBasis_eq_of_coordinates physical frame.result frame.resultDistinct
  · intro index
    rw [encodedPhysicalBit, encodedPhysicalBit, firstGraph,
      congrArg (fun value : Fin (2 ^ resultWidth) => value.val.testBit index.val) address,
      ← secondGraph]
  · exact (resultSetConstant_complement physical frame.result frame.resultDistinct
      0 first).symm.trans
      ((congrArg (fun state => physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition frame.result frame.resultDistinct))
        (physical.basisEquiv.symm (encoding.encode state))) same).trans
          (resultSetConstant_complement physical frame.result frame.resultDistinct 0 second))

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
