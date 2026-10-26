/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Frame
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Pruning

/-!
# Existing physical slices of split-address measurement unlookup

Every unary output is explicitly one of the same original result systems.
The low address, high address and supplied high-prefix slice are distinct
from those result systems. No constructor allocates quantum scratch: the
caller supplies its existing result and shared-pool wire positions.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

/-- Certified existing result positions and low/high address workspace for actual unlookup. -/
structure UnlookupFrame {Data : Type} (encoding : BinaryLabelEncoding Data)
    (resultWidth lowWidth highRemaining : Nat) where
  result : Word encoding resultWidth
  resultDistinct : Function.Injective (fun index => (result.bit index).wire)
  low : UnaryFrame encoding lowWidth
  /-- The unary target is an actual subset of the just-measured original result systems. -/
  lowResult : Fin (2 ^ lowWidth) ↪ Fin resultWidth
  lowResultWire : ∀ index, (low.target index).wire = (result.bit (lowResult index)).wire
  /-- Stack zero is the original top high-address bit; the other positions are supplied prefixes. -/
  high : SelectorFrame encoding highRemaining
  lowAddressResult : ∀ address resultIndex,
    (low.address address).wire ≠ (result.bit resultIndex).wire
  highAddressResult : ∀ address resultIndex,
    (high.address address).wire ≠ (result.bit resultIndex).wire
  highStackResult : ∀ stack resultIndex,
    (high.stack stack).wire ≠ (result.bit resultIndex).wire
  lowHighAddress : ∀ lowAddress highAddress,
    (low.address lowAddress).wire ≠ (high.address highAddress).wire
  lowHighStack : ∀ lowAddress highStack,
    (low.address lowAddress).wire ≠ (high.stack highStack).wire

namespace UnlookupFrame

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {resultWidth lowWidth highRemaining : Nat}

/-- The actual onehot output word occupies the certified original result positions. -/
def lowWord (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining) :
    Word encoding (2 ^ lowWidth) := ⟨frame.low.target⟩

/-- Every selected high-prefix control is outside all actual reused unary targets. -/
lemma highStack_lowWord (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (stack : Fin (highRemaining + 1)) (index : Fin (2 ^ lowWidth)) :
    (frame.high.stack stack).wire ≠ (frame.lowWord.bit index).wire := by
  intro same
  exact frame.highStackResult stack (frame.lowResult index)
    (same.trans (frame.lowResultWire index))

end UnlookupFrame

end

end QuantumAlg.EncodedBit.WindowLookup
