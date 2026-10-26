/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Exchange
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive

/-! # The selected payload is the original source exchange beside an unchanged pool -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange

noncomputable section

open EncodedBit

/-- Exchange Sign with the selected original Work1 coordinate in the source frame. -/
def sourceAction (width : Nat) (index : Fin (width + 3)) : Registers width → Registers width :=
  swapStep (SharedEEA.signBit width) (SharedEEA.firstWordBit width index)
    (source_sign_word width index)

/-- Literal left-product placement preserves the whole pool and the exact source action. -/
lemma action_eq_source (width : Nat) (index : Fin (width + 3)) (state : Data width) :
    action width index state = (sourceAction width index state.1, state.2) :=
  GateSpec.stepList_prodLeft (poolEncoding width)
    (swapGates (SharedEEA.signBit width) (SharedEEA.firstWordBit width index)
      (source_sign_word width index)) state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange
