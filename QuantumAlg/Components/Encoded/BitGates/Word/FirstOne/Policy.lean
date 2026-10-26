/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Frame

/-!
# Actual native complete-subword test policies for the first-one emitter

A policy supplies a static physical X/CNOT/Toffoli list, never a runtime
Boolean callback. Its law checks the complete encoded state, including
every arbitrary borrowed system, against the original subword predicate.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}

/-- Static actual native zero-test words with exact whole-state restored-work semantics. -/
structure TestPolicy (frame : Frame encoding count outputWidth depth) where
  gates : (labels : List (Fin count)) → labels.Nodup →
    (level : Nat) → level < depth → List (GateSpec encoding)
  correct : ∀ labels distinct level present state,
    GateSpec.stepList (gates labels distinct level present) state =
      predicateFlip (frame.nextAt level present)
        (fun value => (frame.enableAt level present).get value &&
          zeroPredicate (frame.subword labels) value) state

end

end QuantumAlg.EncodedBit.FirstOne
