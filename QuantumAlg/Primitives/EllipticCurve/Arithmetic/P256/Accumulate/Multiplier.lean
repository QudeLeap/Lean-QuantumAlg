/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Multiplier

/-! # Original retained quantum multiplier word for source-doubling accumulation -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit

/-- The multiplier is retained independently of the source word that is actually doubled. -/
structure RetainedMultiplier {Saved : Type} (saved : BinaryLabelEncoding Saved) where
  value : Saved → Word
  bits : Fin width → EncodedBit saved
  reads : ∀ retained index, (bits index).get retained = (value retained).val.testBit index.val

namespace RetainedMultiplier

variable {Saved : Type} {saved : BinaryLabelEncoding Saved}

/-- Same real original ports in the selected-add interface, with no source alias. -/
def quantum (multiplier : RetainedMultiplier saved) : Horner.QuantumMultiplier saved :=
  Horner.QuantumMultiplier.retained saved multiplier.value multiplier.bits multiplier.reads

end RetainedMultiplier

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
