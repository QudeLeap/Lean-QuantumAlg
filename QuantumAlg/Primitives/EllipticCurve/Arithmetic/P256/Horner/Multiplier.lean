/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Readout

/-!
# Complete words on original quantum multiplier ports

Only the static physical ports enter circuit construction. The word getter
and its bit laws describe the quantum labels for correctness proofs. The
original addend may supply those ports because every Horner stage restores
it before reading the next bit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit

/-- A complete multiplier word together with its actual original quantum bit ports. -/
structure QuantumMultiplier {Saved : Type} (saved : BinaryLabelEncoding Saved) where
  ports : Fin width → MultiplierPort saved
  value : Word → Saved → Word
  reads : ∀ source retained index,
    operandMultiplierValue saved (ports index) source retained =
      (value source retained).val.testBit index.val

namespace QuantumMultiplier

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)

/-- The restored original addend is also a valid multiplier, including for squaring. -/
def source : QuantumMultiplier saved where
  ports := MultiplierPort.addend
  value := fun word _ => word
  reads := fun _ _ _ => rfl

/-- An independently retained original word supplies every multiplier bit. -/
def retained (word : Saved → Word) (bits : Fin width → EncodedBit saved)
    (reads : ∀ state index, (bits index).get state = (word state).val.testBit index.val) :
    QuantumMultiplier saved where
  ports := fun index => .retained (bits index)
  value := fun _ => word
  reads := fun _ state index => reads state index

end QuantumMultiplier

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
