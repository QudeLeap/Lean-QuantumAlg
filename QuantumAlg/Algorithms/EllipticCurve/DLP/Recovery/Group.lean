/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.EllipticCurve

/-!
# Original transported group powers and natural point scalars

The original group-to-Mathlib theorem retains its name and proof without
importing the old recovery execution, storage layout or scalar backend.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Recovery
namespace AttemptSoundness

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Multiplicative powers of the transported ECDLP group are the ordinary
natural scalar action on the underlying Mathlib point. -/
lemma groupPoint_pow_toMathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (point : GroupPoint E) (exponent : Nat) :
    (point ^ exponent).toMathlib = exponent • point.toMathlib := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [pow_succ]
      change (point ^ exponent).toMathlib + point.toMathlib =
        (exponent + 1) • point.toMathlib
      rw [ih, add_nsmul, one_nsmul]

end

end AttemptSoundness
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Recovery
