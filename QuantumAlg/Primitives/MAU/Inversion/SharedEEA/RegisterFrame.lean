/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers

/-!
# Complete equality of the original shared-register frame

Every physical field in the registered allocation is retained explicitly
[LYL+26, sec_EEA/sub_regshare.tex:16-26]. This equality rule uses the exact
product encoding of both full words, four lengths, and five control bits.
It belongs to the frame representation, independently of any phase or
native execution program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Registers

noncomputable section

/-- Equal actual word, length, phase, parity, and control fields give the same whole frame. -/
theorem ext_fields {width : Nat} (left right : Registers width)
    (word1 : left.firstWord = right.firstWord) (word2 : left.secondWord = right.secondWord)
    (coefficient : left.coefficientLength = right.coefficientLength)
    (quotient : left.quotientLength = right.quotientLength)
    (divisor : left.divisorLength = right.divisorLength) (shift : left.shift = right.shift)
    (first : left.flags.first = right.flags.first) (second : left.flags.second = right.flags.second)
    (sign : left.flags.sign = right.flags.sign)
    (iteration : left.flags.iteration = right.flags.iteration)
    (control : left.control = right.control) : left = right := by
  apply (registerTupleEquiv width).injective
  exact Prod.ext (Prod.ext word1 word2)
    (Prod.ext (Prod.ext (Prod.ext coefficient quotient) (Prod.ext divisor shift))
      (Prod.ext (Prod.ext (Prod.ext first second) (Prod.ext sign iteration)) control))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Registers
