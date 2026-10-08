/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Promotion

/-!
# Sequential model selection

Native bit/word selection keeps the original order of quantum instructions.
-/

namespace QuantumAlg.BitWord

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
  {pre mid post : RuntimeCtx .quantum}

/-- Selection distributes over the same original sequential circuit. -/
theorem selectForCircuit_seq
    (first : Circuit (.quantum gates oracles) pre mid)
    (second : Circuit (.quantum gates oracles) mid post) :
    selectForCircuit (first.seq second) =
      (selectForCircuit first).seq (selectForCircuit second) := by
  rfl

end

end QuantumAlg.BitWord
