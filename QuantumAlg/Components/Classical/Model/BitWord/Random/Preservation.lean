/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Random
public import QuantumAlg.Core.Execution.State
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Components.Classical.Model.BitWord.Random
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Borrowed restoration by selected native random-bit generation

The actual random operation writes only the intrinsic writable output lifted
through its unit-operand scope. Native restoration and actual lexical release
therefore preserve all borrowed classical, quantum and reference correlations.
No initialized output, product-state condition or absence of borrowed wires is
required.
-/

namespace QuantumAlg.BitWord.Random

open Execution

noncomputable section

variable {execution : ExecutionModel} {environment : execution.Environment} [Selected execution]
  {ctx : RuntimeCtx execution.kind} {width : Nat}

/-- Actual sampling and release restore the full arbitrary borrowed joint interface. -/
public lemma randomCode_borrowedRestored (output : CWriteRef ctx (.bits width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (execution.HiddenState × History)) :
    (code (execution := execution) output).BorrowedRestored Reference state
      ((code (execution := execution) output).execute environment Reference state) := by
  apply Circuit.borrowedRestored_workspace
  intro history historyFinite entered
  exact Circuit.borrowedRestored_classical (environment := environment) _ entered

end

end QuantumAlg.BitWord.Random
