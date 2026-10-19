/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State

/-!
# Internal mass-preserving interpreter result

The recursive interpreter carries its mass proof alongside the actual state.
This abbreviation is an internal return type, not an executable instruction or
a certificate supplied by an algorithm caller.
-/

namespace QuantumAlg.Execution

abbrev Preserving {kind : ProblemKind} (Hidden : Type) [Fintype Hidden]
    (pre post : RuntimeCtx kind) (Reference : Register) (Path : Type) [Fintype Path] :=
  {H : Type} → [Fintype H] → (state : State pre Reference (Hidden × H)) →
    {result : State post Reference (Hidden × (H × Path)) // result.mass = state.mass}

end QuantumAlg.Execution
