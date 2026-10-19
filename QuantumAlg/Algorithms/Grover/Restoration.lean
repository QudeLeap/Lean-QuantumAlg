/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete borrowed restoration by the actual Grover execution

The runtime starts with no borrowed quantum wires. The general interpreter
restoration theorem applies to its actual preparation, native word, measured
writes and packing operation. The complete borrowed unit interface and every
external reference correlation are preserved, independently of search success.
-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.Execution

/-- Every actual run preserves its borrowed classical interface and complete external reference. -/
lemma code_borrowedRestored (n : Nat) (k : Nat) (actual : (model n).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    (code n k).BorrowedRestored Reference state ((code n k).execute actual Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (code n k) actual rfl Reference state

end

end QuantumAlg.GroverSearch
