/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete borrowed restoration of the Walsh query execution

The runtime starts with no borrowed quantum wires. The general interpreter
restoration theorem therefore applies to its actual zero preparation, native
word, measured writes and packing operation. It retains the complete borrowed
classical interface jointly with every external reference; no output-state
promise or oracle promise is used.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

open QuantumAlg.Execution

/-- Every real execution preserves the borrowed unit and its complete external reference. -/
lemma code_borrowedRestored (n : Nat) (environment : (model n).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    (code n).BorrowedRestored Reference state ((code n).execute environment Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (code n) environment rfl Reference state

end

end QuantumAlg.WalshHadamard.Readout
