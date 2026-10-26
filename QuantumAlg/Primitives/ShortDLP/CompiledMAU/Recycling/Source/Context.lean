/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Model
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.Classical.Model.BitWord

/-! # Shared execution model and chronological output width -/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

def resultBits (m ell : Nat) : Nat := (ell + m) + ell

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
