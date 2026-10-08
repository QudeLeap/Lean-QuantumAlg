/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Support
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ForwardResources
import all QuantumAlg.Core.Base.Accounting.Support

/-!
# Independent coordinatewise budgets for the complete native inverse

Every possible native coordinate has an independently stated width-only
cap. The proofs combine the actual emitted finite support with the closed
count bounds for the same programs; no budget is chosen by projecting the
program being checked. The actual fixed schedule, complete counter decoder,
loading, physical output-port operations, and same inverse cleanup remain
included [LYL+26, sec_EEA/sub_4phase.tex:119-128].

The in-place interface for measured division retains the original two
shared words and small history [LYL+26, sec_point_add/sec_point_add.tex:51-79].
Its budget is distinct from the separate XOR-output interface, which also
charges its real copy and second complete pass. These conservative bounds
describe this implemented finite-selector construction, not the paper's
claimed leading constant for a different gate realization.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeBudget

noncomputable section

/-- Independent cap on each actual forward event coordinate. -/
def corrected (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ForwardResources.correctedBound width • Addition.Gidney.offsetAlphabet

/-- Independent cap for the in-place forward, including its real load and output-port gates. -/
def inPlace (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ForwardResources.inPlaceBound width • Addition.Gidney.offsetAlphabet

/-- Independent cap for the separate XOR-output interface and all inverse-history cleanup. -/
def xor (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ForwardResources.xorBound width • Addition.Gidney.offsetAlphabet

/-- Actual corrected-forward multiplicities meet the independent cap at every native coordinate. -/
theorem corrected_bound (modulus : Nat) (nontrivial : 1 < modulus) :
    (CorrectedSchedule.program modulus nontrivial).eventCost ≤ corrected modulus.size :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (NativeSupport.corrected modulus nontrivial)
    (ForwardResources.corrected_count modulus nontrivial)

/-- The actual in-place forward meets every independently specified native-coordinate budget. -/
theorem inPlace_bound (modulus : Nat) (nontrivial : 1 < modulus) :
    (InPlaceForward.program modulus nontrivial).eventCost ≤ inPlace modulus.size :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (NativeSupport.inPlace modulus nontrivial) (ForwardResources.inPlace_count modulus nontrivial)

/-- The same dagger has the same coordinatewise budget, including complete history reversal. -/
theorem inPlace_dagger_bound (modulus : Nat) (nontrivial : 1 < modulus) :
    ((InPlaceForward.program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost ≤ inPlace modulus.size :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (NativeSupport.inPlace_dagger modulus nontrivial)
    (ForwardResources.inPlace_dagger_count modulus nontrivial)

/-- The separate XOR interface counts both full passes and its actual native copy at every label. -/
theorem xor_bound (modulus : Nat) (nontrivial : 1 < modulus) :
    (NativeInverse.program modulus nontrivial).eventCost ≤ xor modulus.size :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (NativeSupport.xor modulus nontrivial) (ForwardResources.xor_count modulus nontrivial)

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeBudget
