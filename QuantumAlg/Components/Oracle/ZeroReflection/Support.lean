/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Reflection.Support
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import Mathlib.Tactic.IntervalCases

/-!
# Canonical physical containment of the executable source reflections

Small-width circuits use only their source positions. The one-dirty circuit
uses only its source and actual final work position. Both facts follow from
the addresses of the actual elementary gates.
-/

namespace QuantumAlg.ZeroReflection

open BinaryLabelEncoding

noncomputable section

theorem Small.program_physical_idx_subset_range (width : Nat) (small : width ≤ 3) :
    (Small.program width small).physical_idx ⊆ List.range width := by
  interval_cases width
  · exact List.Subset.refl _
  · exact (finIdentityBit 1 0).pauliZ_physical_idx_subset_range
  · exact (finIdentityBit 2 0).twoWireZeroReflection_physical_idx_subset_range
      (finIdentityBit 2 1) (by decide)
  · exact (finIdentityBit 3 0).threeWireZeroReflection_physical_idx_subset_range
      (finIdentityBit 3 1) (finIdentityBit 3 2) (by decide) (by decide) (by decide)

theorem OneDirty.program_physical_idx_subset_range (controls : Nat) :
    (OneDirty.program controls).physical_idx ⊆ List.range (controls + 1 + 1) :=
  (OneDirty.layout controls).zeroReflectionProgram_physical_idx_subset_range

end

end QuantumAlg.ZeroReflection
