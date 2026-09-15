/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Reflection.Support
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.PhaseProgram
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Coordinates
import Mathlib.Tactic.IntervalCases

/-!
# Complete physical containment of controlled source synthesis

The selected source and actual control/work phase positions lie inside the
original phase-first register. These support facts use the executed elementary
gates and do not depend on their operator equality or resource budget.
-/

namespace QuantumAlg.ZeroReflection

noncomputable section

theorem SmallPhase.program_physical_idx_subset_range
    (phases width : Nat) (small : width ≤ 2) (control : Fin phases) :
    (SmallPhase.program phases width small control).physical_idx ⊆ List.range (phases + width) := by
  interval_cases width
  · exact List.Subset.refl _
  · exact EncodedBit.controlledZ_physical_idx_subset_range _ _ _
  · exact EncodedBit.controlledTwoWireZeroReflection_physical_idx_subset_range _ _ _ _ _ _

theorem PhaseWorkspace.program_physical_idx_subset_range
    (phases controls : Nat) (control work : Fin phases) (different : control ≠ work) :
    (PhaseWorkspace.program phases controls control work different).physical_idx ⊆
      List.range (phases + (controls + 1)) :=
  EncodedBit.Word.OneDirtyLayout.controlledZeroReflectionProgram_physical_idx_subset_range
    (PhaseWorkspace.layout phases controls work)
    (PhaseWorkspace.phaseBit phases controls control)
    (PhaseWorkspace.control_source_ne phases controls control work)
    (PhaseWorkspace.control_output_ne phases controls control work)
    (PhaseWorkspace.control_work_ne phases controls control work different)

end

end QuantumAlg.ZeroReflection
