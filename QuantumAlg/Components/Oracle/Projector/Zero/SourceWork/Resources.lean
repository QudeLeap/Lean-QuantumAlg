/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.Projector.Zero.SourceWork
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Native resource pool of the known zero-projector flip

Both masks, every conjunction leaf and their small-width specializations are
charged to their literal default-model coordinates. The construction issues no
projector or source query.
-/

namespace QuantumAlg.ZeroProjector.SourceWork
open EncodedBit EncodedBit.Word
noncomputable section

/-- Independent native budget, retaining the X and CNOT cases at zero and one controls. -/
def budget (oracles : OracleModel) (m : Nat) :
    ResourcePool (.quantum AlgorithmGate.model oracles) :=
  let single := ResourcePool.singleton
    (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
  let cnot := ResourcePool.singleton
    (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
  let toffoli := ResourcePool.singleton
    (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
  (2 * m) • single +
    (if m = 0 then single else if m = 1 then cnot else OneDirtyLayout.gateCount m • toffoli)

/-- The actual native circuit has exactly the independent coordinate budget. -/
theorem program_events (m n : Nat) (positive : 0 < n)
    (physical : QubitLayout (1 + (m + n))) (oracles : OracleModel) :
    (program m n positive physical oracles).eventCost = budget oracles m := by
  refine (GateSpec.programList_eventCost physical oracles
    ((layout m n positive).patternGates fun _ => false)).trans ?_
  rw [OneDirtyLayout.patternGates_events]
  have masks : (OneDirtyLayout.patternMaskIndices (fun _ : Fin m => false)).length = m := by
    simp [OneDirtyLayout.patternMaskIndices]
  rw [masks, ResourcePool.ofList_append, ResourcePool.ofList_append,
    ResourcePool.ofList_replicate]
  by_cases empty : m = 0
  · simp [budget, empty, ResourcePool.scale]
  · by_cases singleton : m = 1
    · simp [budget, singleton, ResourcePool.scale, two_nsmul, add_comm,
        add_left_comm]
    · simp only [empty, singleton, ↓reduceIte, ResourcePool.ofList_replicate,
        ResourcePool.scale, budget, mul_nsmul, two_nsmul, nsmul_add]
      ac_rfl

end
end QuantumAlg.ZeroProjector.SourceWork
