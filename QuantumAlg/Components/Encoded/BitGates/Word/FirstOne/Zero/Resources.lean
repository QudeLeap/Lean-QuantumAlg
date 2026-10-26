/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Zero
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Resources

/-!
# Exact native trace of the complete controlled first-one zero test

Every negative source control contributes both real X masks. The added
retained enable participates in the actual arbitrary-work conjunction.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Independent exact native trace, including both source masks and the original empty case. -/
def zeroTrace (count : Nat) : List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  List.replicate count (.gate .singleQubit) ++
    (if count = 0 then [.gate .cnot] else
      List.replicate (Word.OneDirtyLayout.gateCount (count + 1)) (.gate .toffoli)) ++
    List.replicate count (.gate .singleQubit)

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}

/-- The actual complete zero-test word has exactly this native ordered trace. -/
lemma zeroGates_events (layout : Word.OneDirtyLayout (encoding := encoding) count)
    (enable : EncodedBit encoding)
    (sources : ∀ index, enable.wire ≠ (layout.source.bit index).wire)
    (output : enable.wire ≠ layout.output.wire) (work : enable.wire ≠ layout.work.wire) :
    (zeroGates layout enable sources output work).map (GateSpec.event .empty) =
      zeroTrace count := by
  have masks : (Word.OneDirtyLayout.patternMaskIndices
      (Word.OneDirtyLayout.controlledPatternValues (fun _ : Fin count => false))).length =
      count := by
    suffices tail : (List.filter
        (fun index : Fin (count + 1) => !Fin.cases true (fun _ : Fin count => false) index)
        (List.ofFn fun index : Fin count => index.succ)).length = count by
      simpa [Word.OneDirtyLayout.patternMaskIndices,
        Word.OneDirtyLayout.controlledPatternValues, List.ofFn_succ] using tail
    rw [List.filter_eq_self.mpr (by
      intro index member
      obtain ⟨original, rfl⟩ := List.mem_ofFn.mp member
      rfl)]
    exact List.length_ofFn
  unfold zeroGates Word.OneDirtyLayout.controlledPatternGates
  rw [Word.OneDirtyLayout.patternGates_events, masks]
  unfold zeroTrace
  have nonempty : count + 1 ≠ 0 := by omega
  by_cases empty : count = 0
  · subst count
    simp only [nonempty, if_false]
  · have notOne : count + 1 ≠ 1 := by omega
    rw [if_neg nonempty, if_neg notOne, if_neg empty]

end

end QuantumAlg.EncodedBit.FirstOne
