/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap

/-!
# Full conditional action of an encoded controlled swap

The literal three-Toffoli sequence selects the corresponding three-CNOT
swap according to its preserved source control. The equality concerns the
entire encoded data value, so every untouched field and correlation is kept.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

private theorem toffoli_if {Data : Type} {label : BinaryLabelEncoding Data}
    (control source target : EncodedBit label) (state : Data) :
    toffoliStep control source target state =
      if control.get state then cnotStep source target state else state := by
  unfold toffoliStep cnotStep
  cases control.get state <;> cases source.get state <;> rfl

/-- The complete three-Toffoli action selects the corresponding three-CNOT swap. -/
theorem controlledSwapStep_eq_if {Data : Type} {label : BinaryLabelEncoding Data}
    (control left right : EncodedBit label)
    (cl : control.wire ≠ left.wire) (cr : control.wire ≠ right.wire)
    (lr : left.wire ≠ right.wire) (state : Data) :
    controlledSwapStep control left right cl cr lr state =
      if control.get state then swapStep left right lr state else state := by
  simp only [controlledSwapStep, controlledSwapGates, swapStep, swapGates,
    GateSpec.stepList, GateSpec.step, id_eq, toffoli_if]
  by_cases chosen : control.get state
  · simp only [chosen, if_true, cnotStep_get_of_target_ne left right control cr.symm,
      cnotStep_get_of_target_ne right left control cl.symm]
  · simp only [chosen, Bool.false_eq_true, if_false]

end

end QuantumAlg.EncodedBit
