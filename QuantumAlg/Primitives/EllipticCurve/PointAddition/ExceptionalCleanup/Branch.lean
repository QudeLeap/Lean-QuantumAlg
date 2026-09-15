/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.ExceptionalCleanup.Layout
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.ExceptionalCleanup.Math

/-!
# Reversible generic/exceptional cleanup branch

This leaf contains the two mutually exclusive cleanup routes selected after
the common generic-addition prefix.  A false selector runs the generic
addition dagger.  A true selector clears the saved input point with the fixed
coordinates of `2(-Q)`.  Both routes are literal X/CNOT/Toffoli lists.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace ExceptionalCleanup
namespace Branch

noncomputable section

private theorem zeroControlledListWithWorkStep_eq_stepList_of_control_false
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (control work : EncodedBit encoding)
    (gates : List (EncodedBit.GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (state : Data) (hcontrolFalse : control.get state = false)
    (hworkClean : work.get state = false) :
    EncodedBit.GateSpec.stepList
        ([EncodedBit.GateSpec.x control] ++
          EncodedBit.GateSpec.controlledListWithWorkGates control work gates
            hcontrol hwork hcontrolWork ++
          [EncodedBit.GateSpec.x control]) state =
      EncodedBit.GateSpec.stepList gates state := by
  let flipped := control.flip state
  have hcontrolFlipped : control.get flipped = true := by
    simp [flipped, EncodedBit.get_flip_self, hcontrolFalse]
  have hworkFlipped : work.get flipped = false := by
    rw [show work.get flipped = work.get state by
      exact EncodedBit.get_flip_of_wire_ne control work hcontrolWork state]
    exact hworkClean
  have hcontrolled :=
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      control work gates hcontrol hwork hcontrolWork flipped
      hcontrolFlipped hworkFlipped
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change control.flip
      (EncodedBit.GateSpec.controlledListWithWorkStep control work gates
        hcontrol hwork hcontrolWork flipped) = _
  rw [hcontrolled]
  rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint gates control hcontrol]
  exact EncodedBit.flip_flip control _

private theorem zeroControlledListWithWorkStep_eq_self_of_control_true
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (control work : EncodedBit encoding)
    (gates : List (EncodedBit.GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (state : Data) (hcontrolTrue : control.get state = true) :
    EncodedBit.GateSpec.stepList
        ([EncodedBit.GateSpec.x control] ++
          EncodedBit.GateSpec.controlledListWithWorkGates control work gates
            hcontrol hwork hcontrolWork ++
          [EncodedBit.GateSpec.x control]) state = state := by
  let flipped := control.flip state
  have hcontrolFlipped : control.get flipped = false := by
    simp [flipped, EncodedBit.get_flip_self, hcontrolTrue]
  have hcontrolled :=
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      control work gates hcontrol hwork hcontrolWork flipped hcontrolFlipped
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change control.flip
      (EncodedBit.GateSpec.controlledListWithWorkStep control work gates
        hcontrol hwork hcontrolWork flipped) = _
  rw [hcontrolled]
  exact EncodedBit.flip_flip control state

private theorem controlledWithWorkGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (observed control work : EncodedBit encoding)
    (gate : EncodedBit.GateSpec encoding)
    (hcontrol : EncodedBit.GateSpec.bitDisjoint control gate)
    (hwork : EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (hobservedControl : control.wire ≠ observed.wire)
    (hobservedWork : work.wire ≠ observed.wire)
    (hobserved : EncodedBit.GateSpec.bitDisjoint observed gate) :
    ∀ lifted,
      lifted ∈ EncodedBit.GateSpec.controlledWithWorkGates control work gate
        hcontrol hwork hcontrolWork →
      EncodedBit.GateSpec.bitDisjoint observed lifted := by
  intro lifted hlifted
  cases gate with
  | x target =>
      simp only [EncodedBit.GateSpec.controlledWithWorkGates,
        List.mem_singleton] at hlifted
      subst lifted
      exact ⟨hobservedControl, hobserved⟩
  | cnot source target hsourceTarget =>
      simp only [EncodedBit.GateSpec.controlledWithWorkGates,
        List.mem_singleton] at hlifted
      subst lifted
      exact ⟨hobservedControl, hobserved.1, hobserved.2⟩
  | toffoli sourceA sourceB target hsourceAB hsourceATarget hsourceBTarget =>
      simp only [EncodedBit.GateSpec.controlledWithWorkGates,
        List.mem_cons, List.not_mem_nil, or_false] at hlifted
      rcases hlifted with hfirst | hmiddle | hlast
      · subst lifted
        exact ⟨hobserved.1, hobserved.2.1, hobservedWork⟩
      · subst lifted
        exact ⟨hobservedControl, hobservedWork, hobserved.2.2⟩
      · subst lifted
        exact ⟨hobserved.1, hobserved.2.1, hobservedWork⟩

private theorem controlledListWithWorkGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (observed control work : EncodedBit encoding)
    (gates : List (EncodedBit.GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (hobservedControl : control.wire ≠ observed.wire)
    (hobservedWork : work.wire ≠ observed.wire)
    (hobserved : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint observed gate) :
    ∀ lifted,
      lifted ∈ EncodedBit.GateSpec.controlledListWithWorkGates control work
        gates hcontrol hwork hcontrolWork →
      EncodedBit.GateSpec.bitDisjoint observed lifted := by
  induction gates with
  | nil =>
      intro lifted hlifted
      simp [EncodedBit.GateSpec.controlledListWithWorkGates] at hlifted
  | cons gate rest ih =>
      intro lifted hlifted
      rw [EncodedBit.GateSpec.controlledListWithWorkGates] at hlifted
      rcases List.mem_append.mp hlifted with hhead | htail
      · exact controlledWithWorkGates_bitDisjoint_observed
          observed control work gate (hcontrol gate (by simp))
          (hwork gate (by simp)) hcontrolWork hobservedControl hobservedWork
          (hobserved gate (by simp)) lifted hhead
      · exact ih
          (fun next hnext => hcontrol next (by simp [hnext]))
          (fun next hnext => hwork next (by simp [hnext]))
          (fun next hnext => hobserved next (by simp [hnext])) lifted htail

private theorem controlledXorConstantGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (observed control : EncodedBit encoding)
    (target : EncodedBit.Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (target.bit bit).wire)
    (hcontrolObserved : control.wire ≠ observed.wire)
    (htargetObserved : ∀ bit,
      (target.bit bit).wire ≠ observed.wire) :
    ∀ gate,
      gate ∈ EncodedBit.Word.controlledXorConstantGates control target
        constant hcontrolTarget →
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [EncodedBit.Word.controlledXorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  exact ⟨hcontrolObserved, htargetObserved bit⟩

variable [params : Arithmetic.VariableModularMul.Parameters]

/-- Primitive gate specification on the complete exceptional-cleanup carrier. -/
abbrev Gate := EncodedBit.GateSpec Layout.rawEncoding

/-- The generic-addition dagger lifted into the exceptional-cleanup carrier. -/
def reverseAdditionGates : List Gate :=
  Layout.liftPipelineGates Pipeline.additionGates.reverse

theorem reverseAdditionGates_bitDisjoint_selectorBit :
    ∀ gate, gate ∈ reverseAdditionGates →
      EncodedBit.GateSpec.bitDisjoint Layout.selectorBit gate :=
  Layout.liftPipelineGates_bitDisjoint_selectorBit
    Pipeline.additionGates.reverse

theorem reverseAdditionGates_bitDisjoint_branchControlWorkBit :
    ∀ gate, gate ∈ reverseAdditionGates →
      EncodedBit.GateSpec.bitDisjoint Layout.branchControlWorkBit gate :=
  Layout.liftPipelineGates_bitDisjoint_branchControlWorkBit
    Pipeline.additionGates.reverse

theorem reverseAdditionGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ reverseAdditionGates →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate := by
  simpa only [reverseAdditionGates, Layout.controlBit] using
    Layout.liftPipelineGates_bitDisjoint_liftPipelineBit Pipeline.controlBit
      Pipeline.additionGates.reverse
      (fun gate hgate =>
        Pipeline.additionGates_bitDisjoint_controlBit gate
          (List.mem_reverse.mp hgate))

theorem reverseAdditionGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ reverseAdditionGates →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate := by
  simpa only [reverseAdditionGates, Layout.controlWorkBit] using
    Layout.liftPipelineGates_bitDisjoint_liftPipelineBit
      Pipeline.controlWorkBit Pipeline.additionGates.reverse
      (fun gate hgate =>
        Pipeline.additionGates_bitDisjoint_controlWorkBit gate
          (List.mem_reverse.mp hgate))

/-- Clean-work control lift of the generic dagger. -/
def controlledReverseAdditionGates : List Gate :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    Layout.selectorBit Layout.branchControlWorkBit reverseAdditionGates
    reverseAdditionGates_bitDisjoint_selectorBit
    reverseAdditionGates_bitDisjoint_branchControlWorkBit
    Layout.selectorBit_wire_ne_branchControlWorkBit

/-- A zero-controlled generic cleanup: the two surrounding X gates turn a
false exceptional selector into the active control value and restore it. -/
def normalCleanupGates : List Gate :=
  [EncodedBit.GateSpec.x Layout.selectorBit] ++
    controlledReverseAdditionGates ++
    [EncodedBit.GateSpec.x Layout.selectorBit]

/-- Lifting and reversing the generic-addition schedule preserves its leaf
count. -/
theorem reverseAdditionGates_length :
    reverseAdditionGates.length = Pipeline.additionGates.length := by
  simp [reverseAdditionGates, Layout.liftPipelineGates_length]

/-- Lifting and reversing the generic-addition schedule preserves its X
coordinate. -/
theorem reverseAdditionGates_xMultiplicity_sum :
    (reverseAdditionGates.map
      EncodedBit.GateSpec.xMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.xMultiplicity).sum := by
  simp [reverseAdditionGates, Layout.liftPipelineGates_xMultiplicity_sum]

/-- Lifting and reversing the generic-addition schedule preserves its CNOT
coordinate. -/
theorem reverseAdditionGates_cnotMultiplicity_sum :
    (reverseAdditionGates.map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp [reverseAdditionGates, Layout.liftPipelineGates_cnotMultiplicity_sum]

/-- Lifting and reversing the generic-addition schedule preserves its
Toffoli coordinate. -/
theorem reverseAdditionGates_toffoliMultiplicity_sum :
    (reverseAdditionGates.map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp [reverseAdditionGates,
    Layout.liftPipelineGates_toffoliMultiplicity_sum]

/-- Exact leaf count of the zero-controlled ordinary cleanup route. -/
theorem normalCleanupGates_length :
    normalCleanupGates.length =
      Pipeline.additionGates.length +
        2 * (Pipeline.additionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum + 2 := by
  simp only [normalCleanupGates, controlledReverseAdditionGates,
    List.length_append, List.length_singleton,
    EncodedBit.GateSpec.controlledListWithWorkGates_length_eq,
    reverseAdditionGates_length,
    reverseAdditionGates_toffoliMultiplicity_sum]
  omega

/-- The two selector flips are the only physical X leaves in the ordinary
cleanup route. -/
theorem normalCleanupGates_xMultiplicity_sum :
    (normalCleanupGates.map EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp [normalCleanupGates, controlledReverseAdditionGates,
    EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum]

/-- Exact CNOT coordinate of the zero-controlled ordinary cleanup route. -/
theorem normalCleanupGates_cnotMultiplicity_sum :
    (normalCleanupGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.xMultiplicity).sum := by
  simp [normalCleanupGates, controlledReverseAdditionGates,
    EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    reverseAdditionGates_xMultiplicity_sum]

/-- Exact Toffoli coordinate of the zero-controlled ordinary cleanup route. -/
theorem normalCleanupGates_toffoliMultiplicity_sum :
    (normalCleanupGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
        3 * (Pipeline.additionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [normalCleanupGates, controlledReverseAdditionGates,
    List.map_append, List.sum_append, List.map_singleton,
    List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.toffoliMultiplicity_x,
    EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    zero_add, add_zero,
    reverseAdditionGates_cnotMultiplicity_sum,
    reverseAdditionGates_toffoliMultiplicity_sum]

private theorem normalCleanupGates_bitDisjoint_observed
    (observed : EncodedBit Layout.rawEncoding)
    (hselector : Layout.selectorBit.wire ≠ observed.wire)
    (hbranchWork : Layout.branchControlWorkBit.wire ≠ observed.wire)
    (hreverse : ∀ gate, gate ∈ reverseAdditionGates →
      EncodedBit.GateSpec.bitDisjoint observed gate) :
    ∀ gate, gate ∈ normalCleanupGates →
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [normalCleanupGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · rcases List.mem_append.mp hgate with hgate | hgate
    · simp only [List.mem_singleton] at hgate
      subst gate
      exact hselector
    · exact controlledListWithWorkGates_bitDisjoint_observed
        observed Layout.selectorBit Layout.branchControlWorkBit
        reverseAdditionGates reverseAdditionGates_bitDisjoint_selectorBit
        reverseAdditionGates_bitDisjoint_branchControlWorkBit
        Layout.selectorBit_wire_ne_branchControlWorkBit hselector hbranchWork
        hreverse gate hgate
  · simp only [List.mem_singleton] at hgate
    subst gate
    exact hselector

theorem normalCleanupGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ normalCleanupGates →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate :=
  normalCleanupGates_bitDisjoint_observed Layout.controlBit
    Layout.selectorBit_wire_ne_controlBit
    Layout.branchControlWorkBit_wire_ne_controlBit
    reverseAdditionGates_bitDisjoint_controlBit

theorem normalCleanupGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ normalCleanupGates →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate :=
  normalCleanupGates_bitDisjoint_observed Layout.controlWorkBit
    Layout.selectorBit_wire_ne_controlWorkBit
    Layout.branchControlWorkBit_wire_ne_controlWorkBit
    reverseAdditionGates_bitDisjoint_controlWorkBit

/-- Register action of the selector-controlled generic-addition dagger. -/
def normalCleanupStep : Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.GateSpec.stepList normalCleanupGates

/-- If the selector marks the normal branch and the branch work bit is clean,
the zero-controlled route executes exactly the lifted generic dagger. -/
theorem normalCleanupStep_eq_reverse_of_selector_false
    (state : Layout.RawRegisters)
    (hselector : Layout.selectorBit.get state = false)
    (hwork : Layout.branchControlWorkBit.get state = false) :
    normalCleanupStep state =
      EncodedBit.GateSpec.stepList reverseAdditionGates state := by
  simpa only [normalCleanupStep, normalCleanupGates,
    controlledReverseAdditionGates] using
    zeroControlledListWithWorkStep_eq_stepList_of_control_false
      Layout.selectorBit Layout.branchControlWorkBit reverseAdditionGates
      reverseAdditionGates_bitDisjoint_selectorBit
      reverseAdditionGates_bitDisjoint_branchControlWorkBit
      Layout.selectorBit_wire_ne_branchControlWorkBit state hselector hwork

/-- A true exceptional selector disables the zero-controlled generic route. -/
theorem normalCleanupStep_eq_self_of_selector_true
    (state : Layout.RawRegisters)
    (hselector : Layout.selectorBit.get state = true) :
    normalCleanupStep state = state := by
  simpa only [normalCleanupStep, normalCleanupGates,
    controlledReverseAdditionGates] using
    zeroControlledListWithWorkStep_eq_self_of_control_true
      Layout.selectorBit Layout.branchControlWorkBit reverseAdditionGates
      reverseAdditionGates_bitDisjoint_selectorBit
      reverseAdditionGates_bitDisjoint_branchControlWorkBit
      Layout.selectorBit_wire_ne_branchControlWorkBit state hselector

variable {E : PrimeFieldShortWeierstrass params.modulus.val}
  [Fact params.modulus.val.Prime]
  {Q : AffinePoint E}

/-- Fixed X coordinate used to clear the exceptional saved input. -/
def exceptionalXConstant : Nat.FixedWidth.Word params.width :=
  ParameterizedPointAddition.residueWord
    (doubleX E (AffinePoint.negate Q))

/-- Fixed Y coordinate used to clear the exceptional saved input. -/
def exceptionalYConstant : Nat.FixedWidth.Word params.width :=
  ParameterizedPointAddition.residueWord
    (doubleY E (AffinePoint.negate Q))

/-- Controlled constant-xor gates that clear the exceptional x-coordinate. -/
def exceptionalXGates : List Gate :=
  EncodedBit.Word.controlledXorConstantGates Layout.selectorBit
    Layout.outputXWord (exceptionalXConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputXWord

/-- Controlled constant-xor gates that clear the exceptional y-coordinate. -/
def exceptionalYGates : List Gate :=
  EncodedBit.Word.controlledXorConstantGates Layout.selectorBit
    Layout.outputYWord (exceptionalYConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputYWord

theorem exceptionalXGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ exceptionalXGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate :=
  controlledXorConstantGates_bitDisjoint_observed Layout.controlBit
    Layout.selectorBit Layout.outputXWord
    (exceptionalXConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputXWord
    Layout.selectorBit_wire_ne_controlBit
    Layout.outputXWord_wire_ne_controlBit

theorem exceptionalXGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ exceptionalXGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate :=
  controlledXorConstantGates_bitDisjoint_observed Layout.controlWorkBit
    Layout.selectorBit Layout.outputXWord
    (exceptionalXConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputXWord
    Layout.selectorBit_wire_ne_controlWorkBit
    Layout.outputXWord_wire_ne_controlWorkBit

theorem exceptionalYGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ exceptionalYGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate :=
  controlledXorConstantGates_bitDisjoint_observed Layout.controlBit
    Layout.selectorBit Layout.outputYWord
    (exceptionalYConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputYWord
    Layout.selectorBit_wire_ne_controlBit
    Layout.outputYWord_wire_ne_controlBit

theorem exceptionalYGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ exceptionalYGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate :=
  controlledXorConstantGates_bitDisjoint_observed Layout.controlWorkBit
    Layout.selectorBit Layout.outputYWord
    (exceptionalYConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputYWord
    Layout.selectorBit_wire_ne_controlWorkBit
    Layout.outputYWord_wire_ne_controlWorkBit

/-- The true-selector route clears both saved coordinates by CNOTs. -/
def exceptionalCleanupGates : List Gate :=
  exceptionalXGates (E := E) (Q := Q) ++
    exceptionalYGates (E := E) (Q := Q)

/-- Number of set coordinate bits cleared by the exceptional route. -/
def exceptionalGateCount : Nat :=
  (EncodedBit.Word.constantOneIndices
      (exceptionalXConstant (E := E) (Q := Q))).length +
    (EncodedBit.Word.constantOneIndices
      (exceptionalYConstant (E := E) (Q := Q))).length

/-- At most two controlled CNOTs are needed per field bit across the fixed
exceptional point coordinates. -/
theorem exceptionalGateCount_le :
    exceptionalGateCount (E := E) (Q := Q) ≤ 2 * params.width := by
  have hx := EncodedBit.Word.constantOneIndices_length_le
    (exceptionalXConstant (E := E) (Q := Q))
  have hy := EncodedBit.Word.constantOneIndices_length_le
    (exceptionalYConstant (E := E) (Q := Q))
  unfold exceptionalGateCount
  omega

/-- Exact leaf count of the exceptional fixed-coordinate cleanup route. -/
theorem exceptionalCleanupGates_length :
    (exceptionalCleanupGates (E := E) (Q := Q)).length =
      exceptionalGateCount (E := E) (Q := Q) := by
  unfold exceptionalCleanupGates exceptionalXGates exceptionalYGates
    exceptionalGateCount
  rw [List.length_append,
    EncodedBit.Word.controlledXorConstantGates_length,
    EncodedBit.Word.controlledXorConstantGates_length]

/-- The exceptional fixed-coordinate cleanup contains no physical X leaves. -/
theorem exceptionalCleanupGates_xMultiplicity_sum :
    ((exceptionalCleanupGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  unfold exceptionalCleanupGates exceptionalXGates exceptionalYGates
  simp [EncodedBit.Word.controlledXorConstantGates_xMultiplicity_sum]

/-- Exact CNOT coordinate of the exceptional fixed-coordinate cleanup. -/
theorem exceptionalCleanupGates_cnotMultiplicity_sum :
    ((exceptionalCleanupGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      exceptionalGateCount (E := E) (Q := Q) := by
  unfold exceptionalCleanupGates exceptionalXGates exceptionalYGates
    exceptionalGateCount
  rw [List.map_append, List.sum_append,
    EncodedBit.Word.controlledXorConstantGates_cnotMultiplicity_sum,
    EncodedBit.Word.controlledXorConstantGates_cnotMultiplicity_sum]

/-- The exceptional fixed-coordinate cleanup contains no Toffoli leaves. -/
theorem exceptionalCleanupGates_toffoliMultiplicity_sum :
    ((exceptionalCleanupGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  unfold exceptionalCleanupGates exceptionalXGates exceptionalYGates
  simp [EncodedBit.Word.controlledXorConstantGates_toffoliMultiplicity_sum]

/-- Register action of the fixed-coordinate exceptional cleanup. -/
def exceptionalCleanupStep : Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.GateSpec.stepList (exceptionalCleanupGates (E := E) (Q := Q))

/-- On a true selector, the two controlled constant-xor lists clear a saved
point whose coordinates are exactly the exceptional constants. -/
theorem exceptionalCleanupStep_selectedBoundary
    (control : Bool)
    (mutable constant : PointAddition.PortFrame.PointWords params.width) :
    exceptionalCleanupStep (E := E) (Q := Q)
        (Layout.selectedBoundaryRegisters control mutable constant
          (exceptionalXConstant (E := E) (Q := Q),
            exceptionalYConstant (E := E) (Q := Q)) true) =
      Layout.selectedBoundaryRegisters control mutable constant
        (PointAddition.PortFrame.zeroPoint params.width) true := by
  let before := Layout.selectedBoundaryRegisters control mutable constant
    (exceptionalXConstant (E := E) (Q := Q),
      exceptionalYConstant (E := E) (Q := Q)) true
  let afterX := Layout.selectedBoundaryRegisters control mutable constant
    (0, exceptionalYConstant (E := E) (Q := Q)) true
  have hx :
      EncodedBit.GateSpec.stepList (exceptionalXGates (E := E) (Q := Q))
          before = afterX := by
    have h := PointAddition.PortFrame.controlledXorConstantStep_eq_set_of_testBit
      (Layout.outputXPort (params := params)) Layout.selectorBit
      (exceptionalXConstant (E := E) (Q := Q))
      Layout.selectorBit_wire_ne_outputXWord before 0 (by
        intro bit
        simp [before, exceptionalXConstant])
    simpa [exceptionalXGates, Layout.outputXWord, before, afterX,
      EncodedBit.Word.controlledXorConstantStep] using h
  have hy :
      EncodedBit.GateSpec.stepList (exceptionalYGates (E := E) (Q := Q))
          afterX =
        Layout.selectedBoundaryRegisters control mutable constant
          (PointAddition.PortFrame.zeroPoint params.width) true := by
    have h := PointAddition.PortFrame.controlledXorConstantStep_eq_set_of_testBit
      (Layout.outputYPort (params := params)) Layout.selectorBit
      (exceptionalYConstant (E := E) (Q := Q))
      Layout.selectorBit_wire_ne_outputYWord afterX 0 (by
        intro bit
        simp [afterX, exceptionalYConstant])
    simpa [exceptionalYGates, Layout.outputYWord, afterX,
      PointAddition.PortFrame.zeroPoint,
      EncodedBit.Word.controlledXorConstantStep] using h
  change EncodedBit.GateSpec.stepList
      (exceptionalCleanupGates (E := E) (Q := Q)) before = _
  rw [exceptionalCleanupGates, EncodedBit.GateSpec.stepList_append, hx, hy]

/-- A false selector disables both exceptional controlled-xor lists. -/
theorem exceptionalCleanupStep_eq_self_of_selector_false
    (state : Layout.RawRegisters)
    (hselector : Layout.selectorBit.get state = false) :
    exceptionalCleanupStep (E := E) (Q := Q) state = state := by
  change EncodedBit.GateSpec.stepList
      (exceptionalXGates (E := E) (Q := Q) ++
        exceptionalYGates (E := E) (Q := Q)) state = state
  rw [EncodedBit.GateSpec.stepList_append]
  have hx := EncodedBit.Word.controlledXorConstantStep_eq_self_of_control_false
    Layout.selectorBit Layout.outputXWord
    (exceptionalXConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputXWord state hselector
  change EncodedBit.Word.controlledXorConstantStep Layout.selectorBit
      Layout.outputYWord (exceptionalYConstant (E := E) (Q := Q))
        Layout.selectorBit_wire_ne_outputYWord
      (EncodedBit.Word.controlledXorConstantStep Layout.selectorBit
        Layout.outputXWord (exceptionalXConstant (E := E) (Q := Q))
        Layout.selectorBit_wire_ne_outputXWord state) = state
  rw [hx]
  exact EncodedBit.Word.controlledXorConstantStep_eq_self_of_control_false
    Layout.selectorBit Layout.outputYWord
    (exceptionalYConstant (E := E) (Q := Q))
    Layout.selectorBit_wire_ne_outputYWord state hselector

/-- Complete mutually exclusive cleanup gate list. -/
def cleanupGates : List Gate :=
  normalCleanupGates ++ exceptionalCleanupGates (E := E) (Q := Q)

/-- Exact leaf count of the two mutually exclusive cleanup routes. -/
theorem cleanupGates_length :
    (cleanupGates (E := E) (Q := Q)).length =
      Pipeline.additionGates.length +
        2 * (Pipeline.additionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum + 2 +
        exceptionalGateCount (E := E) (Q := Q) := by
  unfold cleanupGates
  rw [List.length_append, normalCleanupGates_length,
    exceptionalCleanupGates_length]

/-- The two ordinary-route selector flips are the only X leaves in the
combined cleanup schedule. -/
theorem cleanupGates_xMultiplicity_sum :
    ((cleanupGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  unfold cleanupGates
  rw [List.map_append, List.sum_append,
    normalCleanupGates_xMultiplicity_sum,
    exceptionalCleanupGates_xMultiplicity_sum]

/-- Exact CNOT coordinate of the combined cleanup schedule. -/
theorem cleanupGates_cnotMultiplicity_sum :
    ((cleanupGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.xMultiplicity).sum +
        exceptionalGateCount (E := E) (Q := Q) := by
  unfold cleanupGates
  rw [List.map_append, List.sum_append,
    normalCleanupGates_cnotMultiplicity_sum,
    exceptionalCleanupGates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate of the combined cleanup schedule. -/
theorem cleanupGates_toffoliMultiplicity_sum :
    ((cleanupGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
        3 * (Pipeline.additionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  unfold cleanupGates
  rw [List.map_append, List.sum_append,
    normalCleanupGates_toffoliMultiplicity_sum,
    exceptionalCleanupGates_toffoliMultiplicity_sum]
  omega

/-- Width-closed contribution of the fixed exceptional route to the combined
cleanup leaf count. -/
theorem cleanupGates_length_le :
    (cleanupGates (E := E) (Q := Q)).length ≤
      Pipeline.additionGates.length +
        2 * (Pipeline.additionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum +
        2 * params.width + 2 := by
  rw [cleanupGates_length]
  have hexceptional := exceptionalGateCount_le (E := E) (Q := Q)
  omega

/-- Width-closed CNOT bound for the combined cleanup schedule. -/
theorem cleanupGates_cnotMultiplicity_sum_le :
    ((cleanupGates (E := E) (Q := Q)).map
      EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      (Pipeline.additionGates.map
        EncodedBit.GateSpec.xMultiplicity).sum + 2 * params.width := by
  rw [cleanupGates_cnotMultiplicity_sum]
  have hexceptional := exceptionalGateCount_le (E := E) (Q := Q)
  omega

theorem cleanupGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ cleanupGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate := by
  intro gate hgate
  rw [cleanupGates, exceptionalCleanupGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact normalCleanupGates_bitDisjoint_controlBit gate hgate
  · rcases List.mem_append.mp hgate with hgate | hgate
    · exact exceptionalXGates_bitDisjoint_controlBit gate hgate
    · exact exceptionalYGates_bitDisjoint_controlBit gate hgate

theorem cleanupGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ cleanupGates (E := E) (Q := Q) →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate := by
  intro gate hgate
  rw [cleanupGates, exceptionalCleanupGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact normalCleanupGates_bitDisjoint_controlWorkBit gate hgate
  · rcases List.mem_append.mp hgate with hgate | hgate
    · exact exceptionalXGates_bitDisjoint_controlWorkBit gate hgate
    · exact exceptionalYGates_bitDisjoint_controlWorkBit gate hgate

/-- Register action of the complete normal-or-exceptional cleanup ledger. -/
def cleanupStep : Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.GateSpec.stepList (cleanupGates (E := E) (Q := Q))

/-- On the ordinary branch, the selector mismatch supplies exactly the
generic-domain premise needed by the reverse addition.  The lifted dagger
therefore clears the saved input point while preserving the exceptional
suffix. -/
theorem reverseAdditionGates_selectedBoundary_clean
    (control : Bool) (P : GenericPointAddition.Input E Q)
    (hmatch : (Pipeline.resultWords P).1 ≠ (Pipeline.pointWords Q).1) :
    EncodedBit.GateSpec.stepList reverseAdditionGates
        (Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
          (Pipeline.pointWords (AffinePoint.negate Q))
          (Pipeline.pointWords P.1) false) =
      Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
        (Pipeline.pointWords (AffinePoint.negate Q))
        (PointAddition.PortFrame.zeroPoint params.width) false := by
  have hreverse : GenericAddDomain (Pipeline.resultPoint P)
      (AffinePoint.negate Q) := by
    intro hx
    apply hmatch
    simpa [Pipeline.resultWords, Pipeline.pointWords] using
      congrArg ParameterizedPointAddition.residueWord
        (hx.trans (AffinePoint.negate_x Q))
  let reverseInput : GenericPointAddition.Input E (AffinePoint.negate Q) :=
    ⟨Pipeline.resultPoint P, hreverse⟩
  have hrecovered : Pipeline.resultWords reverseInput =
      Pipeline.pointWords P.1 := by
    unfold Pipeline.resultWords
    rw [Pipeline.reverseResultPoint_eq P hreverse]
  unfold reverseAdditionGates
  rw [Layout.stepList_liftPipelineGates]
  apply Prod.ext
  · rw [← hrecovered]
    change EncodedBit.GateSpec.stepList Pipeline.additionGates.reverse
        (Pipeline.preloadInputRegistersAt (Q := AffinePoint.negate Q)
          (Pipeline.resultWords reverseInput) control reverseInput) =
      Pipeline.preloadInputRegistersAt (Q := AffinePoint.negate Q)
        (PointAddition.PortFrame.zeroPoint params.width) control reverseInput
    exact Pipeline.additionGates_reverse_clean control reverseInput
  · rfl

/-- The ordinary selected boundary executes only the generic dagger and
clears the saved input point. -/
theorem cleanupStep_normal_selectedBoundary
    (control : Bool) (P : GenericPointAddition.Input E Q)
    (hmatch : (Pipeline.resultWords P).1 ≠ (Pipeline.pointWords Q).1) :
    cleanupStep (E := E) (Q := Q)
        (Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
          (Pipeline.pointWords (AffinePoint.negate Q))
          (Pipeline.pointWords P.1) false) =
      Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
        (Pipeline.pointWords (AffinePoint.negate Q))
        (PointAddition.PortFrame.zeroPoint params.width) false := by
  unfold cleanupStep cleanupGates
  rw [EncodedBit.GateSpec.stepList_append]
  change exceptionalCleanupStep (E := E) (Q := Q)
      (normalCleanupStep _) = _
  rw [normalCleanupStep_eq_reverse_of_selector_false _ (by rfl) (by rfl)]
  rw [reverseAdditionGates_selectedBoundary_clean control P hmatch]
  exact exceptionalCleanupStep_eq_self_of_selector_false _ (by rfl)

/-- The exceptional selected boundary executes only the fixed controlled
constant xors.  The exceptional curve identity identifies the saved input
with `2(-Q)`, so the output point is cleared without invoking the generic
dagger. -/
theorem cleanupStep_exceptional_selectedBoundary
    (control : Bool) (P : GenericPointAddition.Input E Q)
    (hmatch : (Pipeline.resultWords P).1 = (Pipeline.pointWords Q).1) :
    cleanupStep (E := E) (Q := Q)
        (Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
          (Pipeline.pointWords (AffinePoint.negate Q))
          (Pipeline.pointWords P.1) true) =
      Layout.selectedBoundaryRegisters control (Pipeline.resultWords P)
        (Pipeline.pointWords (AffinePoint.negate Q))
        (PointAddition.PortFrame.zeroPoint params.width) true := by
  have hx : (Pipeline.resultPoint P).x = Q.x := by
    apply ZMod.val_injective
    have hval := congrArg (fun word ↦ word.val) hmatch
    simpa [Pipeline.resultWords, Pipeline.pointWords] using hval
  have hcoordinates :=
    Pipeline.ExceptionalCleanupMath.doubleNegate_coordinates_eq_input_of_resultPoint_x_eq
      P hx
  have hwords : Pipeline.pointWords P.1 =
      (exceptionalXConstant (E := E) (Q := Q),
        exceptionalYConstant (E := E) (Q := Q)) := by
    apply Prod.ext
    · simp [Pipeline.pointWords, exceptionalXConstant, hcoordinates.1]
    · simp [Pipeline.pointWords, exceptionalYConstant, hcoordinates.2]
  unfold cleanupStep cleanupGates
  rw [EncodedBit.GateSpec.stepList_append]
  change exceptionalCleanupStep (E := E) (Q := Q)
      (normalCleanupStep _) = _
  rw [normalCleanupStep_eq_self_of_selector_true _ (by rfl)]
  rw [hwords]
  exact exceptionalCleanupStep_selectedBoundary control
    (Pipeline.resultWords P) (Pipeline.pointWords (AffinePoint.negate Q))

end

end Branch
end ExceptionalCleanup
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
