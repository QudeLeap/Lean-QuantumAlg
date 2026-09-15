/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.ExceptionalCleanup.Layout

/-!
# Reversible mutable-coordinate selector

This leaf compares the mutable X-coordinate with a fixed field-width word by
xoring the word, applying the explicit clean zero test, and undoing the xor.
The resulting selector is an xor-output: every non-selector register is
restored by the literal gate schedule.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace ExceptionalCleanup
namespace Selector

open Nat.FixedWidth

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

/-- The source position of a mutable-X bit in the widened zero-test word. -/
private def mutableSourceIndex (bit : Fin params.width) :
    Fin (params.width + 2) :=
  Fin.castSucc (Fin.castSucc bit)

/-- The source position of the first high clean padding bit. -/
private def paddingLeftSourceIndex : Fin (params.width + 2) :=
  Fin.castSucc (Fin.last params.width)

/-- The source position of the second high clean padding bit. -/
private def paddingRightSourceIndex : Fin (params.width + 2) :=
  Fin.last (params.width + 1)

private theorem sourceWord_bit_mutable (bit : Fin params.width) :
    (Layout.sourceWord (params := params)).bit
        (mutableSourceIndex (params := params) bit) =
      (Layout.mutableXWord (params := params)).bit bit := by
  simp [Layout.sourceWord, mutableSourceIndex]

private theorem sourceWord_bit_paddingLeft :
    (Layout.sourceWord (params := params)).bit
        (paddingLeftSourceIndex (params := params)) =
      Layout.paddingLeftBit (params := params) := by
  simp [Layout.sourceWord, paddingLeftSourceIndex]

private theorem sourceWord_bit_paddingRight :
    (Layout.sourceWord (params := params)).bit
        (paddingRightSourceIndex (params := params)) =
      Layout.paddingRightBit (params := params) := by
  simp [Layout.sourceWord, paddingRightSourceIndex]

private theorem mutableSourceIndex_ne_paddingLeftSourceIndex
    (bit : Fin params.width) :
    mutableSourceIndex (params := params) bit ≠
      paddingLeftSourceIndex (params := params) := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [mutableSourceIndex, paddingLeftSourceIndex] at hval
  omega

private theorem mutableSourceIndex_ne_paddingRightSourceIndex
    (bit : Fin params.width) :
    mutableSourceIndex (params := params) bit ≠
      paddingRightSourceIndex (params := params) := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [mutableSourceIndex, paddingRightSourceIndex] at hval
  omega

private theorem mutableXWord_wire_ne_selectorBit (bit : Fin params.width) :
    ((Layout.mutableXWord (params := params)).bit bit).wire ≠
      (Layout.selectorBit (params := params)).wire := by
  simpa only [sourceWord_bit_mutable] using
    Layout.sourceWord_wire_ne_selectorBit (params := params)
      (mutableSourceIndex (params := params) bit)

private theorem mutableXWord_wire_ne_zeroWorkBit
    (source work : Fin params.width) :
    ((Layout.mutableXWord (params := params)).bit source).wire ≠
      (Layout.zeroWorkBit (params := params) work).wire := by
  simpa only [sourceWord_bit_mutable, Layout.zeroWorkWord] using
    Layout.sourceWord_wire_ne_zeroWorkWord (params := params)
      (mutableSourceIndex (params := params) source) work

private theorem mutableXWord_wire_ne_paddingLeftBit
    (bit : Fin params.width) :
    ((Layout.mutableXWord (params := params)).bit bit).wire ≠
      (Layout.paddingLeftBit (params := params)).wire := by
  simpa only [sourceWord_bit_mutable, sourceWord_bit_paddingLeft] using
    Layout.sourceWord_pairwise_ne (params := params)
      (mutableSourceIndex (params := params) bit)
      (paddingLeftSourceIndex (params := params))
      (mutableSourceIndex_ne_paddingLeftSourceIndex (params := params) bit)

private theorem mutableXWord_wire_ne_paddingRightBit
    (bit : Fin params.width) :
    ((Layout.mutableXWord (params := params)).bit bit).wire ≠
      (Layout.paddingRightBit (params := params)).wire := by
  simpa only [sourceWord_bit_mutable, sourceWord_bit_paddingRight] using
    Layout.sourceWord_pairwise_ne (params := params)
      (mutableSourceIndex (params := params) bit)
      (paddingRightSourceIndex (params := params))
      (mutableSourceIndex_ne_paddingRightSourceIndex (params := params) bit)

omit params in
private theorem xorConstantGates_bitDisjoint
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (observed : EncodedBit encoding) (target : EncodedBit.Word encoding width)
    (constant : Fin (2 ^ width))
    (htarget : ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (gate : EncodedBit.GateSpec encoding)
    (hgate : gate ∈ EncodedBit.Word.xorConstantGates target constant) :
    EncodedBit.GateSpec.bitDisjoint observed gate := by
  rw [EncodedBit.Word.xorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  exact htarget bit

omit params in
private theorem zeroTestGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data} {tail : Nat}
    (layout : EncodedBit.Word.ZeroTestLayout (encoding := encoding) tail)
    (observed : EncodedBit encoding)
    (hsource : ∀ source,
      (layout.source.bit source).wire ≠ observed.wire)
    (houtput : layout.output.wire ≠ observed.wire)
    (hwork : ∀ work, (layout.work.bit work).wire ≠ observed.wire) :
    ∀ gate, gate ∈ layout.gates →
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  have handGate : ∀ work,
      EncodedBit.GateSpec.bitDisjoint observed
        (EncodedBit.Word.ZeroTestLayout.andGateAt layout work) := by
    intro work
    change
      (EncodedBit.Word.ZeroTestLayout.chainControlA layout work).wire ≠
          observed.wire ∧
        (EncodedBit.Word.ZeroTestLayout.chainControlB layout work).wire ≠
          observed.wire ∧
        (layout.work.bit work).wire ≠ observed.wire
    refine ⟨?_, ?_, hwork work⟩
    · unfold EncodedBit.Word.ZeroTestLayout.chainControlA
      split
      · exact hsource 0
      · exact hwork _
    · exact hsource _
  have hand : ∀ gate,
      gate ∈ EncodedBit.Word.ZeroTestLayout.andGates layout →
        EncodedBit.GateSpec.bitDisjoint observed gate := by
    intro gate hgate
    simp only [EncodedBit.Word.ZeroTestLayout.andGates] at hgate
    rcases List.mem_ofFn.mp hgate with ⟨work, rfl⟩
    exact handGate work
  have hsourceX : ∀ gate,
      gate ∈ EncodedBit.Word.ZeroTestLayout.sourceXGates layout →
        EncodedBit.GateSpec.bitDisjoint observed gate := by
    intro gate hgate
    simp only [EncodedBit.Word.ZeroTestLayout.sourceXGates] at hgate
    rcases List.mem_ofFn.mp hgate with ⟨source, rfl⟩
    exact hsource source
  have hcompute : ∀ gate,
      gate ∈ EncodedBit.Word.ZeroTestLayout.computeGates layout →
        EncodedBit.GateSpec.bitDisjoint observed gate := by
    intro gate hgate
    rw [EncodedBit.Word.ZeroTestLayout.computeGates] at hgate
    rcases List.mem_append.mp hgate with hgate | hgate
    · exact hsourceX gate hgate
    · exact hand gate hgate
  have hfinal : EncodedBit.GateSpec.bitDisjoint observed
      (EncodedBit.Word.ZeroTestLayout.finalGate layout) := by
    unfold EncodedBit.Word.ZeroTestLayout.finalGate
    split
    · exact ⟨hsource 0, hsource 1, houtput⟩
    · exact ⟨hwork _, hsource _, houtput⟩
  intro gate hgate
  rw [EncodedBit.Word.ZeroTestLayout.gates] at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · rcases List.mem_append.mp hgate with hgate | hgate
    · exact hcompute gate hgate
    · simp only [List.mem_singleton] at hgate
      subst gate
      exact hfinal
  · exact hcompute gate (List.mem_reverse.mp hgate)

/-- Literal forward xor of the comparison constant into mutable X. -/
private def forwardStep (constant : Fin (2 ^ params.width)) :
    Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.Word.xorConstantStep (Layout.mutableXWord (params := params))
    constant

/-- Literal reverse xor that restores mutable X after the zero test. -/
private def unloadStep (constant : Fin (2 ^ params.width)) :
    Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.Word.xorConstantUnloadStep
    (Layout.mutableXWord (params := params)) constant

/-- Actual X/zero-test/X gate schedule for comparing mutable X with a fixed
word. -/
def compareGates (constant : Fin (2 ^ params.width)) :
    List (EncodedBit.GateSpec (Layout.rawEncoding (params := params))) :=
  EncodedBit.Word.xorConstantGates (Layout.mutableXWord (params := params))
      constant ++
    (Layout.mutableXZeroTestLayout (params := params)).gates ++
    (EncodedBit.Word.xorConstantGates
      (Layout.mutableXWord (params := params)) constant).reverse

/-- An external observed bit that is disjoint from the widened source word,
selector output, and zero-test work word is disjoint from the complete
comparison schedule. -/
theorem compareGates_bitDisjoint_observed
    (constant : Fin (2 ^ params.width))
    (observed : EncodedBit (Layout.rawEncoding (params := params)))
    (hsource : ∀ source,
      ((Layout.sourceWord (params := params)).bit source).wire ≠ observed.wire)
    (hselector : (Layout.selectorBit (params := params)).wire ≠
      observed.wire)
    (hwork : ∀ work,
      (Layout.zeroWorkBit (params := params) work).wire ≠ observed.wire) :
    ∀ gate, gate ∈ compareGates (params := params) constant →
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  have hmutable : ∀ bit,
      ((Layout.mutableXWord (params := params)).bit bit).wire ≠
        observed.wire := by
    intro bit
    simpa only [sourceWord_bit_mutable] using
      hsource (mutableSourceIndex (params := params) bit)
  intro gate hgate
  rw [compareGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · rcases List.mem_append.mp hgate with hgate | hgate
    · exact xorConstantGates_bitDisjoint observed Layout.mutableXWord
        constant hmutable gate hgate
    · exact zeroTestGates_bitDisjoint_observed
        (Layout.mutableXZeroTestLayout (params := params)) observed hsource
        hselector hwork gate hgate
  · exact xorConstantGates_bitDisjoint observed Layout.mutableXWord
      constant hmutable gate (List.mem_reverse.mp hgate)

/-- The full comparison schedule is disjoint from the public translation
control. -/
theorem compareGates_bitDisjoint_controlBit
    (constant : Fin (2 ^ params.width)) :
    ∀ gate, gate ∈ compareGates (params := params) constant →
      EncodedBit.GateSpec.bitDisjoint Layout.controlBit gate := by
  exact compareGates_bitDisjoint_observed constant Layout.controlBit
    Layout.sourceWord_wire_ne_controlBit
    Layout.selectorBit_wire_ne_controlBit
    Layout.zeroWorkBit_wire_ne_controlBit

/-- The full comparison schedule is disjoint from the clean work bit of the
outer public-control decomposition. -/
theorem compareGates_bitDisjoint_controlWorkBit
    (constant : Fin (2 ^ params.width)) :
    ∀ gate, gate ∈ compareGates (params := params) constant →
      EncodedBit.GateSpec.bitDisjoint Layout.controlWorkBit gate := by
  exact compareGates_bitDisjoint_observed constant Layout.controlWorkBit
    Layout.sourceWord_wire_ne_controlWorkBit
    Layout.selectorBit_wire_ne_controlWorkBit
    Layout.zeroWorkBit_wire_ne_controlWorkBit

/-- Exact leaf count of the reversible comparison schedule. -/
theorem compareGates_length (constant : Fin (2 ^ params.width)) :
    (compareGates (params := params) constant).length =
      2 * (EncodedBit.Word.constantOneIndices constant).length +
        4 * params.width + 5 := by
  unfold compareGates
  simp only [List.length_append, List.length_reverse,
    EncodedBit.Word.xorConstantGates_length,
    EncodedBit.Word.ZeroTestLayout.gates_length]
  omega

/-- Exact X coordinate of the reversible comparison schedule. -/
theorem compareGates_xMultiplicity_sum
    (constant : Fin (2 ^ params.width)) :
    ((compareGates (params := params) constant).map
      EncodedBit.GateSpec.xMultiplicity).sum =
      2 * (EncodedBit.Word.constantOneIndices constant).length +
        2 * params.width + 4 := by
  unfold compareGates
  simp only [List.map_append, List.sum_append, List.map_reverse,
    List.sum_reverse, EncodedBit.Word.xorConstantGates_xMultiplicity_sum,
    EncodedBit.Word.ZeroTestLayout.gates_xMultiplicity_sum]
  omega

/-- The reversible comparison schedule contains no CNOT leaves. -/
theorem compareGates_cnotMultiplicity_sum
    (constant : Fin (2 ^ params.width)) :
    ((compareGates (params := params) constant).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  unfold compareGates
  simp [List.map_reverse, List.sum_reverse,
    EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum,
    EncodedBit.Word.ZeroTestLayout.gates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate of the reversible comparison schedule. -/
theorem compareGates_toffoliMultiplicity_sum
    (constant : Fin (2 ^ params.width)) :
    ((compareGates (params := params) constant).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * params.width + 1 := by
  unfold compareGates
  simp [List.map_reverse, List.sum_reverse,
    EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum,
    EncodedBit.Word.ZeroTestLayout.gates_toffoliMultiplicity_sum]

/-- Closed width-only leaf bound for one reversible comparison. -/
theorem compareGates_length_le (constant : Fin (2 ^ params.width)) :
    (compareGates (params := params) constant).length ≤
      6 * params.width + 5 := by
  rw [compareGates_length]
  have hset := EncodedBit.Word.constantOneIndices_length_le constant
  omega

/-- Closed width-only X-coordinate bound for one reversible comparison. -/
theorem compareGates_xMultiplicity_sum_le
    (constant : Fin (2 ^ params.width)) :
    ((compareGates (params := params) constant).map
      EncodedBit.GateSpec.xMultiplicity).sum ≤
      4 * params.width + 4 := by
  rw [compareGates_xMultiplicity_sum]
  have hset := EncodedBit.Word.constantOneIndices_length_le constant
  omega

/-- Exact folded action of the mutable-X selector gate list. -/
def compareStep (constant : Fin (2 ^ params.width)) :
    Layout.RawRegisters → Layout.RawRegisters :=
  EncodedBit.GateSpec.stepList (compareGates (params := params) constant)

/-- Direct circuit compilation of the literal mutable-X selector schedule. -/
def compareProgram (constant : Fin (2 ^ params.width)) :
    UnitaryCircuit (Qubits (Layout.rawEncoding (params := params)).width) :=
  EncodedBit.GateSpec.programList (compareGates (params := params) constant)

/-- The selector circuit realizes its exact literal gate-list action. -/
theorem compareProgram_realizes (constant : Fin (2 ^ params.width)) :
    UnitaryCircuit.Realizes (Layout.rawEncoding (params := params))
      (compareProgram (params := params) constant)
      (compareStep (params := params) constant) :=
  EncodedBit.GateSpec.realizesList (compareGates (params := params) constant)

private theorem compareStep_eq_schedule
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters) :
    compareStep (params := params) constant state =
      unloadStep (params := params) constant
        ((Layout.mutableXZeroTestLayout (params := params)).step
          (forwardStep (params := params) constant state)) := by
  unfold compareStep compareGates unloadStep forwardStep
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

private theorem forwardStep_get_zeroWork
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (work : Fin params.width) :
    (Layout.zeroWorkBit (params := params) work).get
        (forwardStep (params := params) constant state) =
      (Layout.zeroWorkBit (params := params) work).get state := by
  unfold forwardStep
  exact EncodedBit.Word.xorConstantStep_get_observed_of_target_ne
    (Layout.mutableXWord (params := params)) constant
    (Layout.zeroWorkBit (params := params) work)
    (fun source => mutableXWord_wire_ne_zeroWorkBit (params := params)
      source work) state

private theorem forwardStep_get_paddingLeft
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters) :
    (Layout.paddingLeftBit (params := params)).get
        (forwardStep (params := params) constant state) =
      (Layout.paddingLeftBit (params := params)).get state := by
  unfold forwardStep
  exact EncodedBit.Word.xorConstantStep_get_observed_of_target_ne
    (Layout.mutableXWord (params := params)) constant
    (Layout.paddingLeftBit (params := params))
    (fun bit => mutableXWord_wire_ne_paddingLeftBit (params := params) bit)
    state

private theorem forwardStep_get_paddingRight
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters) :
    (Layout.paddingRightBit (params := params)).get
        (forwardStep (params := params) constant state) =
      (Layout.paddingRightBit (params := params)).get state := by
  unfold forwardStep
  exact EncodedBit.Word.xorConstantStep_get_observed_of_target_ne
    (Layout.mutableXWord (params := params)) constant
    (Layout.paddingRightBit (params := params))
    (fun bit => mutableXWord_wire_ne_paddingRightBit (params := params) bit)
    state

private theorem mutableXWord_get (bit : Fin params.width)
    (state : Layout.RawRegisters) :
    ((Layout.mutableXWord (params := params)).bit bit).get state =
      ((Layout.mutableXPort (params := params)).read state).val.testBit bit.val := by
  exact (Layout.mutableXPort (params := params)).get_bit bit state

private theorem source_zero_iff_mutableX_eq
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hpaddingLeft : (Layout.paddingLeftBit (params := params)).get state = false)
    (hpaddingRight : (Layout.paddingRightBit (params := params)).get state = false) :
    (∀ source,
      ((Layout.sourceWord (params := params)).bit source).get
          (forwardStep (params := params) constant state) = false) ↔
      (Layout.mutableXPort (params := params)).read state = constant := by
  constructor
  · intro hzero
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have hbit := hzero (mutableSourceIndex (params := params) bit)
    rw [sourceWord_bit_mutable] at hbit
    rw [show
      ((Layout.mutableXWord (params := params)).bit bit).get
          (forwardStep (params := params) constant state) =
        (((Layout.mutableXWord (params := params)).bit bit).get state ^^
          constant.val.testBit bit.val) by
        unfold forwardStep
        exact EncodedBit.Word.xorConstantStep_get_target
          (Layout.mutableXWord (params := params)) constant bit
          (fun other hne => Layout.mutableXWord_pairwise_ne
            (params := params) other bit hne) state] at hbit
    rw [mutableXWord_get] at hbit
    cases hread :
        ((Layout.mutableXPort (params := params)).read state).val.testBit bit.val <;>
      cases hconstant : constant.val.testBit bit.val <;> simp_all
  · intro hmatch source
    refine Fin.lastCases ?_ ?_ source
    · simpa [Layout.sourceWord] using
        (forwardStep_get_paddingRight (params := params) constant state).trans
          hpaddingRight
    · intro lower
      refine Fin.lastCases ?_ ?_ lower
      · simpa [Layout.sourceWord] using
          (forwardStep_get_paddingLeft (params := params) constant state).trans
            hpaddingLeft
      · intro bit
        rw [show
          (Layout.sourceWord (params := params)).bit bit.castSucc.castSucc =
            (Layout.mutableXWord (params := params)).bit bit by
          simp [Layout.sourceWord]]
        unfold forwardStep
        rw [EncodedBit.Word.xorConstantStep_get_target
          (Layout.mutableXWord (params := params)) constant bit
          (fun other hne => Layout.mutableXWord_pairwise_ne
            (params := params) other bit hne) state]
        rw [mutableXWord_get, hmatch]
        simp

private theorem zeroTestControl_eq_decide_source_zero
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hclean : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get
          (forwardStep (params := params) constant state) = false) :
    (EncodedBit.Word.ZeroTestLayout.finalControl
      (Layout.mutableXZeroTestLayout (params := params))
      (EncodedBit.GateSpec.stepList
        ((Layout.mutableXZeroTestLayout (params := params)).computeGates)
        (forwardStep (params := params) constant state))) =
      decide (∀ source,
        ((Layout.sourceWord (params := params)).bit source).get
          (forwardStep (params := params) constant state) = false) := by
  by_cases hzero : ∀ source,
      ((Layout.sourceWord (params := params)).bit source).get
        (forwardStep (params := params) constant state) = false
  · have htrue :=
      (EncodedBit.Word.ZeroTestLayout.finalControl_compute_eq_true_iff
        (Layout.mutableXZeroTestLayout (params := params))
        (forwardStep (params := params) constant state) hclean).mpr hzero
    rw [htrue]
    simp [hzero]
  · have hnotTrue :
      (EncodedBit.Word.ZeroTestLayout.finalControl
        (Layout.mutableXZeroTestLayout (params := params))
        (EncodedBit.GateSpec.stepList
          ((Layout.mutableXZeroTestLayout (params := params)).computeGates)
          (forwardStep (params := params) constant state))) ≠ true := by
      intro htrue
      exact hzero
        ((EncodedBit.Word.ZeroTestLayout.finalControl_compute_eq_true_iff
          (Layout.mutableXZeroTestLayout (params := params))
          (forwardStep (params := params) constant state) hclean).mp htrue)
    have hfalse :
      (EncodedBit.Word.ZeroTestLayout.finalControl
        (Layout.mutableXZeroTestLayout (params := params))
        (EncodedBit.GateSpec.stepList
          ((Layout.mutableXZeroTestLayout (params := params)).computeGates)
          (forwardStep (params := params) constant state))) = false :=
      Bool.eq_false_of_not_eq_true hnotTrue
    rw [hfalse]
    simp [hzero]

private theorem zeroTestControl_eq_mutableX_eq
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hzeroWork : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get state = false)
    (hpaddingLeft : (Layout.paddingLeftBit (params := params)).get state = false)
    (hpaddingRight : (Layout.paddingRightBit (params := params)).get state = false) :
    (EncodedBit.Word.ZeroTestLayout.finalControl
      (Layout.mutableXZeroTestLayout (params := params))
      (EncodedBit.GateSpec.stepList
        ((Layout.mutableXZeroTestLayout (params := params)).computeGates)
        (forwardStep (params := params) constant state))) =
      decide ((Layout.mutableXPort (params := params)).read state = constant) := by
  have hclean : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get
        (forwardStep (params := params) constant state) = false := by
    intro work
    rw [forwardStep_get_zeroWork]
    exact hzeroWork work
  calc
    _ = decide (∀ source,
        ((Layout.sourceWord (params := params)).bit source).get
          (forwardStep (params := params) constant state) = false) :=
      zeroTestControl_eq_decide_source_zero (params := params) constant state
        hclean
    _ = decide ((Layout.mutableXPort (params := params)).read state = constant) := by
      congr 1
      apply propext
      exact source_zero_iff_mutableX_eq (params := params) constant state
        hpaddingLeft hpaddingRight

private theorem unloadStep_selectorBit_flip
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters) :
    unloadStep (params := params) constant
        ((Layout.selectorBit (params := params)).flip state) =
      (Layout.selectorBit (params := params)).flip
        (unloadStep (params := params) constant state) := by
  unfold unloadStep
  apply EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate hgate
  apply xorConstantGates_bitDisjoint
    (Layout.selectorBit (params := params))
    (Layout.mutableXWord (params := params)) constant
    (fun bit => mutableXWord_wire_ne_selectorBit (params := params) bit)
  exact List.mem_reverse.mp (by
    simpa only [EncodedBit.Word.xorConstantUnloadGates] using hgate)

private theorem unloadStep_after_forwardStep
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters) :
    unloadStep (params := params) constant
        (forwardStep (params := params) constant state) = state := by
  unfold unloadStep forwardStep
  exact EncodedBit.Word.xorConstantUnloadStep_after_xorConstantStep
    (Layout.mutableXWord (params := params)) constant state

/-- With a clean zero-test workspace and padding, the exact selector schedule
preserves the entire carrier except for xoring the equality predicate into its
dedicated selector bit. -/
theorem compareStep_eq_selectorFlip
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hzeroWork : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get state = false)
    (hpaddingLeft : (Layout.paddingLeftBit (params := params)).get state = false)
    (hpaddingRight : (Layout.paddingRightBit (params := params)).get state = false) :
    compareStep (params := params) constant state =
      if (Layout.mutableXPort (params := params)).read state = constant then
        (Layout.selectorBit (params := params)).flip state
      else state := by
  rw [compareStep_eq_schedule]
  rw [EncodedBit.Word.ZeroTestLayout.step_eq_outputConditional]
  rw [zeroTestControl_eq_mutableX_eq (params := params) constant state
    hzeroWork hpaddingLeft hpaddingRight]
  by_cases hmatch : (Layout.mutableXPort (params := params)).read state = constant
  · have hdecide : decide ((Layout.mutableXPort (params := params)).read state =
        constant) = true := by
      simp [hmatch]
    rw [hdecide]
    change unloadStep (params := params) constant
        ((Layout.selectorBit (params := params)).flip
          (forwardStep (params := params) constant state)) = _
    rw [unloadStep_selectorBit_flip, unloadStep_after_forwardStep]
    rw [if_pos hmatch]
  · have hdecide : decide ((Layout.mutableXPort (params := params)).read state =
        constant) = false := by
      simp [hmatch]
    rw [hdecide]
    rw [if_neg (by decide : false ≠ true)]
    rw [unloadStep_after_forwardStep]
    rw [if_neg hmatch]

/-- Every non-selector bit is preserved by the clean comparison endpoint. -/
theorem compareStep_get_of_selector_ne
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hzeroWork : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get state = false)
    (hpaddingLeft : (Layout.paddingLeftBit (params := params)).get state = false)
    (hpaddingRight : (Layout.paddingRightBit (params := params)).get state = false)
    (observed : EncodedBit (Layout.rawEncoding (params := params)))
    (hselectorObserved : (Layout.selectorBit (params := params)).wire ≠
      observed.wire) :
    observed.get (compareStep (params := params) constant state) =
      observed.get state := by
  rw [compareStep_eq_selectorFlip (params := params) constant state
    hzeroWork hpaddingLeft hpaddingRight]
  split
  · exact EncodedBit.get_flip_of_wire_ne
      (Layout.selectorBit (params := params)) observed hselectorObserved state
  · rfl

/-- The mutable X word is restored exactly by the clean comparison endpoint. -/
theorem compareStep_mutableX_read
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hzeroWork : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get state = false)
    (hpaddingLeft : (Layout.paddingLeftBit (params := params)).get state = false)
    (hpaddingRight : (Layout.paddingRightBit (params := params)).get state = false) :
    (Layout.mutableXPort (params := params)).read
        (compareStep (params := params) constant state) =
      (Layout.mutableXPort (params := params)).read state := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  rw [← mutableXWord_get (params := params) bit
      (compareStep (params := params) constant state)]
  rw [← mutableXWord_get (params := params) bit state]
  exact compareStep_get_of_selector_ne (params := params) constant state
    hzeroWork hpaddingLeft hpaddingRight
    ((Layout.mutableXWord (params := params)).bit bit)
    (mutableXWord_wire_ne_selectorBit (params := params) bit).symm

/-- The selector output is xored with equality of mutable X and the fixed
comparison constant. -/
theorem compareStep_selector_get
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hzeroWork : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get state = false)
    (hpaddingLeft : (Layout.paddingLeftBit (params := params)).get state = false)
    (hpaddingRight : (Layout.paddingRightBit (params := params)).get state = false) :
    (Layout.selectorBit (params := params)).get
        (compareStep (params := params) constant state) =
      ((Layout.selectorBit (params := params)).get state ^^
        decide ((Layout.mutableXPort (params := params)).read state = constant)) := by
  rw [compareStep_eq_selectorFlip (params := params) constant state
    hzeroWork hpaddingLeft hpaddingRight]
  by_cases hmatch : (Layout.mutableXPort (params := params)).read state = constant
  · rw [if_pos hmatch, EncodedBit.get_flip_self]
    simp [hmatch]
  · rw [if_neg hmatch]
    simp [hmatch]

/-- Clean endpoint frame statement for use by the exceptional cleanup branch.
The mutable X word, both source padding bits, and every zero-test work bit are
restored; only the dedicated selector bit receives the equality xor. -/
theorem compareStep_cleanEndpoint
    (constant : Fin (2 ^ params.width)) (state : Layout.RawRegisters)
    (hzeroWork : ∀ work,
      (Layout.zeroWorkBit (params := params) work).get state = false)
    (hpaddingLeft : (Layout.paddingLeftBit (params := params)).get state = false)
    (hpaddingRight : (Layout.paddingRightBit (params := params)).get state = false) :
    (Layout.mutableXPort (params := params)).read
        (compareStep (params := params) constant state) =
      (Layout.mutableXPort (params := params)).read state ∧
    (∀ work, (Layout.zeroWorkBit (params := params) work).get
        (compareStep (params := params) constant state) = false) ∧
    (Layout.paddingLeftBit (params := params)).get
        (compareStep (params := params) constant state) = false ∧
    (Layout.paddingRightBit (params := params)).get
        (compareStep (params := params) constant state) = false ∧
    (Layout.selectorBit (params := params)).get
        (compareStep (params := params) constant state) =
      ((Layout.selectorBit (params := params)).get state ^^
        decide ((Layout.mutableXPort (params := params)).read state = constant)) := by
  refine ⟨compareStep_mutableX_read (params := params) constant state
    hzeroWork hpaddingLeft hpaddingRight, ?_⟩
  refine ⟨?_, ?_⟩
  · intro work
    calc
      (Layout.zeroWorkBit (params := params) work).get
          (compareStep (params := params) constant state) =
        (Layout.zeroWorkBit (params := params) work).get state :=
          compareStep_get_of_selector_ne (params := params) constant state
            hzeroWork hpaddingLeft hpaddingRight
            (Layout.zeroWorkBit (params := params) work)
            (Layout.zeroWorkWord_wire_ne_selectorBit (params := params) work).symm
      _ = false := hzeroWork work
  refine ⟨?_, ?_⟩
  · calc
      (Layout.paddingLeftBit (params := params)).get
          (compareStep (params := params) constant state) =
        (Layout.paddingLeftBit (params := params)).get state :=
          compareStep_get_of_selector_ne (params := params) constant state
            hzeroWork hpaddingLeft hpaddingRight
            (Layout.paddingLeftBit (params := params))
            (Layout.selectorBit_wire_ne_paddingLeftBit (params := params))
      _ = false := hpaddingLeft
  refine ⟨?_, ?_⟩
  · calc
      (Layout.paddingRightBit (params := params)).get
          (compareStep (params := params) constant state) =
        (Layout.paddingRightBit (params := params)).get state :=
          compareStep_get_of_selector_ne (params := params) constant state
            hzeroWork hpaddingLeft hpaddingRight
            (Layout.paddingRightBit (params := params))
            (Layout.selectorBit_wire_ne_paddingRightBit (params := params))
      _ = false := hpaddingRight
  exact compareStep_selector_get (params := params) constant state
    hzeroWork hpaddingLeft hpaddingRight

end

end Selector
end ExceptionalCleanup
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
