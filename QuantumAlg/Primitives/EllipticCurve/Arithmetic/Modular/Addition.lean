/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Resource

/-!
# Width-parameterized odd-modulus addition

The first selected-add block of the actual variable multiply-accumulate
carrier becomes a modular adder when its preserved multiplier is the public
constant one.  This adapter exposes the result as the existing
`MAU.Addition.Data.addIntoRight` endpoint while keeping the cleanup flag on an
untouched physical wire.  It deliberately does not execute the remaining
variable-multiplication rounds.
-/

section

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic
namespace ModularAddition

noncomputable section

variable [params : VariableModularMul.Parameters]

local instance modulusNeZero : NeZero params.modulus.val :=
  ⟨Nat.ne_of_gt params.modulusPos⟩

/-- Physical addition carrier: the variable-product workspace and public
cleanup flag. -/
abbrev RawRegisters := VariableModularMul.Registers × Bool

/-- Actual binary layout of the addition adapter. -/
abbrev rawEncoding : BinaryLabelEncoding RawRegisters :=
  BinaryLabelEncoding.prod VariableModularMul.encoding
    BinaryLabelEncoding.bool

/-- Variable-product datum implementing `right += 1 * left`. -/
def multiplicationData (x : MAU.Addition.Data params.modulus.val) :
    VariableModularMul.Data where
  multiplier := 1
  multiplicand := x.left
  accumulator := x.right

/-- The least-significant multiplier bit, which is set in the public constant
one used by this adapter. -/
def firstBit : Fin params.width :=
  ⟨0, params.widthPos⟩

/-- Canonical clean physical representation of modular-addition data. -/
def cleanRegisters (x : MAU.Addition.Data params.modulus.val) : RawRegisters :=
  (VariableModularMul.cleanRegisters (multiplicationData x), x.flag)

private theorem cleanRegisters_injective : Function.Injective cleanRegisters := by
  intro left right h
  rcases left with ⟨leftSource, leftTarget, leftFlag⟩
  rcases right with ⟨rightSource, rightTarget, rightFlag⟩
  have hsourceVal := congrArg (fun state => state.1.inPlace.multiplicand.val) h
  have hsource : leftSource = rightSource := by
    apply ZMod.val_injective
    change
      ((leftSource.val : VariableModularMul.Word)).val =
        ((rightSource.val : VariableModularMul.Word)).val at hsourceVal
    rw [ZMod.val_natCast_of_lt
        ((ZMod.val_lt leftSource).trans
          VariableModularMul.modulus_lt_capacity),
      ZMod.val_natCast_of_lt
        ((ZMod.val_lt rightSource).trans
          VariableModularMul.modulus_lt_capacity)] at hsourceVal
    exact hsourceVal
  have htargetVal := congrArg (fun state => state.1.accumulator.val) h
  have htarget : leftTarget = rightTarget := by
    apply ZMod.val_injective
    change
      ((leftTarget.val : VariableModularMul.Word)).val =
        ((rightTarget.val : VariableModularMul.Word)).val at htargetVal
    rw [ZMod.val_natCast_of_lt
        ((ZMod.val_lt leftTarget).trans
          VariableModularMul.modulus_lt_capacity),
      ZMod.val_natCast_of_lt
        ((ZMod.val_lt rightTarget).trans
          VariableModularMul.modulus_lt_capacity)] at htargetVal
    exact htargetVal
  have hflag : leftFlag = rightFlag := congrArg (fun state => state.2) h
  cases hsource
  cases htarget
  cases hflag
  rfl

/-- Faithful semantic encoding into the clean product workspace. -/
def encoding : BinaryLabelEncoding (MAU.Addition.Data params.modulus.val) where
  width := rawEncoding.width
  encode := fun x => rawEncoding.encode (cleanRegisters x)
  encode_injective := by
    intro left right h
    exact cleanRegisters_injective (rawEncoding.encode_injective h)

/-- Exact physical width of a width-`f` modular-addition adapter. -/
def physicalWidthFor (f : Nat) : Nat :=
  7 * f + 6

/-- Exact physical width of the modular-addition adapter. -/
theorem encoding_width_exact : encoding.width = physicalWidthFor params.width := by
  change VariableModularMul.encoding.width + 1 = _
  calc
    VariableModularMul.encoding.width + 1 =
        VariableModularMul.physicalWidthFor params.width + 1 := by
      rw [VariableModularMul.encoding_width_exact]
    _ = physicalWidthFor params.width := by
      simp only [VariableModularMul.physicalWidthFor, physicalWidthFor]

/-- One actual selected-add route lifted over the preserved flag. -/
def gates : List (EncodedBit.GateSpec rawEncoding) :=
  ((VariableModularMul.selectedAddGates firstBit).map
      (EncodedBit.GateSpec.relabel VariableModularMul.registersEquiv)).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)

/-- The selected-add route compiled over the preserved flag. -/
def circuit : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical rawEncoding.width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates

/-- The actual inverse emits the same self-adjoint native instructions in reverse order. -/
def reverseCircuit : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical rawEncoding.width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates.reverse

/-- Total raw action of the lifted schedule. -/
def rawStep : RawRegisters → RawRegisters :=
  fun state => (VariableModularMul.selectedAddStep firstBit state.1, state.2)

/-- The literal lifted source list has the displayed flag-preserving action. -/
theorem gates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList gates state = rawStep state := by
  rcases state with ⟨data, flag⟩
  have h :
      EncodedBit.GateSpec.stepList
          (((VariableModularMul.selectedAddGates firstBit).map
              (EncodedBit.GateSpec.relabel
                VariableModularMul.registersEquiv)).map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool))
          (data, flag) =
        (VariableModularMul.selectedAddStep firstBit data, flag) := by
    rw [EncodedBit.GateSpec.stepList_prodLeft]
    rw [EncodedBit.GateSpec.stepList_relabel,
      VariableModularMul.selectedAddGates_stepList,
      VariableModularMul.rawSelectedAddStep_registersEquiv]
    simp only [Equiv.symm_apply_apply]
  simpa only [RawRegisters, rawEncoding, gates, rawStep] using h

/-- Lifting and semantic relabeling preserve the strict event trace. -/
theorem gates_events_eq :
    gates.map (EncodedBit.GateSpec.event .empty) =
      (VariableModularMul.selectedAddGates firstBit).map
        (EncodedBit.GateSpec.event .empty) := by
  rw [show gates =
      ((VariableModularMul.selectedAddGates firstBit).map
        (EncodedBit.GateSpec.relabel
          VariableModularMul.registersEquiv)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool) by rfl]
  calc
    _ = ((VariableModularMul.selectedAddGates firstBit).map
          (EncodedBit.GateSpec.relabel
            VariableModularMul.registersEquiv)).map
          (EncodedBit.GateSpec.event .empty) :=
      EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _
    _ = (VariableModularMul.selectedAddGates firstBit).map
          (EncodedBit.GateSpec.event .empty) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro gate _
      cases gate <;> rfl

/-- Lifting and semantic relabeling preserve the source-list length. -/
@[simp] theorem gates_length :
    gates.length = (VariableModularMul.selectedAddGates firstBit).length := by
  rw [show gates =
      ((VariableModularMul.selectedAddGates firstBit).map
        (EncodedBit.GateSpec.relabel
          VariableModularMul.registersEquiv)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool) by rfl,
    List.length_map, List.length_map]

/-- Closed primitive-length bound for a width-`f` modular-addition adapter. -/
def gateLengthBoundFor (f : Nat) : Nat :=
  116 * f + 15

/-- Closed literal-X bound for a width-`f` modular-addition adapter. -/
def xBoundFor (f : Nat) : Nat :=
  gateLengthBoundFor f

/-- Closed CNOT bound for a width-`f` modular-addition adapter. -/
def cnotBoundFor (f : Nat) : Nat :=
  8 * f + 1

/-- Closed Toffoli bound for a width-`f` modular-addition adapter. -/
def toffoliBoundFor (f : Nat) : Nat :=
  108 * f + 14

/-- Closed unit-depth bound for a width-`f` modular-addition adapter. -/
def unitDepthBoundFor (f : Nat) : Nat :=
  gateLengthBoundFor f

/-- Closed primitive-length bound for the instantiated modular-addition adapter. -/
def gateLengthBound : Nat :=
  gateLengthBoundFor params.width

/-- Closed literal-X bound for the instantiated modular-addition adapter. -/
def xBound : Nat :=
  xBoundFor params.width

/-- Closed CNOT bound for the instantiated modular-addition adapter. -/
def cnotBound : Nat :=
  cnotBoundFor params.width

/-- Closed Toffoli bound for the instantiated modular-addition adapter. -/
def toffoliBound : Nat :=
  toffoliBoundFor params.width

/-- Closed unit-depth bound for the instantiated modular-addition adapter. -/
def unitDepthBound : Nat :=
  unitDepthBoundFor params.width

/-- The lifted addition list preserves the source X coordinate exactly. -/
theorem gates_xMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum =
      ((VariableModularMul.selectedAddGates firstBit).map
        EncodedBit.GateSpec.xMultiplicity).sum :=
  EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq .empty gates_events_eq

/-- The lifted addition list preserves the source CNOT coordinate exactly. -/
theorem gates_cnotMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      ((VariableModularMul.selectedAddGates firstBit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum :=
  EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty gates_events_eq

/-- The lifted addition list preserves the source Toffoli coordinate exactly. -/
theorem gates_toffoliMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((VariableModularMul.selectedAddGates firstBit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum :=
  EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty gates_events_eq

/-- The literal modular-addition list obeys its closed primitive-length bound. -/
theorem gates_length_le : gates.length ≤ gateLengthBound := by
  rw [gates_length]
  simpa only [gateLengthBound, gateLengthBoundFor,
    VariableModularMul.selectedAddCircuit,
    EncodedBit.GateSpec.programList_eventCost_card] using
    VariableModularMul.selectedAddCircuit_eventCount_le firstBit

/-- The literal modular-addition list obeys its closed X-coordinate bound. -/
theorem gates_xMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ xBound := by
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums gates
  have hx :
      (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ gates.length := by
    rw [hcoordinates]
    omega
  simpa only [xBound, xBoundFor, gateLengthBound] using
    hx.trans gates_length_le

/-- The literal modular-addition list obeys its closed CNOT-coordinate bound. -/
theorem gates_cnotMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤ cnotBound := by
  rw [gates_cnotMultiplicity_sum]
  simpa only [cnotBound, cnotBoundFor] using
    (VariableModularMul.selectedAddGates_cnotMultiplicity_sum firstBit).le

/-- The literal modular-addition list obeys its closed Toffoli-coordinate bound. -/
theorem gates_toffoliMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      toffoliBound := by
  rw [gates_toffoliMultiplicity_sum]
  simpa only [toffoliBound, toffoliBoundFor,
    VariableModularMul.selectedAddCircuit,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum] using
    VariableModularMul.selectedAddCircuit_toffoli_count_le firstBit

/-- The actual circuit realizes its total raw action. -/
theorem rawRealizes : UnitaryCircuit.Realizes rawEncoding circuit rawStep := by
  unfold circuit
  exact EncodedBit.GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    gates gates_stepList

noncomputable instance rawFinite : Finite RawRegisters :=
  Finite.of_injective rawEncoding.encode rawEncoding.encode_injective

instance rawNonempty : Nonempty RawRegisters :=
  ⟨cleanRegisters ({ left := 0, right := 0, flag := false } :
    MAU.Addition.Data params.modulus.val)⟩

/-- Total inverse of the realized finite raw modular-addition permutation. -/
noncomputable def rawInverseStep : RawRegisters → RawRegisters :=
  EncodedBit.GateSpec.stepList gates.reverse

/-- The literal reverse schedule is a total right inverse on every raw register state. -/
theorem rawInverseStep_rightInverse :
    Function.RightInverse rawInverseStep rawStep := by
  intro state
  rw [rawInverseStep, ← gates_stepList]
  simpa only [List.reverse_reverse] using
    EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse state

/-- The same actual schedules cancel in the opposite order. -/
theorem rawInverseStep_leftInverse :
    Function.LeftInverse rawInverseStep rawStep := by
  intro state
  rw [rawInverseStep, ← gates_stepList]
  exact EncodedBit.GateSpec.stepList_reverse_stepList gates state

/-- The named inverse is exactly the semantic action of the emitted reverse list. -/
theorem gates_reverse_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList gates.reverse state = rawInverseStep state := rfl

theorem rawDaggerRealizes :
    UnitaryCircuit.Realizes rawEncoding reverseCircuit rawInverseStep :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty gates.reverse

/-- The raw action specializes to modular addition on clean states. -/
theorem rawStep_cleanEndpoint (x : MAU.Addition.Data params.modulus.val) :
    rawStep (cleanRegisters x) = cleanRegisters x.addIntoRight := by
  have hselected := VariableModularMul.selectedAddStep_cleanEndpoint firstBit
    (multiplicationData x)
  have hadd :
      VariableModularMul.Data.addSelected firstBit (multiplicationData x) =
        multiplicationData x.addIntoRight := by
    rcases x with ⟨left, right, flag⟩
    simp only [VariableModularMul.Data.addSelected, multiplicationData,
      MAU.Addition.Data.addIntoRight, firstBit]
    congr 1
    by_cases hmodulus : params.modulus.val = 1
    · apply ZMod.val_injective
      have hbit : (1 : ZMod params.modulus.val).val.testBit 0 = false := by
        simp [ZMod.val_one_eq_one_mod, hmodulus]
      simp only [hbit, Bool.false_eq_true, if_false, add_zero]
      have hleft := ZMod.val_lt right
      have hright := ZMod.val_lt (right + left)
      omega
    · have hmodulusGt : 1 < params.modulus.val := by
        have hmodulusPos := params.modulusPos
        omega
      let _ : Fact (1 < params.modulus.val) := ⟨hmodulusGt⟩
      simp [ZMod.val_one]
  rw [show rawStep (cleanRegisters x) =
      (VariableModularMul.selectedAddStep firstBit
        (VariableModularMul.cleanRegisters (multiplicationData x)), x.flag) by
    rfl]
  rw [hselected]
  rw [hadd]
  rfl

theorem rawInverseStep_cleanEndpoint
    (x : MAU.Addition.Data params.modulus.val) :
    rawInverseStep (cleanRegisters x) = cleanRegisters x.subFromRight := by
  have hforward := rawStep_cleanEndpoint (x.subFromRight)
  have hcancel : x.subFromRight.addIntoRight = x := by
    cases x
    simp [MAU.Addition.Data.subFromRight, MAU.Addition.Data.addIntoRight,
      sub_eq_add_neg, add_assoc]
  rw [hcancel] at hforward
  rw [← hforward]
  exact rawInverseStep_leftInverse _

/-- The actual width-parameterized circuit realizes modular addition. -/
theorem realizes : UnitaryCircuit.Realizes encoding circuit
    (MAU.Addition.Data.addIntoRight) where
  apply_encoded_ket := by
    intro x
    have h := rawRealizes.apply_encoded_ket (cleanRegisters x)
    rw [rawStep_cleanEndpoint] at h
    exact h

/-- The clean encoded datum on the actual certified physical register. -/
def cleanKet (value : MAU.Addition.Data params.modulus.val) :
    NormalizedVector (QubitLayout.canonical rawEncoding.width).toQuantum.register :=
  NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (encoding.encode value))

/-- Exact clean computational-basis modular-addition endpoint. -/
theorem circuit_applyNormalized_clean_ket
    (x : MAU.Addition.Data params.modulus.val) :
    circuit.applyNormalized
        (cleanKet x) =
      cleanKet x.addIntoRight :=
  realizes.apply_encoded_ket x

/-- Reversing the same actual circuit subtracts the preserved left operand. -/
theorem dagger_applyNormalized_clean_ket
    (x : MAU.Addition.Data params.modulus.val) :
    reverseCircuit.applyNormalized
        (cleanKet x) =
      cleanKet x.subFromRight := by
  have actual := rawDaggerRealizes.apply_encoded_ket (cleanRegisters x)
  rw [rawInverseStep_cleanEndpoint] at actual
  exact actual

/-- Uniform Toffoli upper bound inherited from the actual selected-add route. -/
theorem circuit_toffoli_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      circuit.eventCost ≤
      toffoliBound := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates).eventCost ≤ _
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact gates_toffoliMultiplicity_sum_le

/-- Uniform circuit-only depth upper bound inherited from the actual
selected-add route. -/
theorem circuit_unitDepth_le :
    circuit.evaluatedEventDepth (fun _ => 1) ≤ unitDepthBound := by
  change
    (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates).evaluatedEventDepth
      (fun _ => 1) ≤ _
  rw [EncodedBit.GateSpec.programList_evaluatedEventDepth_unit]
  exact gates_length_le

end

end ModularAddition
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic

end
