/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Resource
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.BlockBank

/-!
# Width-parameterized odd-modulus multiply-accumulate

This public clean-subspace adapter exposes the actual variable multiplication
schedule as `target += left * right (mod p)` while preserving both factors and
the cleanup flag.
-/

section

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic
namespace ModularMultiplication

noncomputable section

variable [params : VariableModularMul.Parameters]

local instance modulusNeZero : NeZero params.modulus.val :=
  ⟨Nat.ne_of_gt params.modulusPos⟩

/-- Public multiply-accumulate data. -/
structure Data where
  /-- Preserved left multiplication factor. -/
  left : ZMod params.modulus.val
  /-- Preserved right multiplication factor. -/
  right : ZMod params.modulus.val
  /-- Accumulator updated by the modular product. -/
  target : ZMod params.modulus.val
  /-- Preserved caller-owned cleanup flag. -/
  flag : Bool
deriving DecidableEq

namespace Data

/-- Add the modular product into the target. -/
def addProduct (x : Data) : Data where
  left := x.left
  right := x.right
  target := x.target + x.left * x.right
  flag := x.flag

/-- Subtract the modular product from the target. -/
def subProduct (x : Data) : Data where
  left := x.left
  right := x.right
  target := x.target - x.left * x.right
  flag := x.flag

@[simp] theorem addProduct_subProduct (x : Data) :
    addProduct (subProduct x) = x := by
  cases x
  simp [addProduct, subProduct, sub_eq_add_neg, add_assoc]

end Data

/-- Physical variable-product registers paired with the preserved flag. -/
abbrev RawRegisters := VariableModularMul.Registers × Bool

/-- Product encoding of the arithmetic carrier and preserved flag. -/
abbrev rawEncoding : BinaryLabelEncoding RawRegisters :=
  BinaryLabelEncoding.prod VariableModularMul.encoding
    BinaryLabelEncoding.bool

/-! ## Public word views for fixed-block assembly -/

/-- Preserved left factor in the physical multiplication block. -/
def leftBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodLeftBit VariableModularMul.encoding
    BinaryLabelEncoding.bool (VariableModularMul.multiplierBit bit)

/-- Preserved right factor in the physical multiplication block. -/
def rightBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodLeftBit VariableModularMul.encoding
    BinaryLabelEncoding.bool (VariableModularMul.inPlaceMultiplicandBit bit)

/-- External accumulator in the physical multiplication block. -/
def targetBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodLeftBit VariableModularMul.encoding
    BinaryLabelEncoding.bool (VariableModularMul.accumulatorBit bit)

/-- Complete encoded word for the preserved left factor. -/
def leftWord : EncodedBit.Word rawEncoding params.width where
  bit := leftBit

/-- Complete encoded word for the preserved right factor. -/
def rightWord : EncodedBit.Word rawEncoding params.width where
  bit := rightBit

/-- Complete encoded word for the product accumulator. -/
def targetWord : EncodedBit.Word rawEncoding params.width where
  bit := targetBit

@[simp] theorem leftBit_get (bit : Fin params.width) (state : RawRegisters) :
    (leftBit bit).get state = state.1.multiplier.val.testBit bit.val := by
  change (VariableModularMul.multiplierBit bit).get state.1 = _
  change (VariableModularMul.rawMultiplierBit bit).get
    (VariableModularMul.registersEquiv state.1) = _
  exact VariableModularMul.rawMultiplierBit_get bit
    (VariableModularMul.registersEquiv state.1)

@[simp] theorem rightBit_get (bit : Fin params.width) (state : RawRegisters) :
    (rightBit bit).get state =
      state.1.inPlace.multiplicand.val.testBit bit.val := by
  change (VariableModularMul.inPlaceMultiplicandBit bit).get state.1 = _
  exact VariableModularMul.inPlaceMultiplicandBit_get bit state.1

@[simp] theorem targetBit_get (bit : Fin params.width) (state : RawRegisters) :
    (targetBit bit).get state = state.1.accumulator.val.testBit bit.val := by
  change (VariableModularMul.accumulatorBit bit).get state.1 = _
  change (VariableModularMul.rawAccumulatorBit bit).get
    (VariableModularMul.registersEquiv state.1) = _
  exact VariableModularMul.rawAccumulatorBit_get bit
    (VariableModularMul.registersEquiv state.1)

theorem leftBit_pairwise_ne (a b : Fin params.width) (hne : a ≠ b) :
    (leftBit a).wire ≠ (leftBit b).wire :=
  EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
    (VariableModularMul.multiplierBit_pairwise_ne a b hne)

theorem rightBit_pairwise_ne (a b : Fin params.width) (hne : a ≠ b) :
    (rightBit a).wire ≠ (rightBit b).wire :=
  EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
    (VariableModularMul.inPlaceMultiplicandBit_pairwise_ne a b hne)

theorem targetBit_pairwise_ne (a b : Fin params.width) (hne : a ≠ b) :
    (targetBit a).wire ≠ (targetBit b).wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
  intro hwire
  apply VariableModularMul.rawAccumulator_pairwise_ne a b hne
  apply Fin.ext
  simpa only [VariableModularMul.accumulatorBit, EncodedBit.relabel] using
    congrArg Fin.val hwire

/-- Read the left factor from the raw carrier. -/
def readLeft (state : RawRegisters) : Nat.FixedWidth.Word params.width :=
  ⟨state.1.multiplier.val, ZMod.val_lt state.1.multiplier⟩

/-- Replace the left factor in the raw carrier. -/
def setLeft (state : RawRegisters) (value : Nat.FixedWidth.Word params.width) :
    RawRegisters :=
  ({ state.1 with multiplier := (value.val : VariableModularMul.Word) }, state.2)

/-- Read the right factor from the raw carrier. -/
def readRight (state : RawRegisters) : Nat.FixedWidth.Word params.width :=
  ⟨state.1.inPlace.multiplicand.val,
    ZMod.val_lt state.1.inPlace.multiplicand⟩

/-- Replace the right factor in the raw carrier. -/
def setRight (state : RawRegisters) (value : Nat.FixedWidth.Word params.width) :
    RawRegisters :=
  ({ state.1 with inPlace :=
      { state.1.inPlace with multiplicand := (value.val : VariableModularMul.Word) } },
    state.2)

/-- Read the modular-product accumulator from the raw carrier. -/
def readTarget (state : RawRegisters) : Nat.FixedWidth.Word params.width :=
  ⟨state.1.accumulator.val, ZMod.val_lt state.1.accumulator⟩

/-- Replace the modular-product accumulator in the raw carrier. -/
def setTarget (state : RawRegisters) (value : Nat.FixedWidth.Word params.width) :
    RawRegisters :=
  ({ state.1 with accumulator := (value.val : VariableModularMul.Word) }, state.2)

/-- Structural port for the left multiplication factor. -/
def leftPort : BlockBank.WordPort rawEncoding params.width where
  word := leftWord
  read := readLeft
  set := setLeft
  set_read := by
    intro state
    rcases state with ⟨registers, flag⟩
    rcases registers with ⟨multiplier, accumulator, inPlace, work⟩
    simp [setLeft, readLeft]
  read_set := by
    intro state value
    cases state
    apply Fin.ext
    simp [setLeft, readLeft, Nat.mod_eq_of_lt value.isLt]
  set_set := by intro state first second; cases state; rfl
  get_bit := leftBit_get
  pairwise_ne := leftBit_pairwise_ne
  clear_flip := by intro bit state; cases state; rfl

/-- Structural port for the right multiplication factor. -/
def rightPort : BlockBank.WordPort rawEncoding params.width where
  word := rightWord
  read := readRight
  set := setRight
  set_read := by
    intro state
    rcases state with ⟨registers, flag⟩
    rcases registers with ⟨multiplier, accumulator, inPlace, work⟩
    rcases inPlace with ⟨multiplicand, arithmetic⟩
    simp [setRight, readRight]
  read_set := by
    intro state value
    cases state
    apply Fin.ext
    simp [setRight, readRight, Nat.mod_eq_of_lt value.isLt]
  set_set := by
    intro state first second
    cases state
    rfl
  get_bit := by
    intro bit state
    change (rightBit bit).get state =
      state.1.inPlace.multiplicand.val.testBit bit.val
    exact rightBit_get bit state
  pairwise_ne := rightBit_pairwise_ne
  clear_flip := by
    intro bit state
    rcases state with ⟨registers, flag⟩
    rcases registers with ⟨multiplier, accumulator, inPlace, work⟩
    rcases inPlace with ⟨multiplicand, arithmetic⟩
    rfl

/-- Structural port for the product accumulator. -/
def targetPort : BlockBank.WordPort rawEncoding params.width where
  word := targetWord
  read := readTarget
  set := setTarget
  set_read := by
    intro state
    rcases state with ⟨registers, flag⟩
    rcases registers with ⟨multiplier, accumulator, inPlace, work⟩
    simp [setTarget, readTarget]
  read_set := by
    intro state value
    cases state
    apply Fin.ext
    simp [setTarget, readTarget, Nat.mod_eq_of_lt value.isLt]
  set_set := by intro state first second; cases state; rfl
  get_bit := targetBit_get
  pairwise_ne := targetBit_pairwise_ne
  clear_flip := by intro bit state; cases state; rfl

/-- Translate public multiply-accumulate data to the variable-product kernel. -/
def multiplicationData (x : Data) : VariableModularMul.Data where
  multiplier := x.left
  multiplicand := x.right
  accumulator := x.target

/-- Canonical clean physical representation of public multiplication data. -/
def cleanRegisters (x : Data) : RawRegisters :=
  (VariableModularMul.cleanRegisters (multiplicationData x), x.flag)

private theorem cleanRegisters_injective : Function.Injective cleanRegisters := by
  intro left right h
  rcases left with ⟨leftA, leftB, leftTarget, leftFlag⟩
  rcases right with ⟨rightA, rightB, rightTarget, rightFlag⟩
  have haVal := congrArg (fun state => state.1.multiplier.val) h
  have ha : leftA = rightA := by
    apply ZMod.val_injective
    change ((leftA.val : VariableModularMul.Word)).val =
      ((rightA.val : VariableModularMul.Word)).val at haVal
    simpa only [ZMod.val_cast_of_lt
      ((ZMod.val_lt leftA).trans VariableModularMul.modulus_lt_capacity),
      ZMod.val_cast_of_lt
      ((ZMod.val_lt rightA).trans VariableModularMul.modulus_lt_capacity)]
      using haVal
  have hbVal := congrArg (fun state => state.1.inPlace.multiplicand.val) h
  have hb : leftB = rightB := by
    apply ZMod.val_injective
    change ((leftB.val : VariableModularMul.Word)).val =
      ((rightB.val : VariableModularMul.Word)).val at hbVal
    simpa only [ZMod.val_cast_of_lt
      ((ZMod.val_lt leftB).trans VariableModularMul.modulus_lt_capacity),
      ZMod.val_cast_of_lt
      ((ZMod.val_lt rightB).trans VariableModularMul.modulus_lt_capacity)]
      using hbVal
  have htargetVal := congrArg (fun state => state.1.accumulator.val) h
  have htarget : leftTarget = rightTarget := by
    apply ZMod.val_injective
    change ((leftTarget.val : VariableModularMul.Word)).val =
      ((rightTarget.val : VariableModularMul.Word)).val at htargetVal
    simpa only [ZMod.val_cast_of_lt
      ((ZMod.val_lt leftTarget).trans VariableModularMul.modulus_lt_capacity),
      ZMod.val_cast_of_lt
      ((ZMod.val_lt rightTarget).trans VariableModularMul.modulus_lt_capacity)]
      using htargetVal
  have hflag : leftFlag = rightFlag := congrArg (fun state => state.2) h
  cases ha
  cases hb
  cases htarget
  cases hflag
  rfl

/-- Faithful public multiplication encoding into the clean raw carrier. -/
def encoding : BinaryLabelEncoding Data where
  width := rawEncoding.width
  encode := fun x => rawEncoding.encode (cleanRegisters x)
  encode_injective := by
    intro left right h
    exact cleanRegisters_injective (rawEncoding.encode_injective h)

/-- Exact physical width of a width-`f` modular-multiplication adapter. -/
def physicalWidthFor (f : Nat) : Nat :=
  7 * f + 6

/-- Exact physical width of the modular-multiplication adapter. -/
theorem encoding_width_exact : encoding.width = physicalWidthFor params.width := by
  change VariableModularMul.encoding.width + 1 = _
  calc
    VariableModularMul.encoding.width + 1 =
        VariableModularMul.physicalWidthFor params.width + 1 := by
      rw [VariableModularMul.encoding_width_exact]
    _ = physicalWidthFor params.width := by
      simp only [VariableModularMul.physicalWidthFor, physicalWidthFor]

/-- Actual variable-product schedule lifted over the preserved flag. -/
def gates : List (EncodedBit.GateSpec rawEncoding) :=
  (VariableModularMulSchedule.gates.map
      (EncodedBit.GateSpec.relabel VariableModularMul.registersEquiv)).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)

/-- Actual variable-product schedule lifted over the preserved flag. -/
def circuit : UnitaryCircuit (Qubits rawEncoding.width) :=
  EncodedBit.GateSpec.programList gates

/-- Total basis-state action of the lifted variable-product schedule. -/
def rawStep : RawRegisters → RawRegisters :=
  fun state => (VariableModularMulSchedule.step state.1, state.2)

/-- The literal lifted source list has the displayed flag-preserving action. -/
theorem gates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList gates state = rawStep state := by
  rcases state with ⟨data, flag⟩
  have h :
      EncodedBit.GateSpec.stepList
          ((VariableModularMulSchedule.gates.map
              (EncodedBit.GateSpec.relabel
                VariableModularMul.registersEquiv)).map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool))
          (data, flag) =
        (VariableModularMulSchedule.step data, flag) := by
    rw [EncodedBit.GateSpec.stepList_prodLeft]
    rw [EncodedBit.GateSpec.stepList_relabel,
      VariableModularMulSchedule.gates_stepList,
      VariableModularMulSchedule.rawStep_registersEquiv]
    simp only [Equiv.symm_apply_apply]
  simpa only [RawRegisters, rawEncoding, gates, rawStep] using h

/-- Lifting and semantic relabeling preserve the strict event trace. -/
theorem gates_events_eq :
    gates.map EncodedBit.GateSpec.event =
      VariableModularMulSchedule.gates.map EncodedBit.GateSpec.event := by
  rw [show gates =
      (VariableModularMulSchedule.gates.map
        (EncodedBit.GateSpec.relabel
          VariableModularMul.registersEquiv)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool) by rfl]
  calc
    _ = (VariableModularMulSchedule.gates.map
          (EncodedBit.GateSpec.relabel
            VariableModularMul.registersEquiv)).map
          EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _
    _ = VariableModularMulSchedule.gates.map
          EncodedBit.GateSpec.event := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro gate _
      cases gate <;> rfl

/-- Lifting and semantic relabeling preserve the source-list length. -/
@[simp] theorem gates_length :
    gates.length = VariableModularMulSchedule.gates.length := by
  rw [show gates =
      (VariableModularMulSchedule.gates.map
        (EncodedBit.GateSpec.relabel
          VariableModularMul.registersEquiv)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool) by rfl,
    List.length_map, List.length_map]

/-- Closed primitive-length bound for a width-`f` modular-multiplication adapter. -/
def gateLengthBoundFor (f : Nat) : Nat :=
  VariableModularMulSchedule.eventCountBoundFor f

/-- Closed literal-X bound for a width-`f` modular-multiplication adapter. -/
def xBoundFor (f : Nat) : Nat :=
  VariableModularMulSchedule.xBoundFor f

/-- Closed CNOT bound for a width-`f` modular-multiplication adapter. -/
def cnotBoundFor (f : Nat) : Nat :=
  VariableModularMulSchedule.cnotBoundFor f

/-- Closed Toffoli bound for a width-`f` modular-multiplication adapter. -/
def toffoliBoundFor (f : Nat) : Nat :=
  VariableModularMulSchedule.toffoliBoundFor f

/-- Closed unit-depth bound for a width-`f` modular-multiplication adapter. -/
def unitDepthBoundFor (f : Nat) : Nat :=
  VariableModularMulSchedule.unitDepthBoundFor f

/-- Closed primitive-length bound for the instantiated modular-multiplication adapter. -/
def gateLengthBound : Nat :=
  gateLengthBoundFor params.width

/-- Closed literal-X bound for the instantiated modular-multiplication adapter. -/
def xBound : Nat :=
  xBoundFor params.width

/-- Closed CNOT bound for the instantiated modular-multiplication adapter. -/
def cnotBound : Nat :=
  cnotBoundFor params.width

/-- Closed Toffoli bound for the instantiated modular-multiplication adapter. -/
def toffoliBound : Nat :=
  toffoliBoundFor params.width

/-- Closed unit-depth bound for the instantiated modular-multiplication adapter. -/
def unitDepthBound : Nat :=
  unitDepthBoundFor params.width

/-- The lifted multiplication list preserves the source X coordinate exactly. -/
theorem gates_xMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum =
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.xMultiplicity).sum :=
  EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq gates_events_eq

/-- The lifted multiplication list preserves the source CNOT coordinate exactly. -/
theorem gates_cnotMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum :=
  EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq gates_events_eq

/-- The lifted multiplication list preserves the source Toffoli coordinate exactly. -/
theorem gates_toffoliMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum :=
  EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq gates_events_eq

/-- The literal modular-multiplication list obeys its closed primitive-length bound. -/
theorem gates_length_le : gates.length ≤ gateLengthBound := by
  rw [gates_length]
  exact VariableModularMulSchedule.gates_length_le

/-- The literal modular-multiplication list obeys its closed X-coordinate bound. -/
theorem gates_xMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ xBound := by
  rw [gates_xMultiplicity_sum]
  exact VariableModularMulSchedule.gates_xMultiplicity_sum_le

/-- The literal modular-multiplication list obeys its closed CNOT-coordinate bound. -/
theorem gates_cnotMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤ cnotBound := by
  rw [gates_cnotMultiplicity_sum]
  exact VariableModularMulSchedule.gates_cnotMultiplicity_sum_le

/-- The literal modular-multiplication list obeys its closed Toffoli-coordinate bound. -/
theorem gates_toffoliMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      toffoliBound := by
  rw [gates_toffoliMultiplicity_sum]
  exact VariableModularMulSchedule.gates_toffoliMultiplicity_sum_le

/-- The actual circuit realizes its total raw action. -/
theorem rawRealizes : UnitaryCircuit.Realizes rawEncoding circuit rawStep := by
  unfold circuit
  exact EncodedBit.GateSpec.realizesList_congrStep gates gates_stepList

noncomputable instance rawFinite : Finite RawRegisters :=
  Finite.of_injective rawEncoding.encode rawEncoding.encode_injective

instance rawNonempty : Nonempty RawRegisters :=
  ⟨cleanRegisters ({ left := 0, right := 0, target := 0, flag := false } : Data)⟩

/-- Total inverse of the realized finite raw multiplication permutation. -/
noncomputable def rawInverseStep : RawRegisters → RawRegisters :=
  Function.invFun rawStep

set_option maxHeartbeats 800000 in
-- Finite injectivity of the realized permutation supplies its total inverse.
theorem rawInverseStep_rightInverse :
    Function.RightInverse rawInverseStep rawStep :=
  Function.rightInverse_invFun
    (Finite.surjective_of_injective rawRealizes.injective)

theorem rawInverseStep_leftInverse :
    Function.LeftInverse rawInverseStep rawStep := by
  intro state
  apply rawRealizes.injective
  exact rawInverseStep_rightInverse (rawStep state)

theorem rawDaggerRealizes :
    UnitaryCircuit.Realizes rawEncoding circuit.dagger rawInverseStep :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse rawRealizes rawInverseStep_rightInverse

theorem rawStep_cleanEndpoint (x : Data) :
    rawStep (cleanRegisters x) = cleanRegisters x.addProduct := by
  have h := VariableModularMulSchedule.step_cleanEndpoint
    (multiplicationData x)
  rw [show rawStep (cleanRegisters x) =
      (VariableModularMulSchedule.step
        (VariableModularMul.cleanRegisters (multiplicationData x)), x.flag) by
    rfl]
  rw [h]
  rfl

theorem rawInverseStep_cleanEndpoint (x : Data) :
    rawInverseStep (cleanRegisters x) = cleanRegisters x.subProduct := by
  have hforward := rawStep_cleanEndpoint (x.subProduct)
  rw [Data.addProduct_subProduct] at hforward
  rw [← hforward]
  exact rawInverseStep_leftInverse _

theorem realizes : UnitaryCircuit.Realizes encoding circuit Data.addProduct where
  apply_encoded_ket := by
    intro x
    have h := rawRealizes.apply_encoded_ket (cleanRegisters x)
    rw [rawStep_cleanEndpoint] at h
    exact h

theorem circuit_applyNormalized_clean_ket (x : Data) :
    circuit.applyNormalized (NormalizedVector.ket (encoding.encode x)) =
      NormalizedVector.ket (encoding.encode x.addProduct) :=
  realizes.apply_encoded_ket x

theorem dagger_applyNormalized_clean_ket (x : Data) :
    circuit.dagger.applyNormalized
        (NormalizedVector.ket (encoding.encode x)) =
      NormalizedVector.ket (encoding.encode x.subProduct) := by
  have hforward := circuit_applyNormalized_clean_ket (x.subProduct)
  rw [Data.addProduct_subProduct] at hforward
  rw [← hforward]
  exact UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized circuit _

theorem circuit_toffoli_count_le :
    ResourcePool.count (.gate (.builtin "toffoli")) circuit.eventCost ≤
      toffoliBound := by
  change ResourcePool.count (.gate (.builtin "toffoli"))
      (EncodedBit.GateSpec.programList gates).eventCost ≤ _
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact gates_toffoliMultiplicity_sum_le

theorem circuit_unitDepth_le :
    circuit.evaluatedEventDepth (fun _ => 1) ≤ unitDepthBound := by
  change (EncodedBit.GateSpec.programList gates).evaluatedEventDepth
      (fun _ => 1) ≤ _
  rw [EncodedBit.GateSpec.programList_evaluatedEventDepth_unit]
  exact gates_length_le

end

end ModularMultiplication
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic

end
