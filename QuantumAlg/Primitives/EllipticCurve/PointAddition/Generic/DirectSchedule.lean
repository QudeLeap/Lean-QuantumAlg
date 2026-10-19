/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Parameterized
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.PortFrame

/-!
# Direct-workspace gate schedule for generic affine point addition

This module owns the literal one-carrier schedule.  It contains no seven-bank
layout and no temporal-address compatibility layer.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace DirectSchedule

open Nat.FixedWidth
open ParameterizedPointAddition.Workspace

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

local instance modulusNeZero : NeZero params.modulus.val :=
  ⟨Nat.ne_of_gt params.modulusPos⟩

abbrev AuxRegisters := ParameterizedPointAddition.RawRegisters

abbrev auxEncoding : BinaryLabelEncoding AuxRegisters :=
  ParameterizedPointAddition.rawEncoding

abbrev RawRegisters :=
  PointAddition.PortFrame.RawRegisters AuxRegisters params.width

abbrev rawEncoding : BinaryLabelEncoding RawRegisters :=
  PointAddition.PortFrame.rawEncoding auxEncoding params.width

def liftAuxPort {wordWidth : Nat}
    (port : Arithmetic.BlockBank.WordPort auxEncoding wordWidth) :
    Arithmetic.BlockBank.WordPort rawEncoding wordWidth :=
  PointAddition.PortFrame.liftAuxPort auxEncoding params.width wordWidth port

def liftAuxGates (gates : List (EncodedBit.GateSpec auxEncoding)) :
    List (EncodedBit.GateSpec rawEncoding) :=
  PointAddition.PortFrame.liftAuxGates auxEncoding params.width gates

lemma public_aux_cross_ne
    (publicPort : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (auxPort : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (publicBit auxBit : Fin params.width) :
    ((PointAddition.PortFrame.liftPublicPort auxEncoding params.width
      publicPort).word.bit publicBit).wire ≠
      ((liftAuxPort auxPort).word.bit auxBit).wire := by
  exact PointAddition.PortFrame.liftPublicPort_liftAuxPort_wire_ne
    auxEncoding params.width params.width publicPort auxPort publicBit auxBit

def publicToAuxGates
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  Arithmetic.BlockBank.WordPort.directCopyGates
    (PointAddition.PortFrame.liftPublicPort auxEncoding params.width source)
    (liftAuxPort target)
    (fun bit => public_aux_cross_ne source target bit bit)

/-- Folded action of a direct public-to-workspace CNOT route. -/
def publicToAuxStep
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width) :
    RawRegisters → RawRegisters :=
  Arithmetic.BlockBank.WordPort.directCopyStep
    (PointAddition.PortFrame.liftPublicPort auxEncoding params.width source)
    (liftAuxPort target)
    (fun bit => public_aux_cross_ne source target bit bit)

lemma publicToAuxGates_stepList
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (publicToAuxGates source target) state =
      publicToAuxStep source target state :=
  rfl

/-- A public word is installed exactly when its auxiliary target is clean. -/
lemma publicToAuxStep_eq_set_of_clean
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (state : RawRegisters) (value : Word params.width)
    (hsource :
      (PointAddition.PortFrame.liftPublicPort auxEncoding params.width source).read
        state = value)
    (htarget : (liftAuxPort target).read state = 0) :
    publicToAuxStep source target state =
      (liftAuxPort target).set state value := by
  exact Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_of_clean _ _ _
    (fun sourceBit targetBit =>
      (public_aux_cross_ne source target sourceBit targetBit).symm)
    state value hsource htarget

/-- Repeating a public-to-workspace copy clears an equal auxiliary word. -/
lemma publicToAuxStep_eq_set_zero_of_equal
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (state : RawRegisters)
    (hequal :
      (PointAddition.PortFrame.liftPublicPort auxEncoding params.width source).read
        state = (liftAuxPort target).read state) :
    publicToAuxStep source target state =
      (liftAuxPort target).set state 0 := by
  exact Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_zero_of_equal _ _ _
    (fun sourceBit targetBit =>
      (public_aux_cross_ne source target sourceBit targetBit).symm)
    state hequal

/-- Lift a direct CNOT route between two auxiliary ports through the public
frame. -/
def auxCopyGates {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire) :
    List (EncodedBit.GateSpec rawEncoding) :=
  liftAuxGates (Arithmetic.BlockBank.WordPort.directCopyGates source target
    (fun bit => hcross bit bit))

/-- Folded action of one lifted auxiliary CNOT route. -/
def auxCopyStep {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire) :
    RawRegisters → RawRegisters := fun state =>
  (state.1, ((state.2.1.1,
    Arithmetic.BlockBank.WordPort.directCopyStep source target
      (fun bit => hcross bit bit) state.2.1.2), state.2.2))

lemma auxCopyGates_stepList {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire)
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (auxCopyGates source target hcross) state =
      auxCopyStep source target hcross state := by
  unfold auxCopyGates liftAuxGates
  rw [PointAddition.PortFrame.liftAuxGates_stepList]
  rfl

@[simp] lemma auxCopyGates_length {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire) :
    (auxCopyGates source target hcross).length = wordWidth := by
  unfold auxCopyGates liftAuxGates
  rw [PointAddition.PortFrame.liftAuxGates_length auxEncoding params.width]
  exact Arithmetic.BlockBank.WordPort.directCopyGates_length _ _ _

/-- A lifted auxiliary copy installs its source in a clean target port. -/
lemma auxCopyStep_eq_set_of_clean {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire)
    (state : RawRegisters) (value : Word wordWidth)
    (hsource : (liftAuxPort source).read state = value)
    (htarget : (liftAuxPort target).read state = 0) :
    auxCopyStep source target hcross state =
      (liftAuxPort target).set state value := by
  have h := Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_of_clean
    source target (fun bit => hcross bit bit)
    (fun sourceBit targetBit => (hcross sourceBit targetBit).symm)
    state.2.1.2 value hsource htarget
  change (state.1, ((state.2.1.1,
      Arithmetic.BlockBank.WordPort.directCopyStep source target
        (fun bit => hcross bit bit) state.2.1.2), state.2.2)) =
    (state.1, ((state.2.1.1, target.set state.2.1.2 value), state.2.2))
  rw [h]

/-- A lifted auxiliary copy clears an equal target word. -/
lemma auxCopyStep_eq_set_zero_of_equal {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire)
    (state : RawRegisters)
    (hequal : (liftAuxPort source).read state =
      (liftAuxPort target).read state) :
    auxCopyStep source target hcross state =
      (liftAuxPort target).set state 0 := by
  have h := Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_zero_of_equal
    source target (fun bit => hcross bit bit)
    (fun sourceBit targetBit => (hcross sourceBit targetBit).symm)
    state.2.1.2 hequal
  change (state.1, ((state.2.1.1,
      Arithmetic.BlockBank.WordPort.directCopyStep source target
        (fun bit => hcross bit bit) state.2.1.2), state.2.2)) =
    (state.1, ((state.2.1.1, target.set state.2.1.2 0), state.2.2))
  rw [h]

lemma thin_product_cross_ne
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thinBit productBit : Fin params.width) :
    ((ParameterizedPointAddition.Workspace.thinPort thin).word.bit thinBit).wire ≠
      ((ParameterizedPointAddition.Workspace.productPort product).word.bit
        productBit).wire :=
  (ParameterizedPointAddition.Workspace.productPort_thinPort_cross_ne
    product thin productBit thinBit).symm

lemma product_thin_cross_ne
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (productBit thinBit : Fin params.width) :
    ((ParameterizedPointAddition.Workspace.productPort product).word.bit
      productBit).wire ≠
      ((ParameterizedPointAddition.Workspace.thinPort thin).word.bit thinBit).wire :=
  ParameterizedPointAddition.Workspace.productPort_thinPort_cross_ne
    product thin productBit thinBit

lemma accumulator_multiplier_cross_ne
    (accumulatorBit multiplierBit : Fin params.width) :
    (ParameterizedPointAddition.Workspace.divisionQuotientPort.word.bit
      accumulatorBit).wire ≠
      (ParameterizedPointAddition.Workspace.divisionNumeratorPort.word.bit
        multiplierBit).wire :=
  (ParameterizedPointAddition.Workspace.productMultiplier_productAccumulator_cross_ne
    multiplierBit accumulatorBit).symm

lemma multiplier_accumulator_cross_ne
    (multiplierBit accumulatorBit : Fin params.width) :
    (ParameterizedPointAddition.Workspace.divisionNumeratorPort.word.bit
      multiplierBit).wire ≠
      (ParameterizedPointAddition.Workspace.divisionQuotientPort.word.bit
        accumulatorBit).wire :=
  ParameterizedPointAddition.Workspace.productMultiplier_productAccumulator_cross_ne
    multiplierBit accumulatorBit

def thinToProductGates
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  auxCopyGates
    (ParameterizedPointAddition.Workspace.thinPort thin)
    (ParameterizedPointAddition.Workspace.productPort product)
    (thin_product_cross_ne thin product)

def productToThinGates
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  auxCopyGates
    (ParameterizedPointAddition.Workspace.productPort product)
    (ParameterizedPointAddition.Workspace.thinPort thin)
    (product_thin_cross_ne product thin)

lemma thinToProductGates_stepList
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (thinToProductGates thin product) state =
      auxCopyStep (ParameterizedPointAddition.Workspace.thinPort thin)
        (ParameterizedPointAddition.Workspace.productPort product)
        (thin_product_cross_ne thin product) state := by
  exact auxCopyGates_stepList _ _ (thin_product_cross_ne thin product) state

lemma productToThinGates_stepList
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (productToThinGates product thin) state =
      auxCopyStep (ParameterizedPointAddition.Workspace.productPort product)
        (ParameterizedPointAddition.Workspace.thinPort thin)
        (product_thin_cross_ne product thin) state := by
  exact auxCopyGates_stepList _ _ (product_thin_cross_ne product thin) state

def moveProductToThinGates
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  productToThinGates product thin ++ thinToProductGates thin product

def accumulatorToMultiplierGates : List (EncodedBit.GateSpec rawEncoding) :=
  auxCopyGates
    ParameterizedPointAddition.Workspace.divisionQuotientPort
    ParameterizedPointAddition.Workspace.divisionNumeratorPort
    accumulator_multiplier_cross_ne

def multiplierToAccumulatorGates : List (EncodedBit.GateSpec rawEncoding) :=
  auxCopyGates
    ParameterizedPointAddition.Workspace.divisionNumeratorPort
    ParameterizedPointAddition.Workspace.divisionQuotientPort
    multiplier_accumulator_cross_ne

lemma accumulatorToMultiplierGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList accumulatorToMultiplierGates state =
      auxCopyStep ParameterizedPointAddition.Workspace.divisionQuotientPort
        ParameterizedPointAddition.Workspace.divisionNumeratorPort
        accumulator_multiplier_cross_ne state := by
  exact auxCopyGates_stepList _ _ accumulator_multiplier_cross_ne state

lemma multiplierToAccumulatorGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList multiplierToAccumulatorGates state =
      auxCopyStep ParameterizedPointAddition.Workspace.divisionNumeratorPort
        ParameterizedPointAddition.Workspace.divisionQuotientPort
        multiplier_accumulator_cross_ne state := by
  exact auxCopyGates_stepList _ _ multiplier_accumulator_cross_ne state

def moveAccumulatorToMultiplierGates :
    List (EncodedBit.GateSpec rawEncoding) :=
  accumulatorToMultiplierGates ++ multiplierToAccumulatorGates

def selectedSubtractAuxGates : List (EncodedBit.GateSpec auxEncoding) :=
  ParameterizedPointAddition.Workspace.selectedAdditionToggleGates ++
    (ParameterizedPointAddition.Workspace.sharedProductGates
      (ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit)).reverse ++
    ParameterizedPointAddition.Workspace.selectedAdditionToggleGates

def selectedSubtractGates : List (EncodedBit.GateSpec rawEncoding) :=
  liftAuxGates selectedSubtractAuxGates

/-- The auxiliary selected-subtract schedule subtracts the multiplicand from
the accumulator and returns its one-bit selector to zero. -/
lemma selectedSubtractAuxGates_clean
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (hmodulus : 1 < params.modulus.val)
    (hmultiplier : x.multiplier = 0) :
    EncodedBit.GateSpec.stepList selectedSubtractAuxGates
        (ParameterizedPointAddition.Workspace.productRegistersWithFrame
          inversion x tail) =
      ParameterizedPointAddition.Workspace.productRegistersWithFrame inversion
        { x with accumulator := x.accumulator - x.multiplicand } tail := by
  let _ : Fact (1 < params.modulus.val) := ⟨hmodulus⟩
  let result : Arithmetic.VariableModularMul.Data :=
    { multiplier := 0
      multiplicand := x.multiplicand
      accumulator := x.accumulator - x.multiplicand }
  have hselected :
      ParameterizedPointAddition.Workspace.subtractSelected
          ParameterizedPointAddition.Workspace.selectedAdditionBit
          (ParameterizedPointAddition.Workspace.enableSelectedAddition x) =
        ParameterizedPointAddition.Workspace.enableSelectedAddition result := by
    rcases x with ⟨multiplier, multiplicand, accumulator⟩
    simp [ParameterizedPointAddition.Workspace.subtractSelected,
      ParameterizedPointAddition.Workspace.enableSelectedAddition,
      ParameterizedPointAddition.Workspace.selectedAdditionBit,
      result, ZMod.val_one]
  simp only [selectedSubtractAuxGates,
    EncodedBit.GateSpec.stepList_append]
  rw [ParameterizedPointAddition.Workspace.selectedAdditionToggleGates_enable_clean
      inversion x tail hmodulus hmultiplier,
    ParameterizedPointAddition.Workspace.sharedSelectedAdditionGates_reverse_clean,
    hselected,
    ParameterizedPointAddition.Workspace.selectedAdditionToggleGates_disable_clean
      inversion result tail hmodulus rfl]
  simp [result, hmultiplier]

/-- Lifting selected subtraction through the public frame preserves all public
and framing fields. -/
lemma selectedSubtractGates_clean
    (state : RawRegisters)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (haux : state.2.1.2 =
      ParameterizedPointAddition.Workspace.productRegistersWithFrame
        inversion x tail)
    (hmodulus : 1 < params.modulus.val)
    (hmultiplier : x.multiplier = 0) :
    EncodedBit.GateSpec.stepList selectedSubtractGates state =
      (state.1, ((state.2.1.1,
        ParameterizedPointAddition.Workspace.productRegistersWithFrame inversion
          { x with accumulator := x.accumulator - x.multiplicand } tail),
        state.2.2)) := by
  unfold selectedSubtractGates liftAuxGates
  rw [PointAddition.PortFrame.liftAuxGates_stepList,
    haux, selectedSubtractAuxGates_clean inversion x tail hmodulus hmultiplier]

def subtractPublicGates
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  publicToAuxGates source
      ParameterizedPointAddition.Workspace.divisionProductTargetPort ++
    selectedSubtractGates ++
    publicToAuxGates source
      ParameterizedPointAddition.Workspace.divisionProductTargetPort

def denominatorDifferenceGates : List (EncodedBit.GateSpec rawEncoding) :=
  publicToAuxGates (PointAddition.PortFrame.mutableXPublicPort params.width)
      ParameterizedPointAddition.Workspace.divisionQuotientPort ++
    subtractPublicGates
      (PointAddition.PortFrame.constantXPublicPort params.width)

def denominatorGates : List (EncodedBit.GateSpec rawEncoding) :=
  denominatorDifferenceGates ++
    liftAuxGates
      ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorPreservedGates ++
    liftAuxGates
      ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorWorkingGates ++
    liftAuxGates
      ParameterizedPointAddition.Workspace.denominatorPreservedToProductAccumulatorGates

def numeratorGates : List (EncodedBit.GateSpec rawEncoding) :=
  publicToAuxGates (PointAddition.PortFrame.mutableYPublicPort params.width)
      ParameterizedPointAddition.Workspace.divisionQuotientPort ++
    subtractPublicGates
      (PointAddition.PortFrame.constantYPublicPort params.width) ++
    moveAccumulatorToMultiplierGates

def divisionAndSaveGates : List (EncodedBit.GateSpec rawEncoding) :=
  liftAuxGates ParameterizedPointAddition.Workspace.divisionGates ++
    moveProductToThinGates
      ParameterizedPointAddition.Workspace.productMultiplierPort
      ParameterizedPointAddition.Workspace.numeratorScratchThinPort ++
    moveProductToThinGates
      ParameterizedPointAddition.Workspace.productAccumulatorPort
      ParameterizedPointAddition.Workspace.slopeThinPort

def multiplySlopeSquareGates : List (EncodedBit.GateSpec rawEncoding) :=
  thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplierPort ++
    thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplicandPort ++
    liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
      ParameterizedPointAddition.Workspace.multiplicationGates) ++
    thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplierPort ++
    thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplicandPort

def xCoordinateGates : List (EncodedBit.GateSpec rawEncoding) :=
  multiplySlopeSquareGates ++
    subtractPublicGates
      (PointAddition.PortFrame.mutableXPublicPort params.width) ++
    subtractPublicGates
      (PointAddition.PortFrame.constantXPublicPort params.width) ++
    moveProductToThinGates
      ParameterizedPointAddition.Workspace.productAccumulatorPort
      ParameterizedPointAddition.Workspace.xThinPort

def multiplySlopeMutableXGates : List (EncodedBit.GateSpec rawEncoding) :=
  thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplierPort ++
    publicToAuxGates (PointAddition.PortFrame.mutableXPublicPort params.width)
      ParameterizedPointAddition.Workspace.divisionProductTargetPort ++
    liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
      ParameterizedPointAddition.Workspace.multiplicationGates) ++
    thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplierPort ++
    publicToAuxGates (PointAddition.PortFrame.mutableXPublicPort params.width)
      ParameterizedPointAddition.Workspace.divisionProductTargetPort

def subtractSlopeXGates : List (EncodedBit.GateSpec rawEncoding) :=
  thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplierPort ++
    thinToProductGates ParameterizedPointAddition.Workspace.xThinPort
      ParameterizedPointAddition.Workspace.productMultiplicandPort ++
    liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
      ParameterizedPointAddition.Workspace.multiplicationGates).reverse ++
    thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
      ParameterizedPointAddition.Workspace.productMultiplierPort ++
    thinToProductGates ParameterizedPointAddition.Workspace.xThinPort
      ParameterizedPointAddition.Workspace.productMultiplicandPort

def yCoordinateGates : List (EncodedBit.GateSpec rawEncoding) :=
  multiplySlopeMutableXGates ++ subtractSlopeXGates ++
    subtractPublicGates
      (PointAddition.PortFrame.mutableYPublicPort params.width) ++
    moveProductToThinGates
      ParameterizedPointAddition.Workspace.productAccumulatorPort
      ParameterizedPointAddition.Workspace.yThinPort

/-- One direct forward computation on the sole physical workspace. -/
def computeGates : List (EncodedBit.GateSpec rawEncoding) :=
  denominatorGates ++ numeratorGates ++ divisionAndSaveGates ++
    xCoordinateGates ++ yCoordinateGates

@[simp] lemma liftAuxGates_length
    (gates : List (EncodedBit.GateSpec auxEncoding)) :
    (liftAuxGates gates).length = gates.length :=
  PointAddition.PortFrame.liftAuxGates_length auxEncoding params.width gates

@[simp] lemma publicToAuxGates_length
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width) :
    (publicToAuxGates source target).length = params.width := by
  exact Arithmetic.BlockBank.WordPort.directCopyGates_length _ _ _

@[simp] lemma thinToProductGates_length
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width) :
    (thinToProductGates thin product).length = params.width := by
  rw [thinToProductGates, auxCopyGates, liftAuxGates_length]
  exact Arithmetic.BlockBank.WordPort.directCopyGates_length _ _ _

@[simp] lemma productToThinGates_length
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    (productToThinGates product thin).length = params.width := by
  rw [productToThinGates, auxCopyGates, liftAuxGates_length]
  exact Arithmetic.BlockBank.WordPort.directCopyGates_length _ _ _

@[simp] lemma moveProductToThinGates_length
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    (moveProductToThinGates product thin).length = 2 * params.width := by
  simp only [moveProductToThinGates, List.length_append,
    productToThinGates_length, thinToProductGates_length]
  omega

@[simp] lemma selectedSubtractGates_length :
    selectedSubtractGates.length =
      2 + (ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).length := by
  simp only [selectedSubtractGates, liftAuxGates_length,
    selectedSubtractAuxGates, List.length_append, List.length_reverse,
    ParameterizedPointAddition.Workspace.selectedAdditionToggleGates,
    List.length_cons, List.length_nil,
    ParameterizedPointAddition.Workspace.sharedProductGates_length]
  omega

@[simp] lemma subtractPublicGates_length
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    (subtractPublicGates source).length =
      2 * params.width + 2 +
        (ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).length := by
  simp [subtractPublicGates]
  omega

private lemma denominatorGates_length :
    denominatorGates.length =
      6 * params.width + 2 +
        (ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).length := by
  simp only [denominatorGates, denominatorDifferenceGates, List.length_append,
    publicToAuxGates_length, subtractPublicGates_length, liftAuxGates_length,
    ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorPreservedGates,
    ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorWorkingGates,
    ParameterizedPointAddition.Workspace.productAccumulatorToInversionGates_length,
    ParameterizedPointAddition.Workspace.denominatorPreservedToProductAccumulatorGates_length]
  rw [Arithmetic.ModularInversion.arithmeticWidth_eq]
  omega

private lemma numeratorGates_length :
    numeratorGates.length =
      5 * params.width + 2 +
        (ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).length := by
  simp only [numeratorGates, List.length_append, publicToAuxGates_length,
    subtractPublicGates_length, moveAccumulatorToMultiplierGates,
    accumulatorToMultiplierGates, multiplierToAccumulatorGates,
    auxCopyGates_length]
  omega

private lemma divisionAndSaveGates_length :
    divisionAndSaveGates.length =
      4 * params.width +
        ParameterizedPointAddition.Workspace.divisionGates.length := by
  simp only [divisionAndSaveGates, List.length_append, liftAuxGates_length,
    moveProductToThinGates_length]
  omega

private lemma xCoordinateGates_length :
    xCoordinateGates.length =
      10 * params.width + 4 +
        2 * (ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).length +
        ParameterizedPointAddition.Workspace.multiplicationGates.length := by
  simp only [xCoordinateGates, multiplySlopeSquareGates, List.length_append,
    thinToProductGates_length, liftAuxGates_length,
    ParameterizedPointAddition.Workspace.sharedProductGates_length,
    subtractPublicGates_length, moveProductToThinGates_length]
  omega

private lemma yCoordinateGates_length :
    yCoordinateGates.length =
      12 * params.width + 2 +
        (ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).length +
        2 * ParameterizedPointAddition.Workspace.multiplicationGates.length := by
  simp only [yCoordinateGates, multiplySlopeMutableXGates,
    subtractSlopeXGates, List.length_append, thinToProductGates_length,
    publicToAuxGates_length, liftAuxGates_length, List.length_reverse,
    ParameterizedPointAddition.Workspace.sharedProductGates_length,
    subtractPublicGates_length, moveProductToThinGates_length]
  omega

/-- Exact primitive-leaf count of one direct forward affine computation. -/
lemma computeGates_length :
    computeGates.length =
      37 * params.width + 10 +
        5 * (ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).length +
        3 * ParameterizedPointAddition.Workspace.multiplicationGates.length +
        ParameterizedPointAddition.Workspace.divisionGates.length := by
  simp only [computeGates, List.length_append, denominatorGates_length,
    numeratorGates_length, divisionAndSaveGates_length,
    xCoordinateGates_length, yCoordinateGates_length]
  omega

@[simp] lemma liftAuxGates_cnotMultiplicity_sum
    (gates : List (EncodedBit.GateSpec auxEncoding)) :
    ((liftAuxGates gates).map EncodedBit.GateSpec.cnotMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (PointAddition.PortFrame.liftAuxGates_map_event
      auxEncoding params.width gates)

@[simp] lemma liftAuxGates_toffoliMultiplicity_sum
    (gates : List (EncodedBit.GateSpec auxEncoding)) :
    ((liftAuxGates gates).map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  exact PointAddition.PortFrame.liftAuxGates_toffoliMultiplicity_sum
    auxEncoding params.width gates

@[simp] private lemma publicToAuxGates_cnotMultiplicity_sum
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width) :
    ((publicToAuxGates source target).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = params.width := by
  exact Arithmetic.BlockBank.WordPort.directCopyGates_cnotMultiplicity_sum _ _ _

@[simp] private lemma publicToAuxGates_toffoliMultiplicity_sum
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width) :
    ((publicToAuxGates source target).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  exact Arithmetic.BlockBank.WordPort.directCopyGates_toffoliMultiplicity_sum _ _ _

@[simp] private lemma auxCopyGates_cnotMultiplicity_sum {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire) :
    ((auxCopyGates source target hcross).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = wordWidth := by
  rw [auxCopyGates, liftAuxGates_cnotMultiplicity_sum]
  exact Arithmetic.BlockBank.WordPort.directCopyGates_cnotMultiplicity_sum _ _ _

@[simp] private lemma auxCopyGates_toffoliMultiplicity_sum {wordWidth : Nat}
    (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
    (hcross : ∀ sourceBit targetBit,
      (source.word.bit sourceBit).wire ≠ (target.word.bit targetBit).wire) :
    ((auxCopyGates source target hcross).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  rw [auxCopyGates, liftAuxGates_toffoliMultiplicity_sum]
  exact Arithmetic.BlockBank.WordPort.directCopyGates_toffoliMultiplicity_sum _ _ _

@[simp] private lemma thinToProductGates_cnotMultiplicity_sum
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width) :
    ((thinToProductGates thin product).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = params.width := by
  simp [thinToProductGates]

@[simp] private lemma thinToProductGates_toffoliMultiplicity_sum
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width) :
    ((thinToProductGates thin product).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [thinToProductGates]

@[simp] private lemma productToThinGates_cnotMultiplicity_sum
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    ((productToThinGates product thin).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = params.width := by
  simp [productToThinGates]

@[simp] private lemma productToThinGates_toffoliMultiplicity_sum
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    ((productToThinGates product thin).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [productToThinGates]

@[simp] private lemma moveProductToThinGates_cnotMultiplicity_sum
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    ((moveProductToThinGates product thin).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * params.width := by
  simp [moveProductToThinGates]
  omega

@[simp] private lemma moveProductToThinGates_toffoliMultiplicity_sum
    (product : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width) :
    ((moveProductToThinGates product thin).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [moveProductToThinGates]

private lemma moveAccumulatorToMultiplierGates_cnotMultiplicity_sum :
    (moveAccumulatorToMultiplierGates.map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * params.width := by
  simp [moveAccumulatorToMultiplierGates, accumulatorToMultiplierGates,
    multiplierToAccumulatorGates]
  omega

private lemma moveAccumulatorToMultiplierGates_toffoliMultiplicity_sum :
    (moveAccumulatorToMultiplierGates.map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [moveAccumulatorToMultiplierGates, accumulatorToMultiplierGates,
    multiplierToAccumulatorGates]

private lemma selectedSubtractGates_cnotMultiplicity_sum :
    (selectedSubtractGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  have hshared := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (ParameterizedPointAddition.Workspace.sharedProductGates_map_event
      (ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit))
  rw [selectedSubtractGates, liftAuxGates_cnotMultiplicity_sum]
  simp only [selectedSubtractAuxGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse,
    ParameterizedPointAddition.Workspace.selectedAdditionToggleGates,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.cnotMultiplicity_x, zero_add, add_zero]
  rw [hshared]

private lemma selectedSubtractGates_toffoliMultiplicity_sum :
    (selectedSubtractGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  have hshared := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (ParameterizedPointAddition.Workspace.sharedProductGates_map_event
      (ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit))
  rw [selectedSubtractGates, liftAuxGates_toffoliMultiplicity_sum]
  simp only [selectedSubtractAuxGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse,
    ParameterizedPointAddition.Workspace.selectedAdditionToggleGates,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.toffoliMultiplicity_x, zero_add, add_zero]
  rw [hshared]

private lemma subtractPublicGates_cnotMultiplicity_sum
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    ((subtractPublicGates source).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * params.width +
        ((ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [subtractPublicGates, List.map_append, List.sum_append,
    publicToAuxGates_cnotMultiplicity_sum,
    selectedSubtractGates_cnotMultiplicity_sum]
  omega

private lemma subtractPublicGates_toffoliMultiplicity_sum
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    ((subtractPublicGates source).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [subtractPublicGates, List.map_append, List.sum_append,
    publicToAuxGates_toffoliMultiplicity_sum,
    selectedSubtractGates_toffoliMultiplicity_sum, zero_add, add_zero]

private lemma liftedMultiplicationGates_cnotMultiplicity_sum :
    ((liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
      ParameterizedPointAddition.Workspace.multiplicationGates)).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      (ParameterizedPointAddition.Workspace.multiplicationGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum := by
  rw [liftAuxGates_cnotMultiplicity_sum]
  exact EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (ParameterizedPointAddition.Workspace.sharedProductGates_map_event
      ParameterizedPointAddition.Workspace.multiplicationGates)

private lemma liftedMultiplicationGates_toffoliMultiplicity_sum :
    ((liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
      ParameterizedPointAddition.Workspace.multiplicationGates)).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (ParameterizedPointAddition.Workspace.multiplicationGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  rw [liftAuxGates_toffoliMultiplicity_sum]
  exact EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (ParameterizedPointAddition.Workspace.sharedProductGates_map_event
      ParameterizedPointAddition.Workspace.multiplicationGates)

private lemma liftedReverseMultiplicationGates_cnotMultiplicity_sum :
    ((liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
      ParameterizedPointAddition.Workspace.multiplicationGates).reverse).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      (ParameterizedPointAddition.Workspace.multiplicationGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum := by
  rw [liftAuxGates_cnotMultiplicity_sum, List.map_reverse, List.sum_reverse]
  exact EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (ParameterizedPointAddition.Workspace.sharedProductGates_map_event
      ParameterizedPointAddition.Workspace.multiplicationGates)

private lemma liftedReverseMultiplicationGates_toffoliMultiplicity_sum :
    ((liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
      ParameterizedPointAddition.Workspace.multiplicationGates).reverse).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (ParameterizedPointAddition.Workspace.multiplicationGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  rw [liftAuxGates_toffoliMultiplicity_sum, List.map_reverse, List.sum_reverse]
  exact EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (ParameterizedPointAddition.Workspace.sharedProductGates_map_event
      ParameterizedPointAddition.Workspace.multiplicationGates)

private lemma denominatorGates_cnotMultiplicity_sum :
    (denominatorGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      6 * params.width +
        ((ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [denominatorGates, denominatorDifferenceGates,
    List.map_append, List.sum_append, publicToAuxGates_cnotMultiplicity_sum,
    subtractPublicGates_cnotMultiplicity_sum,
    liftAuxGates_cnotMultiplicity_sum,
    ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorPreservedGates,
    ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorWorkingGates,
    productAccumulatorToInversionGates_cnotMultiplicity_sum,
    denominatorPreservedToProductAccumulatorGates_cnotMultiplicity_sum]
  rw [Arithmetic.ModularInversion.arithmeticWidth_eq]
  omega

private lemma denominatorGates_toffoliMultiplicity_sum :
    (denominatorGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [denominatorGates, denominatorDifferenceGates,
    List.map_append, List.sum_append, publicToAuxGates_toffoliMultiplicity_sum,
    subtractPublicGates_toffoliMultiplicity_sum,
    liftAuxGates_toffoliMultiplicity_sum,
    ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorPreservedGates,
    ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorWorkingGates,
    productAccumulatorToInversionGates_toffoliMultiplicity_sum,
    denominatorPreservedToProductAccumulatorGates_toffoliMultiplicity_sum,
    zero_add, add_zero]

private lemma numeratorGates_cnotMultiplicity_sum :
    (numeratorGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      5 * params.width +
        ((ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [numeratorGates, List.map_append, List.sum_append,
    publicToAuxGates_cnotMultiplicity_sum,
    subtractPublicGates_cnotMultiplicity_sum,
    moveAccumulatorToMultiplierGates_cnotMultiplicity_sum]
  omega

private lemma numeratorGates_toffoliMultiplicity_sum :
    (numeratorGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [numeratorGates, List.map_append, List.sum_append,
    publicToAuxGates_toffoliMultiplicity_sum,
    subtractPublicGates_toffoliMultiplicity_sum,
    moveAccumulatorToMultiplierGates_toffoliMultiplicity_sum,
    zero_add, add_zero]

private lemma divisionAndSaveGates_cnotMultiplicity_sum :
    (divisionAndSaveGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      4 * params.width +
        (ParameterizedPointAddition.Workspace.divisionGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [divisionAndSaveGates, List.map_append, List.sum_append,
    liftAuxGates_cnotMultiplicity_sum,
    moveProductToThinGates_cnotMultiplicity_sum]
  omega

private lemma divisionAndSaveGates_toffoliMultiplicity_sum :
    (divisionAndSaveGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (ParameterizedPointAddition.Workspace.divisionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [divisionAndSaveGates, List.map_append, List.sum_append,
    liftAuxGates_toffoliMultiplicity_sum,
    moveProductToThinGates_toffoliMultiplicity_sum, add_zero]

private lemma xCoordinateGates_cnotMultiplicity_sum :
    (xCoordinateGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      10 * params.width +
        2 * ((ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum +
        (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [xCoordinateGates, multiplySlopeSquareGates,
    List.map_append, List.sum_append,
    thinToProductGates_cnotMultiplicity_sum,
    liftedMultiplicationGates_cnotMultiplicity_sum,
    subtractPublicGates_cnotMultiplicity_sum,
    moveProductToThinGates_cnotMultiplicity_sum]
  omega

private lemma xCoordinateGates_toffoliMultiplicity_sum :
    (xCoordinateGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum +
        (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [xCoordinateGates, multiplySlopeSquareGates,
    List.map_append, List.sum_append,
    thinToProductGates_toffoliMultiplicity_sum,
    liftedMultiplicationGates_toffoliMultiplicity_sum,
    subtractPublicGates_toffoliMultiplicity_sum,
    moveProductToThinGates_toffoliMultiplicity_sum, zero_add, add_zero]
  omega

private lemma yCoordinateGates_cnotMultiplicity_sum :
    (yCoordinateGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      12 * params.width +
        ((ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum +
        2 * (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [yCoordinateGates, multiplySlopeMutableXGates,
    subtractSlopeXGates, List.map_append, List.sum_append,
    thinToProductGates_cnotMultiplicity_sum,
    publicToAuxGates_cnotMultiplicity_sum,
    liftedMultiplicationGates_cnotMultiplicity_sum,
    liftedReverseMultiplicationGates_cnotMultiplicity_sum,
    subtractPublicGates_cnotMultiplicity_sum,
    moveProductToThinGates_cnotMultiplicity_sum]
  omega

private lemma yCoordinateGates_toffoliMultiplicity_sum :
    (yCoordinateGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum +
        2 * (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [yCoordinateGates, multiplySlopeMutableXGates,
    subtractSlopeXGates, List.map_append, List.sum_append,
    thinToProductGates_toffoliMultiplicity_sum,
    publicToAuxGates_toffoliMultiplicity_sum,
    liftedMultiplicationGates_toffoliMultiplicity_sum,
    liftedReverseMultiplicationGates_toffoliMultiplicity_sum,
    subtractPublicGates_toffoliMultiplicity_sum,
    moveProductToThinGates_toffoliMultiplicity_sum, zero_add, add_zero]
  omega

/-- Exact CNOT coordinate of one direct forward affine computation. -/
lemma computeGates_cnotMultiplicity_sum :
    (computeGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      37 * params.width +
        5 * ((ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum +
        3 * (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum +
        (ParameterizedPointAddition.Workspace.divisionGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [computeGates, List.map_append, List.sum_append,
    denominatorGates_cnotMultiplicity_sum,
    numeratorGates_cnotMultiplicity_sum,
    divisionAndSaveGates_cnotMultiplicity_sum,
    xCoordinateGates_cnotMultiplicity_sum,
    yCoordinateGates_cnotMultiplicity_sum]
  omega

/-- Exact Toffoli coordinate of one direct forward affine computation. -/
lemma computeGates_toffoliMultiplicity_sum :
    (computeGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      5 * ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum +
        3 * (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum +
        (ParameterizedPointAddition.Workspace.divisionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [computeGates, List.map_append, List.sum_append,
    denominatorGates_toffoliMultiplicity_sum,
    numeratorGates_toffoliMultiplicity_sum,
    divisionAndSaveGates_toffoliMultiplicity_sum,
    xCoordinateGates_toffoliMultiplicity_sum,
    yCoordinateGates_toffoliMultiplicity_sum]
  omega



private lemma xorIntoGates_bitDisjoint {width : Nat}
    (observed : EncodedBit rawEncoding)
    (source target : EncodedBit.Word rawEncoding width)
    (hcross : ∀ bit, (source.bit bit).wire ≠ (target.bit bit).wire)
    (hsource : ∀ bit, (source.bit bit).wire ≠ observed.wire)
    (htarget : ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (gate : EncodedBit.GateSpec rawEncoding)
    (hgate : gate ∈ EncodedBit.Word.xorIntoGates source target hcross) :
    EncodedBit.GateSpec.bitDisjoint observed gate := by
  rw [EncodedBit.Word.xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  exact ⟨hsource bit, htarget bit⟩

private lemma publicToAuxGates_bitDisjoint_controlBit
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width) :
    ∀ gate, gate ∈ publicToAuxGates source target →
      EncodedBit.GateSpec.bitDisjoint
        (PointAddition.PortFrame.controlBit auxEncoding params.width) gate := by
  intro gate hgate
  unfold publicToAuxGates Arithmetic.BlockBank.WordPort.directCopyGates at hgate
  exact xorIntoGates_bitDisjoint _ _ _ _
    (fun bit => PointAddition.PortFrame.liftPublicBit_wire_ne_controlBit
      auxEncoding params.width (source.word.bit bit))
    (fun bit => PointAddition.PortFrame.liftAuxBit_wire_ne_controlBit
      auxEncoding params.width (target.word.bit bit)) gate hgate

private lemma publicToAuxGates_bitDisjoint_controlWorkBit
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (target : Arithmetic.BlockBank.WordPort auxEncoding params.width) :
    ∀ gate, gate ∈ publicToAuxGates source target →
      EncodedBit.GateSpec.bitDisjoint
        (PointAddition.PortFrame.controlWorkBit auxEncoding params.width) gate := by
  intro gate hgate
  unfold publicToAuxGates Arithmetic.BlockBank.WordPort.directCopyGates at hgate
  exact xorIntoGates_bitDisjoint _ _ _ _
    (fun bit => PointAddition.PortFrame.liftPublicBit_wire_ne_controlWorkBit
      auxEncoding params.width (source.word.bit bit))
    (fun bit => PointAddition.PortFrame.liftAuxBit_wire_ne_controlWorkBit
      auxEncoding params.width (target.word.bit bit)) gate hgate

private def AllBitDisjoint (observed : EncodedBit rawEncoding)
    (gates : List (EncodedBit.GateSpec rawEncoding)) : Prop :=
  ∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint observed gate

private lemma AllBitDisjoint.append
    {observed : EncodedBit rawEncoding}
    {left right : List (EncodedBit.GateSpec rawEncoding)}
    (hleft : AllBitDisjoint observed left)
    (hright : AllBitDisjoint observed right) :
    AllBitDisjoint observed (left ++ right) := by
  intro gate hgate
  exact (List.mem_append.mp hgate).elim (hleft gate) (hright gate)

private lemma computeGates_allBitDisjoint
    (observed : EncodedBit rawEncoding)
    (hpublic : ∀ source target,
      AllBitDisjoint observed (publicToAuxGates source target))
    (hlift : ∀ gates, AllBitDisjoint observed (liftAuxGates gates)) :
    AllBitDisjoint observed computeGates := by
  have hauxCopy : ∀ {wordWidth : Nat}
      (source target : Arithmetic.BlockBank.WordPort auxEncoding wordWidth)
      (hcross : ∀ sourceBit targetBit,
        (source.word.bit sourceBit).wire ≠
          (target.word.bit targetBit).wire),
      AllBitDisjoint observed (auxCopyGates source target hcross) := by
    intro wordWidth source target hcross
    unfold auxCopyGates
    exact hlift _
  have hmoveProduct : ∀
      (product : Arithmetic.BlockBank.WordPort
        ParameterizedPointAddition.Workspace.productEncoding params.width)
      (thin : Arithmetic.BlockBank.WordPort
        ParameterizedPointAddition.Workspace.thinEncoding params.width),
      AllBitDisjoint observed (moveProductToThinGates product thin) := by
    intro product thin
    unfold moveProductToThinGates productToThinGates thinToProductGates
    exact AllBitDisjoint.append
      (hauxCopy _ _ (product_thin_cross_ne product thin))
      (hauxCopy _ _ (thin_product_cross_ne thin product))
  have hmoveAccumulator :
      AllBitDisjoint observed moveAccumulatorToMultiplierGates := by
    unfold moveAccumulatorToMultiplierGates accumulatorToMultiplierGates
      multiplierToAccumulatorGates
    exact AllBitDisjoint.append
      (hauxCopy _ _ accumulator_multiplier_cross_ne)
      (hauxCopy _ _ multiplier_accumulator_cross_ne)
  have hselected : AllBitDisjoint observed selectedSubtractGates := by
    unfold selectedSubtractGates
    exact hlift _
  have hsubtract : ∀ source,
      AllBitDisjoint observed (subtractPublicGates source) := by
    intro source
    unfold subtractPublicGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append (hpublic _ _) hselected) (hpublic _ _)
  have hdenominatorDifference :
      AllBitDisjoint observed denominatorDifferenceGates := by
    unfold denominatorDifferenceGates
    exact AllBitDisjoint.append (hpublic _ _) (hsubtract _)
  have hdenominator : AllBitDisjoint observed denominatorGates := by
    unfold denominatorGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append
        (AllBitDisjoint.append hdenominatorDifference (hlift _)) (hlift _))
      (hlift _)
  have hnumerator : AllBitDisjoint observed numeratorGates := by
    unfold numeratorGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append (hpublic _ _) (hsubtract _)) hmoveAccumulator
  have hdivisionAndSave : AllBitDisjoint observed divisionAndSaveGates := by
    unfold divisionAndSaveGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append (hlift _) (hmoveProduct _ _))
      (hmoveProduct _ _)
  have hsquare : AllBitDisjoint observed multiplySlopeSquareGates := by
    unfold multiplySlopeSquareGates thinToProductGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append
        (AllBitDisjoint.append
          (AllBitDisjoint.append
            (hauxCopy _ _ (thin_product_cross_ne _ _))
            (hauxCopy _ _ (thin_product_cross_ne _ _)))
          (hlift _))
        (hauxCopy _ _ (thin_product_cross_ne _ _)))
      (hauxCopy _ _ (thin_product_cross_ne _ _))
  have hx : AllBitDisjoint observed xCoordinateGates := by
    unfold xCoordinateGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append
        (AllBitDisjoint.append hsquare (hsubtract _)) (hsubtract _))
      (hmoveProduct _ _)
  have hfirstY : AllBitDisjoint observed multiplySlopeMutableXGates := by
    unfold multiplySlopeMutableXGates thinToProductGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append
        (AllBitDisjoint.append
          (AllBitDisjoint.append
            (hauxCopy _ _ (thin_product_cross_ne _ _)) (hpublic _ _))
          (hlift _))
        (hauxCopy _ _ (thin_product_cross_ne _ _)))
      (hpublic _ _)
  have hsecondY : AllBitDisjoint observed subtractSlopeXGates := by
    unfold subtractSlopeXGates thinToProductGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append
        (AllBitDisjoint.append
          (AllBitDisjoint.append
            (hauxCopy _ _ (thin_product_cross_ne _ _))
            (hauxCopy _ _ (thin_product_cross_ne _ _)))
          (hlift _))
        (hauxCopy _ _ (thin_product_cross_ne _ _)))
      (hauxCopy _ _ (thin_product_cross_ne _ _))
  have hy : AllBitDisjoint observed yCoordinateGates := by
    unfold yCoordinateGates
    exact AllBitDisjoint.append
      (AllBitDisjoint.append
        (AllBitDisjoint.append hfirstY hsecondY) (hsubtract _))
      (hmoveProduct _ _)
  unfold computeGates
  exact AllBitDisjoint.append
    (AllBitDisjoint.append
      (AllBitDisjoint.append
        (AllBitDisjoint.append hdenominator hnumerator) hdivisionAndSave) hx)
    hy

/-- The direct affine schedule never touches the leading public control. -/
lemma computeGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ computeGates →
      EncodedBit.GateSpec.bitDisjoint
        (PointAddition.PortFrame.controlBit auxEncoding params.width) gate := by
  exact computeGates_allBitDisjoint _
    (fun source target =>
      publicToAuxGates_bitDisjoint_controlBit source target)
    (fun gates gate hgate =>
      PointAddition.PortFrame.liftAuxGates_bitDisjoint_controlBit
        auxEncoding params.width gates gate hgate)

/-- The direct affine schedule never touches the clean control-work bit. -/
lemma computeGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ computeGates →
      EncodedBit.GateSpec.bitDisjoint
        (PointAddition.PortFrame.controlWorkBit auxEncoding params.width) gate := by
  exact computeGates_allBitDisjoint _
    (fun source target =>
      publicToAuxGates_bitDisjoint_controlWorkBit source target)
    (fun gates gate hgate =>
      PointAddition.PortFrame.liftAuxGates_bitDisjoint_controlWorkBit
        auxEncoding params.width gates gate hgate)

end

end DirectSchedule
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
