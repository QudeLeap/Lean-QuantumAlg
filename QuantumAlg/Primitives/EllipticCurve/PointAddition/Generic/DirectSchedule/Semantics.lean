/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Generic.DirectSchedule

/-!
# Clean semantics of the direct-workspace affine-addition schedule

This module proves the field-level endpoint of the literal one-carrier gate
schedule.  Intermediate states name actual product, inversion, and saved-word
contents; there is no logical arithmetic bank or temporal-address layer.
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

@[simp] theorem divisionResidueWord_zero :
    Arithmetic.ModularDivision.residueWord
        (0 : ZMod params.modulus.val) = 0 := by
  apply Fin.ext
  simp [Arithmetic.ModularDivision.residueWord]

/-- A public frame around one canonical clean direct-product carrier. -/
def framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) : RawRegisters :=
  (control, ((publicWords,
    ParameterizedPointAddition.Workspace.productRegistersWithFrame
      inversion product tail), controlWork))

theorem liftPublicPort_read_framedProductRegisters
    (port : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (PointAddition.PortFrame.liftPublicPort auxEncoding params.width port).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      port.read publicWords :=
  rfl

@[simp] theorem liftProductMultiplicand_read_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (liftAuxPort
      ParameterizedPointAddition.Workspace.divisionProductTargetPort).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      Arithmetic.ModularDivision.residueWord product.multiplicand := by
  exact ParameterizedPointAddition.Workspace.productMultiplicandPort_read_productRegistersWithFrame
    inversion product tail

@[simp] theorem liftProductMultiplier_read_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (liftAuxPort
      ParameterizedPointAddition.Workspace.divisionNumeratorPort).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      Arithmetic.ModularDivision.residueWord product.multiplier := by
  exact ParameterizedPointAddition.Workspace.productMultiplierPort_read_productRegistersWithFrame
    inversion product tail

@[simp] theorem liftSharedProductMultiplier_read_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (liftAuxPort (ParameterizedPointAddition.Workspace.productPort
      ParameterizedPointAddition.Workspace.productMultiplierPort)).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      Arithmetic.ModularDivision.residueWord product.multiplier := by
  exact ParameterizedPointAddition.Workspace.productMultiplierPort_read_productRegistersWithFrame
    inversion product tail

@[simp] theorem liftSharedProductMultiplicand_read_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (liftAuxPort (ParameterizedPointAddition.Workspace.productPort
      ParameterizedPointAddition.Workspace.productMultiplicandPort)).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      Arithmetic.ModularDivision.residueWord product.multiplicand := by
  exact ParameterizedPointAddition.Workspace.productMultiplicandPort_read_productRegistersWithFrame
    inversion product tail

@[simp] theorem liftProductAccumulator_read_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (liftAuxPort
      ParameterizedPointAddition.Workspace.divisionQuotientPort).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      Arithmetic.ModularDivision.residueWord product.accumulator := by
  exact ParameterizedPointAddition.Workspace.productAccumulatorPort_read_productRegistersWithFrame
    inversion product tail

@[simp] theorem liftSharedProductAccumulator_read_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (liftAuxPort (ParameterizedPointAddition.Workspace.productPort
      ParameterizedPointAddition.Workspace.productAccumulatorPort)).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      Arithmetic.ModularDivision.residueWord product.accumulator := by
  exact ParameterizedPointAddition.Workspace.productAccumulatorPort_read_productRegistersWithFrame
    inversion product tail

@[simp] theorem liftThinPort_read_framedProductRegisters
    (port : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    (liftAuxPort (ParameterizedPointAddition.Workspace.thinPort port)).read
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      port.read tail.1 :=
  rfl

theorem liftProductMultiplier_set_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val) :
    (liftAuxPort ParameterizedPointAddition.Workspace.divisionNumeratorPort).set
        (framedProductRegisters control publicWords inversion product tail controlWork)
        (Arithmetic.ModularDivision.residueWord value) =
      framedProductRegisters control publicWords inversion
        { product with multiplier := value } tail controlWork := by
  change (control, ((publicWords,
      ParameterizedPointAddition.Workspace.divisionNumeratorPort.set
        (ParameterizedPointAddition.Workspace.productRegistersWithFrame
          inversion product tail)
        (Arithmetic.ModularDivision.residueWord value)), controlWork)) = _
  rw [ParameterizedPointAddition.Workspace.productMultiplierPort_set_productRegistersWithFrame]
  rfl

theorem liftProductAccumulator_set_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val) :
    (liftAuxPort ParameterizedPointAddition.Workspace.divisionQuotientPort).set
        (framedProductRegisters control publicWords inversion product tail controlWork)
        (Arithmetic.ModularDivision.residueWord value) =
      framedProductRegisters control publicWords inversion
        { product with accumulator := value } tail controlWork := by
  change (control, ((publicWords,
      ParameterizedPointAddition.Workspace.divisionQuotientPort.set
        (ParameterizedPointAddition.Workspace.productRegistersWithFrame
          inversion product tail)
        (Arithmetic.ModularDivision.residueWord value)), controlWork)) = _
  rw [ParameterizedPointAddition.Workspace.productAccumulatorPort_set_productRegistersWithFrame]
  rfl

theorem liftThinPort_set_framedProductRegisters
    (port : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : Word params.width) :
    (liftAuxPort (ParameterizedPointAddition.Workspace.thinPort port)).set
        (framedProductRegisters control publicWords inversion product tail controlWork)
        value =
      framedProductRegisters control publicWords inversion product
        (port.set tail.1 value, tail.2) controlWork :=
  rfl

@[simp] theorem liftProductMultiplicand_set_framedProductRegisters
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val) :
    (liftAuxPort
      ParameterizedPointAddition.Workspace.divisionProductTargetPort).set
        (framedProductRegisters control publicWords inversion product tail controlWork)
        (Arithmetic.ModularDivision.residueWord value) =
      framedProductRegisters control publicWords inversion
        { product with multiplicand := value } tail controlWork := by
  change (control, ((publicWords,
      ParameterizedPointAddition.Workspace.divisionProductTargetPort.set
        (ParameterizedPointAddition.Workspace.productRegistersWithFrame
          inversion product tail)
        (Arithmetic.ModularDivision.residueWord value)), controlWork)) = _
  rw [ParameterizedPointAddition.Workspace.productMultiplicandPort_set_productRegistersWithFrame]
  rfl

/-- Copy one public field word into a clean direct multiplicand. -/
theorem publicToMultiplicandGates_set_of_clean
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val)
    (hsource : source.read publicWords =
      Arithmetic.ModularDivision.residueWord value)
    (htarget : product.multiplicand = 0) :
    EncodedBit.GateSpec.stepList
        (publicToAuxGates source
          ParameterizedPointAddition.Workspace.divisionProductTargetPort)
        (framedProductRegisters control publicWords inversion product tail
          controlWork) =
      framedProductRegisters control publicWords inversion
        { product with multiplicand := value } tail controlWork := by
  rw [publicToAuxGates_stepList,
    publicToAuxStep_eq_set_of_clean _ _ _
      (Arithmetic.ModularDivision.residueWord value)]
  · exact liftProductMultiplicand_set_framedProductRegisters control publicWords
      inversion product tail controlWork value
  · rw [liftPublicPort_read_framedProductRegisters]
    exact hsource
  · rw [liftProductMultiplicand_read_framedProductRegisters, htarget,
      divisionResidueWord_zero]

/-- Reapplying the same public field word clears an equal direct
multiplicand. -/
theorem publicToMultiplicandGates_set_zero_of_equal
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val)
    (hsource : source.read publicWords =
      Arithmetic.ModularDivision.residueWord value)
    (htarget : product.multiplicand = value) :
    EncodedBit.GateSpec.stepList
        (publicToAuxGates source
          ParameterizedPointAddition.Workspace.divisionProductTargetPort)
        (framedProductRegisters control publicWords inversion product tail
          controlWork) =
      framedProductRegisters control publicWords inversion
        { product with multiplicand := 0 } tail controlWork := by
  rw [publicToAuxGates_stepList,
    publicToAuxStep_eq_set_zero_of_equal _ _ _]
  · rw [show (0 : Word params.width) =
        Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
      exact divisionResidueWord_zero.symm]
    exact liftProductMultiplicand_set_framedProductRegisters control publicWords
      inversion product tail controlWork 0
  · rw [liftPublicPort_read_framedProductRegisters,
      liftProductMultiplicand_read_framedProductRegisters, hsource, htarget]

/-- One public subtraction uses the actual selected-add inverse and restores
the multiplier and multiplicand words to zero. -/
theorem subtractPublicGates_clean
    (source : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val)
    (hmodulus : 1 < params.modulus.val)
    (hsource : source.read publicWords =
      Arithmetic.ModularDivision.residueWord value)
    (hmultiplier : product.multiplier = 0)
    (hmultiplicand : product.multiplicand = 0) :
    EncodedBit.GateSpec.stepList (subtractPublicGates source)
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with
          multiplicand := 0
          accumulator := product.accumulator - value }
        tail controlWork := by
  let loaded : Arithmetic.VariableModularMul.Data :=
    { product with multiplicand := value }
  let subtracted : Arithmetic.VariableModularMul.Data :=
    { loaded with accumulator := loaded.accumulator - loaded.multiplicand }
  have hload :
      EncodedBit.GateSpec.stepList
          (publicToAuxGates source
            ParameterizedPointAddition.Workspace.divisionProductTargetPort)
          (framedProductRegisters control publicWords inversion product tail
            controlWork) =
        framedProductRegisters control publicWords inversion loaded tail controlWork := by
    rw [publicToAuxGates_stepList,
      publicToAuxStep_eq_set_of_clean _ _ _
        (Arithmetic.ModularDivision.residueWord value)]
    · exact liftProductMultiplicand_set_framedProductRegisters
        control publicWords inversion product tail controlWork value
    · change source.read publicWords = _
      exact hsource
    · rw [liftProductMultiplicand_read_framedProductRegisters,
        hmultiplicand]
      apply Fin.ext
      simp [Arithmetic.ModularDivision.residueWord]
  have hsubtract :
      EncodedBit.GateSpec.stepList selectedSubtractGates
          (framedProductRegisters control publicWords inversion loaded tail controlWork) =
        framedProductRegisters control publicWords inversion subtracted tail
          controlWork := by
    rw [selectedSubtractGates_clean _ inversion loaded tail rfl hmodulus]
    · rfl
    · simpa [loaded] using hmultiplier
  have hclear :
      EncodedBit.GateSpec.stepList
          (publicToAuxGates source
            ParameterizedPointAddition.Workspace.divisionProductTargetPort)
          (framedProductRegisters control publicWords inversion subtracted tail
            controlWork) =
        framedProductRegisters control publicWords inversion
          { subtracted with multiplicand := 0 } tail controlWork := by
    rw [publicToAuxGates_stepList,
      publicToAuxStep_eq_set_zero_of_equal]
    · rw [show (0 : Word params.width) =
          Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
        apply Fin.ext
        simp [Arithmetic.ModularDivision.residueWord]]
      exact liftProductMultiplicand_set_framedProductRegisters
        control publicWords inversion subtracted tail controlWork 0
    · rw [liftPublicPort_read_framedProductRegisters,
        liftProductMultiplicand_read_framedProductRegisters, hsource]
  simp only [subtractPublicGates, EncodedBit.GateSpec.stepList_append]
  rw [hload, hsubtract, hclear]

/-- Moving the direct accumulator into a clean multiplier uses two CNOT copies:
the first installs the value and the second clears its old location. -/
theorem moveAccumulatorToMultiplierGates_clean
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (hmultiplier : product.multiplier = 0) :
    EncodedBit.GateSpec.stepList moveAccumulatorToMultiplierGates
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with
          multiplier := product.accumulator
          accumulator := 0 }
        tail controlWork := by
  let loaded : Arithmetic.VariableModularMul.Data :=
    { product with multiplier := product.accumulator }
  have hload :
      EncodedBit.GateSpec.stepList accumulatorToMultiplierGates
          (framedProductRegisters control publicWords inversion product tail
            controlWork) =
        framedProductRegisters control publicWords inversion loaded tail
          controlWork := by
    rw [accumulatorToMultiplierGates_stepList,
      auxCopyStep_eq_set_of_clean _ _ accumulator_multiplier_cross_ne _
        (Arithmetic.ModularDivision.residueWord product.accumulator)]
    · exact liftProductMultiplier_set_framedProductRegisters
        control publicWords inversion product tail controlWork product.accumulator
    · exact liftProductAccumulator_read_framedProductRegisters
        control publicWords inversion product tail controlWork
    · rw [liftProductMultiplier_read_framedProductRegisters, hmultiplier,
        divisionResidueWord_zero]
  have hclear :
      EncodedBit.GateSpec.stepList multiplierToAccumulatorGates
          (framedProductRegisters control publicWords inversion loaded tail
            controlWork) =
        framedProductRegisters control publicWords inversion
          { loaded with accumulator := 0 } tail controlWork := by
    rw [multiplierToAccumulatorGates_stepList,
      auxCopyStep_eq_set_zero_of_equal _ _ multiplier_accumulator_cross_ne]
    · rw [show (0 : Word params.width) =
          Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
        exact divisionResidueWord_zero.symm]
      exact liftProductAccumulator_set_framedProductRegisters
        control publicWords inversion loaded tail controlWork 0
    · rw [liftProductMultiplier_read_framedProductRegisters,
        liftProductAccumulator_read_framedProductRegisters]
  simp only [moveAccumulatorToMultiplierGates,
    EncodedBit.GateSpec.stepList_append]
  rw [hload, hclear]

/-- Move the direct product multiplier into a clean saved word and clear the
multiplier's old physical location. -/
theorem moveMultiplierToThinGates_clean
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (htarget : thin.read tail.1 = 0) :
    EncodedBit.GateSpec.stepList
        (moveProductToThinGates
          ParameterizedPointAddition.Workspace.productMultiplierPort thin)
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with multiplier := 0 }
        (thin.set tail.1
          (Arithmetic.ModularDivision.residueWord product.multiplier), tail.2)
        controlWork := by
  let savedTail :=
    (thin.set tail.1
      (Arithmetic.ModularDivision.residueWord product.multiplier), tail.2)
  have hsave :
      EncodedBit.GateSpec.stepList
          (productToThinGates
            ParameterizedPointAddition.Workspace.productMultiplierPort thin)
          (framedProductRegisters control publicWords inversion product tail
            controlWork) =
        framedProductRegisters control publicWords inversion product savedTail
          controlWork := by
    rw [productToThinGates_stepList,
      auxCopyStep_eq_set_of_clean _ _
        (product_thin_cross_ne
          ParameterizedPointAddition.Workspace.productMultiplierPort thin) _
        (Arithmetic.ModularDivision.residueWord product.multiplier)]
    · exact liftThinPort_set_framedProductRegisters thin control publicWords
        inversion product tail controlWork _
    · exact liftProductMultiplier_read_framedProductRegisters
        control publicWords inversion product tail controlWork
    · simpa using htarget
  have hclear :
      EncodedBit.GateSpec.stepList
          (thinToProductGates thin
            ParameterizedPointAddition.Workspace.productMultiplierPort)
          (framedProductRegisters control publicWords inversion product savedTail
            controlWork) =
        framedProductRegisters control publicWords inversion
          { product with multiplier := 0 } savedTail controlWork := by
    rw [thinToProductGates_stepList,
      auxCopyStep_eq_set_zero_of_equal _ _
        (thin_product_cross_ne thin
          ParameterizedPointAddition.Workspace.productMultiplierPort)]
    · rw [show (0 : Word params.width) =
          Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
        exact divisionResidueWord_zero.symm]
      exact liftProductMultiplier_set_framedProductRegisters control publicWords
        inversion product savedTail controlWork 0
    · rw [liftThinPort_read_framedProductRegisters,
        liftSharedProductMultiplier_read_framedProductRegisters]
      exact thin.read_set tail.1 _
  simp only [moveProductToThinGates, EncodedBit.GateSpec.stepList_append]
  rw [hsave, hclear]

/-- Move the direct product accumulator into a clean saved word and clear the
accumulator's old physical location. -/
theorem moveAccumulatorToThinGates_clean
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (htarget : thin.read tail.1 = 0) :
    EncodedBit.GateSpec.stepList
        (moveProductToThinGates
          ParameterizedPointAddition.Workspace.productAccumulatorPort thin)
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with accumulator := 0 }
        (thin.set tail.1
          (Arithmetic.ModularDivision.residueWord product.accumulator), tail.2)
        controlWork := by
  let savedTail :=
    (thin.set tail.1
      (Arithmetic.ModularDivision.residueWord product.accumulator), tail.2)
  have hsave :
      EncodedBit.GateSpec.stepList
          (productToThinGates
            ParameterizedPointAddition.Workspace.productAccumulatorPort thin)
          (framedProductRegisters control publicWords inversion product tail
            controlWork) =
        framedProductRegisters control publicWords inversion product savedTail
          controlWork := by
    rw [productToThinGates_stepList,
      auxCopyStep_eq_set_of_clean _ _
        (product_thin_cross_ne
          ParameterizedPointAddition.Workspace.productAccumulatorPort thin) _
        (Arithmetic.ModularDivision.residueWord product.accumulator)]
    · exact liftThinPort_set_framedProductRegisters thin control publicWords
        inversion product tail controlWork _
    · exact liftProductAccumulator_read_framedProductRegisters
        control publicWords inversion product tail controlWork
    · simpa using htarget
  have hclear :
      EncodedBit.GateSpec.stepList
          (thinToProductGates thin
            ParameterizedPointAddition.Workspace.productAccumulatorPort)
          (framedProductRegisters control publicWords inversion product savedTail
            controlWork) =
        framedProductRegisters control publicWords inversion
          { product with accumulator := 0 } savedTail controlWork := by
    rw [thinToProductGates_stepList,
      auxCopyStep_eq_set_zero_of_equal _ _
        (thin_product_cross_ne thin
          ParameterizedPointAddition.Workspace.productAccumulatorPort)]
    · rw [show (0 : Word params.width) =
          Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
        exact divisionResidueWord_zero.symm]
      exact liftProductAccumulator_set_framedProductRegisters control publicWords
        inversion product savedTail controlWork 0
    · rw [liftThinPort_read_framedProductRegisters,
        liftSharedProductAccumulator_read_framedProductRegisters]
      exact thin.read_set tail.1 _
  simp only [moveProductToThinGates, EncodedBit.GateSpec.stepList_append]
  rw [hsave, hclear]

/-- Lifting the real shared multiplication ledger through the public frame
preserves the frame and adds the direct product to the accumulator. -/
theorem liftSharedMultiplicationGates_clean
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    EncodedBit.GateSpec.stepList
        (liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
          ParameterizedPointAddition.Workspace.multiplicationGates))
        (framedProductRegisters control publicWords inversion product tail
          controlWork) =
      framedProductRegisters control publicWords inversion
        (Arithmetic.VariableModularMul.Data.addProduct product) tail
        controlWork := by
  unfold liftAuxGates
  rw [PointAddition.PortFrame.liftAuxGates_stepList]
  change (control, ((publicWords,
      EncodedBit.GateSpec.stepList
        (ParameterizedPointAddition.Workspace.sharedProductGates
          ParameterizedPointAddition.Workspace.multiplicationGates)
        (ParameterizedPointAddition.Workspace.productRegistersWithFrame
          inversion product tail)), controlWork)) = _
  rw [ParameterizedPointAddition.Workspace.sharedMultiplicationGates_clean]
  rfl

/-- The reversed lifted multiplication ledger subtracts the direct product and
preserves the complete public frame. -/
theorem liftSharedMultiplicationGates_reverse_clean
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool) :
    EncodedBit.GateSpec.stepList
        (liftAuxGates (ParameterizedPointAddition.Workspace.sharedProductGates
          ParameterizedPointAddition.Workspace.multiplicationGates).reverse)
        (framedProductRegisters control publicWords inversion product tail
          controlWork) =
      framedProductRegisters control publicWords inversion
        (ParameterizedPointAddition.Workspace.subtractProduct product) tail
        controlWork := by
  unfold liftAuxGates
  rw [PointAddition.PortFrame.liftAuxGates_stepList]
  change (control, ((publicWords,
      EncodedBit.GateSpec.stepList
        (ParameterizedPointAddition.Workspace.sharedProductGates
          ParameterizedPointAddition.Workspace.multiplicationGates).reverse
        (ParameterizedPointAddition.Workspace.productRegistersWithFrame
          inversion product tail)), controlWork)) = _
  rw [ParameterizedPointAddition.Workspace.sharedMultiplicationGates_reverse_clean]
  rfl

/-- Load a saved field word into a clean direct multiplier. -/
theorem thinToMultiplierGates_set_of_clean
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val)
    (hsource : thin.read tail.1 =
      Arithmetic.ModularDivision.residueWord value)
    (htarget : product.multiplier = 0) :
    EncodedBit.GateSpec.stepList
        (thinToProductGates thin
          ParameterizedPointAddition.Workspace.productMultiplierPort)
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with multiplier := value } tail controlWork := by
  rw [thinToProductGates_stepList,
    auxCopyStep_eq_set_of_clean _ _
      (thin_product_cross_ne thin
        ParameterizedPointAddition.Workspace.productMultiplierPort) _
      (Arithmetic.ModularDivision.residueWord value)]
  · exact liftProductMultiplier_set_framedProductRegisters control publicWords
      inversion product tail controlWork value
  · simpa using hsource
  · rw [liftSharedProductMultiplier_read_framedProductRegisters, htarget,
      divisionResidueWord_zero]

/-- Reapplying the same saved word clears an equal direct multiplier. -/
theorem thinToMultiplierGates_set_zero_of_equal
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val)
    (hsource : thin.read tail.1 =
      Arithmetic.ModularDivision.residueWord value)
    (htarget : product.multiplier = value) :
    EncodedBit.GateSpec.stepList
        (thinToProductGates thin
          ParameterizedPointAddition.Workspace.productMultiplierPort)
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with multiplier := 0 } tail controlWork := by
  rw [thinToProductGates_stepList,
    auxCopyStep_eq_set_zero_of_equal _ _
      (thin_product_cross_ne thin
        ParameterizedPointAddition.Workspace.productMultiplierPort)]
  · rw [show (0 : Word params.width) =
        Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
      exact divisionResidueWord_zero.symm]
    exact liftProductMultiplier_set_framedProductRegisters control publicWords
      inversion product tail controlWork 0
  · rw [liftThinPort_read_framedProductRegisters,
      liftSharedProductMultiplier_read_framedProductRegisters, hsource, htarget]

/-- Load a saved field word into a clean direct multiplicand. -/
theorem thinToMultiplicandGates_set_of_clean
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val)
    (hsource : thin.read tail.1 =
      Arithmetic.ModularDivision.residueWord value)
    (htarget : product.multiplicand = 0) :
    EncodedBit.GateSpec.stepList
        (thinToProductGates thin
          ParameterizedPointAddition.Workspace.productMultiplicandPort)
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with multiplicand := value } tail controlWork := by
  rw [thinToProductGates_stepList,
    auxCopyStep_eq_set_of_clean _ _
      (thin_product_cross_ne thin
        ParameterizedPointAddition.Workspace.productMultiplicandPort) _
      (Arithmetic.ModularDivision.residueWord value)]
  · exact liftProductMultiplicand_set_framedProductRegisters control publicWords
      inversion product tail controlWork value
  · simpa using hsource
  · rw [liftSharedProductMultiplicand_read_framedProductRegisters, htarget,
      divisionResidueWord_zero]

/-- Reapplying the same saved word clears an equal direct multiplicand. -/
theorem thinToMultiplicandGates_set_zero_of_equal
    (thin : Arithmetic.BlockBank.WordPort
      ParameterizedPointAddition.Workspace.thinEncoding params.width)
    (control : Bool)
    (publicWords : PointAddition.PortFrame.PublicWords params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (product : Arithmetic.VariableModularMul.Data)
    (tail : ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters)
    (controlWork : Bool)
    (value : ZMod params.modulus.val)
    (hsource : thin.read tail.1 =
      Arithmetic.ModularDivision.residueWord value)
    (htarget : product.multiplicand = value) :
    EncodedBit.GateSpec.stepList
        (thinToProductGates thin
          ParameterizedPointAddition.Workspace.productMultiplicandPort)
        (framedProductRegisters control publicWords inversion product tail controlWork) =
      framedProductRegisters control publicWords inversion
        { product with multiplicand := 0 } tail controlWork := by
  rw [thinToProductGates_stepList,
    auxCopyStep_eq_set_zero_of_equal _ _
      (thin_product_cross_ne thin
        ParameterizedPointAddition.Workspace.productMultiplicandPort)]
  · rw [show (0 : Word params.width) =
        Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
      exact divisionResidueWord_zero.symm]
    exact liftProductMultiplicand_set_framedProductRegisters control publicWords
      inversion product tail controlWork 0
  · rw [liftThinPort_read_framedProductRegisters,
      liftSharedProductMultiplicand_read_framedProductRegisters, hsource, htarget]

/-! ## Generic-affine clean states -/

variable {E : PrimeFieldShortWeierstrass params.modulus.val}
  [Fact params.modulus.val.Prime]
  {Q : AffinePoint E}

/-- Canonical public fixed-width words of one affine point. -/
def pointWords (P : AffinePoint E) :
    PointAddition.PortFrame.PointWords params.width :=
  (Arithmetic.ModularDivision.residueWord P.x,
    Arithmetic.ModularDivision.residueWord P.y)

/-- Public frame used by the direct computation before its output copy. -/
def inputPublicWordsAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (P : GenericPointAddition.Input E Q) :
    PointAddition.PortFrame.PublicWords params.width :=
  (pointWords P.1, (pointWords Q, output))

omit [Fact params.modulus.val.Prime] in
@[simp] theorem mutableXPublicPort_read_inputPublicWordsAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (P : GenericPointAddition.Input E Q) :
    (PointAddition.PortFrame.mutableXPublicPort params.width).read
        (inputPublicWordsAt output P) =
      Arithmetic.ModularDivision.residueWord P.1.x :=
  rfl

omit [Fact params.modulus.val.Prime] in
@[simp] theorem mutableYPublicPort_read_inputPublicWordsAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (P : GenericPointAddition.Input E Q) :
    (PointAddition.PortFrame.mutableYPublicPort params.width).read
        (inputPublicWordsAt output P) =
      Arithmetic.ModularDivision.residueWord P.1.y :=
  rfl

omit [Fact params.modulus.val.Prime] in
@[simp] theorem constantXPublicPort_read_inputPublicWordsAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (P : GenericPointAddition.Input E Q) :
    (PointAddition.PortFrame.constantXPublicPort params.width).read
        (inputPublicWordsAt output P) =
      Arithmetic.ModularDivision.residueWord Q.x :=
  rfl

omit [Fact params.modulus.val.Prime] in
@[simp] theorem constantYPublicPort_read_inputPublicWordsAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (P : GenericPointAddition.Input E Q) :
    (PointAddition.PortFrame.constantYPublicPort params.width).read
        (inputPublicWordsAt output P) =
      Arithmetic.ModularDivision.residueWord Q.y :=
  rfl

/-- Clean product datum used whenever the one carrier is between arithmetic
microkernels. -/
def zeroProductData : Arithmetic.VariableModularMul.Data where
  multiplier := 0
  multiplicand := 0
  accumulator := 0

/-- Clean saved-word/output tail before direct affine computation. -/
def blankTail : ParameterizedPointAddition.Workspace.ThinRegisters ×
    ParameterizedPointAddition.Workspace.OutputRegisters :=
  (ParameterizedPointAddition.Workspace.blankThinRegisters,
    ParameterizedPointAddition.Workspace.blankOutputRegisters)

/-- Direct initial boundary with the public inputs explicit and the sole
arithmetic workspace clean. -/
def initialRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    Arithmetic.ModularInversion.blankRegisters zeroProductData blankTail false

/-- The first public difference computes `P.x-Q.x` in the direct accumulator. -/
theorem denominatorDifferenceGates_initial
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList denominatorDifferenceGates
        (initialRegistersAt output control P) =
      framedProductRegisters control (inputPublicWordsAt output P)
        Arithmetic.ModularInversion.blankRegisters
        { zeroProductData with accumulator := P.1.x - Q.x }
        blankTail false := by
  have hmodulus : 1 < params.modulus.val :=
    (Fact.out : params.modulus.val.Prime).one_lt
  let loaded : Arithmetic.VariableModularMul.Data :=
    { zeroProductData with accumulator := P.1.x }
  have hload :
      EncodedBit.GateSpec.stepList
          (publicToAuxGates
            (PointAddition.PortFrame.mutableXPublicPort params.width)
            ParameterizedPointAddition.Workspace.divisionQuotientPort)
          (initialRegistersAt output control P) =
        framedProductRegisters control (inputPublicWordsAt output P)
          Arithmetic.ModularInversion.blankRegisters loaded blankTail false := by
    rw [publicToAuxGates_stepList,
      publicToAuxStep_eq_set_of_clean _ _ _
        (Arithmetic.ModularDivision.residueWord P.1.x)]
    · exact liftProductAccumulator_set_framedProductRegisters control
        (inputPublicWordsAt output P) Arithmetic.ModularInversion.blankRegisters
        zeroProductData blankTail false P.1.x
    · rfl
    · unfold initialRegistersAt
      rw [liftProductAccumulator_read_framedProductRegisters]
      exact divisionResidueWord_zero
  have hsubtract := subtractPublicGates_clean
    (PointAddition.PortFrame.constantXPublicPort params.width) control
    (inputPublicWordsAt output P) Arithmetic.ModularInversion.blankRegisters
    loaded blankTail false Q.x hmodulus
    (constantXPublicPort_read_inputPublicWordsAt output P) rfl rfl
  simp only [denominatorDifferenceGates,
    EncodedBit.GateSpec.stepList_append]
  rw [hload, hsubtract]
  rfl

/-- Named state after the field-width denominator difference is available in
the direct accumulator. -/
def denominatorDifferenceRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    Arithmetic.ModularInversion.blankRegisters
    { zeroProductData with accumulator := P.1.x - Q.x }
    blankTail false

/-- State after loading the preserved Kaliski denominator copy. -/
def denominatorPreservedRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  (liftAuxPort ParameterizedPointAddition.Workspace.denominatorPreservedPort).set
    (denominatorDifferenceRegistersAt output control P)
    (ParameterizedPointAddition.Workspace.zeroExtendWord
      (Arithmetic.ModularDivision.residueWord (P.1.x - Q.x)))

/-- State after loading both Kaliski denominator copies. -/
def denominatorLoadedRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  (liftAuxPort ParameterizedPointAddition.Workspace.denominatorWorkingPort).set
    (denominatorPreservedRegistersAt output control P)
    (ParameterizedPointAddition.Workspace.zeroExtendWord
      (Arithmetic.ModularDivision.residueWord (P.1.x - Q.x)))

/-- State after both Kaliski copies have been loaded and the temporary direct
accumulator has been cleared. -/
def denominatorReadyRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  (liftAuxPort ParameterizedPointAddition.Workspace.divisionQuotientPort).set
    (denominatorLoadedRegistersAt output control P) 0

/-- The three literal denominator routes load both Kaliski copies and clear
the temporary direct accumulator. -/
theorem denominatorGates_initial
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList denominatorGates
        (initialRegistersAt output control P) =
      denominatorReadyRegistersAt output control P := by
  let value := Arithmetic.ModularDivision.residueWord (P.1.x - Q.x)
  let extended := ParameterizedPointAddition.Workspace.zeroExtendWord value
  have hdifference :
      EncodedBit.GateSpec.stepList denominatorDifferenceGates
          (initialRegistersAt output control P) =
        denominatorDifferenceRegistersAt output control P := by
    exact denominatorDifferenceGates_initial output control P
  have hpreserved :
      EncodedBit.GateSpec.stepList
          (liftAuxGates
            ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorPreservedGates)
          (denominatorDifferenceRegistersAt output control P) =
        denominatorPreservedRegistersAt output control P := by
    unfold liftAuxGates
    rw [PointAddition.PortFrame.liftAuxGates_stepList]
    change (control, (((inputPublicWordsAt output P),
        ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorPreservedStep
            (denominatorDifferenceRegistersAt output control P).2.1.2), false)) = _
    rw [productAccumulatorToDenominatorPreservedStep_eq_set_of_clean]
    · rfl
    · exact productAccumulatorPort_read_productRegistersWithFrame _ _ _
    · rfl
  have hworking :
      EncodedBit.GateSpec.stepList
          (liftAuxGates
            ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorWorkingGates)
          (denominatorPreservedRegistersAt output control P) =
        denominatorLoadedRegistersAt output control P := by
    unfold liftAuxGates
    rw [PointAddition.PortFrame.liftAuxGates_stepList]
    change (control, (((inputPublicWordsAt output P),
        ParameterizedPointAddition.Workspace.productAccumulatorToDenominatorWorkingStep
            (denominatorPreservedRegistersAt output control P).2.1.2), false)) = _
    rw [productAccumulatorToDenominatorWorkingStep_eq_set_of_clean]
    · rfl
    · simp [denominatorPreservedRegistersAt,
        denominatorDifferenceRegistersAt, framedProductRegisters, liftAuxPort,
        PointAddition.PortFrame.liftAuxPort,
        ParameterizedPointAddition.Workspace.denominatorPreservedPort,
        ParameterizedPointAddition.Workspace.inversionPort,
        ParameterizedPointAddition.Workspace.productPort,
        ParameterizedPointAddition.Workspace.productAccumulatorPort,
        ParameterizedPointAddition.Workspace.readProductAccumulator,
        ParameterizedPointAddition.Workspace.productRegistersWithFrame,
        Arithmetic.VariableModularMul.cleanRegisters,
        Arithmetic.ModularDivision.residueWord,
        Arithmetic.BlockBank.WordPort.prodLeft,
        Arithmetic.BlockBank.WordPort.prodRight, zeroProductData]
    · rfl
  have hclear :
      EncodedBit.GateSpec.stepList
          (liftAuxGates
            ParameterizedPointAddition.Workspace.denominatorPreservedToProductAccumulatorGates)
          (denominatorLoadedRegistersAt output control P) =
        denominatorReadyRegistersAt output control P := by
    unfold liftAuxGates
    rw [PointAddition.PortFrame.liftAuxGates_stepList,
      ParameterizedPointAddition.Workspace.denominatorPreservedToProductAccumulatorGates_stepList]
    change (control, (((inputPublicWordsAt output P),
        ParameterizedPointAddition.Workspace.denominatorPreservedToProductAccumulatorStep
            (denominatorLoadedRegistersAt output control P).2.1.2), false)) = _
    rw [denominatorPreservedToProductAccumulatorStep_eq_set_zero_of_equal]
    · rfl
    · simp [denominatorLoadedRegistersAt, denominatorPreservedRegistersAt,
        denominatorDifferenceRegistersAt, framedProductRegisters, liftAuxPort,
        PointAddition.PortFrame.liftAuxPort,
        ParameterizedPointAddition.Workspace.denominatorPreservedPort,
        ParameterizedPointAddition.Workspace.denominatorWorkingPort,
        ParameterizedPointAddition.Workspace.inversionPort,
        ParameterizedPointAddition.Workspace.productPort,
        ParameterizedPointAddition.Workspace.productAccumulatorPort,
        ParameterizedPointAddition.Workspace.readProductAccumulator,
        ParameterizedPointAddition.Workspace.productRegistersWithFrame,
        ParameterizedPointAddition.Workspace.zeroExtendWord,
        Arithmetic.VariableModularMul.cleanRegisters,
        Arithmetic.ModularDivision.residueWord,
        Arithmetic.ModularInversion.preservedInputPort,
        Arithmetic.ModularInversion.workingInputPort,
        Arithmetic.ModularInversion.readPreservedInput,
        Arithmetic.ModularInversion.setPreservedInput,
        Arithmetic.ModularInversion.setWorkingInput,
        Arithmetic.BlockBank.WordPort.prodLeft,
        Arithmetic.BlockBank.WordPort.prodRight, zeroProductData]
  simp only [denominatorGates, EncodedBit.GateSpec.stepList_append]
  rw [hdifference, hpreserved, hworking, hclear]

/-- The actual inversion prefix after loading both denominator copies. -/
def denominatorInversionRegisters (P : GenericPointAddition.Input E Q) :
    Arithmetic.ModularInversion.RawRegisters :=
  let value := Arithmetic.ModularDivision.residueWord (P.1.x - Q.x)
  let extended := ParameterizedPointAddition.Workspace.zeroExtendWord value
  Arithmetic.ModularInversion.workingInputPort.set
    (Arithmetic.ModularInversion.preservedInputPort.set
      Arithmetic.ModularInversion.blankRegisters extended) extended

theorem denominatorLoadedRegistersAt_eq_framed
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    denominatorLoadedRegistersAt output control P =
      framedProductRegisters control (inputPublicWordsAt output P)
        (denominatorInversionRegisters P)
        { zeroProductData with accumulator := P.1.x - Q.x }
        blankTail false := by
  rfl

theorem denominatorReadyRegistersAt_eq_framed
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    denominatorReadyRegistersAt output control P =
      framedProductRegisters control (inputPublicWordsAt output P)
        (denominatorInversionRegisters P) zeroProductData blankTail false := by
  rw [denominatorReadyRegistersAt, denominatorLoadedRegistersAt_eq_framed]
  rw [show (0 : Word params.width) =
      Arithmetic.ModularDivision.residueWord (0 : ZMod params.modulus.val) by
    exact divisionResidueWord_zero.symm]
  rw [liftProductAccumulator_set_framedProductRegisters]
  rfl

/-- Named direct-division input after the public numerator has been formed and
moved into the physical numerator word. -/
def divisionReadyRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (denominatorInversionRegisters P)
    { zeroProductData with multiplier := P.1.y - Q.y }
    blankTail false

/-- The numerator schedule computes `P.y-Q.y`, moves it into the division
numerator, and clears the direct accumulator. -/
theorem numeratorGates_denominatorReady
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList numeratorGates
        (denominatorReadyRegistersAt output control P) =
      divisionReadyRegistersAt output control P := by
  have hmodulus : 1 < params.modulus.val :=
    (Fact.out : params.modulus.val.Prime).one_lt
  let loaded : Arithmetic.VariableModularMul.Data :=
    { zeroProductData with accumulator := P.1.y }
  let numerator : Arithmetic.VariableModularMul.Data :=
    { zeroProductData with accumulator := P.1.y - Q.y }
  have hload :
      EncodedBit.GateSpec.stepList
          (publicToAuxGates
            (PointAddition.PortFrame.mutableYPublicPort params.width)
            ParameterizedPointAddition.Workspace.divisionQuotientPort)
          (denominatorReadyRegistersAt output control P) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (denominatorInversionRegisters P) loaded blankTail false := by
    rw [denominatorReadyRegistersAt_eq_framed,
      publicToAuxGates_stepList,
      publicToAuxStep_eq_set_of_clean _ _ _
        (Arithmetic.ModularDivision.residueWord P.1.y)]
    · exact liftProductAccumulator_set_framedProductRegisters control
        (inputPublicWordsAt output P) (denominatorInversionRegisters P)
        zeroProductData blankTail false P.1.y
    · rfl
    · rw [liftProductAccumulator_read_framedProductRegisters]
      exact divisionResidueWord_zero
  have hsubtract := subtractPublicGates_clean
    (PointAddition.PortFrame.constantYPublicPort params.width) control
    (inputPublicWordsAt output P) (denominatorInversionRegisters P)
    loaded blankTail false Q.y hmodulus
    (constantYPublicPort_read_inputPublicWordsAt output P) rfl rfl
  have hmove := moveAccumulatorToMultiplierGates_clean control
    (inputPublicWordsAt output P) (denominatorInversionRegisters P)
    numerator blankTail false rfl
  simp only [numeratorGates, EncodedBit.GateSpec.stepList_append]
  rw [hload, hsubtract]
  simpa [loaded, numerator, divisionReadyRegistersAt, zeroProductData] using hmove

/-- Denominator and numerator loading produce exactly the canonical clean
division carrier expected by the proved direct division endpoint. -/
theorem divisionReadyRegistersAt_eq_divisionRegistersWithTail
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    divisionReadyRegistersAt output control P =
      (control, ((inputPublicWordsAt output P,
        ParameterizedPointAddition.Workspace.divisionRegistersWithTail
          (ParameterizedPointAddition.slopeDivisionData P) blankTail), false)) := by
  unfold divisionReadyRegistersAt framedProductRegisters
  apply congrArg (fun auxiliary : AuxRegisters =>
    (control, ((inputPublicWordsAt output P, auxiliary), false)))
  change
    (denominatorInversionRegisters P,
      (Arithmetic.VariableModularMul.cleanRegisters
        { multiplier := P.1.y - Q.y, multiplicand := 0, accumulator := 0 },
      blankTail)) = _
  unfold ParameterizedPointAddition.Workspace.divisionRegistersWithTail
    ParameterizedPointAddition.Workspace.divisionCoreWithTail
  have hload := Arithmetic.ModularDivision.loadBlankRegisters_eq_cleanRegisters
    (genericAddDenominatorUnit P.1 Q P.2) (genericAddNumerator P.1 Q)
  have hdenominator :
      ParameterizedPointAddition.Workspace.zeroExtendWord
          (Arithmetic.ModularDivision.residueWord (P.1.x - Q.x)) =
        Arithmetic.ModularInversion.inputWord
          (genericAddDenominatorUnit P.1 Q P.2) := by
    apply Fin.ext
    simp [ParameterizedPointAddition.Workspace.zeroExtendWord,
      Arithmetic.ModularDivision.residueWord,
      Arithmetic.ModularInversion.inputWord, genericAddDenominator]
  have hcore :
      (denominatorInversionRegisters P,
        Arithmetic.VariableModularMul.cleanRegisters
          { multiplier := P.1.y - Q.y, multiplicand := 0, accumulator := 0 }) =
        Arithmetic.ModularDivision.cleanRegisters
          (ParameterizedPointAddition.slopeDivisionData P) := by
    rw [denominatorInversionRegisters, hdenominator]
    simpa [denominatorInversionRegisters,
      ParameterizedPointAddition.slopeDivisionData, genericAddNumerator,
      ParameterizedPointAddition.Workspace.zeroExtendWord,
      Arithmetic.ModularDivision.residueWord,
      Arithmetic.ModularDivision.blankRegisters,
      Arithmetic.ModularDivision.numeratorPort,
      Arithmetic.ModularDivision.productNumeratorPort,
      Arithmetic.ModularDivision.denominatorPreservedPort,
      Arithmetic.ModularDivision.denominatorWorkingPort,
      Arithmetic.VariableModularMul.cleanRegisters,
      Arithmetic.BlockBank.WordPort.prodLeft,
      Arithmetic.BlockBank.WordPort.prodRight,
      ParameterizedPointAddition.Workspace.productRegistersWithFrame,
      zeroProductData] using hload
  have hinversion : denominatorInversionRegisters P =
      (Arithmetic.ModularDivision.cleanRegisters
        (ParameterizedPointAddition.slopeDivisionData P)).1 := by
    exact congrArg Prod.fst hcore
  have hproduct :
      Arithmetic.VariableModularMul.cleanRegisters
          { multiplier := P.1.y - Q.y, multiplicand := 0, accumulator := 0 } =
        (Arithmetic.ModularDivision.cleanRegisters
          (ParameterizedPointAddition.slopeDivisionData P)).2 := by
    exact congrArg Prod.snd hcore
  rw [hinversion, hproduct]

/-- Canonical endpoint after direct modular division has added the quotient to
the shared accumulator. -/
def divisionCompleteRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  (control, ((inputPublicWordsAt output P,
    ParameterizedPointAddition.Workspace.divisionRegistersWithTail
      (ParameterizedPointAddition.slopeDivisionData P).addQuotientIntoTarget
      blankTail), false))

/-- Lifting the proved direct-division ledger through the public frame preserves
the public words and produces its canonical quotient endpoint. -/
theorem divisionGates_divisionReady
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList
        (liftAuxGates ParameterizedPointAddition.Workspace.divisionGates)
        (divisionReadyRegistersAt output control P) =
      divisionCompleteRegistersAt output control P := by
  rw [divisionReadyRegistersAt_eq_divisionRegistersWithTail]
  unfold liftAuxGates
  rw [PointAddition.PortFrame.liftAuxGates_stepList]
  change (control, ((inputPublicWordsAt output P,
      EncodedBit.GateSpec.stepList
        ParameterizedPointAddition.Workspace.divisionGates
        (ParameterizedPointAddition.Workspace.divisionRegistersWithTail
          (ParameterizedPointAddition.slopeDivisionData P) blankTail)), false)) = _
  rw [ParameterizedPointAddition.Workspace.divisionGates_cleanEndpoint]
  rfl

/-- Clean inversion prefix retained after the quotient has been computed. -/
def slopeInversionRegisters (P : GenericPointAddition.Input E Q) :
    Arithmetic.ModularInversion.RawRegisters :=
  Arithmetic.ModularInversion.cleanRegisters
    (Arithmetic.ModularDivision.inversionData
      (ParameterizedPointAddition.slopeDivisionData P))

/-- Product fields at the quotient endpoint: numerator retained in the
multiplier and affine slope in the accumulator. -/
def slopeProductData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data where
  multiplier := P.1.y - Q.y
  multiplicand := 0
  accumulator := ParameterizedPointAddition.slopeValue P

/-- The canonical division endpoint has the explicit field-level slope shape
needed by the following saved-word routes. -/
theorem divisionCompleteRegistersAt_eq_framed
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    divisionCompleteRegistersAt output control P =
      framedProductRegisters control (inputPublicWordsAt output P)
        (slopeInversionRegisters P) (slopeProductData P) blankTail false := by
  unfold divisionCompleteRegistersAt framedProductRegisters
    ParameterizedPointAddition.Workspace.divisionRegistersWithTail
    ParameterizedPointAddition.Workspace.divisionCoreWithTail
    ParameterizedPointAddition.Workspace.productRegistersWithFrame
    Arithmetic.ModularDivision.cleanRegisters
    Arithmetic.ModularDivision.cleanRegistersWithAccumulator
    Arithmetic.ModularDivision.productData slopeInversionRegisters
    slopeProductData ParameterizedPointAddition.slopeDivisionData
    ParameterizedPointAddition.slopeValue
  simp only [MAU.Division.Data.addQuotientIntoTarget_numerator,
    MAU.Division.Data.addQuotientIntoTarget_target,
    zero_add]
  rw [genericAddSlope_eq_quotientResidue E P.1 Q P.2]
  rfl

/-- Tail after the preserved numerator has been moved out of the product
multiplier. -/
def numeratorSavedTail (P : GenericPointAddition.Input E Q) :
    ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters :=
  (ParameterizedPointAddition.Workspace.numeratorScratchThinPort.set
      ParameterizedPointAddition.Workspace.blankThinRegisters
      (Arithmetic.ModularDivision.residueWord (P.1.y - Q.y)),
    ParameterizedPointAddition.Workspace.blankOutputRegisters)

/-- Tail after both the numerator and affine slope have been retained. -/
def slopeSavedTail (P : GenericPointAddition.Input E Q) :
    ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters :=
  (ParameterizedPointAddition.Workspace.slopeThinPort.set
      (numeratorSavedTail P).1
      (Arithmetic.ModularDivision.residueWord
        (ParameterizedPointAddition.slopeValue P)),
    (numeratorSavedTail P).2)

/-- State between the two saved-word moves. -/
def numeratorSavedRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (slopeInversionRegisters P)
    { slopeProductData P with multiplier := 0 }
    (numeratorSavedTail P) false

/-- Clean direct carrier after division data have been moved into the two thin
saved words. -/
def slopeSavedRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (slopeInversionRegisters P) zeroProductData (slopeSavedTail P) false

/-- The direct division ledger computes the slope, then the two move routes
retain the numerator and slope while clearing the product carrier. -/
theorem divisionAndSaveGates_divisionReady
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList divisionAndSaveGates
        (divisionReadyRegistersAt output control P) =
      slopeSavedRegistersAt output control P := by
  have hdivision := divisionGates_divisionReady output control P
  have hsaveNumerator := moveMultiplierToThinGates_clean
    ParameterizedPointAddition.Workspace.numeratorScratchThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (slopeProductData P) blankTail false (by rfl)
  have hsaveSlope := moveAccumulatorToThinGates_clean
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    { slopeProductData P with multiplier := 0 }
    (numeratorSavedTail P) false (by rfl)
  simp only [divisionAndSaveGates, EncodedBit.GateSpec.stepList_append]
  rw [hdivision, divisionCompleteRegistersAt_eq_framed, hsaveNumerator]
  simpa [slopeSavedRegistersAt, slopeSavedTail, numeratorSavedTail,
    slopeProductData, zeroProductData, blankTail] using hsaveSlope

/-- Product carrier after loading the saved slope into the multiplier. -/
def squareMultiplierData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { zeroProductData with
    multiplier := ParameterizedPointAddition.slopeValue P }

/-- Product carrier after loading the saved slope into both operands. -/
def squareOperandsData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { squareMultiplierData P with
    multiplicand := ParameterizedPointAddition.slopeValue P }

/-- Product carrier after the real multiplication ledger has accumulated the
slope square. -/
def squareAccumulatedData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  Arithmetic.VariableModularMul.Data.addProduct (squareOperandsData P)

/-- Slope-square carrier after clearing its multiplier operand. -/
def squareMultiplierClearedData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { squareAccumulatedData P with multiplier := 0 }

/-- Clean product carrier containing only the computed slope square. -/
def slopeSquareData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { squareMultiplierClearedData P with multiplicand := 0 }

/-- State after the slope-square microkernel has restored both operand words. -/
def slopeSquareRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (slopeInversionRegisters P) (slopeSquareData P) (slopeSavedTail P) false

/-- The slope-square schedule loads the same saved slope into both operands,
runs the actual multiplication ledger, and clears both operand words. -/
theorem multiplySlopeSquareGates_slopeSaved
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList multiplySlopeSquareGates
        (slopeSavedRegistersAt output control P) =
      slopeSquareRegistersAt output control P := by
  have hslope :
      ParameterizedPointAddition.Workspace.slopeThinPort.read
          (slopeSavedTail P).1 =
        Arithmetic.ModularDivision.residueWord
          (ParameterizedPointAddition.slopeValue P) := by
    exact ParameterizedPointAddition.Workspace.slopeThinPort.read_set _ _
  have hmultiplier := thinToMultiplierGates_set_of_clean
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P) zeroProductData
    (slopeSavedTail P) false (ParameterizedPointAddition.slopeValue P)
    hslope rfl
  have hmultiplicand := thinToMultiplicandGates_set_of_clean
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (squareMultiplierData P) (slopeSavedTail P) false
    (ParameterizedPointAddition.slopeValue P) hslope rfl
  have hproduct := liftSharedMultiplicationGates_clean control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (squareOperandsData P) (slopeSavedTail P) false
  have hclearMultiplier := thinToMultiplierGates_set_zero_of_equal
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (squareAccumulatedData P) (slopeSavedTail P) false
    (ParameterizedPointAddition.slopeValue P) hslope (by rfl)
  have hclearMultiplicand := thinToMultiplicandGates_set_zero_of_equal
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (squareMultiplierClearedData P)
    (slopeSavedTail P) false (ParameterizedPointAddition.slopeValue P)
    hslope (by rfl)
  have hmultiplier' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplierPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) zeroProductData (slopeSavedTail P)
            false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (squareMultiplierData P)
          (slopeSavedTail P) false := by
    simpa [squareMultiplierData] using hmultiplier
  have hmultiplicand' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplicandPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (squareMultiplierData P)
            (slopeSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (squareOperandsData P)
          (slopeSavedTail P) false := by
    simpa [squareOperandsData] using hmultiplicand
  have hproduct' :
      EncodedBit.GateSpec.stepList
          (liftAuxGates
            (ParameterizedPointAddition.Workspace.sharedProductGates
              ParameterizedPointAddition.Workspace.multiplicationGates))
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (squareOperandsData P)
            (slopeSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (squareAccumulatedData P)
          (slopeSavedTail P) false := by
    simpa [squareAccumulatedData] using hproduct
  have hclearMultiplier' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplierPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (squareAccumulatedData P)
            (slopeSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (squareMultiplierClearedData P)
          (slopeSavedTail P) false := by
    simpa [squareMultiplierClearedData] using hclearMultiplier
  have hclearMultiplicand' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplicandPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (squareMultiplierClearedData P)
            (slopeSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (slopeSquareData P)
          (slopeSavedTail P) false := by
    simpa [slopeSquareData] using hclearMultiplicand
  simp only [multiplySlopeSquareGates,
    EncodedBit.GateSpec.stepList_append]
  rw [show slopeSavedRegistersAt output control P =
      framedProductRegisters control (inputPublicWordsAt output P)
        (slopeInversionRegisters P) zeroProductData (slopeSavedTail P) false by
    rfl]
  rw [hmultiplier', hmultiplicand', hproduct', hclearMultiplier',
    hclearMultiplicand']
  rfl

/-- Product value after subtracting the mutable public x-coordinate. -/
def squareMinusMutableXData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { slopeSquareData P with
    multiplicand := 0
    accumulator := (slopeSquareData P).accumulator - P.1.x }

/-- Product value after both public x-coordinate subtractions. -/
def xCoordinateData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { squareMinusMutableXData P with
    multiplicand := 0
    accumulator := (squareMinusMutableXData P).accumulator - Q.x }

/-- Tail retaining the computed affine x-coordinate. -/
def xSavedTail (P : GenericPointAddition.Input E Q) :
    ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters :=
  (ParameterizedPointAddition.Workspace.xThinPort.set (slopeSavedTail P).1
      (Arithmetic.ModularDivision.residueWord
        (xCoordinateData P).accumulator),
    (slopeSavedTail P).2)

/-- Clean product carrier after the computed x-coordinate has been saved. -/
def xSavedRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (slopeInversionRegisters P) zeroProductData (xSavedTail P) false

@[simp] theorem xCoordinateData_accumulator
    (P : GenericPointAddition.Input E Q) :
    (xCoordinateData P).accumulator =
      ParameterizedPointAddition.xScratch P := by
  simp [xCoordinateData, squareMinusMutableXData, slopeSquareData,
    squareMultiplierClearedData, squareAccumulatedData, squareOperandsData,
    squareMultiplierData, zeroProductData,
    Arithmetic.VariableModularMul.Data.addProduct,
    ParameterizedPointAddition.xScratch]

/-- The x-coordinate schedule subtracts both public x inputs from the computed
slope square, saves the result, and restores the product carrier. -/
theorem xCoordinateGates_slopeSaved
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList xCoordinateGates
        (slopeSavedRegistersAt output control P) =
      xSavedRegistersAt output control P := by
  have hmodulus : 1 < params.modulus.val :=
    (Fact.out : params.modulus.val.Prime).one_lt
  have hsubtractMutable := subtractPublicGates_clean
    (PointAddition.PortFrame.mutableXPublicPort params.width) control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (slopeSquareData P) (slopeSavedTail P) false P.1.x hmodulus
    (mutableXPublicPort_read_inputPublicWordsAt output P)
    (by simp [slopeSquareData, squareMultiplierClearedData,
      squareAccumulatedData, squareOperandsData, squareMultiplierData,
      zeroProductData, Arithmetic.VariableModularMul.Data.addProduct])
    (by simp [slopeSquareData, squareMultiplierClearedData,
      squareAccumulatedData, squareOperandsData, squareMultiplierData,
      zeroProductData, Arithmetic.VariableModularMul.Data.addProduct])
  have hsubtractConstant := subtractPublicGates_clean
    (PointAddition.PortFrame.constantXPublicPort params.width) control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (squareMinusMutableXData P) (slopeSavedTail P) false Q.x hmodulus
    (constantXPublicPort_read_inputPublicWordsAt output P)
    (by simp [squareMinusMutableXData, slopeSquareData,
      squareMultiplierClearedData, squareAccumulatedData, squareOperandsData,
      squareMultiplierData, zeroProductData,
      Arithmetic.VariableModularMul.Data.addProduct])
    (by simp [squareMinusMutableXData])
  have hsave := moveAccumulatorToThinGates_clean
    ParameterizedPointAddition.Workspace.xThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (xCoordinateData P) (slopeSavedTail P) false (by rfl)
  have hsubtractMutable' :
      EncodedBit.GateSpec.stepList
          (subtractPublicGates
            (PointAddition.PortFrame.mutableXPublicPort params.width))
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (slopeSquareData P)
            (slopeSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (squareMinusMutableXData P)
          (slopeSavedTail P) false := by
    simpa [squareMinusMutableXData] using hsubtractMutable
  have hsubtractConstant' :
      EncodedBit.GateSpec.stepList
          (subtractPublicGates
            (PointAddition.PortFrame.constantXPublicPort params.width))
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (squareMinusMutableXData P)
            (slopeSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (xCoordinateData P)
          (slopeSavedTail P) false := by
    simpa [xCoordinateData] using hsubtractConstant
  simp only [xCoordinateGates, EncodedBit.GateSpec.stepList_append]
  rw [multiplySlopeSquareGates_slopeSaved]
  unfold slopeSquareRegistersAt
  rw [hsubtractMutable', hsubtractConstant', hsave]
  simp [xSavedRegistersAt, xSavedTail, xCoordinateData,
    squareMinusMutableXData, slopeSquareData, squareMultiplierClearedData,
    squareAccumulatedData, squareOperandsData, squareMultiplierData,
    zeroProductData, Arithmetic.VariableModularMul.Data.addProduct]

/-- Product carrier after loading the saved slope for the y-coordinate's first
product. -/
def ySlopeMultiplierData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { zeroProductData with
    multiplier := ParameterizedPointAddition.slopeValue P }

/-- Operands for the first y-coordinate product `slope * P.x`. -/
def ySlopeMutableXOperandsData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { ySlopeMultiplierData P with multiplicand := P.1.x }

/-- Accumulated first y-coordinate product before clearing its operands. -/
def ySlopeMutableXAccumulatedData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  Arithmetic.VariableModularMul.Data.addProduct
    (ySlopeMutableXOperandsData P)

/-- First y-coordinate product after clearing its slope operand. -/
def ySlopeMutableXMultiplierClearedData
    (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { ySlopeMutableXAccumulatedData P with multiplier := 0 }

/-- Clean carrier containing only `slope * P.x`. -/
def ySlopeMutableXData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { ySlopeMutableXMultiplierClearedData P with multiplicand := 0 }

/-- State after the first y-coordinate product and both operand clears. -/
def ySlopeMutableXRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (slopeInversionRegisters P) (ySlopeMutableXData P) (xSavedTail P) false

/-- The first y-coordinate product loads the saved slope and public mutable x,
runs the actual multiplication ledger, and clears both operands. -/
theorem multiplySlopeMutableXGates_xSaved
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList multiplySlopeMutableXGates
        (xSavedRegistersAt output control P) =
      ySlopeMutableXRegistersAt output control P := by
  have hslope :
      ParameterizedPointAddition.Workspace.slopeThinPort.read
          (xSavedTail P).1 =
        Arithmetic.ModularDivision.residueWord
          (ParameterizedPointAddition.slopeValue P) := by
    rfl
  have hmultiplier := thinToMultiplierGates_set_of_clean
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P) zeroProductData
    (xSavedTail P) false (ParameterizedPointAddition.slopeValue P) hslope rfl
  have hmultiplicand := publicToMultiplicandGates_set_of_clean
    (PointAddition.PortFrame.mutableXPublicPort params.width) control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySlopeMultiplierData P) (xSavedTail P) false P.1.x
    (mutableXPublicPort_read_inputPublicWordsAt output P) rfl
  have hproduct := liftSharedMultiplicationGates_clean control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySlopeMutableXOperandsData P) (xSavedTail P) false
  have hclearMultiplier := thinToMultiplierGates_set_zero_of_equal
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySlopeMutableXAccumulatedData P) (xSavedTail P) false
    (ParameterizedPointAddition.slopeValue P) hslope (by rfl)
  have hclearMultiplicand := publicToMultiplicandGates_set_zero_of_equal
    (PointAddition.PortFrame.mutableXPublicPort params.width) control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySlopeMutableXMultiplierClearedData P) (xSavedTail P) false P.1.x
    (mutableXPublicPort_read_inputPublicWordsAt output P) (by rfl)
  have hmultiplier' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplierPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) zeroProductData (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySlopeMultiplierData P)
          (xSavedTail P) false := by
    simpa [ySlopeMultiplierData] using hmultiplier
  have hmultiplicand' :
      EncodedBit.GateSpec.stepList
          (publicToAuxGates
            (PointAddition.PortFrame.mutableXPublicPort params.width)
            ParameterizedPointAddition.Workspace.divisionProductTargetPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (ySlopeMultiplierData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySlopeMutableXOperandsData P)
          (xSavedTail P) false := by
    simpa [ySlopeMutableXOperandsData] using hmultiplicand
  have hproduct' :
      EncodedBit.GateSpec.stepList
          (liftAuxGates
            (ParameterizedPointAddition.Workspace.sharedProductGates
              ParameterizedPointAddition.Workspace.multiplicationGates))
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (ySlopeMutableXOperandsData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySlopeMutableXAccumulatedData P)
          (xSavedTail P) false := by
    simpa [ySlopeMutableXAccumulatedData] using hproduct
  have hclearMultiplier' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplierPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (ySlopeMutableXAccumulatedData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySlopeMutableXMultiplierClearedData P)
          (xSavedTail P) false := by
    simpa [ySlopeMutableXMultiplierClearedData] using hclearMultiplier
  have hclearMultiplicand' :
      EncodedBit.GateSpec.stepList
          (publicToAuxGates
            (PointAddition.PortFrame.mutableXPublicPort params.width)
            ParameterizedPointAddition.Workspace.divisionProductTargetPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P)
            (ySlopeMutableXMultiplierClearedData P) (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySlopeMutableXData P)
          (xSavedTail P) false := by
    simpa [ySlopeMutableXData] using hclearMultiplicand
  simp only [multiplySlopeMutableXGates,
    EncodedBit.GateSpec.stepList_append]
  rw [show xSavedRegistersAt output control P =
      framedProductRegisters control (inputPublicWordsAt output P)
        (slopeInversionRegisters P) zeroProductData (xSavedTail P) false by
    rfl]
  rw [hmultiplier', hmultiplicand', hproduct', hclearMultiplier',
    hclearMultiplicand']
  rfl

/-- Carrier after reloading the slope for subtracting `slope * x`. -/
def ySubtractSlopeMultiplierData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { ySlopeMutableXData P with
    multiplier := ParameterizedPointAddition.slopeValue P }

/-- Operands for subtracting `slope * x` from the first y product. -/
def ySubtractSlopeXOperandsData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { ySubtractSlopeMultiplierData P with
    multiplicand := ParameterizedPointAddition.xScratch P }

/-- Carrier after the reversed multiplication ledger has subtracted
`slope * x`. -/
def ySubtractSlopeXAccumulatedData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  ParameterizedPointAddition.Workspace.subtractProduct
    (ySubtractSlopeXOperandsData P)

/-- The second y product after clearing its slope operand. -/
def ySubtractSlopeXMultiplierClearedData
    (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { ySubtractSlopeXAccumulatedData P with multiplier := 0 }

/-- Clean carrier containing `slope * P.x - slope * x`. -/
def yBeforePublicSubtractionData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { ySubtractSlopeXMultiplierClearedData P with multiplicand := 0 }

/-- State immediately before subtracting the public mutable y-coordinate. -/
def yBeforePublicSubtractionRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (slopeInversionRegisters P) (yBeforePublicSubtractionData P)
    (xSavedTail P) false

/-- The reversed multiplication route subtracts `slope * x` and then clears
both reloaded operands. -/
theorem subtractSlopeXGates_ySlopeMutableX
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList subtractSlopeXGates
        (ySlopeMutableXRegistersAt output control P) =
      yBeforePublicSubtractionRegistersAt output control P := by
  have hslope :
      ParameterizedPointAddition.Workspace.slopeThinPort.read
          (xSavedTail P).1 =
        Arithmetic.ModularDivision.residueWord
          (ParameterizedPointAddition.slopeValue P) := by
    rfl
  have hx :
      ParameterizedPointAddition.Workspace.xThinPort.read (xSavedTail P).1 =
        Arithmetic.ModularDivision.residueWord
          (ParameterizedPointAddition.xScratch P) := by
    rw [xSavedTail,
      ParameterizedPointAddition.Workspace.xThinPort.read_set,
      xCoordinateData_accumulator]
  have hmultiplier := thinToMultiplierGates_set_of_clean
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySlopeMutableXData P) (xSavedTail P) false
    (ParameterizedPointAddition.slopeValue P) hslope
    (by simp [ySlopeMutableXData, ySlopeMutableXMultiplierClearedData,
      ySlopeMutableXAccumulatedData, ySlopeMutableXOperandsData,
      ySlopeMultiplierData, zeroProductData,
      Arithmetic.VariableModularMul.Data.addProduct])
  have hmultiplicand := thinToMultiplicandGates_set_of_clean
    ParameterizedPointAddition.Workspace.xThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySubtractSlopeMultiplierData P) (xSavedTail P) false
    (ParameterizedPointAddition.xScratch P) hx
    (by simp [ySubtractSlopeMultiplierData, ySlopeMutableXData,
      ySlopeMutableXMultiplierClearedData])
  have hsubtract := liftSharedMultiplicationGates_reverse_clean control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySubtractSlopeXOperandsData P) (xSavedTail P) false
  have hclearMultiplier := thinToMultiplierGates_set_zero_of_equal
    ParameterizedPointAddition.Workspace.slopeThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySubtractSlopeXAccumulatedData P) (xSavedTail P) false
    (ParameterizedPointAddition.slopeValue P) hslope (by rfl)
  have hclearMultiplicand := thinToMultiplicandGates_set_zero_of_equal
    ParameterizedPointAddition.Workspace.xThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (ySubtractSlopeXMultiplierClearedData P) (xSavedTail P) false
    (ParameterizedPointAddition.xScratch P) hx (by rfl)
  have hmultiplier' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplierPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (ySlopeMutableXData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySubtractSlopeMultiplierData P)
          (xSavedTail P) false := by
    simpa [ySubtractSlopeMultiplierData] using hmultiplier
  have hmultiplicand' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.xThinPort
            ParameterizedPointAddition.Workspace.productMultiplicandPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (ySubtractSlopeMultiplierData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySubtractSlopeXOperandsData P)
          (xSavedTail P) false := by
    simpa [ySubtractSlopeXOperandsData] using hmultiplicand
  have hsubtract' :
      EncodedBit.GateSpec.stepList
          (liftAuxGates
            (ParameterizedPointAddition.Workspace.sharedProductGates
              ParameterizedPointAddition.Workspace.multiplicationGates).reverse)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (ySubtractSlopeXOperandsData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySubtractSlopeXAccumulatedData P)
          (xSavedTail P) false := by
    simpa [ySubtractSlopeXAccumulatedData] using hsubtract
  have hclearMultiplier' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.slopeThinPort
            ParameterizedPointAddition.Workspace.productMultiplierPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (ySubtractSlopeXAccumulatedData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (ySubtractSlopeXMultiplierClearedData P)
          (xSavedTail P) false := by
    simpa [ySubtractSlopeXMultiplierClearedData] using hclearMultiplier
  have hclearMultiplicand' :
      EncodedBit.GateSpec.stepList
          (thinToProductGates ParameterizedPointAddition.Workspace.xThinPort
            ParameterizedPointAddition.Workspace.productMultiplicandPort)
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P)
            (ySubtractSlopeXMultiplierClearedData P) (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (yBeforePublicSubtractionData P)
          (xSavedTail P) false := by
    simpa [yBeforePublicSubtractionData] using hclearMultiplicand
  simp only [subtractSlopeXGates, EncodedBit.GateSpec.stepList_append]
  rw [show ySlopeMutableXRegistersAt output control P =
      framedProductRegisters control (inputPublicWordsAt output P)
        (slopeInversionRegisters P) (ySlopeMutableXData P) (xSavedTail P)
        false by rfl]
  rw [hmultiplier', hmultiplicand', hsubtract', hclearMultiplier',
    hclearMultiplicand']
  rfl

/-- Final y-coordinate value before it is moved into its thin saved word. -/
def yCoordinateData (P : GenericPointAddition.Input E Q) :
    Arithmetic.VariableModularMul.Data :=
  { yBeforePublicSubtractionData P with
    multiplicand := 0
    accumulator := (yBeforePublicSubtractionData P).accumulator - P.1.y }

/-- Tail retaining both computed affine coordinates. -/
def ySavedTail (P : GenericPointAddition.Input E Q) :
    ParameterizedPointAddition.Workspace.ThinRegisters ×
      ParameterizedPointAddition.Workspace.OutputRegisters :=
  (ParameterizedPointAddition.Workspace.yThinPort.set (xSavedTail P).1
      (Arithmetic.ModularDivision.residueWord
        (yCoordinateData P).accumulator),
    (xSavedTail P).2)

/-- Clean direct carrier at the end of the forward affine computation. -/
def computedRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  framedProductRegisters control (inputPublicWordsAt output P)
    (slopeInversionRegisters P) zeroProductData (ySavedTail P) false

@[simp] theorem yCoordinateData_accumulator
    (P : GenericPointAddition.Input E Q) :
    (yCoordinateData P).accumulator =
      ParameterizedPointAddition.yScratch P := by
  simp [yCoordinateData, yBeforePublicSubtractionData,
    ySubtractSlopeXMultiplierClearedData, ySubtractSlopeXAccumulatedData,
    ySubtractSlopeXOperandsData, ySubtractSlopeMultiplierData,
    ySlopeMutableXData, ySlopeMutableXMultiplierClearedData,
    ySlopeMutableXAccumulatedData, ySlopeMutableXOperandsData,
    ySlopeMultiplierData, ParameterizedPointAddition.Workspace.subtractProduct,
    Arithmetic.VariableModularMul.Data.addProduct, zeroProductData,
    ParameterizedPointAddition.yScratch]

/-- The y-coordinate schedule computes `slope * P.x - slope * x - P.y`, saves
the result, and restores the sole product carrier. -/
theorem yCoordinateGates_xSaved
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList yCoordinateGates
        (xSavedRegistersAt output control P) =
      computedRegistersAt output control P := by
  have hmodulus : 1 < params.modulus.val :=
    (Fact.out : params.modulus.val.Prime).one_lt
  have hsubtractPublic := subtractPublicGates_clean
    (PointAddition.PortFrame.mutableYPublicPort params.width) control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (yBeforePublicSubtractionData P) (xSavedTail P) false P.1.y hmodulus
    (mutableYPublicPort_read_inputPublicWordsAt output P)
    (by simp [yBeforePublicSubtractionData,
      ySubtractSlopeXMultiplierClearedData, ySubtractSlopeXAccumulatedData,
      ySubtractSlopeXOperandsData, ySubtractSlopeMultiplierData,
      ySlopeMutableXData, ySlopeMutableXMultiplierClearedData,
      ySlopeMutableXAccumulatedData, ySlopeMutableXOperandsData,
      ySlopeMultiplierData, ParameterizedPointAddition.Workspace.subtractProduct,
      Arithmetic.VariableModularMul.Data.addProduct, zeroProductData])
    (by simp [yBeforePublicSubtractionData])
  have hsave := moveAccumulatorToThinGates_clean
    ParameterizedPointAddition.Workspace.yThinPort control
    (inputPublicWordsAt output P) (slopeInversionRegisters P)
    (yCoordinateData P) (xSavedTail P) false (by rfl)
  have hsubtractPublic' :
      EncodedBit.GateSpec.stepList
          (subtractPublicGates
            (PointAddition.PortFrame.mutableYPublicPort params.width))
          (framedProductRegisters control (inputPublicWordsAt output P)
            (slopeInversionRegisters P) (yBeforePublicSubtractionData P)
            (xSavedTail P) false) =
        framedProductRegisters control (inputPublicWordsAt output P)
          (slopeInversionRegisters P) (yCoordinateData P) (xSavedTail P)
          false := by
    simpa [yCoordinateData] using hsubtractPublic
  simp only [yCoordinateGates, EncodedBit.GateSpec.stepList_append]
  rw [multiplySlopeMutableXGates_xSaved,
    subtractSlopeXGates_ySlopeMutableX]
  unfold yBeforePublicSubtractionRegistersAt
  rw [hsubtractPublic', hsave]
  simp [computedRegistersAt, ySavedTail, yCoordinateData,
    yBeforePublicSubtractionData, ySubtractSlopeXMultiplierClearedData,
    ySubtractSlopeXAccumulatedData, ySubtractSlopeXOperandsData,
    ySubtractSlopeMultiplierData, ySlopeMutableXData,
    ySlopeMutableXMultiplierClearedData, ySlopeMutableXAccumulatedData,
    ySlopeMutableXOperandsData, ySlopeMultiplierData,
    ParameterizedPointAddition.Workspace.subtractProduct,
    Arithmetic.VariableModularMul.Data.addProduct, zeroProductData]

/-- The complete direct forward schedule computes the two generic affine
coordinates while retaining every public input and restoring its single
product carrier. -/
theorem computeGates_initial
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList computeGates
        (initialRegistersAt output control P) =
      computedRegistersAt output control P := by
  simp only [computeGates, EncodedBit.GateSpec.stepList_append]
  rw [denominatorGates_initial, numeratorGates_denominatorReady,
    divisionAndSaveGates_divisionReady, xCoordinateGates_slopeSaved,
    yCoordinateGates_xSaved]

end

end DirectSchedule
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
