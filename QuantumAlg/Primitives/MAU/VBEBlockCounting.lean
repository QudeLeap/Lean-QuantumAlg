/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularAddition

/-!
# VBE block-counting model for modular addition

This module records the source-facing block inventory used before assigning
gate-level constants to the Vedral--Barenco--Ekert modular-arithmetic route.
The VBE paper gives the plain-adder, modular-adder, and controlled modular-add
composition textually [VBE95, 9511018.tex:218-370] and records the linear
gate-count scaling and register footprint [VBE95, 9511018.tex:419-459]. It does
not give gate-level constants in the text.  We therefore keep primitive carry,
sum, copy, and controlled-load block costs as explicit inputs and derive only
the block-composition upper bounds from the registered source.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularAddition

/-! ### VBE block inventory -/

namespace VBECounting

/-- Primitive gate basis selected for the VBE modular-addition counting model.

The current standard basis counts Toffoli and CNOT gates as primitive named
blocks, following the source discussion of basic gates and the note that
Toffoli may alternatively be simulated by six CNOT gates [VBE95,
9511018.tex:575-583, 423-433]. -/
inductive PrimitiveGateModel where
  /-- Count Toffoli and CNOT gates directly. -/
  | toffoliCNOT
deriving DecidableEq

namespace PrimitiveGateModel

/-- Resource profile for one CNOT in the selected modular-arithmetic model. -/
def cnotProfile : PrimitiveGateModel → ModularArithmeticResourceProfile
  | .toffoliCNOT =>
      { ModularArithmeticResourceProfile.zero with
        logicalQubits := 2
        dataQubits := 2
        cnotGates := 1
        circuitDepth := 1 }

/-- Resource profile for one Toffoli in the selected modular-arithmetic model. -/
def toffoliProfile : PrimitiveGateModel → ModularArithmeticResourceProfile
  | .toffoliCNOT =>
      { ModularArithmeticResourceProfile.zero with
        logicalQubits := 3
        dataQubits := 3
        toffoliGates := 1
        circuitDepth := 1
        toffoliDepth := 1 }

end PrimitiveGateModel

/-- Primitive source blocks used by the VBE ADD/modular-ADD counting model.

The fields are profiles rather than fixed constants because the registered VBE
TeX source specifies the route and scaling, while the exact gate-level
realization of the carry/sum/control-load drawings must be supplied by a
separate source-backed or Lean-counted primitive gate model. -/
structure PrimitiveBlockProfiles where
  /-- Basic carry block from the VBE plain-adder figure. -/
  carryBlock : ModularArithmeticResourceProfile
  /-- Basic sum block from the VBE plain-adder figure. -/
  sumBlock : ModularArithmeticResourceProfile
  /-- One overflow-copy/reset control operation. -/
  overflowCopyBlock : ModularArithmeticResourceProfile
  /-- One register-bit rewrite controlled by the modular-adder overflow flag. -/
  conditionalRegisterRewriteBit : ModularArithmeticResourceProfile
  /-- One controlled constant-load/unload bit in the controlled modular-add
  stage used by controlled modular multiplication. -/
  controlledConstantLoadBit : ModularArithmeticResourceProfile

namespace PrimitiveBlockProfiles

/-- Predicate recording that primitive block costs come from the selected VBE
primitive gate model rather than arbitrary caller-supplied profiles. -/
structure SourceBacked (model : PrimitiveGateModel)
    (blocks : PrimitiveBlockProfiles) : Prop where
  /-- The carry block profile is exactly the selected conservative primitive
  model: two Toffoli gates and two CNOT gates. This is a Lean-side primitive
  decomposition policy for the VBE carry drawing, not a claim that the TeX text
  enumerates this count. -/
  carry_eq :
    blocks.carryBlock =
      ModularArithmeticResourceProfile.sequential
        (ModularArithmeticResourceProfile.repeatSequential 2 model.toffoliProfile)
        (ModularArithmeticResourceProfile.repeatSequential 2 model.cnotProfile)
  /-- The sum block profile is exactly the selected conservative primitive
  model: two CNOT gates. -/
  sum_eq :
    blocks.sumBlock =
      ModularArithmeticResourceProfile.repeatSequential 2 model.cnotProfile
  /-- Copying or resetting the overflow flag is modeled as exactly one CNOT
  gate in the selected primitive policy. -/
  overflowCopy_eq :
    blocks.overflowCopyBlock = model.cnotProfile
  /-- Rewriting one classically known register bit under the overflow flag is
  modeled as exactly one CNOT gate in the selected primitive policy. -/
  conditionalRegisterRewriteBit_eq :
    blocks.conditionalRegisterRewriteBit = model.cnotProfile
  /-- Loading or unloading one controlled constant bit is modeled as exactly one
  Toffoli gate, matching the VBE controlled-load operation. -/
  controlledConstantLoadBit_eq :
    blocks.controlledConstantLoadBit = model.toffoliProfile

/-- Standard primitive block profiles for the current VBE gate model.  The
profile values are conservative upper-bound blocks; route-level repetition and
composition are handled by `plainAdderProfile`, `modularAdderProfile`, and
`controlledModularAdditionStepProfile`. -/
def standardPrimitiveProfiles (model : PrimitiveGateModel) :
    PrimitiveBlockProfiles where
  carryBlock :=
    ModularArithmeticResourceProfile.sequential
      (ModularArithmeticResourceProfile.repeatSequential 2 model.toffoliProfile)
      (ModularArithmeticResourceProfile.repeatSequential 2 model.cnotProfile)
  sumBlock := ModularArithmeticResourceProfile.repeatSequential 2 model.cnotProfile
  overflowCopyBlock := model.cnotProfile
  conditionalRegisterRewriteBit := model.cnotProfile
  controlledConstantLoadBit := model.toffoliProfile

/-- The standard primitive block package is source-routed and no longer lets
downstream code choose synthetic zero-cost primitive profiles. -/
theorem standardPrimitiveProfiles_sourceBacked (model : PrimitiveGateModel) :
    SourceBacked model (standardPrimitiveProfiles model) where
  carry_eq := rfl
  sum_eq := rfl
  overflowCopy_eq := rfl
  conditionalRegisterRewriteBit_eq := rfl
  controlledConstantLoadBit_eq := rfl

/-- Conservative upper-bound profile for the VBE plain adder.

VBE first computes carries, then performs the corresponding sums while undoing
the carry operations except the leading carry [VBE95, 9511018.tex:244-264,
591-604].  We use `n` carry blocks for the forward pass, `n` sum blocks, and
`n` carry-block costs for the reverse pass; this is a source-aligned upper
bound, not a claim that every pass uses exactly `n` distinct carry blocks. -/
def plainAdderProfile (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential
    (ModularArithmeticResourceProfile.repeatSequential n blocks.carryBlock)
    (ModularArithmeticResourceProfile.sequential
      (ModularArithmeticResourceProfile.repeatSequential n blocks.sumBlock)
      (ModularArithmeticResourceProfile.repeatSequential n blocks.carryBlock))

/-- Conservative upper-bound profile for VBE modular addition.

The source route uses the first two add/subtract networks, a third plain adder
after the overflow-controlled register rewrite, and the last two blocks to
restore the temporary overflow bit [VBE95, 9511018.tex:295-328, 631-642].
The `5` factor counts these five plain-adder/subtractor-shaped blocks.  The
`2 * n` bit rewrites cover the before/after arrows around the third plain
adder, and the two overflow-copy blocks cover recording and resetting `t`. -/
def modularAdderProfile (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential
    (ModularArithmeticResourceProfile.repeatSequential 5
      (blocks.plainAdderProfile n))
    (ModularArithmeticResourceProfile.sequential
      (ModularArithmeticResourceProfile.repeatSequential (2 * n)
        blocks.conditionalRegisterRewriteBit)
      (ModularArithmeticResourceProfile.repeatSequential 2
        blocks.overflowCopyBlock))

/-- Conservative upper-bound profile for one VBE controlled modular-addition
stage.

For the `i`th controlled-multiplication stage, VBE loads either `2^i a` or `0`
into the first register using Toffoli controls, applies modular addition, and
then undoes the same controlled load [VBE95, 9511018.tex:333-367, 655-664].
The `2 * n` bit-load bound covers load and unload for an `n`-bit constant. -/
def controlledModularAdditionStepProfile
    (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential
    (ModularArithmeticResourceProfile.repeatSequential (2 * n)
      blocks.controlledConstantLoadBit)
    (blocks.modularAdderProfile n)

/-- Turn the modular-adder block-count upper bound into the formula-parameter
shape consumed by the reusable `ADD_N` resource API. -/
def modularAdderFormulaParameters
    (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    ResourceParameters.PublicBaselineBounds.FormulaParameters where
  width := n
  workQubitBound := (blocks.modularAdderProfile n).workQubits
  toffoliGateBound := (blocks.modularAdderProfile n).toffoliGates
  tGateBound := (blocks.modularAdderProfile n).tGates
  cnotGateBound := (blocks.modularAdderProfile n).cnotGates
  singleQubitGateBound := (blocks.modularAdderProfile n).singleQubitGates
  circuitDepthBound := (blocks.modularAdderProfile n).circuitDepth
  toffoliDepthBound := (blocks.modularAdderProfile n).toffoliDepth

/-- Turn the controlled modular-addition stage bound into the formula-parameter
shape used by downstream MAC/modular-multiplication packages. -/
def controlledAdderFormulaParameters
    (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    ResourceParameters.PublicBaselineBounds.FormulaParameters where
  width := n
  workQubitBound := (blocks.controlledModularAdditionStepProfile n).workQubits
  toffoliGateBound := (blocks.controlledModularAdditionStepProfile n).toffoliGates
  tGateBound := (blocks.controlledModularAdditionStepProfile n).tGates
  cnotGateBound := (blocks.controlledModularAdditionStepProfile n).cnotGates
  singleQubitGateBound :=
    (blocks.controlledModularAdditionStepProfile n).singleQubitGates
  circuitDepthBound := (blocks.controlledModularAdditionStepProfile n).circuitDepth
  toffoliDepthBound :=
    (blocks.controlledModularAdditionStepProfile n).toffoliDepth

@[simp] theorem modularAdderFormulaParameters_width
    (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    (blocks.modularAdderFormulaParameters n).width = n :=
  rfl

@[simp] theorem controlledAdderFormulaParameters_width
    (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    (blocks.controlledAdderFormulaParameters n).width = n :=
  rfl

@[simp] theorem modularAdderFormulaParameters_workQubitBound
    (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    (blocks.modularAdderFormulaParameters n).workQubitBound =
      (blocks.modularAdderProfile n).workQubits :=
  rfl

@[simp] theorem controlledAdderFormulaParameters_workQubitBound
    (blocks : PrimitiveBlockProfiles) (n : ℕ) :
    (blocks.controlledAdderFormulaParameters n).workQubitBound =
      (blocks.controlledModularAdditionStepProfile n).workQubits :=
  rfl

/-! ### Standard VBE package for downstream MAU resources -/

/-- Standard VBE primitive block package in the Toffoli/CNOT primitive model. -/
def standardBlocks : PrimitiveBlockProfiles :=
  standardPrimitiveProfiles .toffoliCNOT

/-- The standard VBE primitive block package is exact in the selected primitive
policy and cannot be replaced by caller-supplied synthetic profiles. -/
private theorem standardBlocks_sourceBacked :
    SourceBacked .toffoliCNOT standardBlocks :=
  standardPrimitiveProfiles_sourceBacked .toffoliCNOT

/-- Standard VBE modular-adder block-composition profile. -/
def standardModularAdderProfile (n : ℕ) : ModularArithmeticResourceProfile :=
  standardBlocks.modularAdderProfile n

/-- Standard VBE controlled modular-addition step profile. -/
def standardControlledAdderStepProfile (n : ℕ) :
    ModularArithmeticResourceProfile :=
  standardBlocks.controlledModularAdditionStepProfile n

/-- Formula parameters for the standard VBE modular-adder package. -/
def standardModularAdderFormulaParameters (n : ℕ) :
    ResourceParameters.PublicBaselineBounds.FormulaParameters :=
  standardBlocks.modularAdderFormulaParameters n

/-- Formula parameters for the standard VBE controlled-addition package used by
MAC and modular multiplication. -/
def standardControlledAdderFormulaParameters (n : ℕ) :
    ResourceParameters.PublicBaselineBounds.FormulaParameters :=
  standardBlocks.controlledAdderFormulaParameters n

@[simp] theorem standardModularAdderFormulaParameters_width (n : ℕ) :
    (standardModularAdderFormulaParameters n).width = n :=
  rfl

@[simp] theorem standardControlledAdderFormulaParameters_width (n : ℕ) :
    (standardControlledAdderFormulaParameters n).width = n :=
  rfl

end PrimitiveBlockProfiles

/-! ### ADD and controlled-ADD resource functions -/

/-- Source-backed VBE ADD formula parameters for an `n`-bit modular adder. -/
def vbeADDFormulaParameters (n : ℕ) :
    ResourceParameters.PublicBaselineBounds.FormulaParameters :=
  PrimitiveBlockProfiles.standardModularAdderFormulaParameters n

/-- Source-backed VBE controlled-ADD step formula parameters for MAC and
modular-multiplication packages. -/
def vbeControlledADDStepFormulaParameters (n : ℕ) :
    ResourceParameters.PublicBaselineBounds.FormulaParameters :=
  PrimitiveBlockProfiles.standardControlledAdderFormulaParameters n

/-- Canonical VBE `ADD_N` resource parameters, obtained directly from the
source-backed formula package. -/
def vbeADDResourceParameters (n : ℕ) : ResourceParameters where
  workQubits := (vbeADDFormulaParameters n).workQubitBound
  toffoliGates := (vbeADDFormulaParameters n).toffoliGateBound
  tGates := (vbeADDFormulaParameters n).tGateBound
  cnotGates := (vbeADDFormulaParameters n).cnotGateBound
  singleQubitGates := (vbeADDFormulaParameters n).singleQubitGateBound
  circuitDepth := (vbeADDFormulaParameters n).circuitDepthBound
  toffoliDepth := (vbeADDFormulaParameters n).toffoliDepthBound

/-- Canonical VBE controlled-ADD step resource parameters, obtained directly
from the source-backed formula package. -/
def vbeControlledADDStepResourceParameters (n : ℕ) : ResourceParameters where
  workQubits := (vbeControlledADDStepFormulaParameters n).workQubitBound
  toffoliGates := (vbeControlledADDStepFormulaParameters n).toffoliGateBound
  tGates := (vbeControlledADDStepFormulaParameters n).tGateBound
  cnotGates := (vbeControlledADDStepFormulaParameters n).cnotGateBound
  singleQubitGates := (vbeControlledADDStepFormulaParameters n).singleQubitGateBound
  circuitDepth := (vbeControlledADDStepFormulaParameters n).circuitDepthBound
  toffoliDepth := (vbeControlledADDStepFormulaParameters n).toffoliDepthBound

/-- The VBE ADD formula parameters are supplied by the standard source-routed
block package. -/
private theorem vbeADDFormulaParameters_sourceBacked (n : ℕ) :
    vbeADDFormulaParameters n =
      PrimitiveBlockProfiles.standardBlocks.modularAdderFormulaParameters n :=
  rfl

/-- The VBE controlled-ADD formula parameters are supplied by the standard
source-routed block package. -/
private theorem vbeControlledADDStepFormulaParameters_sourceBacked (n : ℕ) :
    vbeControlledADDStepFormulaParameters n =
      PrimitiveBlockProfiles.standardBlocks.controlledAdderFormulaParameters n :=
  rfl

@[simp] theorem vbeADDFormulaParameters_width (n : ℕ) :
    (vbeADDFormulaParameters n).width = n :=
  rfl

@[simp] theorem vbeControlledADDStepFormulaParameters_width (n : ℕ) :
    (vbeControlledADDStepFormulaParameters n).width = n :=
  rfl

/-- The canonical VBE `ADD_N` parameters satisfy their source-backed public
baseline bounds without caller-supplied field choices. -/
private theorem vbeADDSupportsPublicBaseline (n : ℕ) :
    ResourceParameters.SupportsPublicBaseline
      ((vbeADDResourceParameters n).toProfile n)
      (vbeADDFormulaParameters n).toPublicBaselineBounds := by
  exact
    ResourceParameters.supportsPublicBaseline_of_formulaBounds
      (n := n) (params := vbeADDResourceParameters n)
      (bounds := vbeADDFormulaParameters n)
      rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl

/-- The canonical VBE controlled-ADD step parameters satisfy their source-backed
public baseline bounds without caller-supplied field choices. -/
theorem vbeControlledADDSupportsPublicBaseline (n : ℕ) :
    ResourceParameters.SupportsPublicBaseline
      ((vbeControlledADDStepResourceParameters n).toProfile n)
      (vbeControlledADDStepFormulaParameters n).toPublicBaselineBounds := by
  exact
    ResourceParameters.supportsPublicBaseline_of_formulaBounds
      (n := n) (params := vbeControlledADDStepResourceParameters n)
      (bounds := vbeControlledADDStepFormulaParameters n)
      rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl

end VBECounting

end ModularAddition
end QuantumAlg
