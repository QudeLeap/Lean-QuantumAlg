/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.StructuredCircuit
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Workspace

/-!
# Width-parameterized affine point addition

The arithmetic carrier for parameterized affine point addition is the direct
physical workspace in `Workspace`: one Kaliski inversion prefix, one shared
variable modular multiply-accumulate carrier, four saved field words, and the
output suffix.  There is no logical arithmetic bank, temporal workspace epoch,
or compatibility addressing layer.

The generic pipeline owns source-dependent routing into this workspace.  This
module owns the canonical carrier names and the field-level result formulas
used to state that pipeline's clean compute endpoint.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ParameterizedPointAddition

open Nat.FixedWidth

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

/-! ## Canonical physical workspace -/

/-- The direct variable modular multiply-accumulate carrier used by every
division and later arithmetic stage. -/
abbrev ProductRegisters := Workspace.ProductRegisters

/-- The four field words that survive a reset of the product carrier. -/
abbrev ThinRegisters := Workspace.ThinRegisters

/-- The complete direct physical point-addition workspace. -/
abbrev RawRegisters := Workspace.RawRegisters

/-- Canonical direct-workspace encoding. -/
abbrev rawEncoding : BinaryLabelEncoding RawRegisters := Workspace.rawEncoding

/-- Input-independent clean direct workspace. -/
abbrev blankRegisters : RawRegisters := Workspace.blankRegisters

/-- The actual direct product carrier inside the workspace. -/
abbrev productEncoding : BinaryLabelEncoding ProductRegisters :=
  Workspace.productEncoding

/-- The retained output suffix encoding. -/
abbrev outputEncoding : BinaryLabelEncoding Workspace.OutputRegisters :=
  Workspace.outputEncoding

/-- The physical numerator word used by the shared division/product route. -/
abbrev divisionNumeratorPort := Workspace.divisionNumeratorPort

/-- The physical quotient word produced by the shared division/product route. -/
abbrev divisionQuotientPort := Workspace.divisionQuotientPort

/-- The preserved numerator word used when the shared product carrier is
recycled after division. -/
abbrev numeratorScratchPort := Workspace.numeratorScratchPort

/-- The saved affine slope word. -/
abbrev slopePort := Workspace.slopePort

/-- The saved affine x-coordinate word. -/
abbrev xPort := Workspace.xPort

/-- The saved affine y-coordinate word. -/
abbrev yPort := Workspace.yPort

/-- The retained direct-workspace x result/output word. -/
abbrev outputXPort := Workspace.retainedOutputXPort

/-- The retained direct-workspace y result/output word. -/
abbrev outputYPort := Workspace.retainedOutputYPort

/-- Direct physical division, with its product stage on the one shared
carrier. -/
abbrev divisionGates : List (EncodedBit.GateSpec rawEncoding) :=
  Workspace.divisionGates

/-- Circuit compiled from the literal direct physical division ledger. -/
def divisionProgram : UnitaryCircuit (Qubits rawEncoding.width) :=
  EncodedBit.GateSpec.programList divisionGates

/-- Folded basis-state action of the literal direct division route. -/
def divisionStep : RawRegisters → RawRegisters :=
  EncodedBit.GateSpec.stepList divisionGates

/-- The compiled direct division program realizes its displayed gate ledger. -/
theorem divisionProgram_realizes :
    UnitaryCircuit.Realizes rawEncoding divisionProgram divisionStep :=
  EncodedBit.GateSpec.realizesList divisionGates

/-- Exact primitive length of the direct division route. -/
theorem divisionGates_length :
    divisionGates.length =
      2 * Arithmetic.ModularInversion.gates.length + 2 * params.width +
        Arithmetic.VariableModularMulSchedule.gates.length :=
  Workspace.divisionGates_length

/-- Exact CNOT coordinate of the direct division route. -/
theorem divisionGates_cnotMultiplicity_sum :
    (divisionGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * (Arithmetic.ModularInversion.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum + 2 * params.width +
        (Arithmetic.VariableModularMulSchedule.gates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum :=
  Workspace.divisionGates_cnotMultiplicity_sum

/-- Exact Toffoli coordinate of the direct division route. -/
theorem divisionGates_toffoliMultiplicity_sum :
    (divisionGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * (Arithmetic.ModularInversion.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum +
        (Arithmetic.VariableModularMulSchedule.gates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum :=
  Workspace.divisionGates_toffoliMultiplicity_sum

/-- Width-only primitive-event bound of the direct division route. -/
theorem divisionGates_length_le :
    divisionGates.length ≤ Workspace.divisionGateLengthBound :=
  Workspace.divisionGates_length_le

/-- Width-only CNOT bound of the direct division route. -/
theorem divisionGates_cnotMultiplicity_sum_le :
    (divisionGates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      Workspace.divisionCnotBound :=
  Workspace.divisionGates_cnotMultiplicity_sum_le

/-- Width-only Toffoli bound of the direct division route. -/
theorem divisionGates_toffoliMultiplicity_sum_le :
    (divisionGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      Workspace.divisionToffoliBound :=
  Workspace.divisionGates_toffoliMultiplicity_sum_le

/-- Direct variable-multiplication gates before their lift to the complete
point-addition workspace. -/
abbrev multiplicationGates := Workspace.multiplicationGates

/-- Direct selected-add gates before their lift to the complete workspace. -/
abbrev selectedAdditionGates := Workspace.selectedAdditionGates

/-- The literal lift of a shared-product subprogram through the unchanged
inversion prefix and retained tail. -/
abbrev sharedProductGates := Workspace.sharedProductGates

/-- Exact physical width of one direct parameterized point-addition
workspace. -/
theorem rawEncoding_width_exact :
    rawEncoding.width =
      Arithmetic.ModularInversion.physicalWidthFor params.width +
        13 * params.width + 7 :=
  Workspace.rawEncoding_width_exact

/-! ## Field-level clean-compute specification -/

variable {E : PrimeFieldShortWeierstrass params.modulus.val}
  [Fact params.modulus.val.Prime]
  {Q : AffinePoint E}

/-- Canonical `f`-bit representative of one field residue. -/
abbrev residueWord (value : ZMod params.modulus.val) : Word params.width :=
  Arithmetic.ModularDivision.residueWord value

omit [Fact params.modulus.val.Prime] in
@[simp] theorem residueWord_val (value : ZMod params.modulus.val) :
    (residueWord value).val = value.val :=
  rfl

@[simp] theorem residueWord_zero : residueWord (0 : ZMod params.modulus.val) = 0 := by
  apply Fin.ext
  simp [residueWord]

/-- Division datum for the generic affine slope.  Its numerator is placed in
the shared product multiplier and its denominator in the Kaliski prefix. -/
def slopeDivisionData (P : GenericPointAddition.Input E Q) :
    MAU.Division.Data params.modulus.val where
  denominator := genericAddDenominatorUnit P.1 Q P.2
  numerator := genericAddNumerator P.1 Q
  target := 0
  flag := false

/-- Generic affine slope associated with the input point and fixed addend. -/
def slopeValue (P : GenericPointAddition.Input E Q) : ZMod params.modulus.val :=
  genericAddSlope E P.1 Q

/-- Field value of the generic affine output x-coordinate. -/
def xScratch (P : GenericPointAddition.Input E Q) :
    ZMod params.modulus.val :=
  slopeValue P * slopeValue P - P.1.x - Q.x

/-- Field value of the generic affine output y-coordinate. -/
def yScratch (P : GenericPointAddition.Input E Q) :
    ZMod params.modulus.val :=
  slopeValue P * P.1.x - slopeValue P * xScratch P - P.1.y

theorem xScratch_eq_genericAddXFromSlope
    (P : GenericPointAddition.Input E Q) :
    xScratch P = genericAddXFromSlope E P.1 Q (slopeValue P) := by
  simp [xScratch, slopeValue, genericAddXFromSlope,
    PrimeFieldShortWeierstrass.toWeierstrassCurve]
  ring

theorem yScratch_eq_genericAddYFromSlope
    (P : GenericPointAddition.Input E Q) :
    yScratch P = genericAddYFromSlope E P.1 Q (slopeValue P) := by
  simp [yScratch, xScratch, slopeValue, genericAddYFromSlope,
    PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  ring

theorem xScratch_eq_genericAddX
    (P : GenericPointAddition.Input E Q) :
    xScratch P = genericAddX E P.1 Q := by
  rw [xScratch_eq_genericAddXFromSlope]
  rfl

theorem yScratch_eq_genericAddY
    (P : GenericPointAddition.Input E Q) :
    yScratch P = genericAddY E P.1 Q := by
  rw [yScratch_eq_genericAddYFromSlope]
  rfl

/-!
The direct carrier deliberately does not recreate the old source-dependent
seven-bank seed.  The successor of the old `computeGates` endpoint is the
generic pipeline's direct preload/compute/copy/uncompute protocol: it loads
the numerator and denominator into `divisionNumeratorPort` and the inversion
ports, preserves the numerator through `numeratorScratchPort`, and exposes
the two computed words at `xPort` and `yPort`.  Its literal routing and clean
correctness theorem must be changed together with `GenericPipeline`; keeping
the old bank theorem here would assert a false physical layout.
-/

end

end ParameterizedPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
