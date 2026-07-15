/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
public import QuantumAlg.Primitives.MAU.ModularAddition.StructuredCircuit
public import QuantumAlg.Primitives.MAU.ModularDivision.StructuredCircuit
public import QuantumAlg.Primitives.MAU.ModularInversion.StructuredCircuit

/-!
# P-256 prime-field MAU bridge

This module fixes the prime-modulus residue-register encoding used when the
P-256 resource stack consumes modular-addition, modular-inversion, and
modular-division same-Circuit witnesses.  The bridge is deliberately
prime-field-specific: concrete power-of-two carry schedules remain separate
implementation support, while this API requires P-256 endpoint witnesses to act
on `ZMod P256DomainParameters.primeModulus` labels and to project correctness
and resources from the same folded circuit object.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve

namespace P256PrimeFieldBridge

noncomputable section

/-- The P-256 prime-field modulus used by the MAU bridge. -/
abbrev modulus : Nat :=
  P256DomainParameters.primeModulus

/-- The P-256 field-register width. -/
abbrev width : Nat :=
  P256DomainParameters.bitSize

/-- The P-256 prime field. -/
abbrev Field :=
  ZMod modulus

/-- The unit group of the P-256 prime field. -/
abbrev Unit :=
  (ZMod modulus)ˣ

/-- The P-256 modulus is positive. -/
theorem modulus_pos : 0 < modulus := by
  norm_num [modulus, P256DomainParameters.primeModulus]

/-- The P-256 modulus fits in the standard 256-bit field register. -/
theorem modulus_fits_width : modulus ≤ 2 ^ width := by
  norm_num [modulus, width, P256DomainParameters.primeModulus,
    P256DomainParameters.bitSize]

/-- Canonical binary residue encoding for P-256 field elements. -/
@[nolint defLemma]
def residueEncoding : BinaryResidueEncoding modulus width where
  modulus_pos := modulus_pos
  register_fits := modulus_fits_width

/-- Encoding a P-256 field element always produces a canonical register label. -/
theorem encode_isValid (z : Field) :
    residueEncoding.IsValid (residueEncoding.encode z) :=
  BinaryResidueEncoding.encode_isValid residueEncoding z

/-- P-256 canonical field labels decode back to the encoded field element. -/
theorem decode_encode (z : Field) :
    residueEncoding.decode (residueEncoding.encode z) = z :=
  BinaryResidueEncoding.decode_encode residueEncoding z

/-- Valid P-256 labels round-trip through decode and canonical re-encoding. -/
theorem encode_decode_of_valid
    (x : Fin (2 ^ width)) (hx : residueEncoding.IsValid x) :
    residueEncoding.encode (residueEncoding.decode x) = x :=
  BinaryResidueEncoding.encode_decode_of_valid residueEncoding x hx

/-! ## Prime-field modular-addition legs -/

/-- P-256 target-add field encoding. -/
def targetAddEncoding :
    BinaryLabelEncoding (ModularAddition.TargetAdd.Data modulus) :=
  ModularAddition.TargetAdd.encoding residueEncoding

/-- P-256 target-add-with-aux field encoding. -/
def targetAddWithAuxEncoding :
    BinaryLabelEncoding (ModularAddition.TargetAddWithAux.Data modulus) :=
  ModularAddition.TargetAddWithAux.encoding residueEncoding

/-- A P-256 target-add witness must use the P-256 prime-field encoding. -/
abbrev TargetAddWitness :=
  ModularAddition.TargetAdd.Witness residueEncoding

/-- A P-256 target-add-with-aux witness must use the P-256 prime-field encoding. -/
abbrev TargetAddWithAuxWitness :=
  ModularAddition.TargetAddWithAux.Witness residueEncoding

/-- Encoded-basis correctness for a P-256 target-add witness. -/
theorem targetAdd_apply_ket
    (w : TargetAddWitness) (x : ModularAddition.TargetAdd.Data modulus) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits targetAddEncoding.width)
          (targetAddEncoding.encode x) :
          PureState (Qubits targetAddEncoding.width)) :
          StateVector (Qubits targetAddEncoding.width)) =
      (PureState.ket (R := Qubits targetAddEncoding.width)
        (targetAddEncoding.encode (ModularAddition.TargetAdd.step x)) :
        StateVector (Qubits targetAddEncoding.width)) := by
  simpa [targetAddEncoding, ModularAddition.TargetAdd.Witness.sameCircuit] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit x

/-- Target-add resources are projected from the same P-256 circuit object used
for correctness. -/
theorem targetAdd_resources_eq (w : TargetAddWitness) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Target-add circuit depth is projected from the same P-256 circuit object
used for correctness. -/
theorem targetAdd_depth_eq (w : TargetAddWitness) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Target-add query depth is projected from the same P-256 circuit object used
for correctness. -/
theorem targetAdd_queryDepth_eq (w : TargetAddWitness) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

/-- Encoded-basis correctness for a P-256 target-add-with-aux witness. -/
theorem targetAddWithAux_apply_ket
    (w : TargetAddWithAuxWitness)
    (x : ModularAddition.TargetAddWithAux.Data modulus) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits targetAddWithAuxEncoding.width)
          (targetAddWithAuxEncoding.encode x) :
          PureState (Qubits targetAddWithAuxEncoding.width)) :
          StateVector (Qubits targetAddWithAuxEncoding.width)) =
      (PureState.ket (R := Qubits targetAddWithAuxEncoding.width)
        (targetAddWithAuxEncoding.encode
          (ModularAddition.TargetAddWithAux.step x)) :
        StateVector (Qubits targetAddWithAuxEncoding.width)) := by
  simpa [targetAddWithAuxEncoding,
    ModularAddition.TargetAddWithAux.Witness.sameCircuit] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit x

/-- Target-add-with-aux resources are projected from the same P-256 circuit
object used for correctness. -/
theorem targetAddWithAux_resources_eq (w : TargetAddWithAuxWitness) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Target-add-with-aux circuit depth is projected from the same P-256 circuit
object used for correctness. -/
theorem targetAddWithAux_depth_eq (w : TargetAddWithAuxWitness) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Target-add-with-aux query depth is projected from the same P-256 circuit
object used for correctness. -/
theorem targetAddWithAux_queryDepth_eq (w : TargetAddWithAuxWitness) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

/-! ## Prime-field inversion and division legs -/

/-- P-256 staged modular-inversion field encoding. -/
def inversionEncoding :
    BinaryLabelEncoding (ModularInversion.StageState modulus) :=
  ModularInversion.StageState.fieldEncoding residueEncoding

/-- P-256 modular-division pipeline field encoding. -/
def divisionEncoding :
    BinaryLabelEncoding (ModularDivision.PipelineState modulus) :=
  ModularDivision.PipelineState.fieldEncoding residueEncoding

/-- Decomposed P-256 modular-inversion witness over the prime-field encoding.
The inherited program is the same object used for clean correctness and
resource projection. -/
structure InversionWitness extends
    ModularInversion.DecomposedStageWitness modulus where
  /-- The witness acts on the P-256 prime-field encoding, not on a power-of-two
  modulus. -/
  encoding_eq : toDecomposedStageWitness.encoding = inversionEncoding

namespace InversionWitness

/-- Build a P-256 inversion witness from decomposed subprograms over the
prime-field encoding. -/
def ofFieldEncoding
    (computeProgram targetAddProgram : BaseGateProgram inversionEncoding.width)
    (computeRealizes :
      BaseGateProgram.Realizes inversionEncoding computeProgram
        ModularInversion.StageState.addInverseToScratch)
    (targetAddRealizes :
      BaseGateProgram.Realizes inversionEncoding targetAddProgram
        ModularInversion.StageState.addScratchToTarget) :
    InversionWitness where
  toDecomposedStageWitness :=
    ModularInversion.DecomposedStageWitness.ofFieldEncoding residueEncoding
      computeProgram targetAddProgram computeRealizes targetAddRealizes
  encoding_eq := rfl

/-- Same-Circuit witness induced by the decomposed P-256 inversion program. -/
def baseWitness (w : InversionWitness) :
    BaseGateSameCircuitWitness (ModularInversion.StageState modulus)
      (ModularInversion.decomposedStageStep (N := modulus)) :=
  w.toDecomposedStageWitness.baseWitness

/-- The decomposed P-256 inversion circuit history bottoms out in
X/CNOT/Toffoli atoms. -/
theorem structured (w : InversionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  ModularInversion.DecomposedStageWitness.structured
    w.toDecomposedStageWitness

/-- Clean encoded-basis action for the P-256 modular-inversion leg. -/
theorem apply_clean_ket (w : InversionWitness)
    (u : Unit) (z : Field) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (ModularInversion.StageState.initial u z)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := u
             target := z + ModularInversion.inverseResidue u
             inverseScratch := 0
             flag := false } : ModularInversion.StageState modulus)) :
        StateVector (Qubits w.encoding.width)) :=
  ModularInversion.DecomposedStageWitness.apply_clean_ket
    w.toDecomposedStageWitness u z

/-- P-256 inversion resources are projected from the same circuit object used
for correctness. -/
theorem resources_eq (w : InversionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  ModularInversion.DecomposedStageWitness.resources_eq
    w.toDecomposedStageWitness

/-- P-256 inversion circuit depth is projected from the same circuit object
used for correctness. -/
theorem depth_eq (w : InversionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  ModularInversion.DecomposedStageWitness.depth_eq
    w.toDecomposedStageWitness

/-- P-256 inversion query depth is projected from the same circuit object used
for correctness. -/
theorem queryDepth_eq (w : InversionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  ModularInversion.DecomposedStageWitness.queryDepth_eq
    w.toDecomposedStageWitness

end InversionWitness

/-- Resource-correct witness for clean P-256 modular inversion. -/
def inversionCleanResourceCorrectWitness (w : InversionWitness) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ u : Unit, ∀ z : Field,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (ModularInversion.StageState.initial u z)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ input := u
                 target := z + ModularInversion.inverseResidue u
                 inverseScratch := 0
                 flag := false } : ModularInversion.StageState modulus)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun u z => InversionWitness.apply_clean_ket w u z
  resources := ⟨InversionWitness.resources_eq w, InversionWitness.depth_eq w,
    InversionWitness.queryDepth_eq w⟩

/-- Decomposed P-256 modular-division witness over the prime-field encoding.
The inherited program is the same object used for clean correctness and
resource projection. -/
structure DivisionWitness extends
    ModularDivision.DecomposedPipelineWitness modulus where
  /-- The witness acts on the P-256 prime-field encoding, not on a power-of-two
  modulus. -/
  encoding_eq : toDecomposedPipelineWitness.encoding = divisionEncoding

namespace DivisionWitness

/-- Build a P-256 division witness from decomposed subprograms over the
prime-field encoding. -/
def ofFieldEncoding
    (inverseProgram productProgram targetAddProgram :
      BaseGateProgram divisionEncoding.width)
    (inverseRealizes :
      BaseGateProgram.Realizes divisionEncoding inverseProgram
        ModularDivision.PipelineState.addInverseToScratch)
    (productRealizes :
      BaseGateProgram.Realizes divisionEncoding productProgram
        ModularDivision.PipelineState.addProductToQuotientScratch)
    (targetAddRealizes :
      BaseGateProgram.Realizes divisionEncoding targetAddProgram
        ModularDivision.PipelineState.addQuotientToTarget) :
    DivisionWitness where
  toDecomposedPipelineWitness :=
    ModularDivision.DecomposedPipelineWitness.ofFieldEncoding residueEncoding
      inverseProgram productProgram targetAddProgram
      inverseRealizes productRealizes targetAddRealizes
  encoding_eq := rfl

/-- Same-Circuit witness induced by the decomposed P-256 division program. -/
def baseWitness (w : DivisionWitness) :
    BaseGateSameCircuitWitness (ModularDivision.PipelineState modulus)
      (ModularDivision.decomposedPipelineStep (N := modulus)) :=
  w.toDecomposedPipelineWitness.baseWitness

/-- The decomposed P-256 division circuit history bottoms out in
X/CNOT/Toffoli atoms. -/
theorem structured (w : DivisionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  ModularDivision.DecomposedPipelineWitness.structured
    w.toDecomposedPipelineWitness

/-- Clean encoded-basis action for the P-256 modular-division leg. -/
theorem apply_clean_ket (w : DivisionWitness)
    (u : Unit) (v z : Field) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (ModularDivision.PipelineState.initial u v z)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ denominator := u
             numerator := v
             target := z + ModularDivision.quotientResidue u v
             inverseScratch := 0
             quotientScratch := 0
             flag := false } : ModularDivision.PipelineState modulus)) :
        StateVector (Qubits w.encoding.width)) :=
  ModularDivision.DecomposedPipelineWitness.apply_clean_ket
    w.toDecomposedPipelineWitness u v z

/-- P-256 division resources are projected from the same circuit object used
for correctness. -/
theorem resources_eq (w : DivisionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  ModularDivision.DecomposedPipelineWitness.resources_eq
    w.toDecomposedPipelineWitness

/-- P-256 division circuit depth is projected from the same circuit object used
for correctness. -/
theorem depth_eq (w : DivisionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  ModularDivision.DecomposedPipelineWitness.depth_eq
    w.toDecomposedPipelineWitness

/-- P-256 division query depth is projected from the same circuit object used
for correctness. -/
theorem queryDepth_eq (w : DivisionWitness) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  ModularDivision.DecomposedPipelineWitness.queryDepth_eq
    w.toDecomposedPipelineWitness

end DivisionWitness

/-- Resource-correct witness for clean P-256 modular division. -/
def divisionCleanResourceCorrectWitness (w : DivisionWitness) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ u : Unit, ∀ v z : Field,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (ModularDivision.PipelineState.initial u v z)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ denominator := u
                 numerator := v
                 target := z + ModularDivision.quotientResidue u v
                 inverseScratch := 0
                 quotientScratch := 0
                 flag := false } : ModularDivision.PipelineState modulus)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun u v z => DivisionWitness.apply_clean_ket w u v z
  resources := ⟨DivisionWitness.resources_eq w, DivisionWitness.depth_eq w,
    DivisionWitness.queryDepth_eq w⟩

/-- The P-256 MAU endpoint witnesses whose labels must all use the P-256
prime-field encoding.  This is the bundle consumed by later scalar-recovery
resource wiring: target-add covers affine coordinate updates, target-add-with-aux
covers the modular-division target leg, and the inversion/division witnesses
provide the clean unit-domain endpoints. -/
structure WitnessBundle where
  /-- P-256 target-add witness over `ZMod p` labels. -/
  targetAdd : TargetAddWitness
  /-- P-256 target-add-with-aux witness over `ZMod p` labels. -/
  targetAddWithAux : TargetAddWithAuxWitness
  /-- P-256 clean modular-inversion witness over `ZMod p` labels. -/
  inversion : InversionWitness
  /-- P-256 clean modular-division witness over `ZMod p` labels. -/
  division : DivisionWitness

namespace WitnessBundle

/-- Resource-correct clean inversion witness from the bundled P-256 MAU route. -/
def inversionResourceCorrectWitness (w : WitnessBundle) :
    ResourceCorrectWitness (R := Qubits w.inversion.encoding.width)
      (∀ u : Unit, ∀ z : Field,
        Circuit.apply
          (BaseGateSameCircuitWitness.circuit w.inversion.baseWitness)
          ((PureState.ket (R := Qubits w.inversion.encoding.width)
            (w.inversion.encoding.encode
              (ModularInversion.StageState.initial u z)) :
            PureState (Qubits w.inversion.encoding.width)) :
            StateVector (Qubits w.inversion.encoding.width)) =
          (PureState.ket (R := Qubits w.inversion.encoding.width)
            (w.inversion.encoding.encode
              ({ input := u
                 target := z + ModularInversion.inverseResidue u
                 inverseScratch := 0
                 flag := false } : ModularInversion.StageState modulus)) :
            StateVector (Qubits w.inversion.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.inversion.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile
            w.inversion.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.inversion.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile
            w.inversion.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.inversion.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile
            w.inversion.baseWitness).oracleQueries) :=
  inversionCleanResourceCorrectWitness w.inversion

/-- Resource-correct clean division witness from the bundled P-256 MAU route. -/
def divisionResourceCorrectWitness (w : WitnessBundle) :
    ResourceCorrectWitness (R := Qubits w.division.encoding.width)
      (∀ u : Unit, ∀ v z : Field,
        Circuit.apply
          (BaseGateSameCircuitWitness.circuit w.division.baseWitness)
          ((PureState.ket (R := Qubits w.division.encoding.width)
            (w.division.encoding.encode
              (ModularDivision.PipelineState.initial u v z)) :
            PureState (Qubits w.division.encoding.width)) :
            StateVector (Qubits w.division.encoding.width)) =
          (PureState.ket (R := Qubits w.division.encoding.width)
            (w.division.encoding.encode
              ({ denominator := u
                 numerator := v
                 target := z + ModularDivision.quotientResidue u v
                 inverseScratch := 0
                 quotientScratch := 0
                 flag := false } : ModularDivision.PipelineState modulus)) :
            StateVector (Qubits w.division.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.division.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile
            w.division.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.division.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile
            w.division.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.division.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile
            w.division.baseWitness).oracleQueries) :=
  divisionCleanResourceCorrectWitness w.division

end WitnessBundle

end

end P256PrimeFieldBridge

end EllipticCurve
end QuantumAlg
