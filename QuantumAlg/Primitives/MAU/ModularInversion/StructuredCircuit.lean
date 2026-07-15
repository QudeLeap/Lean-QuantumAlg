/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.BaseGateRealization
public import QuantumAlg.Primitives.MAU.ModularAddition.StructuredCircuit
public import QuantumAlg.Primitives.MAU.ModularInversion.Layout
public import QuantumAlg.Primitives.MAU.ModularInversion.MontgomeryKaliski
public import QuantumAlg.Primitives.MAU.ModularInversion.Schedule

/-!
# Encoded base-gate modular-inversion witnesses

This module provides the MAU-facing wrapper for a future concrete
Toffoli/CNOT/X modular-inversion program following the fixed-round
Montgomery-Kaliski inversion route [RNSL17, ECDLP.tex:390-465,753-755].  The
wrapper is intentionally encoded: a closing witness must supply a binary label
encoding and a `BaseGateProgram` whose label action implements the unit-domain
inversion update.  The resulting folded `Circuit` is then the same object used
for encoded-basis correctness and resource accounting.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularInversion

noncomputable section

namespace StageState

/-- Reversible compute stage: add the modular inverse into the scratch register
rather than overwriting scratch. -/
def addInverseToScratch {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target
  inverseScratch := s.inverseScratch + inverseResidue s.input
  flag := s.flag

/-- Inverse of the reversible compute stage. -/
def subInverseFromScratch {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target
  inverseScratch := s.inverseScratch - inverseResidue s.input
  flag := s.flag

@[simp] theorem addInverseToScratch_subInverseFromScratch {N : Nat}
    (s : StageState N) :
    addInverseToScratch (subInverseFromScratch s) = s := by
  cases s
  simp [addInverseToScratch, subInverseFromScratch, sub_eq_add_neg, add_assoc]

@[simp] theorem subInverseFromScratch_addInverseToScratch {N : Nat}
    (s : StageState N) :
    subInverseFromScratch (addInverseToScratch s) = s := by
  cases s
  simp [addInverseToScratch, subInverseFromScratch, sub_eq_add_neg, add_assoc]

/-- Reversible compute/add/uncompute stage update for modular inversion,
following the fixed-round inversion route used for elliptic-curve resources
[RNSL17, ECDLP.tex:390-465]. -/
def reversibleScheduleStep {N : Nat} (s : StageState N) : StageState N :=
  subInverseFromScratch (addScratchToTarget (addInverseToScratch s))

/-- The reversible staged update agrees with the public clean inversion action
on clean scratch input. -/
theorem reversibleScheduleStep_initial {N : Nat}
    (u : (ZMod N)ˣ) (z : ZMod N) :
    reversibleScheduleStep (initial u z) =
      { input := u
        target := z + inverseResidue u
        inverseScratch := 0
        flag := false } := by
  simp [reversibleScheduleStep, initial, addInverseToScratch,
    addScratchToTarget, subInverseFromScratch]

/-- Product-tuple view used before relabeling a staged target-add witness back
to `StageState`. -/
abbrev FieldTuple (N : Nat) :=
  (ZMod N)ˣ × ModularAddition.TargetAdd.Data N

/-- Tuple-level target-add action: add inverse scratch into the target field. -/
def tupleAddScratchToTarget {N : Nat} : FieldTuple N -> FieldTuple N
  | (input, fields) => (input, ModularAddition.TargetAdd.step fields)

@[simp] theorem tupleAddScratchToTarget_toStage {N : Nat}
    (s : StageState N) :
    (tupleEquiv N).symm (tupleAddScratchToTarget (tupleEquiv N s)) =
      addScratchToTarget s := by
  cases s
  rfl

/-- A tuple-level target-add program over the explicit product field layout. -/
structure TupleTargetAddWitness {N n : Nat}
    (E : BinaryResidueEncoding N n) where
  /-- Program acting on the field tuple layout. -/
  program : BaseGateProgram (fieldTupleEncoding E).width
  /-- Correctness of the target-add program on tuple labels. -/
  realizes :
    BaseGateProgram.Realizes (fieldTupleEncoding E) program
      tupleAddScratchToTarget

namespace TupleTargetAddWitness

variable {N n : Nat} {E : BinaryResidueEncoding N n}

/-- Same-Circuit witness for the tuple-level target-add program. -/
def tupleWitness (w : TupleTargetAddWitness E) :
    BaseGateSameCircuitWitness (FieldTuple N) tupleAddScratchToTarget where
  encoding := fieldTupleEncoding E
  program := w.program
  realizes := w.realizes

/-- Relabel a tuple-level target-add witness into the staged-state record
encoding used by the decomposed modular-inversion witness. -/
def stageWitness (w : TupleTargetAddWitness E) :
    BaseGateSameCircuitWitness (StageState N) addScratchToTarget :=
  ((tupleWitness w).relabel (tupleEquiv N)).congrStep
    tupleAddScratchToTarget_toStage

/-- The relabeled target-add program realizes `StageState.addScratchToTarget`
on the staged-state field encoding. -/
theorem stage_realizes (w : TupleTargetAddWitness E) :
    BaseGateProgram.Realizes (fieldEncoding E) w.program addScratchToTarget :=
  (stageWitness w).realizes

/-- Embed a modular-add target-update witness into the inversion field-tuple
layout by preserving the unit-input field. -/
def ofModularAddition (w : ModularAddition.TargetAdd.Witness E) :
    TupleTargetAddWitness E where
  program :=
    (BaseGateSameCircuitWitness.prodRight
      (BinaryLabelEncoding.ofUnitResidueEncoding E) w.sameCircuit).program
  realizes := by
    have h :=
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofUnitResidueEncoding E) w.sameCircuit).realizes
    change BaseGateProgram.Realizes
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofUnitResidueEncoding E) w.sameCircuit).encoding
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofUnitResidueEncoding E) w.sameCircuit).program
      (fun x : (ZMod N)ˣ × ModularAddition.TargetAdd.Data N =>
        (x.1, ModularAddition.TargetAdd.step x.2))
    exact h

end TupleTargetAddWitness

/-! ## Power-of-two clean-work target-add bridge -/

namespace PowerOfTwoTargetAdd

/-- Carry-work labels for the VBE target-add bridge used inside the staged
inversion layout [VBE95, 9511018.tex:237-264,591-618]. -/
abbrev CarryWork (n : Nat) : Type :=
  ModularAddition.TargetAdd.PowerOfTwo.CarryWork n

/-- Distinguished clean carry-work label for the power-of-two target-add
bridge. -/
def cleanWork (n : Nat) : CarryWork n :=
  (ModularAddition.TargetAdd.PowerOfTwo.cleanWorkWitness n).cleanWork

/-- Inverse-scratch bit lens for the power-of-two staged inversion encoding. -/
def inverseScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit
      (fieldEncoding
        (ModularAddition.TargetAdd.PowerOfTwo.residueEncoding n)) :=
  let E := ModularAddition.TargetAdd.PowerOfTwo.residueEncoding n
  (BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding E)
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodLeftBit
        (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool
        (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)))).relabel
    (tupleEquiv (2 ^ n))

/-- Little-endian value bit lens for the staged inverse-scratch register. -/
def inverseScratchValueBit (n : Nat) (bit : Fin n) :
    EncodedBit
      (fieldEncoding
        (ModularAddition.TargetAdd.PowerOfTwo.residueEncoding n)) :=
  inverseScratchBit n bit

@[simp] theorem inverseScratchValueBit_get
    (n : Nat) (bit : Fin n) (s : StageState (2 ^ n)) :
    (inverseScratchValueBit n bit).get s =
      s.inverseScratch.val.testBit bit.val := by
  cases s with
  | mk input target inverseScratch flag =>
      change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get
          inverseScratch = inverseScratch.val.testBit bit.val
      exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit inverseScratch

/-- Field tuple plus target-add carry work.  The physical wire order is
input/target/inverse-scratch/flag/work, matching the staged inversion fields
followed by the VBE carry-work register [RNSL17, ECDLP.tex:390-465]. -/
abbrev FieldTupleWithWork (n : Nat) : Type :=
  FieldTuple (2 ^ n) × CarryWork n

/-- Product reassociation between the staged inversion field tuple with a
trailing work register and the product shape required by `prodRight`. -/
def fieldTupleWithWorkEquiv (n : Nat) :
    FieldTupleWithWork n ≃
      ((ZMod (2 ^ n))ˣ ×
        (ModularAddition.TargetAdd.Data (2 ^ n) × CarryWork n)) where
  toFun := fun x => (x.1.1, (x.1.2, x.2))
  invFun := fun x => ((x.1, x.2.1), x.2.2)
  left_inv := by
    intro x
    rcases x with ⟨⟨input, fields⟩, work⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨input, rest⟩
    rcases rest with ⟨fields, work⟩
    rfl

/-- Tuple-level target-add with explicit carry work.  This is the same
wire-addressed VBE target-add circuit lifted under the preserved unit-input
field [VBE95, 9511018.tex:237-264,591-618]. -/
def tupleAddScratchToTargetWithWork (n : Nat) :
    FieldTupleWithWork n -> FieldTupleWithWork n
  | ((input, fields), work) =>
      let y :=
        (ModularAddition.TargetAdd.PowerOfTwo.cleanWorkWitness n).stepWithWork
          (fields, work)
      ((input, y.1), y.2)

/-- Same-Circuit witness for tuple-level target-add with explicit carry work.
Correctness and resources are tied to the same lifted VBE base-gate program
used by the modular-addition bridge. -/
def tupleWithWorkSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness (FieldTupleWithWork n)
      (tupleAddScratchToTargetWithWork n) :=
  let targetAdd :=
    (ModularAddition.TargetAdd.PowerOfTwo.cleanWorkWitness n).sameCircuit
  let lifted :=
    BaseGateSameCircuitWitness.prodRight
      (BinaryLabelEncoding.ofUnitResidueEncoding
        (ModularAddition.TargetAdd.PowerOfTwo.residueEncoding n))
      targetAdd
  ((lifted.relabel (fieldTupleWithWorkEquiv n)).congrStep
    (by
      intro x
      rcases x with ⟨⟨input, fields⟩, work⟩
      rfl))

/-- Clean tuple endpoint: on a clean flag and clean carry work, the work-aware
bridge agrees with the old tuple target-add action and restores work. -/
theorem tupleAddScratchToTargetWithWork_cleanEndpoint
    (n : Nat) (x : FieldTuple (2 ^ n)) (hflag : x.2.2.2 = false) :
    tupleAddScratchToTargetWithWork n (x, cleanWork n) =
      (tupleAddScratchToTarget x, cleanWork n) := by
  rcases x with ⟨input, fields⟩
  have h :=
    (ModularAddition.TargetAdd.PowerOfTwo.cleanWorkWitness n).cleanEndpoint
      fields hflag
  simpa [tupleAddScratchToTargetWithWork, tupleAddScratchToTarget, cleanWork]
    using congrArg (fun y => ((input, y.1), y.2)) h

/-- Staged inversion state plus carry work. -/
abbrev StageWithWork (n : Nat) : Type :=
  StageState (2 ^ n) × CarryWork n

/-- Relabel staged records to the tuple-with-work layout used by the lifted
target-add circuit. -/
def stageWithWorkEquiv (n : Nat) :
    StageWithWork n ≃ FieldTupleWithWork n where
  toFun := fun x => ((tupleEquiv (2 ^ n)) x.1, x.2)
  invFun := fun x => ((tupleEquiv (2 ^ n)).symm x.1, x.2)
  left_inv := by
    intro x
    rcases x with ⟨s, work⟩
    simp
  right_inv := by
    intro x
    rcases x with ⟨fields, work⟩
    simp

/-- Work-aware staged target-add step.  This is only the target-add leg of the
RNSL fixed-round compute/add/uncompute route, with VBE carry work made explicit
[RNSL17, ECDLP.tex:390-465; VBE95, 9511018.tex:237-264,591-618]. -/
def addScratchToTargetWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n
  | (s, work) =>
      let y :=
        tupleAddScratchToTargetWithWork n ((tupleEquiv (2 ^ n)) s, work)
      ((tupleEquiv (2 ^ n)).symm y.1, y.2)

/-- Same-Circuit staged target-add witness with explicit carry work. -/
def stageWithWorkSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness (StageWithWork n)
      (addScratchToTargetWithWork n) :=
  ((tupleWithWorkSameCircuit n).relabel (stageWithWorkEquiv n)).congrStep
    (by
      intro x
      rcases x with ⟨s, work⟩
      rfl)

/-- Inverse-scratch bit lens in the staged-state-plus-carry-work encoding. -/
def stageWithWorkInverseScratchValueBit (n : Nat) (bit : Fin n) :
    EncodedBit (stageWithWorkSameCircuit n).encoding :=
  ((BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAdd.PowerOfTwo.residueEncoding n))
    (ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkEncoding n)
    (ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit n bit)
    ).relabel (fieldTupleWithWorkEquiv n)).relabel
      (stageWithWorkEquiv n)

/-- Target bit in the staged-state-plus-carry-work encoding. -/
def stageWithWorkTargetValueBit (n : Nat) (bit : Fin n) :
    EncodedBit (stageWithWorkSameCircuit n).encoding :=
  ((BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAdd.PowerOfTwo.residueEncoding n))
    (ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkEncoding n)
    (ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkTargetBit n bit)
    ).relabel (fieldTupleWithWorkEquiv n)).relabel
      (stageWithWorkEquiv n)

@[simp] theorem stageWithWorkInverseScratchValueBit_wire_val
    (n : Nat) (bit : Fin n) :
    (stageWithWorkInverseScratchValueBit n bit).wire.val =
      n + (n + (n - 1 - bit.val)) := by
  simp [stageWithWorkInverseScratchValueBit,
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit,
    ModularAddition.TargetAdd.PowerOfTwo.scratchBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    WireAddress.bitIndex, WireAddress.littleEndianWire,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire]

@[simp] theorem stageWithWorkTargetValueBit_wire_val
    (n : Nat) (bit : Fin n) :
    (stageWithWorkTargetValueBit n bit).wire.val =
      n + (n - 1 - bit.val) := by
  simp [stageWithWorkTargetValueBit,
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkTargetBit,
    ModularAddition.TargetAdd.PowerOfTwo.targetBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    WireAddress.bitIndex, WireAddress.littleEndianWire,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire]

/-- Staged inversion state with both VBE target-add carry work and the finite
Montgomery--Kaliski compute workspace.  The extra workspace is the RNSL17
`u,v,r,s,m_i,f,k` register family plus the comparison-work bits needed by the
concrete word-comparison selector slices; adding it here keeps the Euclidean
workspace present when the target-add leg is lifted into the eventual
compute/add/uncompute composition [RNSL17, ECDLP.tex:425-475; VBE95,
9511018.tex:237-264,591-618]. -/
abbrev StageWithWorkspace (n counterWidth : Nat) : Type :=
  StageWithWork n ×
    MontgomeryKaliski.RegistersWithComparisonWork n counterWidth

/-- Encoding for the staged public fields, VBE carry work, and finite
Montgomery--Kaliski compute/comparison workspace as one basis-label object. -/
def stageWithWorkspaceEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (StageWithWorkspace n counterWidth) :=
  (BaseGateSameCircuitWitness.prodLeft (stageWithWorkSameCircuit n)
    (MontgomeryKaliski.registersWithComparisonWorkEncoding n counterWidth)).encoding

/-- Target-add lifted to a full inversion workspace.  This is only the
target-add leg; the concrete Montgomery--Kaliski compute program remains a
separate obligation [RNSL17, ECDLP.tex:425-475; VBE95,
9511018.tex:237-264,591-618]. -/
def addScratchToTargetWithWorkspace (n counterWidth : Nat) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth
  | (stage, workspace) => (addScratchToTargetWithWork n stage, workspace)

/-- Same-Circuit target-add witness over the full inversion workspace.  The
folded base-gate program is the same VBE target-add program, lifted over the
finite Montgomery--Kaliski registers and comparison work. -/
def stageWithWorkspaceTargetAddSameCircuit (n counterWidth : Nat) :
    BaseGateSameCircuitWitness (StageWithWorkspace n counterWidth)
      (addScratchToTargetWithWorkspace n counterWidth) :=
  BaseGateSameCircuitWitness.prodLeft (stageWithWorkSameCircuit n)
    (MontgomeryKaliski.registersWithComparisonWorkEncoding n counterWidth)

@[simp] theorem stageWithWorkspaceEncoding_width (n counterWidth : Nat) :
    (stageWithWorkspaceEncoding n counterWidth).width =
      (stageWithWorkSameCircuit n).encoding.width +
        (MontgomeryKaliski.registersWithComparisonWorkEncoding
          n counterWidth).width :=
  rfl

/-- Lift a semantic Montgomery--Kaliski workspace step over the staged public
fields and VBE carry work. -/
def stageWithWorkspaceKaliskiStep {n counterWidth : Nat}
    (step : MontgomeryKaliski.RegistersWithComparisonWork n counterWidth ->
      MontgomeryKaliski.RegistersWithComparisonWork n counterWidth) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  fun x => (x.1, step x.2)

@[simp] theorem stageWithWorkspaceKaliskiStep_left
    {n counterWidth : Nat}
    (step : MontgomeryKaliski.RegistersWithComparisonWork n counterWidth ->
      MontgomeryKaliski.RegistersWithComparisonWork n counterWidth)
    (x : StageWithWorkspace n counterWidth) :
    (stageWithWorkspaceKaliskiStep step x).1 = x.1 := by
  cases x
  rfl

@[simp] theorem stageWithWorkspaceKaliskiStep_right
    {n counterWidth : Nat}
    (step : MontgomeryKaliski.RegistersWithComparisonWork n counterWidth ->
      MontgomeryKaliski.RegistersWithComparisonWork n counterWidth)
    (x : StageWithWorkspace n counterWidth) :
    (stageWithWorkspaceKaliskiStep step x).2 = step x.2 := by
  cases x
  rfl

/-- Lift a same-Circuit witness for the Montgomery--Kaliski workspace side
over the staged public fields and VBE carry work. -/
def stageWithWorkspaceKaliskiSameCircuit {n counterWidth : Nat}
    {step : MontgomeryKaliski.RegistersWithComparisonWork n counterWidth ->
      MontgomeryKaliski.RegistersWithComparisonWork n counterWidth}
    (w : BaseGateSameCircuitWitness
      (MontgomeryKaliski.RegistersWithComparisonWork n counterWidth) step) :
    BaseGateSameCircuitWitness (StageWithWorkspace n counterWidth)
      (stageWithWorkspaceKaliskiStep step) :=
  BaseGateSameCircuitWitness.prodRight (stageWithWorkSameCircuit n).encoding w

/-- Full-workspace semantic step for the `uEven` branch-history write, lifted
over the staged public fields and VBE carry work [RNSL17,
ECDLP.tex:468-475]. -/
def uEvenBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MontgomeryKaliski.liftedUEvenBranchHistoryWriteStep
      n counterWidth bit historyIndex)

/-- Same-Circuit witness for the `uEven` branch-history write inside the full
staged inversion workspace. -/
def uEvenBranchHistoryWithWorkspaceSameCircuit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    BaseGateSameCircuitWitness (StageWithWorkspace n counterWidth)
      (uEvenBranchHistoryWithWorkspaceStep
        n counterWidth bit historyIndex) :=
  stageWithWorkspaceKaliskiSameCircuit
    (MontgomeryKaliski.liftedUEvenBranchHistoryWriteSameCircuit
      n counterWidth bit historyIndex)

/-- Full-workspace semantic step for the `vEven` branch-history write, lifted
over the staged public fields and VBE carry work [RNSL17,
ECDLP.tex:468-475]. -/
def vEvenBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MontgomeryKaliski.liftedVEvenBranchHistoryWriteStep
      n counterWidth uIndex vIndex historyIndex)

/-- Same-Circuit witness for the `vEven` branch-history write inside the full
staged inversion workspace. -/
def vEvenBranchHistoryWithWorkspaceSameCircuit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    BaseGateSameCircuitWitness (StageWithWorkspace n counterWidth)
      (vEvenBranchHistoryWithWorkspaceStep
        n counterWidth uIndex vIndex historyIndex) :=
  stageWithWorkspaceKaliskiSameCircuit
    (MontgomeryKaliski.liftedVEvenBranchHistoryWriteSameCircuit
      n counterWidth uIndex vIndex historyIndex)

/-- Full-workspace semantic step for the `uGreater` selector/history-write
slice, lifted over the staged public fields and VBE carry work. -/
def uGreaterSelectorBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MontgomeryKaliski.uGreaterSelectorBranchHistoryWriteStep
      n counterWidth bit historyIndex)

/-- Same-Circuit witness for the `uGreater` selector/history-write slice inside
the full staged inversion workspace. -/
def uGreaterSelectorBranchHistoryWithWorkspaceSameCircuit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    BaseGateSameCircuitWitness (StageWithWorkspace n counterWidth)
      (uGreaterSelectorBranchHistoryWithWorkspaceStep
        n counterWidth bit historyIndex) :=
  stageWithWorkspaceKaliskiSameCircuit
    (MontgomeryKaliski.uGreaterSelectorBranchHistoryWriteSameCircuit
      n counterWidth bit historyIndex)

/-- Full-workspace semantic step for the `vLe` selector/history-write slice,
lifted over the staged public fields and VBE carry work. -/
def vLeSelectorBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MontgomeryKaliski.vLeSelectorBranchHistoryWriteStep
      n counterWidth bit historyIndex)

/-- Same-Circuit witness for the `vLe` selector/history-write slice inside the
full staged inversion workspace. -/
def vLeSelectorBranchHistoryWithWorkspaceSameCircuit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    BaseGateSameCircuitWitness (StageWithWorkspace n counterWidth)
      (vLeSelectorBranchHistoryWithWorkspaceStep
        n counterWidth bit historyIndex) :=
  stageWithWorkspaceKaliskiSameCircuit
    (MontgomeryKaliski.vLeSelectorBranchHistoryWriteSameCircuit
      n counterWidth bit historyIndex)

/-- Clean staged endpoint for the work-aware target-add leg. -/
theorem addScratchToTargetWithWork_cleanEndpoint
    (n : Nat) (s : StageState (2 ^ n)) (hflag : s.flag = false) :
    addScratchToTargetWithWork n (s, cleanWork n) =
      (addScratchToTarget s, cleanWork n) := by
  have htupleFlag :
      ((tupleEquiv (2 ^ n)) s).2.2.2 = false := by
    cases s
    simpa [tupleEquiv] using hflag
  have htuple :=
    tupleAddScratchToTargetWithWork_cleanEndpoint n
      ((tupleEquiv (2 ^ n)) s) htupleFlag
  change
    (let y :=
      tupleAddScratchToTargetWithWork n
        ((tupleEquiv (2 ^ n)) s, cleanWork n);
      ((tupleEquiv (2 ^ n)).symm y.1, y.2)) =
      (addScratchToTarget s, cleanWork n)
  rw [htuple]
  simp [tupleAddScratchToTarget_toStage]

/-- Clean endpoint for the target-add leg after lifting it over the finite
Montgomery--Kaliski compute workspace. -/
theorem addScratchToTargetWithWorkspace_cleanEndpoint
    (n counterWidth : Nat) (s : StageState (2 ^ n))
    (hflag : s.flag = false)
    (workspace :
      MontgomeryKaliski.RegistersWithComparisonWork n counterWidth) :
    addScratchToTargetWithWorkspace n counterWidth ((s, cleanWork n), workspace) =
      ((addScratchToTarget s, cleanWork n), workspace) := by
  simp [addScratchToTargetWithWorkspace,
    addScratchToTargetWithWork_cleanEndpoint n s hflag]

/-- The target-add leg preserves the Montgomery--Kaliski register/comparison
workspace pointwise. -/
theorem addScratchToTargetWithWorkspace_preservesWorkspace
    (n counterWidth : Nat) (x : StageWithWorkspace n counterWidth) :
    (addScratchToTargetWithWorkspace n counterWidth x).2 = x.2 := by
  cases x
  rfl

/-- Staged inversion state with VBE target-add carry work and the full
Montgomery--Kaliski fixed-round workspace: registers, comparison work,
coefficient-adder work, and padding-counter increment work. -/
abbrev StageWithFullRoundWorkspace (n counterWidth : Nat) : Type :=
  StageWithWork n ×
    MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth

/-- Encoding for the staged public fields, VBE carry work, and the full finite
Montgomery--Kaliski fixed-round workspace. -/
def stageWithFullRoundWorkspaceEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (StageWithFullRoundWorkspace n counterWidth) :=
  (BaseGateSameCircuitWitness.prodLeft (stageWithWorkSameCircuit n)
    (MontgomeryKaliski.registersWithFullRoundWorkEncoding
      n counterWidth)).encoding

/-- Target-add lifted over the full fixed-round workspace.  This is still only
the target-add leg; the concrete Montgomery--Kaliski round program remains a
separate compute obligation [RNSL17, ECDLP.tex:390-465; VBE95,
9511018.tex:237-264,591-618]. -/
def addScratchToTargetWithFullRoundWorkspace (n counterWidth : Nat) :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth
  | (stage, workspace) => (addScratchToTargetWithWork n stage, workspace)

/-- Same-Circuit target-add witness over the staged inversion fields and the
full fixed-round workspace.  The folded base-gate program is still the VBE
target-add program, lifted over the preserved Montgomery--Kaliski workspace. -/
def stageWithFullRoundWorkspaceTargetAddSameCircuit (n counterWidth : Nat) :
    BaseGateSameCircuitWitness (StageWithFullRoundWorkspace n counterWidth)
      (addScratchToTargetWithFullRoundWorkspace n counterWidth) :=
  BaseGateSameCircuitWitness.prodLeft (stageWithWorkSameCircuit n)
    (MontgomeryKaliski.registersWithFullRoundWorkEncoding n counterWidth)

@[simp] theorem stageWithFullRoundWorkspaceEncoding_width
    (n counterWidth : Nat) :
    (stageWithFullRoundWorkspaceEncoding n counterWidth).width =
      (stageWithWorkSameCircuit n).encoding.width +
        (MontgomeryKaliski.registersWithFullRoundWorkEncoding
          n counterWidth).width :=
  rfl

/-- Lift a semantic Montgomery--Kaliski full-workspace step over the staged
public fields and VBE carry work. -/
def stageWithFullRoundWorkspaceKaliskiStep {n counterWidth : Nat}
    (step : MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth) :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth :=
  fun x => (x.1, step x.2)

@[simp] theorem stageWithFullRoundWorkspaceKaliskiStep_left
    {n counterWidth : Nat}
    (step : MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth)
    (x : StageWithFullRoundWorkspace n counterWidth) :
    (stageWithFullRoundWorkspaceKaliskiStep step x).1 = x.1 := by
  cases x
  rfl

@[simp] theorem stageWithFullRoundWorkspaceKaliskiStep_right
    {n counterWidth : Nat}
    (step : MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth)
    (x : StageWithFullRoundWorkspace n counterWidth) :
    (stageWithFullRoundWorkspaceKaliskiStep step x).2 = step x.2 := by
  cases x
  rfl

/-- Lift a same-Circuit witness for a Montgomery--Kaliski full-workspace step
over the staged public fields and VBE carry work. -/
def stageWithFullRoundWorkspaceKaliskiSameCircuit {n counterWidth : Nat}
    {step : MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth}
    (w : BaseGateSameCircuitWitness
      (MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth) step) :
    BaseGateSameCircuitWitness (StageWithFullRoundWorkspace n counterWidth)
      (stageWithFullRoundWorkspaceKaliskiStep step) :=
  BaseGateSameCircuitWitness.prodRight (stageWithWorkSameCircuit n).encoding w

/-- Clean endpoint for the target-add leg after lifting it over the full
fixed-round workspace. -/
theorem addScratchToTargetWithFullRoundWorkspace_cleanEndpoint
    (n counterWidth : Nat) (s : StageState (2 ^ n))
    (hflag : s.flag = false)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth) :
    addScratchToTargetWithFullRoundWorkspace n counterWidth
        ((s, cleanWork n), workspace) =
      ((addScratchToTarget s, cleanWork n), workspace) := by
  simp [addScratchToTargetWithFullRoundWorkspace,
    addScratchToTargetWithWork_cleanEndpoint n s hflag]

/-- The target-add leg preserves the full Montgomery--Kaliski fixed-round
workspace pointwise. -/
theorem addScratchToTargetWithFullRoundWorkspace_preservesWorkspace
    (n counterWidth : Nat)
    (x : StageWithFullRoundWorkspace n counterWidth) :
    (addScratchToTargetWithFullRoundWorkspace n counterWidth x).2 = x.2 := by
  cases x
  rfl

/-- Staged inversion state with VBE target-add carry work and the path/control
fixed-round Montgomery--Kaliski workspace.  The extra path bit records the
original active route, and the control-work bit supports controlled execution
of the active body without reusing mutated source predicates. -/
abbrev StageWithFullRoundPathControlWorkspace
    (n counterWidth : Nat) : Type :=
  StageWithWork n ×
    MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth

/-- Encoding for the staged public fields, VBE carry work, and the
path/control fixed-round workspace. -/
def stageWithFullRoundPathControlWorkspaceEncoding
    (n counterWidth : Nat) :
    BinaryLabelEncoding
      (StageWithFullRoundPathControlWorkspace n counterWidth) :=
  (BaseGateSameCircuitWitness.prodLeft (stageWithWorkSameCircuit n)
    (MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
      n counterWidth)).encoding

/-- Target-add lifted over the path/control fixed-round workspace. -/
def addScratchToTargetWithFullRoundPathControlWorkspace
    (n counterWidth : Nat) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth
  | (stage, workspace) => (addScratchToTargetWithWork n stage, workspace)

/-- Same-Circuit target-add witness over the staged fields and path/control
fixed-round workspace. -/
def stageWithFullRoundPathControlWorkspaceTargetAddSameCircuit
    (n counterWidth : Nat) :
    BaseGateSameCircuitWitness
      (StageWithFullRoundPathControlWorkspace n counterWidth)
      (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth) :=
  BaseGateSameCircuitWitness.prodLeft (stageWithWorkSameCircuit n)
    (MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
      n counterWidth)

@[simp] theorem stageWithFullRoundPathControlWorkspaceEncoding_width
    (n counterWidth : Nat) :
    (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width =
      (stageWithWorkSameCircuit n).encoding.width +
        (MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
          n counterWidth).width :=
  rfl

/-- Inverse-scratch bit lifted over the full path/control workspace. -/
def stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (stageWithWorkSameCircuit n).encoding
    (MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
      n counterWidth)
    (stageWithWorkInverseScratchValueBit n bit)

@[simp] theorem
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_wire_val
    (n counterWidth : Nat) (bit : Fin n) :
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
      n counterWidth bit).wire.val =
      n + (n + (n - 1 - bit.val)) := by
  simp [stageWithFullRoundPathControlWorkspaceInverseScratchValueBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire]

/-- Target bit lifted over the full path/control workspace. -/
def stageWithFullRoundPathControlWorkspaceTargetValueBit
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (stageWithWorkSameCircuit n).encoding
    (MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
      n counterWidth)
    (stageWithWorkTargetValueBit n bit)

@[simp] theorem stageWithFullRoundPathControlWorkspaceTargetValueBit_wire_val
    (n counterWidth : Nat) (bit : Fin n) :
    (stageWithFullRoundPathControlWorkspaceTargetValueBit
      n counterWidth bit).wire.val =
      n + (n - 1 - bit.val) := by
  simp [stageWithFullRoundPathControlWorkspaceTargetValueBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire]

/-- Kaliski register bit lifted over the full path/control workspace and the
staged public fields. -/
def stageWithFullRoundPathControlWorkspaceRegisterBit
    (n counterWidth : Nat)
    (bit :
      EncodedBit
        (MontgomeryKaliski.registerEncoding n counterWidth)) :
    EncodedBit
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth) :=
  let fullRoundBit :
      EncodedBit
        (MontgomeryKaliski.registersWithFullRoundWorkEncoding
          n counterWidth) :=
    BinaryLabelEncoding.prodLeftBit
      (MontgomeryKaliski.registersWithCoeffAdderWorkEncoding
        n counterWidth)
      (MontgomeryKaliski.counterIncrementWorkEncoding counterWidth)
      (MontgomeryKaliski.liftComparisonStateBitToCoeffAdderWork
        n counterWidth
        (MontgomeryKaliski.liftRegisterBitToComparisonWork n counterWidth
          bit))
  let pathControlBit :
      EncodedBit
        (MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
          n counterWidth) :=
    BinaryLabelEncoding.prodLeftBit
      (MontgomeryKaliski.registersWithFullRoundPathWorkEncoding
        n counterWidth)
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prodLeftBit
        (MontgomeryKaliski.registersWithFullRoundWorkEncoding
          n counterWidth)
        BinaryLabelEncoding.bool
        fullRoundBit)
  BinaryLabelEncoding.prodRightBit
    (stageWithWorkSameCircuit n).encoding
    (MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
      n counterWidth)
    pathControlBit

@[simp] theorem stageWithFullRoundPathControlWorkspaceRegisterBit_get
    (n counterWidth : Nat)
    (bit :
      EncodedBit
        (MontgomeryKaliski.registerEncoding n counterWidth))
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceRegisterBit
        n counterWidth bit).get x =
      bit.get x.2.1.1.1.1.1 := by
  rcases x with ⟨stage, workspace⟩
  rcases workspace with ⟨pathWork, controlWork⟩
  rcases pathWork with ⟨fullRoundWork, path⟩
  rcases fullRoundWork with ⟨coeffAdderWorkState, counterWork⟩
  rcases coeffAdderWorkState with ⟨comparisonWorkState, coeffAdderWork⟩
  rcases comparisonWorkState with ⟨registers, comparisonWork⟩
  simp [stageWithFullRoundPathControlWorkspaceRegisterBit,
    MontgomeryKaliski.liftComparisonStateBitToCoeffAdderWork,
    MontgomeryKaliski.liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit]

/-- Low `r`-coefficient value bit lifted into the staged full path/control
workspace.  This is a workspace-register bit, not the corrected inverse
residue by itself. -/
def stageWithFullRoundPathControlWorkspaceRCoeffLowBit
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth) :=
  stageWithFullRoundPathControlWorkspaceRegisterBit n counterWidth
    (MontgomeryKaliski.RegisterBits.rCoeffValueBit n counterWidth
      bit.castSucc)

@[simp] theorem stageWithFullRoundPathControlWorkspaceRCoeffLowBit_get
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceRCoeffLowBit
        n counterWidth bit).get x =
      x.2.1.1.1.1.1.rCoeff.val.testBit bit.val := by
  simp [stageWithFullRoundPathControlWorkspaceRCoeffLowBit]

/-- Low `r`-coefficient word lifted into the staged full path/control
workspace. -/
def stageWithFullRoundPathControlWorkspaceRCoeffLowWord
    (n counterWidth : Nat) :
    EncodedBit.Word
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth) n where
  bit := stageWithFullRoundPathControlWorkspaceRCoeffLowBit n counterWidth

/-- Staged inverse-scratch word lifted over the full path/control workspace. -/
def stageWithFullRoundPathControlWorkspaceInverseScratchValueWord
    (n counterWidth : Nat) :
    EncodedBit.Word
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth) n where
  bit :=
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit n counterWidth

@[simp] theorem
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_get
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).get x =
      x.1.1.inverseScratch.val.testBit bit.val := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  rcases s with ⟨input, target, inverseScratch, flag⟩
  change
    (ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit n bit).get
        ((target, inverseScratch, flag), work) =
      inverseScratch.val.testBit bit.val
  exact
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit_get_testBit
      n bit (target, inverseScratch, flag) work

@[simp] theorem stageWithFullRoundPathControlWorkspaceTargetValueBit_get
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceTargetValueBit
        n counterWidth bit).get x =
      x.1.1.target.val.testBit bit.val := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  rcases s with ⟨input, target, inverseScratch, flag⟩
  change
    (ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkTargetBit n bit).get
        ((target, inverseScratch, flag), work) =
      target.val.testBit bit.val
  exact
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkTargetBit_get_fst
      n bit ((target, inverseScratch, flag), work)

@[simp] theorem
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_workspace
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    ((stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).flip x).2 = x.2 := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  rcases s with ⟨input, target, inverseScratch, flag⟩
  simp [stageWithFullRoundPathControlWorkspaceInverseScratchValueBit,
    stageWithWorkInverseScratchValueBit,
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit,
    ModularAddition.TargetAdd.PowerOfTwo.scratchBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit]

@[simp] theorem
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_input
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    ((stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).flip x).1.1.input =
      x.1.1.input := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  rcases s with ⟨input, target, inverseScratch, flag⟩
  simp [stageWithFullRoundPathControlWorkspaceInverseScratchValueBit,
    stageWithWorkInverseScratchValueBit,
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit,
    ModularAddition.TargetAdd.PowerOfTwo.scratchBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit, stageWithWorkEquiv,
    fieldTupleWithWorkEquiv, tupleEquiv,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit]

@[simp] theorem
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_work
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    ((stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).flip x).1.2 =
      x.1.2 := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  rcases s with ⟨input, target, inverseScratch, flag⟩
  simp [stageWithFullRoundPathControlWorkspaceInverseScratchValueBit,
    stageWithWorkInverseScratchValueBit,
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit,
    ModularAddition.TargetAdd.PowerOfTwo.scratchBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit, stageWithWorkEquiv,
    fieldTupleWithWorkEquiv, tupleEquiv,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit]

@[simp] theorem
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_flag
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    ((stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).flip x).1.1.flag =
      x.1.1.flag := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  rcases s with ⟨input, target, inverseScratch, flag⟩
  simp [stageWithFullRoundPathControlWorkspaceInverseScratchValueBit,
    stageWithWorkInverseScratchValueBit,
    ModularAddition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit,
    ModularAddition.TargetAdd.PowerOfTwo.scratchBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit, stageWithWorkEquiv,
    fieldTupleWithWorkEquiv, tupleEquiv,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit]

/-- Staged target bits and inverse-scratch bits occupy disjoint wires in the
full path/control workspace. -/
theorem
    stageWithFullRoundPathControlWorkspaceTargetBit_wire_ne_inverseScratch
    (n counterWidth : Nat) (targetBit scratchBit : Fin n) :
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth scratchBit).wire ≠
      (stageWithFullRoundPathControlWorkspaceTargetValueBit
        n counterWidth targetBit).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  simp at hval
  omega

/-- The lifted low `r`-coefficient source bit and corresponding staged
inverse-scratch target bit occupy disjoint wires. -/
theorem stageWithFullRoundPathControlWorkspaceRCoeffLowBit_wire_ne_inverseScratch
    (n counterWidth : Nat) (bit : Fin n) :
    (stageWithFullRoundPathControlWorkspaceRCoeffLowBit
        n counterWidth bit).wire ≠
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  have htarget :
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).wire.val <
        (stageWithWorkSameCircuit n).encoding.width :=
    by
      simpa [stageWithFullRoundPathControlWorkspaceInverseScratchValueBit,
        BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire]
        using (stageWithWorkInverseScratchValueBit n bit).wire.isLt
  have hsource :
      (stageWithWorkSameCircuit n).encoding.width ≤
        (stageWithFullRoundPathControlWorkspaceRCoeffLowBit
          n counterWidth bit).wire.val := by
    simp [stageWithFullRoundPathControlWorkspaceRCoeffLowBit,
      stageWithFullRoundPathControlWorkspaceRegisterBit,
      BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire]
  omega

/-- Any lifted Kaliski register bit is disjoint from every staged
inverse-scratch target bit in the full path/control workspace. -/
theorem stageWithFullRoundPathControlWorkspaceRegisterBit_wire_ne_inverseScratch
    (n counterWidth : Nat)
    (registerBit :
      EncodedBit (MontgomeryKaliski.registerEncoding n counterWidth))
    (bit : Fin n) :
    (stageWithFullRoundPathControlWorkspaceRegisterBit
        n counterWidth registerBit).wire ≠
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  have htarget :
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).wire.val <
        (stageWithWorkSameCircuit n).encoding.width :=
    by
      simpa [stageWithFullRoundPathControlWorkspaceInverseScratchValueBit,
        BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire]
        using (stageWithWorkInverseScratchValueBit n bit).wire.isLt
  have hsource :
      (stageWithWorkSameCircuit n).encoding.width ≤
        (stageWithFullRoundPathControlWorkspaceRegisterBit
          n counterWidth registerBit).wire.val := by
    simp [stageWithFullRoundPathControlWorkspaceRegisterBit,
      BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire]
  omega

/-- Distinct staged inverse-scratch bits occupy distinct wires in the full
path/control workspace. -/
theorem stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_wire_ne
    (n counterWidth : Nat) {left right : Fin n} (h : left ≠ right) :
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth left).wire ≠
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth right).wire := by
  intro hwire
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hwire
  have hleft := left.isLt
  have hright := right.isLt
  simp at hval
  omega

/-- Semantic step for xoring the low `r`-coefficient word into the staged
inverse-scratch word. -/
def rCoeffLowToInverseScratchXorStep (n counterWidth : Nat) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  EncodedBit.Word.xorIntoStep
    (stageWithFullRoundPathControlWorkspaceRCoeffLowWord n counterWidth)
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueWord
      n counterWidth)
    (stageWithFullRoundPathControlWorkspaceRCoeffLowBit_wire_ne_inverseScratch
      n counterWidth)

/-- Same-Circuit witness for bitwise xoring the low `r`-coefficient workspace
word into the staged inverse-scratch word. -/
def rCoeffLowToInverseScratchXorSameCircuit
    (n counterWidth : Nat) :
    BaseGateSameCircuitWitness
      (StageWithFullRoundPathControlWorkspace n counterWidth)
      (rCoeffLowToInverseScratchXorStep n counterWidth) :=
  EncodedBit.Word.xorIntoWitness
    (stageWithFullRoundPathControlWorkspaceRCoeffLowWord n counterWidth)
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueWord
      n counterWidth)
    (stageWithFullRoundPathControlWorkspaceRCoeffLowBit_wire_ne_inverseScratch
      n counterWidth)

/-- Semantic inverse selected for the finite low-`r` transfer circuit.  The
inverse is tied to the realized finite base-gate program below rather than to
an independent arithmetic simplification of the xor fold. -/
noncomputable def rCoeffLowToInverseScratchXorUncomputeStep
    (n counterWidth : Nat) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  letI : Nonempty
      (StageWithFullRoundPathControlWorkspace n counterWidth) :=
    ⟨((StageState.initial (1 : (ZMod (2 ^ n))ˣ) 0, cleanWork n),
      MontgomeryKaliski.withCleanFullRoundPathControlWork n counterWidth
        (MontgomeryKaliski.initialRegisters n counterWidth 0 0))⟩
  Function.invFun (rCoeffLowToInverseScratchXorStep n counterWidth)

/-- The low-`r` transfer action is surjective on the finite encoded staged
workspace because it is realized by a reversible base-gate program. -/
theorem rCoeffLowToInverseScratchXorStep_surjective
    (n counterWidth : Nat) :
    Function.Surjective
      (rCoeffLowToInverseScratchXorStep n counterWidth) :=
  letI : Finite
      (StageWithFullRoundPathControlWorkspace n counterWidth) :=
    Finite.of_injective
      (stageWithFullRoundPathControlWorkspaceEncoding
        n counterWidth).encode
      (stageWithFullRoundPathControlWorkspaceEncoding
        n counterWidth).encode_injective
  Finite.surjective_of_injective
    (BaseGateProgram.Realizes.injective
      (rCoeffLowToInverseScratchXorSameCircuit n counterWidth).realizes)

/-- The selected finite inverse is a right inverse for the low-`r` transfer
step, so the reversed transfer program may be used as a semantic uncompute
leg. -/
theorem rCoeffLowToInverseScratchXorStep_compute_rightInverse
    (n counterWidth : Nat) :
    ∀ x,
      rCoeffLowToInverseScratchXorStep n counterWidth
          (rCoeffLowToInverseScratchXorUncomputeStep n counterWidth x) =
        x :=
  letI : Nonempty
      (StageWithFullRoundPathControlWorkspace n counterWidth) :=
    ⟨((StageState.initial (1 : (ZMod (2 ^ n))ˣ) 0, cleanWork n),
      MontgomeryKaliski.withCleanFullRoundPathControlWork n counterWidth
        (MontgomeryKaliski.initialRegisters n counterWidth 0 0))⟩
  Function.rightInverse_invFun
    (rCoeffLowToInverseScratchXorStep_surjective n counterWidth)

/-- Xoring low `r`-coefficient bits into staged inverse scratch preserves the
Montgomery--Kaliski path/control workspace. -/
theorem rCoeffLowToInverseScratchXorStep_workspace
    (n counterWidth : Nat)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (rCoeffLowToInverseScratchXorStep n counterWidth x).2 = x.2 := by
  unfold rCoeffLowToInverseScratchXorStep EncodedBit.Word.xorIntoStep
    EncodedBit.Word.xorIntoGates
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [List.mem_ofFn] at hgate
  rcases hgate with ⟨i, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_workspace
      n counterWidth i y

/-- Xoring the low `r`-coefficient word into inverse scratch preserves the
staged input field. -/
theorem rCoeffLowToInverseScratchXorStep_input
    (n counterWidth : Nat)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (rCoeffLowToInverseScratchXorStep n counterWidth x).1.1.input =
      x.1.1.input := by
  unfold rCoeffLowToInverseScratchXorStep EncodedBit.Word.xorIntoStep
    EncodedBit.Word.xorIntoGates
  change
    (fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
      y.1.1.input)
      (EncodedBit.GateSpec.stepList _ x) =
    (fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
      y.1.1.input) x
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          y.1.1.input) _ ?_ x
  intro gate hgate
  simp only [List.mem_ofFn] at hgate
  rcases hgate with ⟨i, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_input
      n counterWidth i y

/-- Xoring the low `r`-coefficient word into inverse scratch preserves the
target-add carry work. -/
theorem rCoeffLowToInverseScratchXorStep_work
    (n counterWidth : Nat)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (rCoeffLowToInverseScratchXorStep n counterWidth x).1.2 =
      x.1.2 := by
  unfold rCoeffLowToInverseScratchXorStep EncodedBit.Word.xorIntoStep
    EncodedBit.Word.xorIntoGates
  change
    (fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
      y.1.2)
      (EncodedBit.GateSpec.stepList _ x) =
    (fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
      y.1.2) x
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          y.1.2) _ ?_ x
  intro gate hgate
  simp only [List.mem_ofFn] at hgate
  rcases hgate with ⟨i, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_work
      n counterWidth i y

/-- Xoring the low `r`-coefficient word into inverse scratch preserves the
staged cleanup flag. -/
theorem rCoeffLowToInverseScratchXorStep_flag
    (n counterWidth : Nat)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (rCoeffLowToInverseScratchXorStep n counterWidth x).1.1.flag =
      x.1.1.flag := by
  unfold rCoeffLowToInverseScratchXorStep EncodedBit.Word.xorIntoStep
    EncodedBit.Word.xorIntoGates
  change
    (fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
      y.1.1.flag)
      (EncodedBit.GateSpec.stepList _ x) =
    (fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
      y.1.1.flag) x
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          y.1.1.flag) _ ?_ x
  intro gate hgate
  simp only [List.mem_ofFn] at hgate
  rcases hgate with ⟨i, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_flag
      n counterWidth i y

/-- Xoring the low `r`-coefficient word into inverse scratch preserves the
staged target field bitwise. -/
theorem rCoeffLowToInverseScratchXorStep_target_testBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (rCoeffLowToInverseScratchXorStep
        n counterWidth x).1.1.target.val.testBit bit.val =
      x.1.1.target.val.testBit bit.val := by
  rw [← stageWithFullRoundPathControlWorkspaceTargetValueBit_get
      n counterWidth bit (rCoeffLowToInverseScratchXorStep n counterWidth x)]
  rw [← stageWithFullRoundPathControlWorkspaceTargetValueBit_get
      n counterWidth bit x]
  unfold rCoeffLowToInverseScratchXorStep
  rw [EncodedBit.Word.xorIntoStep_get_observed_of_target_ne]
  intro i
  exact
    stageWithFullRoundPathControlWorkspaceTargetBit_wire_ne_inverseScratch
      n counterWidth bit i

/-- Xoring the low `r`-coefficient word into inverse scratch preserves the
staged target field. -/
theorem rCoeffLowToInverseScratchXorStep_target
    (n counterWidth : Nat)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (rCoeffLowToInverseScratchXorStep n counterWidth x).1.1.target =
      x.1.1.target := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  exact rCoeffLowToInverseScratchXorStep_target_testBit n counterWidth bit x

/-- Readout of a staged inverse-scratch bit after xoring in the low
`r`-coefficient word. -/
theorem rCoeffLowToInverseScratchXorStep_get_inverseScratchValueBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).get
        (rCoeffLowToInverseScratchXorStep n counterWidth x) =
      ((stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
          n counterWidth bit).get x ^^
        (stageWithFullRoundPathControlWorkspaceRCoeffLowBit
          n counterWidth bit).get x) := by
  unfold rCoeffLowToInverseScratchXorStep
  exact
    EncodedBit.Word.xorIntoStep_get_target
      (stageWithFullRoundPathControlWorkspaceRCoeffLowWord n counterWidth)
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueWord
        n counterWidth)
      (stageWithFullRoundPathControlWorkspaceRCoeffLowBit_wire_ne_inverseScratch
        n counterWidth)
      bit
      (fun j hji =>
        stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_wire_ne
          n counterWidth hji)
      (fun j =>
        by
          simpa [stageWithFullRoundPathControlWorkspaceRCoeffLowWord,
            stageWithFullRoundPathControlWorkspaceInverseScratchValueWord,
            stageWithFullRoundPathControlWorkspaceRCoeffLowBit] using
            Ne.symm
              (stageWithFullRoundPathControlWorkspaceRegisterBit_wire_ne_inverseScratch
                n counterWidth
                (MontgomeryKaliski.RegisterBits.rCoeffValueBit n counterWidth
                  bit.castSucc)
                j))
      x

/-- Semantic readout of a staged inverse-scratch bit after xoring in the low
`r`-coefficient word. -/
theorem rCoeffLowToInverseScratchXorStep_get_inverseScratch_testBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    Nat.testBit
        (rCoeffLowToInverseScratchXorStep n counterWidth x).1.1.inverseScratch.val
        bit.val =
      (x.1.1.inverseScratch.val.testBit bit.val ^^
        x.2.1.1.1.1.1.rCoeff.val.testBit bit.val) := by
  simpa using
    rCoeffLowToInverseScratchXorStep_get_inverseScratchValueBit
      n counterWidth bit x

/-- On clean staged input, xoring the low `r`-coefficient word into inverse
scratch makes each staged inverse-scratch bit read as the corresponding low
`r`-coefficient bit. -/
theorem rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit
    (n counterWidth : Nat) (bit : Fin n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    Nat.testBit
        (rCoeffLowToInverseScratchXorStep n counterWidth
          ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch.val
        bit.val =
      workspace.1.1.1.1.1.rCoeff.val.testBit bit.val := by
  rw [rCoeffLowToInverseScratchXorStep_get_inverseScratch_testBit]
  simp [StageState.initial]

/-- Clean staged low-`r` transfer fills the inverse scratch with the full
low-word value of the path/control workspace's `r` coefficient. -/
theorem rCoeffLowToInverseScratchXorStep_initial_inverseScratch
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    (rCoeffLowToInverseScratchXorStep n counterWidth
      ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch =
      (workspace.1.1.1.1.1.rCoeff.val : ZMod (2 ^ n)) := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit]
  rw [ZMod.val_natCast]
  rw [Nat.testBit_mod_two_pow]
  simp [bit.isLt]

/-- Clean staged low-`r` transfer updates only inverse scratch, leaving the
input, target, target-add carry work, cleanup flag, and path/control workspace
unchanged. -/
theorem rCoeffLowToInverseScratchXorStep_initial
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    rCoeffLowToInverseScratchXorStep n counterWidth
        ((StageState.initial u z, cleanWork n), workspace) =
      (({ input := u
          target := z
          inverseScratch :=
            (workspace.1.1.1.1.1.rCoeff.val : ZMod (2 ^ n))
          flag := false }, cleanWork n), workspace) := by
  let y :=
    rCoeffLowToInverseScratchXorStep n counterWidth
      ((StageState.initial u z, cleanWork n), workspace)
  have hinput : y.1.1.input = u := by
    simpa [y, StageState.initial] using
      rCoeffLowToInverseScratchXorStep_input
        n counterWidth ((StageState.initial u z, cleanWork n), workspace)
  have htarget : y.1.1.target = z := by
    simpa [y, StageState.initial] using
      rCoeffLowToInverseScratchXorStep_target
        n counterWidth ((StageState.initial u z, cleanWork n), workspace)
  have hinverse :
      y.1.1.inverseScratch =
        (workspace.1.1.1.1.1.rCoeff.val : ZMod (2 ^ n)) := by
    simpa [y] using
      rCoeffLowToInverseScratchXorStep_initial_inverseScratch
        n counterWidth u z workspace
  have hflag : y.1.1.flag = false := by
    simpa [y, StageState.initial] using
      rCoeffLowToInverseScratchXorStep_flag
        n counterWidth ((StageState.initial u z, cleanWork n), workspace)
  have hwork : y.1.2 = cleanWork n := by
    simpa [y] using
      rCoeffLowToInverseScratchXorStep_work
        n counterWidth ((StageState.initial u z, cleanWork n), workspace)
  have hworkspace : y.2 = workspace := by
    simpa [y] using
      rCoeffLowToInverseScratchXorStep_workspace
        n counterWidth ((StageState.initial u z, cleanWork n), workspace)
  apply Prod.ext
  · apply Prod.ext
    · cases hstage : y.1.1 with
      | mk input target inverseScratch flag =>
          rw [hstage] at hinput htarget hinverse hflag
          have hinput0 : input = u := by simpa using hinput
          have htarget0 : target = z := by simpa using htarget
          have hinverse0 :
              inverseScratch =
                (workspace.1.1.1.1.1.rCoeff.val : ZMod (2 ^ n)) := by
            simpa using hinverse
          have hflag0 : flag = false := by simpa using hflag
          subst input
          subst target
          subst inverseScratch
          subst flag
          simp
    · simpa [y] using hwork
  · simpa [y] using hworkspace

/-- Clean staged readout against a supplied source-level raw coefficient.  This
is the pre-correction pseudo-residue slot, not the corrected inverse residue. -/
theorem rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit_of_rCoeff_eq
    (n counterWidth : Nat) (bit : Fin n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (rawCoeff : Nat)
    (hrCoeff : workspace.1.1.1.1.1.rCoeff.val = rawCoeff) :
    Nat.testBit
        (rCoeffLowToInverseScratchXorStep n counterWidth
          ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch.val
        bit.val =
      rawCoeff.testBit bit.val := by
  rw [rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit]
  rw [hrCoeff]

/-- Clean staged readout against the trace finish state's raw `r` coefficient.
This records the copied pseudo-residue slot before Montgomery correction. -/
theorem rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit_of_trace_finish
    (n counterWidth : Nat) (bit : Fin n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (trace : MontgomeryKaliski.Trace n)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      MontgomeryKaliski.RoundState.fromRegisters n counterWidth
          workspace.1.1.1.1.1 trace.finish.kaliskiSteps
          trace.finish.paddingSteps =
        trace.finish) :
    Nat.testBit
        (rCoeffLowToInverseScratchXorStep n counterWidth
          ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch.val
        bit.val =
      trace.finish.rCoeff.testBit bit.val := by
  apply
    rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit_of_rCoeff_eq
      n counterWidth bit u z workspace trace.finish.rCoeff
  have hcoeff :=
    congrArg (fun st : MontgomeryKaliski.RoundState => st.rCoeff) hfinish
  simpa [MontgomeryKaliski.RoundState.fromRegisters] using hcoeff

/-- Low-bit readout of the trace pseudo-residue in the staged `2^n` residue
ring agrees with the raw finish-state `r` coefficient. -/
theorem tracePseudoInverseResidue_twoPow_val_testBit
    (n : Nat) (trace : MontgomeryKaliski.Trace n) (bit : Fin n) :
    (trace.pseudoInverseResidue (2 ^ n)).val.testBit bit.val =
      trace.finish.rCoeff.testBit bit.val := by
  rw [MontgomeryKaliski.Trace.pseudoInverseResidue,
    MontgomeryKaliski.RoundState.pseudoInverseResidue]
  rw [ZMod.val_natCast]
  rw [Nat.testBit_mod_two_pow]
  simp [bit.isLt]

/-- Clean staged readout against the trace pseudo-residue, before the
Montgomery correction factor is applied. -/
theorem rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit_of_trace_pseudo
    (n counterWidth : Nat) (bit : Fin n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (trace : MontgomeryKaliski.Trace n)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      MontgomeryKaliski.RoundState.fromRegisters n counterWidth
          workspace.1.1.1.1.1 trace.finish.kaliskiSteps
          trace.finish.paddingSteps =
        trace.finish) :
    Nat.testBit
        (rCoeffLowToInverseScratchXorStep n counterWidth
          ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch.val
        bit.val =
      (trace.pseudoInverseResidue (2 ^ n)).val.testBit bit.val := by
  calc
    Nat.testBit
        (rCoeffLowToInverseScratchXorStep n counterWidth
          ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch.val
        bit.val =
        trace.finish.rCoeff.testBit bit.val :=
      rCoeffLowToInverseScratchXorStep_initial_get_inverseScratch_testBit_of_trace_finish
        n counterWidth bit u z trace workspace hfinish
    _ = (trace.pseudoInverseResidue (2 ^ n)).val.testBit bit.val :=
      (tracePseudoInverseResidue_twoPow_val_testBit n trace bit).symm

/-- Lift a path/control Montgomery--Kaliski workspace step over the staged
public fields and VBE carry work. -/
def stageWithFullRoundPathControlWorkspaceKaliskiStep
    {n counterWidth : Nat}
    (step :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  fun x => (x.1, step x.2)

@[simp] theorem stageWithFullRoundPathControlWorkspaceKaliskiStep_left
    {n counterWidth : Nat}
    (step :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceKaliskiStep step x).1 = x.1 := by
  cases x
  rfl

@[simp] theorem stageWithFullRoundPathControlWorkspaceKaliskiStep_right
    {n counterWidth : Nat}
    (step :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceKaliskiStep step x).2 =
      step x.2 := by
  cases x
  rfl

/-- Lift a same-Circuit witness for a path/control Montgomery--Kaliski
workspace step over the staged public fields and VBE carry work. -/
def stageWithFullRoundPathControlWorkspaceKaliskiSameCircuit
    {n counterWidth : Nat}
    {step :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth}
    (w : BaseGateSameCircuitWitness
      (MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth) step) :
    BaseGateSameCircuitWitness
      (StageWithFullRoundPathControlWorkspace n counterWidth)
      (stageWithFullRoundPathControlWorkspaceKaliskiStep step) :=
  BaseGateSameCircuitWitness.prodRight (stageWithWorkSameCircuit n).encoding w

/-- Clean endpoint for the target-add leg after lifting it over the
path/control fixed-round workspace. -/
theorem addScratchToTargetWithFullRoundPathControlWorkspace_cleanEndpoint
    (n counterWidth : Nat) (s : StageState (2 ^ n))
    (hflag : s.flag = false)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth
        ((s, cleanWork n), workspace) =
      ((addScratchToTarget s, cleanWork n), workspace) := by
  simp [addScratchToTargetWithFullRoundPathControlWorkspace,
    addScratchToTargetWithWork_cleanEndpoint n s hflag]

/-- The target-add leg preserves the path/control fixed-round workspace
pointwise. -/
theorem addScratchToTargetWithFullRoundPathControlWorkspace_preservesWorkspace
    (n counterWidth : Nat)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth x).2 =
      x.2 := by
  cases x
  rfl

/-- Workspace-aware compute/add/uncompute schedule.  The compute leg may leave
the Montgomery--Kaliski finite workspace dirty; the inverse folded
`BaseGateProgram` must clean it through the supplied semantic right inverse.
This is the wrapper shape required before a concrete RNSL17 compute circuit is
plugged into the work-aware target-add bridge [RNSL17, ECDLP.tex:390-465,
753-755; VBE95, 9511018.tex:237-264,591-618]. -/
def reversibleScheduleStepWithWorkspace (n counterWidth : Nat)
    (computeStep uncomputeStep :
      StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  fun x =>
    uncomputeStep
      (addScratchToTargetWithWorkspace n counterWidth (computeStep x))

/-- Decomposed staged inversion witness over the full finite
Montgomery--Kaliski compute workspace.  Unlike the older work-aware wrapper,
this interface does not require the compute leg to preserve the workspace
pointwise; it only requires the reversed base-gate program to uncompute the
workspace by a proved semantic right inverse [RNSL17, ECDLP.tex:390-465,
753-755]. -/
structure DecomposedStageWithWorkspaceWitness (n counterWidth : Nat) where
  /-- Semantic action of the supplied compute program. -/
  computeStep :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth
  /-- Semantic action used by the reversed compute program. -/
  uncomputeStep :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth
  /-- Program for the Montgomery--Kaliski compute leg over the full workspace. -/
  computeProgram : BaseGateProgram (stageWithWorkspaceEncoding n counterWidth).width
  /-- Correctness of the compute program on full workspace labels. -/
  computeRealizes :
    BaseGateProgram.Realizes (stageWithWorkspaceEncoding n counterWidth)
      computeProgram computeStep
  /-- The supplied uncompute semantic action is a right inverse of compute. -/
  compute_rightInverse : ∀ x, computeStep (uncomputeStep x) = x

namespace DecomposedStageWithWorkspaceWitness

/-- The public semantic update selected by a workspace-aware witness. -/
def step {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  reversibleScheduleStepWithWorkspace n counterWidth w.computeStep w.uncomputeStep

/-- Compute, target-add over the same full workspace, and reverse-compute as
one base-gate program. -/
def program {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    BaseGateProgram (stageWithWorkspaceEncoding n counterWidth).width :=
  BaseGateProgram.append w.computeProgram
    (BaseGateProgram.append (stageWithWorkspaceTargetAddSameCircuit n counterWidth).program
      (BaseGateProgram.inverse w.computeProgram))

/-- The decomposed full-workspace program realizes the selected
compute/add/uncompute semantic update. -/
theorem realizes {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    BaseGateProgram.Realizes (stageWithWorkspaceEncoding n counterWidth) w.program
      w.step := by
  have htarget :
      BaseGateProgram.Realizes (stageWithWorkspaceEncoding n counterWidth)
        (stageWithWorkspaceTargetAddSameCircuit n counterWidth).program
        (addScratchToTargetWithWorkspace n counterWidth) := by
    simpa [stageWithWorkspaceTargetAddSameCircuit, stageWithWorkspaceEncoding]
      using (stageWithWorkspaceTargetAddSameCircuit n counterWidth).realizes
  have huncompute :
      BaseGateProgram.Realizes (stageWithWorkspaceEncoding n counterWidth)
        (BaseGateProgram.inverse w.computeProgram) w.uncomputeStep :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.computeRealizes
      w.compute_rightInverse
  have htail :
      BaseGateProgram.Realizes (stageWithWorkspaceEncoding n counterWidth)
        (BaseGateProgram.append
          (stageWithWorkspaceTargetAddSameCircuit n counterWidth).program
          (BaseGateProgram.inverse w.computeProgram))
        (fun x : StageWithWorkspace n counterWidth =>
          w.uncomputeStep (addScratchToTargetWithWorkspace n counterWidth x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := addScratchToTargetWithWorkspace n counterWidth)
      (secondStep := w.uncomputeStep)
      htarget huncompute
  have hfull :
      BaseGateProgram.Realizes (stageWithWorkspaceEncoding n counterWidth)
        w.program w.step :=
    BaseGateProgram.Realizes.append
      (firstStep := w.computeStep)
      (secondStep := fun x : StageWithWorkspace n counterWidth =>
        w.uncomputeStep (addScratchToTargetWithWorkspace n counterWidth x))
      w.computeRealizes htail
  simpa [program, step, reversibleScheduleStepWithWorkspace] using hfull

/-- Running the reversed compute semantics after the compute leg restores the
full semantic workspace.  The proof uses injectivity of the realized base-gate
program, so the cleanup fact stays tied to the same concrete program that
supplies correctness and resource accounting. -/
theorem compute_leftInverse {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    ∀ x, w.uncomputeStep (w.computeStep x) = x := by
  intro x
  have hinj := BaseGateProgram.Realizes.injective w.computeRealizes
  apply hinj
  exact w.compute_rightInverse (w.computeStep x)

/-- Same-Circuit witness induced by the full-workspace decomposed staged
program. -/
def baseWitness {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    BaseGateSameCircuitWitness (StageWithWorkspace n counterWidth) w.step where
  encoding := stageWithWorkspaceEncoding n counterWidth
  program := w.program
  realizes := w.realizes

/-- The full-workspace decomposed inversion circuit history bottoms out in
X/CNOT/Toffoli atoms. -/
theorem structured {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all full-workspace staged inversion labels. -/
theorem apply_ket {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth)
    (x : StageWithWorkspace n counterWidth) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (stageWithWorkspaceEncoding n counterWidth).width)
          ((stageWithWorkspaceEncoding n counterWidth).encode x) :
          PureState (Qubits (stageWithWorkspaceEncoding n counterWidth).width)) :
          StateVector (Qubits (stageWithWorkspaceEncoding n counterWidth).width)) =
      (PureState.ket
        (R := Qubits (stageWithWorkspaceEncoding n counterWidth).width)
        ((stageWithWorkspaceEncoding n counterWidth).encode (w.step x)) :
        StateVector (Qubits (stageWithWorkspaceEncoding n counterWidth).width)) := by
  simpa [baseWitness] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Resource counters are projected from the same full-workspace decomposed
inversion circuit. -/
theorem resources_eq {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same full-workspace decomposed
inversion circuit. -/
theorem depth_eq {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same full-workspace decomposed inversion
circuit. -/
theorem queryDepth_eq {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

end DecomposedStageWithWorkspaceWitness

/-- Workspace-aware compute/add/uncompute schedule over the full finite
Montgomery--Kaliski fixed-round workspace.  The compute leg may leave that
workspace dirty; the inverse folded `BaseGateProgram` must clean it through the
supplied semantic right inverse. -/
def reversibleScheduleStepWithFullRoundWorkspace (n counterWidth : Nat)
    (computeStep uncomputeStep :
      StageWithFullRoundWorkspace n counterWidth ->
        StageWithFullRoundWorkspace n counterWidth) :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth :=
  fun x =>
    uncomputeStep
      (addScratchToTargetWithFullRoundWorkspace n counterWidth
        (computeStep x))

/-- Decomposed staged inversion witness over the full Montgomery--Kaliski
fixed-round workspace.  The target-add leg is fixed to the lifted VBE
same-Circuit witness; the compute program must supply the concrete
Montgomery--Kaliski fixed-round computation over the same workspace. -/
structure DecomposedStageWithFullRoundWorkspaceWitness
    (n counterWidth : Nat) where
  /-- Semantic action of the supplied compute program. -/
  computeStep :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth
  /-- Semantic action used by the reversed compute program. -/
  uncomputeStep :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth
  /-- Program for the Montgomery--Kaliski compute leg over the full workspace. -/
  computeProgram :
    BaseGateProgram
      (stageWithFullRoundWorkspaceEncoding n counterWidth).width
  /-- Correctness of the compute program on full workspace labels. -/
  computeRealizes :
    BaseGateProgram.Realizes
      (stageWithFullRoundWorkspaceEncoding n counterWidth)
      computeProgram computeStep
  /-- The supplied uncompute semantic action is a right inverse of compute. -/
  compute_rightInverse : ∀ x, computeStep (uncomputeStep x) = x

namespace DecomposedStageWithFullRoundWorkspaceWitness

/-- Package a Montgomery--Kaliski full-workspace compute witness as the compute
leg of the staged decomposed inversion wrapper.  The supplied compute witness
must use the standard full-round work encoding; data-dependent selected-branch
round dispatch remains a separate obligation. -/
def ofKaliskiSameCircuit {n counterWidth : Nat}
    {computeStep uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth}
    (w : BaseGateSameCircuitWitness
      (MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth)
      computeStep)
    (hencoding :
      w.encoding =
        MontgomeryKaliski.registersWithFullRoundWorkEncoding n counterWidth)
    (hright : ∀ x, computeStep (uncomputeStep x) = x) :
    DecomposedStageWithFullRoundWorkspaceWitness n counterWidth := by
  cases w with
  | mk encoding program realizes =>
      dsimp at hencoding
      subst encoding
      let kaliskiWitness :
          BaseGateSameCircuitWitness
            (MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth)
            computeStep :=
        { encoding :=
            MontgomeryKaliski.registersWithFullRoundWorkEncoding
              n counterWidth
          program := program
          realizes := realizes }
      refine
        { computeStep := stageWithFullRoundWorkspaceKaliskiStep computeStep
          uncomputeStep := stageWithFullRoundWorkspaceKaliskiStep uncomputeStep
          computeProgram :=
            (stageWithFullRoundWorkspaceKaliskiSameCircuit
              kaliskiWitness).program
          computeRealizes := ?_
          compute_rightInverse := ?_ }
      · exact
          (stageWithFullRoundWorkspaceKaliskiSameCircuit
            kaliskiWitness).realizes
      · intro x
        cases x
        simp [stageWithFullRoundWorkspaceKaliskiStep, hright]

/-- Package one explicit Montgomery--Kaliski active-branch full-round witness
as the compute leg of the staged decomposed inversion wrapper.  This exposes
the fixed-branch family through the standard full-round work encoding; the
data-dependent branch selector remains a separate compute obligation. -/
def ofKaliskiActiveBranchSameCircuit {n counterWidth : Nat}
    (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : MontgomeryKaliski.Branch)
    (uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundWork n counterWidth)
    (hright :
      ∀ x,
        MontgomeryKaliski.fullRoundWorkKaliskiActiveBranchRoundStep
          n counterWidth uIndex vIndex comparisonIndex historyIndex branch
          (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness n counterWidth :=
  ofKaliskiSameCircuit
    (MontgomeryKaliski.fullRoundWorkKaliskiActiveBranchRoundSameCircuit
      n counterWidth uIndex vIndex comparisonIndex historyIndex branch)
    (MontgomeryKaliski.fullRoundWorkKaliskiActiveBranchRoundSameCircuit_encoding
      n counterWidth uIndex vIndex comparisonIndex historyIndex branch)
    hright

/-- Package the terminating counter-mode full-round witness as the compute leg
of the staged decomposed inversion wrapper.  The witness uses the standard
full-round work encoding, so it can be consumed by the same adapter as the
active branch routes. -/
def ofKaliskiTerminatingSameCircuit {tail counterWidth : Nat}
    (uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MontgomeryKaliski.fullRoundWorkTerminatingStep tail counterWidth
          (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliskiSameCircuit
    (MontgomeryKaliski.fullRoundWorkTerminatingStandardLayoutSameCircuit
      tail counterWidth)
    (MontgomeryKaliski.fullRoundWorkTerminatingStandardLayoutSameCircuit_encoding
      tail counterWidth)
    hright

/-- Package the inactive padding full-round witness as the compute leg of the
staged decomposed inversion wrapper.  This covers the inactive fixed-round
padding route under the standard full-round work encoding. -/
def ofKaliskiInactivePaddingSameCircuit {tail counterWidth : Nat}
    (uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MontgomeryKaliski.fullRoundWorkInactivePaddingStep tail counterWidth
          (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliskiSameCircuit
    (MontgomeryKaliski.fullRoundWorkInactivePaddingSameCircuit
      tail counterWidth)
    (MontgomeryKaliski.fullRoundWorkInactivePaddingSameCircuit_encoding
      tail counterWidth)
    hright

/-- Package the selected branch-code/history/aux-shift full-round dispatch as
the compute leg of the staged decomposed inversion wrapper.  This is the
gate-level selected branch-code dispatch used by the even nonzero cases; the
odd carried dispatch and outer data-dependent selector remain separate
obligations. -/
def ofKaliskiSelectedBranchCodeDispatchSameCircuit
    {tail counterWidth : Nat}
    (tempIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MontgomeryKaliski.fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliskiSameCircuit
    (MontgomeryKaliski.fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchSameCircuit
      tail counterWidth tempIndex historyIndex)
    (MontgomeryKaliski.fullRoundWorkSelectedBranchCodeDispatchSameCircuit_encoding
      tail counterWidth tempIndex historyIndex)
    hright

/-- Package the compare-conditioned carried odd dispatch as the compute leg of
the staged decomposed inversion wrapper.  This supplies a concrete gate-level
route for the odd carried branch code; the outer active-round selector and full
compute instantiation remain separate obligations. -/
def ofKaliskiCompareCarriedDispatchSameCircuit
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MontgomeryKaliski.fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliskiSameCircuit
    (MontgomeryKaliski.fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchSameCircuit
      tail counterWidth comparisonIndex historyIndex)
    (MontgomeryKaliski.fullRoundWorkCompareCarriedDispatchSameCircuit_encoding
      tail counterWidth comparisonIndex historyIndex)
    hright

/-- Package the odd-odd latch-then-body full-round dispatch as the compute leg
of the staged decomposed inversion wrapper.  The supplied compute leg carries
its own reversed uncompute witness, so the latched counter carry-in bit is
cleaned by reversing the same wire-addressed program rather than by
recomputing branch predicates after the data path mutates source words. -/
def ofKaliskiOddOddLatchThenBodySameCircuit
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  open MontgomeryKaliski in
  ofKaliskiSameCircuit
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchSameCircuit
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchSameCircuit_encoding
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkOddOddLatchThenBody_compute_rightInverse
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Package the active-guarded odd-odd latch-then-body full-round dispatch as
the compute leg of the staged decomposed inversion wrapper.  The compute leg
carries its reversed uncompute witness, so the active-guarded counter carry-in
latch is cleaned by reversing the same wire-addressed program. -/
def ofKaliskiActiveOddOddLatchThenBodySameCircuit
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  open MontgomeryKaliski in
  ofKaliskiSameCircuit
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchSameCircuit
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchSameCircuit_encoding
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkActiveOddOddLatchThenBody_compute_rightInverse
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The public semantic update selected by a full-workspace witness. -/
def step {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth :=
  reversibleScheduleStepWithFullRoundWorkspace
    n counterWidth w.computeStep w.uncomputeStep

/-- Compute, target-add over the same full workspace, and reverse-compute as
one base-gate program. -/
def program {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    BaseGateProgram
      (stageWithFullRoundWorkspaceEncoding n counterWidth).width :=
  BaseGateProgram.append w.computeProgram
    (BaseGateProgram.append
      (stageWithFullRoundWorkspaceTargetAddSameCircuit
        n counterWidth).program
      (BaseGateProgram.inverse w.computeProgram))

/-- The decomposed full-round-workspace program realizes the selected
compute/add/uncompute semantic update. -/
theorem realizes {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    BaseGateProgram.Realizes
      (stageWithFullRoundWorkspaceEncoding n counterWidth)
      w.program w.step := by
  have htarget :
      BaseGateProgram.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        (stageWithFullRoundWorkspaceTargetAddSameCircuit
          n counterWidth).program
        (addScratchToTargetWithFullRoundWorkspace n counterWidth) := by
    simpa [stageWithFullRoundWorkspaceTargetAddSameCircuit,
      stageWithFullRoundWorkspaceEncoding] using
      (stageWithFullRoundWorkspaceTargetAddSameCircuit
        n counterWidth).realizes
  have huncompute :
      BaseGateProgram.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        (BaseGateProgram.inverse w.computeProgram) w.uncomputeStep :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.computeRealizes
      w.compute_rightInverse
  have htail :
      BaseGateProgram.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        (BaseGateProgram.append
          (stageWithFullRoundWorkspaceTargetAddSameCircuit
            n counterWidth).program
          (BaseGateProgram.inverse w.computeProgram))
        (fun x : StageWithFullRoundWorkspace n counterWidth =>
          w.uncomputeStep
            (addScratchToTargetWithFullRoundWorkspace n counterWidth x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := addScratchToTargetWithFullRoundWorkspace n counterWidth)
      (secondStep := w.uncomputeStep)
      htarget huncompute
  have hfull :
      BaseGateProgram.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        w.program w.step :=
    BaseGateProgram.Realizes.append
      (firstStep := w.computeStep)
      (secondStep := fun x : StageWithFullRoundWorkspace n counterWidth =>
        w.uncomputeStep
          (addScratchToTargetWithFullRoundWorkspace n counterWidth x))
      w.computeRealizes htail
  simpa [program, step, reversibleScheduleStepWithFullRoundWorkspace] using
    hfull

/-- Running the reversed compute semantics after the compute leg restores the
full fixed-round workspace.  This derives the forward cleanup projection from
the realized reversible program plus the supplied semantic right inverse. -/
theorem compute_leftInverse {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    ∀ x, w.uncomputeStep (w.computeStep x) = x := by
  intro x
  have hinj := BaseGateProgram.Realizes.injective w.computeRealizes
  apply hinj
  exact w.compute_rightInverse (w.computeStep x)

/-- Same-Circuit witness induced by the full-round-workspace decomposed staged
program. -/
def baseWitness {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    BaseGateSameCircuitWitness
      (StageWithFullRoundWorkspace n counterWidth) w.step where
  encoding := stageWithFullRoundWorkspaceEncoding n counterWidth
  program := w.program
  realizes := w.realizes

/-- The full-round-workspace decomposed inversion circuit history bottoms out
in X/CNOT/Toffoli atoms. -/
theorem structured {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all full-round-workspace staged inversion
labels. -/
theorem apply_ket {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth)
    (x : StageWithFullRoundWorkspace n counterWidth) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits
            (stageWithFullRoundWorkspaceEncoding n counterWidth).width)
          ((stageWithFullRoundWorkspaceEncoding n counterWidth).encode x) :
          PureState (Qubits
            (stageWithFullRoundWorkspaceEncoding n counterWidth).width)) :
          StateVector (Qubits
            (stageWithFullRoundWorkspaceEncoding n counterWidth).width)) =
      (PureState.ket
        (R := Qubits
          (stageWithFullRoundWorkspaceEncoding n counterWidth).width)
        ((stageWithFullRoundWorkspaceEncoding n counterWidth).encode
          (w.step x)) :
        StateVector (Qubits
          (stageWithFullRoundWorkspaceEncoding n counterWidth).width)) := by
  simpa [baseWitness] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Resource counters are projected from the same full-round-workspace
decomposed inversion circuit. -/
theorem resources_eq {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same full-round-workspace decomposed
inversion circuit. -/
theorem depth_eq {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same full-round-workspace decomposed
inversion circuit. -/
theorem queryDepth_eq {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

end DecomposedStageWithFullRoundWorkspaceWitness

/-- Workspace-aware compute/add/uncompute schedule over the path/control
fixed-round workspace.  The compute leg may leave the path/control workspace
dirty; the reversed base-gate program must clean it through the supplied
semantic right inverse. -/
def reversibleScheduleStepWithFullRoundPathControlWorkspace
    (n counterWidth : Nat)
    (computeStep uncomputeStep :
      StageWithFullRoundPathControlWorkspace n counterWidth ->
        StageWithFullRoundPathControlWorkspace n counterWidth) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  fun x =>
    uncomputeStep
      (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth
        (computeStep x))

/-- Decomposed staged inversion witness over the path/control
Montgomery--Kaliski fixed-round workspace.  This adapter consumes the
path/control route without treating the clean-restoring semantic total
selector as a reversible compute target. -/
structure DecomposedStageWithFullRoundPathControlWorkspaceWitness
    (n counterWidth : Nat) where
  /-- Semantic action of the supplied compute program. -/
  computeStep :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth
  /-- Semantic action used by the reversed compute program. -/
  uncomputeStep :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth
  /-- Program for the path/control Montgomery--Kaliski compute leg. -/
  computeProgram :
    BaseGateProgram
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width
  /-- Correctness of the compute program on path/control workspace labels. -/
  computeRealizes :
    BaseGateProgram.Realizes
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
      computeProgram computeStep
  /-- The supplied uncompute semantic action is a right inverse of compute. -/
  compute_rightInverse : ∀ x, computeStep (uncomputeStep x) = x

namespace DecomposedStageWithFullRoundPathControlWorkspaceWitness

/-- Package a path/control Montgomery--Kaliski compute witness as the compute
leg of the staged decomposed inversion wrapper. -/
def ofKaliskiSameCircuit {n counterWidth : Nat}
    {computeStep uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
          n counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundPathControlWork
          n counterWidth}
    (w : BaseGateSameCircuitWitness
      (MontgomeryKaliski.RegistersWithFullRoundPathControlWork
        n counterWidth) computeStep)
    (hencoding :
      w.encoding =
        MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
          n counterWidth)
    (hright : ∀ x, computeStep (uncomputeStep x) = x) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness n counterWidth := by
  cases w with
  | mk encoding program realizes =>
      dsimp at hencoding
      subst encoding
      let kaliskiWitness :
          BaseGateSameCircuitWitness
            (MontgomeryKaliski.RegistersWithFullRoundPathControlWork
              n counterWidth)
            computeStep :=
        { encoding :=
            MontgomeryKaliski.registersWithFullRoundPathControlWorkEncoding
              n counterWidth
          program := program
          realizes := realizes }
      refine
        { computeStep :=
            stageWithFullRoundPathControlWorkspaceKaliskiStep computeStep
          uncomputeStep :=
            stageWithFullRoundPathControlWorkspaceKaliskiStep uncomputeStep
          computeProgram :=
            (stageWithFullRoundPathControlWorkspaceKaliskiSameCircuit
              kaliskiWitness).program
          computeRealizes := ?_
          compute_rightInverse := ?_ }
      · exact
          (stageWithFullRoundPathControlWorkspaceKaliskiSameCircuit
            kaliskiWitness).realizes
      · intro x
        cases x
        simp [stageWithFullRoundPathControlWorkspaceKaliskiStep, hright]

/-- Package the folded fixed-round path/control route as the compute leg of the
staged decomposed inversion wrapper.  The supplied uncompute step is kept
explicit so callers can use the reversed same program once a semantic inverse
for the folded route is available. -/
def ofKaliskiFixedRoundPathControlSameCircuit
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (uncomputeStep :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork
          tail.succ counterWidth ->
        MontgomeryKaliski.RegistersWithFullRoundPathControlWork
          tail.succ counterWidth)
    (hright :
      ∀ x,
        MontgomeryKaliski.fixedRoundPathControlWorkKaliskiRoundFoldStep
          tail counterWidth comparisonIndex workIndex (uncomputeStep x) =
        x) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness
      tail.succ counterWidth :=
  ofKaliskiSameCircuit
    (MontgomeryKaliski.fixedRoundPathControlWorkKaliskiRoundFoldSameCircuit
      tail counterWidth comparisonIndex workIndex)
    (by rfl)
    hright

/-- Package the folded fixed-round path/control route using the semantic
inverse selected from the finite reversible workspace.  The concrete uncompute
program remains the inverse of the same folded path/control compute program. -/
noncomputable def ofKaliskiFixedRoundPathControlFiniteInverseSameCircuit
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness
      tail.succ counterWidth :=
  ofKaliskiFixedRoundPathControlSameCircuit comparisonIndex workIndex
    (MontgomeryKaliski.fixedRoundPathControlWorkKaliskiRoundFoldUncomputeStep
      tail counterWidth comparisonIndex workIndex)
    (MontgomeryKaliski.fixedRoundPathControlWorkKaliskiRoundFold_compute_rightInverse
      tail counterWidth comparisonIndex workIndex)

/-- The public semantic update selected by a path/control full-workspace
witness. -/
def step {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  reversibleScheduleStepWithFullRoundPathControlWorkspace
    n counterWidth w.computeStep w.uncomputeStep

/-- Compute, target-add over the same path/control workspace, and
reverse-compute as one base-gate program. -/
def program {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    BaseGateProgram
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width :=
  BaseGateProgram.append w.computeProgram
    (BaseGateProgram.append
      (stageWithFullRoundPathControlWorkspaceTargetAddSameCircuit
        n counterWidth).program
      (BaseGateProgram.inverse w.computeProgram))

/-- The decomposed path/control workspace program realizes the selected
compute/add/uncompute semantic update. -/
theorem realizes {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    BaseGateProgram.Realizes
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
      w.program w.step := by
  have htarget :
      BaseGateProgram.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        (stageWithFullRoundPathControlWorkspaceTargetAddSameCircuit
          n counterWidth).program
        (addScratchToTargetWithFullRoundPathControlWorkspace
          n counterWidth) := by
    simpa [stageWithFullRoundPathControlWorkspaceTargetAddSameCircuit,
      stageWithFullRoundPathControlWorkspaceEncoding] using
      (stageWithFullRoundPathControlWorkspaceTargetAddSameCircuit
        n counterWidth).realizes
  have huncompute :
      BaseGateProgram.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        (BaseGateProgram.inverse w.computeProgram) w.uncomputeStep :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.computeRealizes
      w.compute_rightInverse
  have htail :
      BaseGateProgram.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        (BaseGateProgram.append
          (stageWithFullRoundPathControlWorkspaceTargetAddSameCircuit
            n counterWidth).program
          (BaseGateProgram.inverse w.computeProgram))
        (fun x : StageWithFullRoundPathControlWorkspace n counterWidth =>
          w.uncomputeStep
            (addScratchToTargetWithFullRoundPathControlWorkspace
              n counterWidth x)) :=
    BaseGateProgram.Realizes.append
      (firstStep :=
        addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth)
      (secondStep := w.uncomputeStep)
      htarget huncompute
  have hfull :
      BaseGateProgram.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        w.program w.step :=
    BaseGateProgram.Realizes.append
      (firstStep := w.computeStep)
      (secondStep :=
        fun x : StageWithFullRoundPathControlWorkspace n counterWidth =>
          w.uncomputeStep
            (addScratchToTargetWithFullRoundPathControlWorkspace
              n counterWidth x))
      w.computeRealizes htail
  simpa [program, step,
    reversibleScheduleStepWithFullRoundPathControlWorkspace] using hfull

/-- Running the reversed compute semantics after the path/control compute leg
restores the full staged workspace. -/
theorem compute_leftInverse {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    ∀ x, w.uncomputeStep (w.computeStep x) = x := by
  intro x
  have hinj := BaseGateProgram.Realizes.injective w.computeRealizes
  apply hinj
  exact w.compute_rightInverse (w.computeStep x)

/-- Same-Circuit witness induced by the path/control full-workspace decomposed
staged program. -/
def baseWitness {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    BaseGateSameCircuitWitness
      (StageWithFullRoundPathControlWorkspace n counterWidth) w.step where
  encoding := stageWithFullRoundPathControlWorkspaceEncoding n counterWidth
  program := w.program
  realizes := w.realizes

/-- The path/control decomposed inversion circuit history bottoms out in
X/CNOT/Toffoli atoms. -/
theorem structured {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    (BaseGateSameCircuitWitness.circuit
      w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all path/control full-workspace staged
inversion labels. -/
theorem apply_ket {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode x) :
          PureState (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) =
      (PureState.ket
        (R := Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)
        ((stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).encode (w.step x)) :
        StateVector (Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)) := by
  simpa [baseWitness] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Resource counters are projected from the same path/control decomposed
inversion circuit. -/
theorem resources_eq {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same path/control decomposed inversion
circuit. -/
theorem depth_eq {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same path/control decomposed inversion
circuit. -/
theorem queryDepth_eq {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

/-- Resource-correct witness for all encoded path/control full-workspace labels.
This packages the same decomposed compute / target-add / uncompute circuit object
for correctness and resource accounting, without asserting a clean unit-domain
endpoint. -/
def resourceCorrectWitness {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    ResourceCorrectWitness
      (R := Qubits
        (stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).width)
      (∀ x : StageWithFullRoundPathControlWorkspace n counterWidth,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
            ((PureState.ket
              (R := Qubits
                (stageWithFullRoundPathControlWorkspaceEncoding
                  n counterWidth).width)
              ((stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).encode x) :
              PureState (Qubits
                (stageWithFullRoundPathControlWorkspaceEncoding
                  n counterWidth).width)) :
              StateVector (Qubits
                (stageWithFullRoundPathControlWorkspaceEncoding
                  n counterWidth).width)) =
          (PureState.ket
            (R := Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)
            ((stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).encode (w.step x)) :
            StateVector (Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun x => apply_ket w x
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end DecomposedStageWithFullRoundPathControlWorkspaceWitness

/-- Decomposed staged witness whose compute leg xors the path/control
workspace's low `r` coefficient into inverse scratch.  This packages the
scratch-transfer circuit with its reversed program and the target-add bridge;
the resulting endpoint is still the raw pseudo-residue transfer, before the
Montgomery correction factor is applied. -/
noncomputable def rCoeffLowToInverseScratchDecomposedWitness
    (n counterWidth : Nat) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth where
  computeStep := rCoeffLowToInverseScratchXorStep n counterWidth
  uncomputeStep :=
    rCoeffLowToInverseScratchXorUncomputeStep n counterWidth
  computeProgram :=
    (rCoeffLowToInverseScratchXorSameCircuit n counterWidth).program
  computeRealizes :=
    (rCoeffLowToInverseScratchXorSameCircuit n counterWidth).realizes
  compute_rightInverse :=
    rCoeffLowToInverseScratchXorStep_compute_rightInverse n counterWidth

/-- Clean staged output for the decomposed raw low-`r` transfer.  The target
receives the uncorrected low `r` coefficient read from the path/control
workspace; this is still before the Montgomery correction normalization used
by the unit-inverse endpoint. -/
def cleanRawRCoeffOutputWithFullRoundPathControlWorkspace
    {n counterWidth : Nat} (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    StageWithFullRoundPathControlWorkspace n counterWidth :=
  let raw : ZMod (2 ^ n) :=
    workspace.1.1.1.1.1.rCoeff.val
  (({ input := u
      target := z + raw
      inverseScratch := 0
      flag := false }, cleanWork n), workspace)

/-- Clean endpoint of the decomposed raw low-`r` transfer wrapper.  This closes
the compute/add/uncompute shape for the finite transfer circuit, while keeping
the mathematical statement at the raw pre-correction residue boundary. -/
theorem rCoeffLowToInverseScratchDecomposedWitness_step_initial
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    (rCoeffLowToInverseScratchDecomposedWitness
        n counterWidth).step
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanRawRCoeffOutputWithFullRoundPathControlWorkspace
        u z workspace := by
  let raw : ZMod (2 ^ n) :=
    workspace.1.1.1.1.1.rCoeff.val
  let y : StageWithFullRoundPathControlWorkspace n counterWidth :=
    ((StageState.initial u (z + raw), cleanWork n), workspace)
  unfold DecomposedStageWithFullRoundPathControlWorkspaceWitness.step
  unfold reversibleScheduleStepWithFullRoundPathControlWorkspace
  change
    rCoeffLowToInverseScratchXorUncomputeStep n counterWidth
      (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth
        (rCoeffLowToInverseScratchXorStep n counterWidth
          ((StageState.initial u z, cleanWork n), workspace))) =
    cleanRawRCoeffOutputWithFullRoundPathControlWorkspace
      u z workspace
  rw [rCoeffLowToInverseScratchXorStep_initial]
  rw [addScratchToTargetWithFullRoundPathControlWorkspace_cleanEndpoint]
  · have htarget :
        ((StageState.addScratchToTarget
            { input := u
              target := z
              inverseScratch := raw
              flag := false }, cleanWork n), workspace) =
          rCoeffLowToInverseScratchXorStep n counterWidth y := by
      rw [rCoeffLowToInverseScratchXorStep_initial]
      simp [raw, StageState.addScratchToTarget]
    rw [htarget]
    simpa [y, cleanRawRCoeffOutputWithFullRoundPathControlWorkspace,
      StageState.initial, raw, rCoeffLowToInverseScratchDecomposedWitness] using
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.compute_leftInverse
        (rCoeffLowToInverseScratchDecomposedWitness n counterWidth) y
  · rfl

/-- Encoded-basis clean action for the decomposed raw low-`r` transfer
circuit.  The statement is deliberately raw/pre-correction; the same
`baseWitness.circuit` remains the object used for resource accounting through
`resourceCorrectWitness`. -/
theorem rCoeffLowToInverseScratchDecomposedWitness_apply_clean_raw_ket
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    Circuit.apply
        (BaseGateSameCircuitWitness.circuit
          (rCoeffLowToInverseScratchDecomposedWitness
            n counterWidth).baseWitness)
        ((PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode
            ((StageState.initial u z, cleanWork n), workspace)) :
          PureState (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) =
      (PureState.ket
        (R := Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)
        ((stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).encode
          (cleanRawRCoeffOutputWithFullRoundPathControlWorkspace
            u z workspace)) :
        StateVector (Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)) := by
  simpa [rCoeffLowToInverseScratchDecomposedWitness_step_initial]
    using
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.apply_ket
        (rCoeffLowToInverseScratchDecomposedWitness n counterWidth)
        ((StageState.initial u z, cleanWork n), workspace)

/-- Compute the inverse scratch while preserving the target-add carry work. -/
def addInverseToScratchWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n
  | (s, work) => (addInverseToScratch s, work)

/-- Reverse the inverse-scratch computation while preserving carry work. -/
def subInverseFromScratchWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n
  | (s, work) => (subInverseFromScratch s, work)

@[simp] theorem addInverseToScratchWithWork_subInverseFromScratchWithWork
    (n : Nat) (x : StageWithWork n) :
    addInverseToScratchWithWork n (subInverseFromScratchWithWork n x) = x := by
  rcases x with ⟨s, work⟩
  simp [addInverseToScratchWithWork, subInverseFromScratchWithWork]

/-- Work-aware reversible inversion schedule:
compute inverse scratch, add scratch into the target through the explicit VBE
carry-work bridge, then uncompute inverse scratch [RNSL17,
ECDLP.tex:390-465,753-755; VBE95, 9511018.tex:237-264,591-618]. -/
def reversibleScheduleStepWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n :=
  fun x =>
    subInverseFromScratchWithWork n
      (addScratchToTargetWithWork n
        (addInverseToScratchWithWork n x))

/-- The work-aware decomposed schedule agrees with the clean public inversion
action when scratch, flag, and carry work start clean. -/
theorem reversibleScheduleStepWithWork_initial
    (n : Nat) (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n)) :
    reversibleScheduleStepWithWork n (initial u z, cleanWork n) =
      (({ input := u
          target := z + inverseResidue u
          inverseScratch := 0
          flag := false } : StageState (2 ^ n)),
        cleanWork n) := by
  unfold reversibleScheduleStepWithWork addInverseToScratchWithWork
    subInverseFromScratchWithWork
  rw [addScratchToTargetWithWork_cleanEndpoint n
    (addInverseToScratch (initial u z))]
  · simp [initial, addInverseToScratch, addScratchToTarget,
      subInverseFromScratch]
  · simp [initial, addInverseToScratch]

/-- Decomposed staged inversion witness with explicit VBE target-add carry work.
The target-add leg is fixed to `stageWithWorkSameCircuit`; a closing proof must
still provide the inverse-scratch compute program under the same stage/work
encoding.  The compute program must instantiate the `MontgomeryKaliski.Trace`
fixed-round state machine, including the `2n` round count and per-round `m_i`
history bits from the public RNSL17 circuit [RNSL17,
ECDLP.tex:390-465,753-755]. -/
structure DecomposedStageWithTargetAddWitness (n : Nat) where
  /-- Program adding the inverse residue into scratch, in the same work-aware
  stage encoding used by the target-add bridge. -/
  computeProgram :
    BaseGateProgram (stageWithWorkSameCircuit n).encoding.width
  /-- Correctness of the compute program on stage/work labels. -/
  computeRealizes :
    BaseGateProgram.Realizes (stageWithWorkSameCircuit n).encoding
      computeProgram (addInverseToScratchWithWork n)

namespace DecomposedStageWithTargetAddWitness

/-- Compute, work-aware target-add, and reverse-compute as one base-gate
program. -/
def program {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    BaseGateProgram (stageWithWorkSameCircuit n).encoding.width :=
  BaseGateProgram.append w.computeProgram
    (BaseGateProgram.append (stageWithWorkSameCircuit n).program
      (BaseGateProgram.inverse w.computeProgram))

/-- The decomposed work-aware program realizes the reversible inversion
schedule with explicit carry work. -/
theorem realizes {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    BaseGateProgram.Realizes (stageWithWorkSameCircuit n).encoding w.program
      (reversibleScheduleStepWithWork n) := by
  have huncompute :
      BaseGateProgram.Realizes (stageWithWorkSameCircuit n).encoding
        (BaseGateProgram.inverse w.computeProgram)
        (subInverseFromScratchWithWork n) :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.computeRealizes
      (addInverseToScratchWithWork_subInverseFromScratchWithWork n)
  have htail :
      BaseGateProgram.Realizes (stageWithWorkSameCircuit n).encoding
        (BaseGateProgram.append (stageWithWorkSameCircuit n).program
          (BaseGateProgram.inverse w.computeProgram))
        (fun x : StageWithWork n =>
          subInverseFromScratchWithWork n
            (addScratchToTargetWithWork n x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := addScratchToTargetWithWork n)
      (secondStep := subInverseFromScratchWithWork n)
      (stageWithWorkSameCircuit n).realizes huncompute
  have hfull :
      BaseGateProgram.Realizes (stageWithWorkSameCircuit n).encoding w.program
        (reversibleScheduleStepWithWork n) :=
    BaseGateProgram.Realizes.append
      (firstStep := addInverseToScratchWithWork n)
      (secondStep := fun x : StageWithWork n =>
        subInverseFromScratchWithWork n
          (addScratchToTargetWithWork n x))
      w.computeRealizes htail
  simpa [program, reversibleScheduleStepWithWork] using hfull

/-- Same-Circuit witness induced by the work-aware decomposed staged program. -/
def baseWitness {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    BaseGateSameCircuitWitness (StageWithWork n)
      (reversibleScheduleStepWithWork n) where
  encoding := (stageWithWorkSameCircuit n).encoding
  program := w.program
  realizes := w.realizes

/-- The work-aware decomposed inversion circuit history bottoms out in
X/CNOT/Toffoli atoms. -/
theorem structured {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all work-aware staged inversion labels. -/
theorem apply_ket {n : Nat}
    (w : DecomposedStageWithTargetAddWitness n) (x : StageWithWork n) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (stageWithWorkSameCircuit n).encoding.width)
          ((stageWithWorkSameCircuit n).encoding.encode x) :
          PureState (Qubits (stageWithWorkSameCircuit n).encoding.width)) :
          StateVector (Qubits (stageWithWorkSameCircuit n).encoding.width)) =
      (PureState.ket
        (R := Qubits (stageWithWorkSameCircuit n).encoding.width)
        ((stageWithWorkSameCircuit n).encoding.encode
          (reversibleScheduleStepWithWork n x)) :
        StateVector (Qubits (stageWithWorkSameCircuit n).encoding.width)) := by
  simpa [baseWitness] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Clean encoded-basis action for the work-aware decomposed staged inversion
wrapper. -/
theorem apply_clean_ket {n : Nat}
    (w : DecomposedStageWithTargetAddWitness n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n)) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (stageWithWorkSameCircuit n).encoding.width)
          ((stageWithWorkSameCircuit n).encoding.encode
            (initial u z, cleanWork n)) :
          PureState (Qubits (stageWithWorkSameCircuit n).encoding.width)) :
          StateVector (Qubits (stageWithWorkSameCircuit n).encoding.width)) =
      (PureState.ket
        (R := Qubits (stageWithWorkSameCircuit n).encoding.width)
        ((stageWithWorkSameCircuit n).encoding.encode
          (({ input := u
              target := z + inverseResidue u
              inverseScratch := 0
              flag := false } : StageState (2 ^ n)),
            cleanWork n)) :
        StateVector (Qubits (stageWithWorkSameCircuit n).encoding.width)) := by
  simpa [baseWitness, reversibleScheduleStepWithWork_initial] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness
      (initial u z, cleanWork n)

/-- Resource counters are projected from the same work-aware decomposed
inversion circuit. -/
theorem resources_eq {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same work-aware decomposed inversion
circuit. -/
theorem depth_eq {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same work-aware decomposed inversion
circuit. -/
theorem queryDepth_eq {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

/-- Resource-correct witness for the clean work-aware staged inversion
statement, conditional on the supplied compute subprogram and the fixed VBE
target-add bridge [RNSL17, ECDLP.tex:390-465,753-755; VBE95,
9511018.tex:237-264,591-618]. -/
def cleanResourceCorrectWitness {n : Nat}
    (w : DecomposedStageWithTargetAddWitness n) :
    ResourceCorrectWitness
      (R := Qubits (stageWithWorkSameCircuit n).encoding.width)
      (∀ u : (ZMod (2 ^ n))ˣ, ∀ z : ZMod (2 ^ n),
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket
            (R := Qubits (stageWithWorkSameCircuit n).encoding.width)
            ((stageWithWorkSameCircuit n).encoding.encode
              (initial u z, cleanWork n)) :
            PureState (Qubits (stageWithWorkSameCircuit n).encoding.width)) :
            StateVector (Qubits (stageWithWorkSameCircuit n).encoding.width)) =
          (PureState.ket
            (R := Qubits (stageWithWorkSameCircuit n).encoding.width)
            ((stageWithWorkSameCircuit n).encoding.encode
              (({ input := u
                  target := z + inverseResidue u
                  inverseScratch := 0
                  flag := false } : StageState (2 ^ n)),
                cleanWork n)) :
            StateVector (Qubits (stageWithWorkSameCircuit n).encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun u z => apply_clean_ket w u z
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end DecomposedStageWithTargetAddWitness

end PowerOfTwoTargetAdd

/- Finite two-bit integration smoke for the staged target-add bridge.  This
reuses the concrete `ZMod 4` Toffoli/CNOT/CNOT target-add program inside the
field-packed inversion stage layout; it is not the full inversion compute
program [RNSL17, ECDLP.tex:390-465]. -/
namespace Mod4TargetAdd

/-- Tuple-level staged target-add witness induced by the concrete `ZMod 4`
modular-addition target update. -/
def tupleWitness :
    TupleTargetAddWitness ModularAddition.TargetAdd.Mod4.residueEncoding :=
  TupleTargetAddWitness.ofModularAddition
    ModularAddition.TargetAdd.Mod4.witness

/-- Same-Circuit staged target-add witness over the inversion `StageState 4`
field-packed encoding. -/
def sameCircuit :
    BaseGateSameCircuitWitness (StageState 4) addScratchToTarget :=
  tupleWitness.stageWitness

/-- The concrete `ZMod 4` target-add program realizes the staged target update
after relabeling through the inversion field tuple. -/
theorem realizes :
    BaseGateProgram.Realizes
      (fieldEncoding ModularAddition.TargetAdd.Mod4.residueEncoding)
      tupleWitness.program addScratchToTarget :=
  tupleWitness.stage_realizes

end Mod4TargetAdd

end StageState

namespace MontgomeryKaliski
namespace Trace

/-- Add the trace-corrected inverse residue into the staged scratch register.
This is the additive form needed by compute/add/uncompute decompositions. -/
def addCorrectedInverseToScratch {n p : Nat}
    (trace : Trace n) (s : StageState p) : StageState p where
  input := s.input
  target := s.target
  inverseScratch := s.inverseScratch + trace.correctedInverseResidue p
  flag := s.flag

/-- Reverse the additive transfer of the trace-corrected inverse residue from
the staged scratch register. -/
def subCorrectedInverseFromScratch {n p : Nat}
    (trace : Trace n) (s : StageState p) : StageState p where
  input := s.input
  target := s.target
  inverseScratch := s.inverseScratch - trace.correctedInverseResidue p
  flag := s.flag

@[simp] theorem addCorrectedInverseToScratch_subCorrectedInverseFromScratch
    {n p : Nat} (trace : Trace n) (s : StageState p) :
    trace.addCorrectedInverseToScratch
        (trace.subCorrectedInverseFromScratch s) = s := by
  cases s
  simp [addCorrectedInverseToScratch, subCorrectedInverseFromScratch,
    sub_eq_add_neg, add_assoc]

@[simp] theorem subCorrectedInverseFromScratch_addCorrectedInverseToScratch
    {n p : Nat} (trace : Trace n) (s : StageState p) :
    trace.subCorrectedInverseFromScratch
        (trace.addCorrectedInverseToScratch s) = s := by
  cases s
  simp [addCorrectedInverseToScratch, subCorrectedInverseFromScratch,
    sub_eq_add_neg, add_assoc]

/-- When the trace-corrected residue is the staged unit inverse, the additive
trace transfer agrees with the generic inverse-scratch compute step. -/
theorem addCorrectedInverseToScratch_eq_addInverseToScratch_of_matches
    {n p : Nat} (trace : Trace n) (s : StageState p)
    (hmatch : trace.CorrectedResidueMatchesUnitInverse s.input) :
    trace.addCorrectedInverseToScratch s =
      StageState.addInverseToScratch s := by
  cases s with
  | mk input target inverseScratch flag =>
      change trace.correctedInverseResidue p = inverseResidue input at hmatch
      change
        ({ input := input
           target := target
           inverseScratch := inverseScratch +
             trace.correctedInverseResidue p
           flag := flag } : StageState p) =
          { input := input
            target := target
            inverseScratch := inverseScratch + inverseResidue input
            flag := flag }
      rw [hmatch]

end Trace
end MontgomeryKaliski

namespace StageState
namespace PowerOfTwoTargetAdd

/-- Lift trace-corrected additive inverse-scratch transfer over the target-add
carry work and the path/control fixed-round workspace. -/
def addCorrectedInverseToScratchWithFullRoundPathControlWorkspace
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth
  | ((s, work), workspace) =>
      ((trace.addCorrectedInverseToScratch s, work), workspace)

/-- Lift trace-corrected inverse-scratch subtraction over the target-add carry
work and the path/control fixed-round workspace. -/
def subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth
  | ((s, work), workspace) =>
      ((trace.subCorrectedInverseFromScratch s, work), workspace)

@[simp] theorem
    addCorrectedInverseToScratchWithFullRoundPathControlWorkspace_sub
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    addCorrectedInverseToScratchWithFullRoundPathControlWorkspace trace
        (subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace
          trace x) = x := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  simp [addCorrectedInverseToScratchWithFullRoundPathControlWorkspace,
    subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace]

@[simp] theorem
    subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace_add
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace trace
        (addCorrectedInverseToScratchWithFullRoundPathControlWorkspace
          trace x) = x := by
  rcases x with ⟨⟨s, work⟩, workspace⟩
  simp [addCorrectedInverseToScratchWithFullRoundPathControlWorkspace,
    subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace]

/-- Under the corrected-residue match condition, the lifted trace transfer
agrees with the generic inverse-scratch compute step while preserving both
workspaces. -/
theorem
    addCorrectedInverseToScratchWithFullRoundPathControlWorkspace_eq_addInverseToScratchWithWork
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n)
    (s : StageState (2 ^ n)) (work : CarryWork n)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hmatch : trace.CorrectedResidueMatchesUnitInverse s.input) :
    addCorrectedInverseToScratchWithFullRoundPathControlWorkspace
        (n := n) (counterWidth := counterWidth) trace
        ((s, work), workspace) =
      (addInverseToScratchWithWork n (s, work), workspace) := by
  simp [addCorrectedInverseToScratchWithFullRoundPathControlWorkspace,
    addInverseToScratchWithWork,
    MontgomeryKaliski.Trace.addCorrectedInverseToScratch_eq_addInverseToScratch_of_matches
      trace s hmatch]

/-- Compute/add/uncompute schedule for a trace-corrected additive transfer,
lifted over target-add carry work and the path/control fixed-round workspace. -/
def traceCorrectedReversibleScheduleStepWithFullRoundPathControlWorkspace
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  fun x =>
    subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace trace
      (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth
        (addCorrectedInverseToScratchWithFullRoundPathControlWorkspace
          trace x))

/-- Clean staged output after adding the unit inverse to the target while
restoring the inverse scratch and target-add carry work. -/
def cleanInverseOutputWithFullRoundPathControlWorkspace
    {n counterWidth : Nat} (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    StageWithFullRoundPathControlWorkspace n counterWidth :=
  let finalState : StageState (2 ^ n) :=
    { input := u
      target := z + inverseResidue u
      inverseScratch := 0
      flag := false }
  ((finalState, cleanWork n), workspace)

/-- Clean unit-inverse endpoint for the decomposed raw-transfer circuit under
an explicit raw-residue bridge.  The premise is intentionally not hidden: the
Montgomery correction/formulation route must prove that the workspace low `r`
coefficient is already the staged inverse before this theorem can be applied as
the final unit-domain endpoint. -/
theorem
    rCoeffLowToInverseScratchDecomposedWitness_step_initial_of_raw_inverse
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hraw :
      (workspace.1.1.1.1.1.rCoeff.val : ZMod (2 ^ n)) =
        inverseResidue u) :
    (rCoeffLowToInverseScratchDecomposedWitness
        n counterWidth).step
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanInverseOutputWithFullRoundPathControlWorkspace u z workspace := by
  rw [rCoeffLowToInverseScratchDecomposedWitness_step_initial]
  simp [cleanRawRCoeffOutputWithFullRoundPathControlWorkspace,
    cleanInverseOutputWithFullRoundPathControlWorkspace, hraw]

/-- Encoded-basis clean unit-inverse action for the decomposed raw-transfer
circuit under the same explicit raw-residue bridge.  Correctness and resource
accounting still use the same `baseWitness.circuit`; this theorem only exposes
the clean ket specialization once the raw/corrected residue bridge is supplied. -/
theorem
    rCoeffLowToInverseScratchDecomposedWitness_apply_clean_ket_of_raw_inverse
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hraw :
      (workspace.1.1.1.1.1.rCoeff.val : ZMod (2 ^ n)) =
        inverseResidue u) :
    Circuit.apply
        (BaseGateSameCircuitWitness.circuit
          (rCoeffLowToInverseScratchDecomposedWitness
            n counterWidth).baseWitness)
        ((PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode
            ((StageState.initial u z, cleanWork n), workspace)) :
          PureState (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) =
      (PureState.ket
        (R := Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)
        ((stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).encode
          (cleanInverseOutputWithFullRoundPathControlWorkspace
            u z workspace)) :
        StateVector (Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)) := by
  simpa [
    rCoeffLowToInverseScratchDecomposedWitness_step_initial_of_raw_inverse,
    hraw] using
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.apply_ket
        (rCoeffLowToInverseScratchDecomposedWitness n counterWidth)
        ((StageState.initial u z, cleanWork n), workspace)

/-- If the concrete path/control workspace readout is a trace finish state,
then its low `r` register is exactly the trace pseudo-inverse residue in the
staged `2^n` residue ring. -/
theorem workspaceRCoeff_eq_tracePseudoInverseResidue
    (n counterWidth : Nat)
    (trace : MontgomeryKaliski.Trace n)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      MontgomeryKaliski.RoundState.fromRegisters n counterWidth
          workspace.1.1.1.1.1 trace.finish.kaliskiSteps
          trace.finish.paddingSteps =
        trace.finish) :
    (workspace.1.1.1.1.1.rCoeff.val : ZMod (2 ^ n)) =
      trace.pseudoInverseResidue (2 ^ n) := by
  have hcoeff :=
    congrArg (fun st : MontgomeryKaliski.RoundState => st.rCoeff) hfinish
  have hcoeffNat :
      workspace.1.1.1.1.1.rCoeff.val = trace.finish.rCoeff := by
    simpa [MontgomeryKaliski.RoundState.fromRegisters] using hcoeff
  rw [hcoeffNat]
  rfl

/-- Clean unit-inverse endpoint for the decomposed raw-transfer circuit from a
trace-facing pseudo-residue bridge.  This exposes the exact remaining
obligation: the trace pseudo residue, not merely the corrected residue, must be
identified with the staged inverse before this raw-transfer circuit is the
final inversion endpoint. -/
theorem
    rCoeffLowToInverseScratchDecomposedWitness_step_initial_of_trace_pseudo
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (trace : MontgomeryKaliski.Trace n)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      MontgomeryKaliski.RoundState.fromRegisters n counterWidth
          workspace.1.1.1.1.1 trace.finish.kaliskiSteps
          trace.finish.paddingSteps =
        trace.finish)
    (hpseudo :
      trace.pseudoInverseResidue (2 ^ n) = inverseResidue u) :
    (rCoeffLowToInverseScratchDecomposedWitness
        n counterWidth).step
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanInverseOutputWithFullRoundPathControlWorkspace u z workspace := by
  apply
    rCoeffLowToInverseScratchDecomposedWitness_step_initial_of_raw_inverse
  rw [workspaceRCoeff_eq_tracePseudoInverseResidue
    n counterWidth trace workspace hfinish]
  exact hpseudo

/-- Encoded-basis clean unit-inverse action for the decomposed raw-transfer
circuit from a trace-facing pseudo-residue bridge. -/
theorem
    rCoeffLowToInverseScratchDecomposedWitness_apply_clean_ket_of_trace_pseudo
    (n counterWidth : Nat)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (trace : MontgomeryKaliski.Trace n)
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      MontgomeryKaliski.RoundState.fromRegisters n counterWidth
          workspace.1.1.1.1.1 trace.finish.kaliskiSteps
          trace.finish.paddingSteps =
        trace.finish)
    (hpseudo :
      trace.pseudoInverseResidue (2 ^ n) = inverseResidue u) :
    Circuit.apply
        (BaseGateSameCircuitWitness.circuit
          (rCoeffLowToInverseScratchDecomposedWitness
            n counterWidth).baseWitness)
        ((PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode
            ((StageState.initial u z, cleanWork n), workspace)) :
          PureState (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) =
      (PureState.ket
        (R := Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)
        ((stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).encode
          (cleanInverseOutputWithFullRoundPathControlWorkspace
            u z workspace)) :
        StateVector (Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)) := by
  have hstep :=
    rCoeffLowToInverseScratchDecomposedWitness_step_initial_of_trace_pseudo
      n counterWidth u z trace workspace hfinish hpseudo
  simpa [hstep] using
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.apply_ket
        (rCoeffLowToInverseScratchDecomposedWitness n counterWidth)
        ((StageState.initial u z, cleanWork n), workspace)

/-- On clean staged input, a matching trace-corrected additive transfer updates
the target by the staged unit inverse and restores inverse scratch to zero. -/
theorem
    traceCorrectedReversibleScheduleStepWithFullRoundPathControlWorkspace_initial_of_matches
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hmatch : trace.CorrectedResidueMatchesUnitInverse u) :
    traceCorrectedReversibleScheduleStepWithFullRoundPathControlWorkspace
        (n := n) (counterWidth := counterWidth) trace
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanInverseOutputWithFullRoundPathControlWorkspace u z workspace := by
  change trace.correctedInverseResidue (2 ^ n) = inverseResidue u at hmatch
  unfold traceCorrectedReversibleScheduleStepWithFullRoundPathControlWorkspace
  unfold addCorrectedInverseToScratchWithFullRoundPathControlWorkspace
  rw [addScratchToTargetWithFullRoundPathControlWorkspace_cleanEndpoint]
  · simp [cleanInverseOutputWithFullRoundPathControlWorkspace,
      subCorrectedInverseFromScratchWithFullRoundPathControlWorkspace,
      MontgomeryKaliski.Trace.addCorrectedInverseToScratch,
      MontgomeryKaliski.Trace.subCorrectedInverseFromScratch,
      StageState.initial, StageState.addScratchToTarget, hmatch]
  · simp [MontgomeryKaliski.Trace.addCorrectedInverseToScratch,
      StageState.initial]

/-- Clean staged endpoint for the canonical unit-input trace, with both the
final-state and normalization premises explicit. -/
theorem unitTraceCorrectedScheduleStep_initial_of_final_state
    {n counterWidth : Nat} [NeZero (2 ^ n)]
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u).finish.u = 1)
    (hnormalize : -((2 : ZMod (2 ^ n)) ^ (2 * n)) = 1) :
    traceCorrectedReversibleScheduleStepWithFullRoundPathControlWorkspace
        (n := n) (counterWidth := counterWidth)
        (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanInverseOutputWithFullRoundPathControlWorkspace u z workspace := by
  exact
    traceCorrectedReversibleScheduleStepWithFullRoundPathControlWorkspace_initial_of_matches
      (n := n) (counterWidth := counterWidth)
      (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)
      u z workspace
      (MontgomeryKaliski.Trace.ofUnitInput_correctedResidueMatchesUnitInverse_of_final_state
        n (2 ^ n) u hfinish hnormalize)

private def encodedWordXIndicesStep
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width) (indices : List (Fin width)) :
    Data -> Data :=
  fun x => indices.foldl (fun y bit => (word.bit bit).flip y) x

private theorem encodedWordXIndicesStep_get_bit
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width) (indices : List (Fin width))
    (hnodup : indices.Nodup) (bit : Fin width)
    (hword :
      ∀ left right : Fin width,
        left ≠ right -> (word.bit left).wire ≠ (word.bit right).wire)
    (x : Data) :
    (word.bit bit).get (encodedWordXIndicesStep word indices x) =
      ((word.bit bit).get x ^^ decide (bit ∈ indices)) := by
  induction indices generalizing x with
  | nil =>
      simp [encodedWordXIndicesStep]
  | cons head rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hheadNotMem : head ∉ rest := hnodup.notMem
      unfold encodedWordXIndicesStep at *
      change
        (word.bit bit).get
            (rest.foldl (fun y bit => (word.bit bit).flip y)
              ((word.bit head).flip x)) =
          ((word.bit bit).get x ^^ decide (bit ∈ head :: rest))
      by_cases hhead : head = bit
      · subst head
        rw [ih hrestNodup ((word.bit bit).flip x)]
        rw [EncodedBit.get_flip_self]
        simp [hheadNotMem]
      · rw [ih hrestNodup ((word.bit head).flip x)]
        have hget :
            (word.bit bit).get ((word.bit head).flip x) =
              (word.bit bit).get x := by
          rw [EncodedBit.get_flip_of_wire_ne (word.bit head)
            (word.bit bit) (hword head bit hhead)]
        rw [hget]
        have hbitHead : bit ≠ head := Ne.symm hhead
        by_cases hmem : bit ∈ rest <;> simp [hbitHead, hmem]

private theorem encodedWordXGateList_stepList_eq_indicesStep
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width) (indices : List (Fin width)) :
    EncodedBit.GateSpec.stepList
        (indices.map fun bit => EncodedBit.GateSpec.x (word.bit bit)) =
      encodedWordXIndicesStep word indices := by
  funext x
  rw [EncodedBit.GateSpec.stepList_eq_foldl, encodedWordXIndicesStep]
  induction indices generalizing x with
  | nil =>
      rfl
  | cons bit rest ih =>
      simpa [EncodedBit.GateSpec.step] using ih ((word.bit bit).flip x)

/-- Scratch bit positions where the trace-corrected residue has value `1`.
These are the constant X gates used to load the corrected source residue into
clean inverse scratch. -/
def correctedInverseScratchXorSources
    (n : Nat) (trace : MontgomeryKaliski.Trace n) : List (Fin n) :=
  (List.ofFn fun bit : Fin n => bit).filter
    (fun bit =>
      (trace.correctedInverseResidue (2 ^ n)).val.testBit bit.val)

theorem correctedInverseScratchXorSources_nodup
    (n : Nat) (trace : MontgomeryKaliski.Trace n) :
    (correctedInverseScratchXorSources n trace).Nodup := by
  unfold correctedInverseScratchXorSources
  exact (List.nodup_ofFn_ofInjective (fun _ _ h => h)).filter _

theorem mem_correctedInverseScratchXorSources
    (n : Nat) (trace : MontgomeryKaliski.Trace n) (bit : Fin n) :
    bit ∈ correctedInverseScratchXorSources n trace ↔
      (trace.correctedInverseResidue (2 ^ n)).val.testBit bit.val = true := by
  simp [correctedInverseScratchXorSources]

/-- Constant X gates loading the trace-corrected residue into inverse scratch
when that scratch register is initially clean. -/
def correctedInverseToScratchXorGates
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n) :
    List (EncodedBit.GateSpec
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)) :=
  (correctedInverseScratchXorSources n trace).map fun bit =>
    EncodedBit.GateSpec.x
      ((stageWithFullRoundPathControlWorkspaceInverseScratchValueWord
        n counterWidth).bit bit)

/-- Semantic action of the constant corrected-residue scratch-load program. -/
def correctedInverseToScratchXorStep
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  EncodedBit.GateSpec.stepList
    (correctedInverseToScratchXorGates n counterWidth trace)

/-- Semantic action of the reversed constant corrected-residue scratch-load
program. -/
def correctedInverseFromScratchXorStep
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  EncodedBit.GateSpec.stepList
    (correctedInverseToScratchXorGates n counterWidth trace).reverse

/-- Same-Circuit witness for loading a trace-corrected constant residue into
staged inverse scratch by X gates. -/
def correctedInverseToScratchXorSameCircuit
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n) :
    BaseGateSameCircuitWitness
      (StageWithFullRoundPathControlWorkspace n counterWidth)
      (correctedInverseToScratchXorStep n counterWidth trace) where
  encoding := stageWithFullRoundPathControlWorkspaceEncoding n counterWidth
  program :=
    EncodedBit.GateSpec.programList
      (correctedInverseToScratchXorGates n counterWidth trace)
  realizes :=
    EncodedBit.GateSpec.realizesList
      (correctedInverseToScratchXorGates n counterWidth trace)

theorem correctedInverseToScratchXorStep_compute_rightInverse
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n) :
    ∀ x,
      correctedInverseToScratchXorStep n counterWidth trace
          (correctedInverseFromScratchXorStep n counterWidth trace x) =
        x := by
  intro x
  simpa [correctedInverseToScratchXorStep,
    correctedInverseFromScratchXorStep, List.reverse_reverse] using
    EncodedBit.GateSpec.stepList_reverse_stepList
      (gates := (correctedInverseToScratchXorGates
        n counterWidth trace).reverse) x

theorem correctedInverseToScratchXorStep_workspace
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (correctedInverseToScratchXorStep n counterWidth trace x).2 = x.2 := by
  unfold correctedInverseToScratchXorStep
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          y.2) _ ?_ x
  intro gate hgate
  rcases List.mem_map.mp
      (by simpa [correctedInverseToScratchXorGates] using hgate) with
    ⟨bit, _hbit, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_workspace
      n counterWidth bit y

theorem correctedInverseToScratchXorStep_input
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (correctedInverseToScratchXorStep n counterWidth trace x).1.1.input =
      x.1.1.input := by
  unfold correctedInverseToScratchXorStep
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          y.1.1.input) _ ?_ x
  intro gate hgate
  rcases List.mem_map.mp
      (by simpa [correctedInverseToScratchXorGates] using hgate) with
    ⟨bit, _hbit, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_input
      n counterWidth bit y

theorem correctedInverseToScratchXorStep_work
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (correctedInverseToScratchXorStep n counterWidth trace x).1.2 =
      x.1.2 := by
  unfold correctedInverseToScratchXorStep
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          y.1.2) _ ?_ x
  intro gate hgate
  rcases List.mem_map.mp
      (by simpa [correctedInverseToScratchXorGates] using hgate) with
    ⟨bit, _hbit, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_work
      n counterWidth bit y

theorem correctedInverseToScratchXorStep_flag
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (correctedInverseToScratchXorStep n counterWidth trace x).1.1.flag =
      x.1.1.flag := by
  unfold correctedInverseToScratchXorStep
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          y.1.1.flag) _ ?_ x
  intro gate hgate
  rcases List.mem_map.mp
      (by simpa [correctedInverseToScratchXorGates] using hgate) with
    ⟨bit, _hbit, rfl⟩
  intro y
  exact
    stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_flip_flag
      n counterWidth bit y

theorem correctedInverseToScratchXorStep_target_testBit
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (correctedInverseToScratchXorStep
        n counterWidth trace x).1.1.target.val.testBit bit.val =
      x.1.1.target.val.testBit bit.val := by
  rw [← stageWithFullRoundPathControlWorkspaceTargetValueBit_get
      n counterWidth bit
      (correctedInverseToScratchXorStep n counterWidth trace x)]
  rw [← stageWithFullRoundPathControlWorkspaceTargetValueBit_get
      n counterWidth bit x]
  unfold correctedInverseToScratchXorStep
  refine
    EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project :=
        fun y : StageWithFullRoundPathControlWorkspace n counterWidth =>
          (stageWithFullRoundPathControlWorkspaceTargetValueBit
            n counterWidth bit).get y) _ ?_ x
  intro gate hgate
  rcases List.mem_map.mp
      (by simpa [correctedInverseToScratchXorGates] using hgate) with
    ⟨scratchBit, _hbit, rfl⟩
  intro y
  exact
    EncodedBit.get_flip_of_wire_ne
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth scratchBit)
      (stageWithFullRoundPathControlWorkspaceTargetValueBit
        n counterWidth bit)
      (stageWithFullRoundPathControlWorkspaceTargetBit_wire_ne_inverseScratch
        n counterWidth bit scratchBit) y

theorem correctedInverseToScratchXorStep_target
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (correctedInverseToScratchXorStep n counterWidth trace x).1.1.target =
      x.1.1.target := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  exact correctedInverseToScratchXorStep_target_testBit
    n counterWidth trace bit x

theorem correctedInverseToScratchXorStep_get_inverseScratchValueBit
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
        n counterWidth bit).get
        (correctedInverseToScratchXorStep n counterWidth trace x) =
      ((stageWithFullRoundPathControlWorkspaceInverseScratchValueBit
          n counterWidth bit).get x ^^
        decide (bit ∈ correctedInverseScratchXorSources n trace)) := by
  unfold correctedInverseToScratchXorStep correctedInverseToScratchXorGates
  rw [encodedWordXGateList_stepList_eq_indicesStep]
  exact
    encodedWordXIndicesStep_get_bit
      (stageWithFullRoundPathControlWorkspaceInverseScratchValueWord
        n counterWidth)
      (correctedInverseScratchXorSources n trace)
      (correctedInverseScratchXorSources_nodup n trace)
      bit
      (fun left right h =>
        stageWithFullRoundPathControlWorkspaceInverseScratchValueBit_wire_ne
          n counterWidth h)
      x

theorem correctedInverseToScratchXorStep_get_inverseScratch_testBit
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (bit : Fin n)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    Nat.testBit
        (correctedInverseToScratchXorStep
          n counterWidth trace x).1.1.inverseScratch.val bit.val =
      (x.1.1.inverseScratch.val.testBit bit.val ^^
        decide (bit ∈ correctedInverseScratchXorSources n trace)) := by
  simpa using
    correctedInverseToScratchXorStep_get_inverseScratchValueBit
      n counterWidth trace bit x

theorem correctedInverseToScratchXorStep_initial_get_inverseScratch_testBit
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (bit : Fin n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    Nat.testBit
        (correctedInverseToScratchXorStep n counterWidth trace
          ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch.val
        bit.val =
      (trace.correctedInverseResidue (2 ^ n)).val.testBit bit.val := by
  rw [correctedInverseToScratchXorStep_get_inverseScratch_testBit]
  by_cases hmem : bit ∈ correctedInverseScratchXorSources n trace
  · have hbit :=
      (mem_correctedInverseScratchXorSources n trace bit).mp hmem
    simp [StageState.initial, hmem, hbit]
  · have hbit :
        (trace.correctedInverseResidue (2 ^ n)).val.testBit bit.val =
          false := by
      cases h :
          (trace.correctedInverseResidue (2 ^ n)).val.testBit bit.val
      · rfl
      · exact False.elim
          (hmem
            ((mem_correctedInverseScratchXorSources n trace bit).mpr h))
    simp [StageState.initial, hmem, hbit]

theorem correctedInverseToScratchXorStep_initial_inverseScratch
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    (correctedInverseToScratchXorStep n counterWidth trace
      ((StageState.initial u z, cleanWork n), workspace)).1.1.inverseScratch =
      trace.correctedInverseResidue (2 ^ n) := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [correctedInverseToScratchXorStep_initial_get_inverseScratch_testBit]

theorem correctedInverseToScratchXorStep_initial
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    correctedInverseToScratchXorStep n counterWidth trace
        ((StageState.initial u z, cleanWork n), workspace) =
      (({ input := u
          target := z
          inverseScratch := trace.correctedInverseResidue (2 ^ n)
          flag := false }, cleanWork n), workspace) := by
  let y :=
    correctedInverseToScratchXorStep n counterWidth trace
      ((StageState.initial u z, cleanWork n), workspace)
  have hinput : y.1.1.input = u := by
    simpa [y, StageState.initial] using
      correctedInverseToScratchXorStep_input
        n counterWidth trace
        ((StageState.initial u z, cleanWork n), workspace)
  have htarget : y.1.1.target = z := by
    simpa [y, StageState.initial] using
      correctedInverseToScratchXorStep_target
        n counterWidth trace
        ((StageState.initial u z, cleanWork n), workspace)
  have hinverse :
      y.1.1.inverseScratch =
        trace.correctedInverseResidue (2 ^ n) := by
    simpa [y] using
      correctedInverseToScratchXorStep_initial_inverseScratch
        n counterWidth trace u z workspace
  have hflag : y.1.1.flag = false := by
    simpa [y, StageState.initial] using
      correctedInverseToScratchXorStep_flag
        n counterWidth trace
        ((StageState.initial u z, cleanWork n), workspace)
  have hwork : y.1.2 = cleanWork n := by
    simpa [y] using
      correctedInverseToScratchXorStep_work
        n counterWidth trace
        ((StageState.initial u z, cleanWork n), workspace)
  have hworkspace : y.2 = workspace := by
    simpa [y] using
      correctedInverseToScratchXorStep_workspace
        n counterWidth trace
        ((StageState.initial u z, cleanWork n), workspace)
  apply Prod.ext
  · apply Prod.ext
    · cases hstage : y.1.1 with
      | mk input target inverseScratch flag =>
          rw [hstage] at hinput htarget hinverse hflag
          have hinput0 : input = u := by simpa using hinput
          have htarget0 : target = z := by simpa using htarget
          have hinverse0 :
              inverseScratch = trace.correctedInverseResidue (2 ^ n) := by
            simpa using hinverse
          have hflag0 : flag = false := by simpa using hflag
          subst input
          subst target
          subst inverseScratch
          subst flag
          simp
    · simpa [y] using hwork
  · simpa [y] using hworkspace

/-- Decomposed staged witness whose compute leg loads the trace-corrected
residue into inverse scratch by constant X gates.  The same compute program is
reversed to clean the scratch after the target-add leg. -/
def correctedInverseToScratchDecomposedWitness
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth where
  computeStep := correctedInverseToScratchXorStep n counterWidth trace
  uncomputeStep := correctedInverseFromScratchXorStep n counterWidth trace
  computeProgram :=
    (correctedInverseToScratchXorSameCircuit n counterWidth trace).program
  computeRealizes :=
    (correctedInverseToScratchXorSameCircuit n counterWidth trace).realizes
  compute_rightInverse :=
    correctedInverseToScratchXorStep_compute_rightInverse
      n counterWidth trace

/-- Clean staged output for the decomposed trace-corrected residue transfer. -/
def cleanCorrectedResidueOutputWithFullRoundPathControlWorkspace
    {n counterWidth : Nat} (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    StageWithFullRoundPathControlWorkspace n counterWidth :=
  let corrected : ZMod (2 ^ n) :=
    trace.correctedInverseResidue (2 ^ n)
  (({ input := u
      target := z + corrected
      inverseScratch := 0
      flag := false }, cleanWork n), workspace)

theorem correctedInverseToScratchDecomposedWitness_step_initial
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth) :
    (correctedInverseToScratchDecomposedWitness
        n counterWidth trace).step
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanCorrectedResidueOutputWithFullRoundPathControlWorkspace
        trace u z workspace := by
  let corrected : ZMod (2 ^ n) :=
    trace.correctedInverseResidue (2 ^ n)
  let y : StageWithFullRoundPathControlWorkspace n counterWidth :=
    ((StageState.initial u (z + corrected), cleanWork n), workspace)
  unfold DecomposedStageWithFullRoundPathControlWorkspaceWitness.step
  unfold reversibleScheduleStepWithFullRoundPathControlWorkspace
  change
    correctedInverseFromScratchXorStep n counterWidth trace
      (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth
        (correctedInverseToScratchXorStep n counterWidth trace
          ((StageState.initial u z, cleanWork n), workspace))) =
    cleanCorrectedResidueOutputWithFullRoundPathControlWorkspace
      trace u z workspace
  rw [correctedInverseToScratchXorStep_initial]
  rw [addScratchToTargetWithFullRoundPathControlWorkspace_cleanEndpoint]
  · have htarget :
        ((StageState.addScratchToTarget
            { input := u
              target := z
              inverseScratch := corrected
              flag := false }, cleanWork n), workspace) =
          correctedInverseToScratchXorStep n counterWidth trace y := by
      rw [correctedInverseToScratchXorStep_initial]
      simp [corrected, StageState.addScratchToTarget]
    rw [htarget]
    simpa [y, cleanCorrectedResidueOutputWithFullRoundPathControlWorkspace,
      StageState.initial, corrected, correctedInverseToScratchDecomposedWitness]
      using
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.compute_leftInverse
        (correctedInverseToScratchDecomposedWitness n counterWidth trace) y
  · rfl

theorem
    correctedInverseToScratchDecomposedWitness_step_initial_of_matches
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hmatch : trace.CorrectedResidueMatchesUnitInverse u) :
    (correctedInverseToScratchDecomposedWitness
        n counterWidth trace).step
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanInverseOutputWithFullRoundPathControlWorkspace u z workspace := by
  rw [correctedInverseToScratchDecomposedWitness_step_initial]
  change trace.correctedInverseResidue (2 ^ n) = inverseResidue u at hmatch
  simp [cleanCorrectedResidueOutputWithFullRoundPathControlWorkspace,
    cleanInverseOutputWithFullRoundPathControlWorkspace, hmatch]

theorem
    correctedInverseToScratchDecomposedWitness_apply_clean_ket_of_matches
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hmatch : trace.CorrectedResidueMatchesUnitInverse u) :
    Circuit.apply
        (BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth trace).baseWitness)
        ((PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode
            ((StageState.initial u z, cleanWork n), workspace)) :
          PureState (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) =
      (PureState.ket
        (R := Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)
        ((stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).encode
          (cleanInverseOutputWithFullRoundPathControlWorkspace
            u z workspace)) :
        StateVector (Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)) := by
  have hstep :=
    correctedInverseToScratchDecomposedWitness_step_initial_of_matches
      n counterWidth trace u z workspace hmatch
  simpa [hstep] using
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.apply_ket
        (correctedInverseToScratchDecomposedWitness
          n counterWidth trace)
        ((StageState.initial u z, cleanWork n), workspace)

/-- Resource-correct clean endpoint for the corrected-residue scratch-transfer
circuit under an explicit trace/unit-inverse match premise. -/
def correctedInverseToScratchDecomposedWitnessCleanResourceCorrectWitnessOfMatches
    (n counterWidth : Nat) (trace : MontgomeryKaliski.Trace n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hmatch : trace.CorrectedResidueMatchesUnitInverse u) :
    ResourceCorrectWitness
      (R := Qubits
        (stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).width)
      (Circuit.apply
          (BaseGateSameCircuitWitness.circuit
            (correctedInverseToScratchDecomposedWitness
              n counterWidth trace).baseWitness)
          ((PureState.ket
            (R := Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)
            ((stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).encode
              ((StageState.initial u z, cleanWork n), workspace)) :
            PureState (Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)) :
            StateVector (Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)) =
        (PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode
            (cleanInverseOutputWithFullRoundPathControlWorkspace
              u z workspace)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)))
      ((BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth trace).baseWitness).resources =
          (BaseGateSameCircuitWitness.profile
            (correctedInverseToScratchDecomposedWitness
              n counterWidth trace).baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth trace).baseWitness).depth =
          (BaseGateSameCircuitWitness.profile
            (correctedInverseToScratchDecomposedWitness
              n counterWidth trace).baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth trace).baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile
            (correctedInverseToScratchDecomposedWitness
              n counterWidth trace).baseWitness).oracleQueries) where
  circuit :=
    BaseGateSameCircuitWitness.circuit
      (correctedInverseToScratchDecomposedWitness
        n counterWidth trace).baseWitness
  correctness :=
    correctedInverseToScratchDecomposedWitness_apply_clean_ket_of_matches
      n counterWidth trace u z workspace hmatch
  resources :=
    let w :=
      correctedInverseToScratchDecomposedWitness n counterWidth trace
    ⟨DecomposedStageWithFullRoundPathControlWorkspaceWitness.resources_eq w,
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.depth_eq w,
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.queryDepth_eq w⟩

theorem
    correctedInverseToScratchDecomposedWitness_step_initial_of_final_state
    {n counterWidth : Nat} [NeZero (2 ^ n)]
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u).finish.u = 1)
    (hnormalize : -((2 : ZMod (2 ^ n)) ^ (2 * n)) = 1) :
    (correctedInverseToScratchDecomposedWitness
        n counterWidth
        (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).step
        ((StageState.initial u z, cleanWork n), workspace) =
      cleanInverseOutputWithFullRoundPathControlWorkspace u z workspace := by
  exact
    correctedInverseToScratchDecomposedWitness_step_initial_of_matches
      n counterWidth
      (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)
      u z workspace
      (MontgomeryKaliski.Trace.ofUnitInput_correctedResidueMatchesUnitInverse_of_final_state
        n (2 ^ n) u hfinish hnormalize)

theorem
    correctedInverseToScratchDecomposedWitness_apply_clean_ket_of_final_state
    {n counterWidth : Nat} [NeZero (2 ^ n)]
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u).finish.u = 1)
    (hnormalize : -((2 : ZMod (2 ^ n)) ^ (2 * n)) = 1) :
    Circuit.apply
        (BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth
            (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness)
        ((PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode
            ((StageState.initial u z, cleanWork n), workspace)) :
          PureState (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)) =
      (PureState.ket
        (R := Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)
        ((stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).encode
          (cleanInverseOutputWithFullRoundPathControlWorkspace
            u z workspace)) :
        StateVector (Qubits
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width)) := by
  exact
    correctedInverseToScratchDecomposedWitness_apply_clean_ket_of_matches
      n counterWidth
      (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)
      u z workspace
      (MontgomeryKaliski.Trace.ofUnitInput_correctedResidueMatchesUnitInverse_of_final_state
        n (2 ^ n) u hfinish hnormalize)

/-- Resource-correct clean endpoint for the canonical unit-input corrected
trace, with the source final-state and normalization premises explicit. -/
def correctedInverseToScratchDecomposedWitnessCleanResourceCorrectWitnessOfFinalState
    {n counterWidth : Nat} [NeZero (2 ^ n)]
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n))
    (workspace :
      MontgomeryKaliski.RegistersWithFullRoundPathControlWork n counterWidth)
    (hfinish :
      (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u).finish.u = 1)
    (hnormalize : -((2 : ZMod (2 ^ n)) ^ (2 * n)) = 1) :
    ResourceCorrectWitness
      (R := Qubits
        (stageWithFullRoundPathControlWorkspaceEncoding
          n counterWidth).width)
      (Circuit.apply
          (BaseGateSameCircuitWitness.circuit
            (correctedInverseToScratchDecomposedWitness
              n counterWidth
              (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness)
          ((PureState.ket
            (R := Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)
            ((stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).encode
              ((StageState.initial u z, cleanWork n), workspace)) :
            PureState (Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)) :
            StateVector (Qubits
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width)) =
        (PureState.ket
          (R := Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode
            (cleanInverseOutputWithFullRoundPathControlWorkspace
              u z workspace)) :
          StateVector (Qubits
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width)))
      ((BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth
            (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness).resources =
          (BaseGateSameCircuitWitness.profile
            (correctedInverseToScratchDecomposedWitness
              n counterWidth
              (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth
            (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness).depth =
          (BaseGateSameCircuitWitness.profile
            (correctedInverseToScratchDecomposedWitness
              n counterWidth
              (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit
          (correctedInverseToScratchDecomposedWitness
            n counterWidth
            (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile
            (correctedInverseToScratchDecomposedWitness
              n counterWidth
              (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness).oracleQueries) where
  circuit :=
    BaseGateSameCircuitWitness.circuit
      (correctedInverseToScratchDecomposedWitness
        n counterWidth
        (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)).baseWitness
  correctness :=
    correctedInverseToScratchDecomposedWitness_apply_clean_ket_of_final_state
      u z workspace hfinish hnormalize
  resources :=
    let w :=
      correctedInverseToScratchDecomposedWitness
        n counterWidth
        (MontgomeryKaliski.Trace.ofUnitInput n (2 ^ n) u)
    ⟨DecomposedStageWithFullRoundPathControlWorkspaceWitness.resources_eq w,
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.depth_eq w,
      DecomposedStageWithFullRoundPathControlWorkspaceWitness.queryDepth_eq w⟩

end PowerOfTwoTargetAdd
end StageState

/-- Semantic update implemented by a decomposed gate-structured modular
inversion stage witness. -/
abbrev decomposedStageStep {N : Nat} : StageState N -> StageState N :=
  StageState.reversibleScheduleStep

/-- Decomposed gate-program witnesses for the reversible compute/add/uncompute
modular-inversion schedule.  The cleanup program is generated by reversing the
compute program, so compute and uncompute share one concrete gate sequence
[RNSL17, ECDLP.tex:390-465,753-755]. -/
structure DecomposedStageWitness (N : Nat) where
  /-- Faithful encoding of staged inversion labels, including scratch. -/
  encoding : BinaryLabelEncoding (StageState N)
  /-- Program adding the inverse residue into scratch. -/
  computeProgram : BaseGateProgram encoding.width
  /-- Program adding scratch into the target accumulator. -/
  targetAddProgram : BaseGateProgram encoding.width
  /-- Correctness of the compute program on encoded stage labels. -/
  computeRealizes :
    BaseGateProgram.Realizes encoding computeProgram StageState.addInverseToScratch
  /-- Correctness of the target-add program on encoded stage labels. -/
  targetAddRealizes :
    BaseGateProgram.Realizes encoding targetAddProgram StageState.addScratchToTarget

namespace DecomposedStageWitness

variable {N : Nat}

/-- Build a decomposed staged witness over the canonical field-packed
modular-inversion layout. -/
def ofFieldEncoding {N n : Nat} (E : BinaryResidueEncoding N n)
    (computeProgram targetAddProgram :
      BaseGateProgram (StageState.fieldEncoding E).width)
    (computeRealizes :
      BaseGateProgram.Realizes (StageState.fieldEncoding E) computeProgram
        StageState.addInverseToScratch)
    (targetAddRealizes :
      BaseGateProgram.Realizes (StageState.fieldEncoding E) targetAddProgram
        StageState.addScratchToTarget) :
    DecomposedStageWitness N where
  encoding := StageState.fieldEncoding E
  computeProgram := computeProgram
  targetAddProgram := targetAddProgram
  computeRealizes := computeRealizes
  targetAddRealizes := targetAddRealizes

@[simp] theorem ofFieldEncoding_encoding {N n : Nat}
    (E : BinaryResidueEncoding N n)
    (computeProgram targetAddProgram :
      BaseGateProgram (StageState.fieldEncoding E).width)
    (computeRealizes :
      BaseGateProgram.Realizes (StageState.fieldEncoding E) computeProgram
        StageState.addInverseToScratch)
    (targetAddRealizes :
      BaseGateProgram.Realizes (StageState.fieldEncoding E) targetAddProgram
        StageState.addScratchToTarget) :
    (ofFieldEncoding E computeProgram targetAddProgram computeRealizes
      targetAddRealizes).encoding = StageState.fieldEncoding E :=
  rfl

/-- Compute, target-add, and reverse-compute as one base-gate program. -/
def program (w : DecomposedStageWitness N) : BaseGateProgram w.encoding.width :=
  BaseGateProgram.append w.computeProgram
    (BaseGateProgram.append w.targetAddProgram
      (BaseGateProgram.inverse w.computeProgram))

/-- The decomposed program realizes the reversible inversion schedule. -/
theorem realizes (w : DecomposedStageWitness N) :
    BaseGateProgram.Realizes w.encoding w.program
      (decomposedStageStep (N := N)) := by
  have huncompute :
      BaseGateProgram.Realizes w.encoding
        (BaseGateProgram.inverse w.computeProgram) StageState.subInverseFromScratch :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.computeRealizes
      StageState.addInverseToScratch_subInverseFromScratch
  have htail :
      BaseGateProgram.Realizes w.encoding
        (BaseGateProgram.append w.targetAddProgram
          (BaseGateProgram.inverse w.computeProgram))
        (fun x : StageState N =>
          StageState.subInverseFromScratch (StageState.addScratchToTarget x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := StageState.addScratchToTarget)
      (secondStep := StageState.subInverseFromScratch)
      w.targetAddRealizes huncompute
  have hfull :
      BaseGateProgram.Realizes w.encoding w.program
        (decomposedStageStep (N := N)) :=
    BaseGateProgram.Realizes.append
      (firstStep := StageState.addInverseToScratch)
      (secondStep := fun x : StageState N =>
        StageState.subInverseFromScratch (StageState.addScratchToTarget x))
      w.computeRealizes htail
  simpa [program, decomposedStageStep, StageState.reversibleScheduleStep] using hfull

/-- Same-Circuit witness induced by the decomposed staged program. -/
def baseWitness (w : DecomposedStageWitness N) :
    BaseGateSameCircuitWitness (StageState N) (decomposedStageStep (N := N)) where
  encoding := w.encoding
  program := w.program
  realizes := w.realizes

/-- The decomposed inversion circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : DecomposedStageWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all staged modular-inversion labels. -/
theorem apply_ket (w : DecomposedStageWitness N) (x : StageState N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (StageState.reversibleScheduleStep x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Clean staged action:
`|enc(u,z,0,0)> -> |enc(u,z+u^{-1},0,0)>`. -/
theorem apply_clean_ket (w : DecomposedStageWitness N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (StageState.initial u z)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := u
             target := z + inverseResidue u
             inverseScratch := 0
             flag := false } : StageState N)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [StageState.reversibleScheduleStep_initial] using
    apply_ket w (StageState.initial u z)

/-- Resource counters are projected from the same decomposed inversion circuit. -/
theorem resources_eq (w : DecomposedStageWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same decomposed inversion circuit. -/
theorem depth_eq (w : DecomposedStageWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same decomposed inversion circuit. -/
theorem queryDepth_eq (w : DecomposedStageWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

/-- Resource-correct witness for the clean staged encoded modular-inversion
statement, conditional on concrete decomposed subprograms supplied by `w`. -/
def cleanResourceCorrectWitness (w : DecomposedStageWitness N) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ u : (ZMod N)ˣ, ∀ z : ZMod N,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (StageState.initial u z)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ input := u
                 target := z + inverseResidue u
                 inverseScratch := 0
                 flag := false } : StageState N)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun u z => apply_clean_ket w u z
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

/-- Decomposed same-Circuit witness for clean unit-domain modular inversion.
This is the structured artifact to use when correctness and resources must be
audited on the same compute / target-add / uncompute `BaseGateProgram`, rather
than through the endpoint permutation wrapper [RNSL17,
ECDLP.tex:390-465,753-755]. -/
def decomposedCleanResourceCorrectWitness (w : DecomposedStageWitness N) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ u : (ZMod N)ˣ, ∀ z : ZMod N,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (StageState.initial u z)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ input := u
                 target := z + inverseResidue u
                 inverseScratch := 0
                 flag := false } : StageState N)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) :=
  cleanResourceCorrectWitness w

end DecomposedStageWitness

/-- Semantic update implemented by a gate-structured modular-inversion witness. -/
abbrev encodedStep {N : Nat} : Data N -> Data N :=
  Data.addInverseIntoTarget

/-- Gate-structured encoded modular-inversion witness. -/
abbrev StructuredCircuitWitness (N : Nat) :=
  BaseGateSameCircuitWitness (Data N) (encodedStep (N := N))

namespace StructuredCircuitWitness

variable {N : Nat}

/-- The structured inversion circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w

/-- Encoded-basis correctness for all modular-inversion data labels. -/
theorem apply_ket (w : StructuredCircuitWitness N) (x : Data N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addInverseIntoTarget) :
        StateVector (Qubits w.encoding.width)) :=
  by
    simpa [encodedStep] using BaseGateSameCircuitWitness.apply_encoded_ket w x

/-- Clean public-form encoded-basis action:
`|enc(u,z,0)> -> |enc(u,z+u^{-1},0)>`. -/
theorem apply_clean_ket (w : StructuredCircuitWitness N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := u, target := z, flag := false } : Data N)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := u, target := z + inverseResidue u, flag := false } : Data N)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [encodedStep, Data.addInverseIntoTarget] using
    apply_ket (N := N) w
      ({ input := u, target := z, flag := false } : Data N)

/-- Resource counters are projected from the same structured inversion circuit. -/
theorem resources_eq (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).resources =
      (BaseGateSameCircuitWitness.profile w).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w

/-- Circuit depth is projected from the same structured inversion circuit. -/
theorem depth_eq (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).depth =
      (BaseGateSameCircuitWitness.profile w).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w

/-- Query depth is projected from the same structured inversion circuit. -/
theorem queryDepth_eq (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).queryDepth =
      (BaseGateSameCircuitWitness.profile w).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w

/-- Resource-correct witness for the clean encoded modular-inversion statement. -/
def cleanResourceCorrectWitness (w : StructuredCircuitWitness N) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ u : (ZMod N)ˣ, ∀ z : ZMod N,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ input := u, target := z, flag := false } : Data N)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ input := u, target := z + inverseResidue u, flag := false } : Data N)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w).resources =
          (BaseGateSameCircuitWitness.profile w).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w).depth =
          (BaseGateSameCircuitWitness.profile w).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w).queryDepth =
          (BaseGateSameCircuitWitness.profile w).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w
  correctness := fun u z => apply_clean_ket w u z
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end StructuredCircuitWitness

end

end ModularInversion
end QuantumAlg
