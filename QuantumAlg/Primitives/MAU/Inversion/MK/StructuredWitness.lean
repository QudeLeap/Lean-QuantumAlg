/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Primitives.MAU.Inversion.MK.Readout.Trace
import all QuantumAlg.Primitives.MAU.Inversion.StructuredCircuit

/-!
# Structured fixed-round inversion witnesses
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace StructuredWitness

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth
open NumberTheory.BinaryGCD
open StageState.PowerOfTwoTargetAdd


/-- Raw-vector companion of a normalized actual-circuit realization. -/
private lemma applyVec_encoded_ket_of_realizes {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    {program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum} {step : Data -> Data}
    (h : UnitaryCircuit.Realizes encoding program environment step) (x : Data) :
    UnitaryCircuit.applyVec program environment
        (NormalizedVector.ket
          ((QubitLayout.canonical encoding.width).basisEquiv.symm
            (encoding.encode x)) : HilbertVector
              (QubitLayout.canonical encoding.width).toQuantum.register) =
      (NormalizedVector.ket
        ((QubitLayout.canonical encoding.width).basisEquiv.symm
          (encoding.encode (step x))) : HilbertVector
            (QubitLayout.canonical encoding.width).toQuantum.register) := by
  change
    (program.applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical encoding.width).basisEquiv.symm
          (encoding.encode x)))).vec =
      (NormalizedVector.ket
        ((QubitLayout.canonical encoding.width).basisEquiv.symm
          (encoding.encode (step x)))).vec
  exact congrArg NormalizedVector.vec (h.apply_encoded_ket x)

/-- Staged inversion state with both VBE target-add carry work and the finite
Montgomery--Kaliski compute workspace.  The extra workspace is the RNSL17
`u,v,r,s,m_i,f,k` register family plus the comparison-work bits needed by the
concrete word-comparison selector slices; adding it here keeps the Euclidean
workspace present when the target-add leg is lifted into the eventual
compute/add/uncompute composition [RNSL17, ECDLP.tex:425-475; VBE95,
9511018.tex:237-264,591-618]. -/
abbrev StageWithWorkspace (n counterWidth : Nat) : Type :=
  StageWithWork n ×
    MK.RegistersWithComparisonWork n counterWidth

/-- Encoding for the staged public fields, VBE carry work, and finite
Montgomery--Kaliski compute/comparison workspace as one basis-label object. -/
def stageWithWorkspaceEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (StageWithWorkspace n counterWidth) :=
  BinaryLabelEncoding.prod (stageWithWorkEncoding n)
    (MK.registersWithComparisonWorkEncoding n counterWidth)

/-- Target-add lifted to a full inversion workspace.  This is only the
target-add leg; the concrete Montgomery--Kaliski compute program remains a
separate obligation [RNSL17, ECDLP.tex:425-475; VBE95,
9511018.tex:237-264,591-618]. -/
def addScratchToTargetWithWorkspace (n counterWidth : Nat) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth
  | (stage, workspace) => (addScratchToTargetWithWork n stage, workspace)

/-- Actual target-add program over the full inversion workspace. -/
def stageWithWorkspaceTargetAddProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryPrefix
    (MK.registersWithComparisonWorkEncoding n counterWidth).width
    (stageWithWorkProgram n)

/-- The lifted target-add program realizes the full-workspace target update. -/
lemma stageWithWorkspaceTargetAdd_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
      (stageWithWorkspaceTargetAddProgram n counterWidth) environment
      (addScratchToTargetWithWorkspace n counterWidth) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := MK.registersWithComparisonWorkEncoding n counterWidth)
    (stageWithWork_realizes n)

@[simp] lemma stageWithWorkspaceEncoding_width (n counterWidth : Nat) :
    (stageWithWorkspaceEncoding n counterWidth).width =
      (stageWithWorkEncoding n).width +
        (MK.registersWithComparisonWorkEncoding
          n counterWidth).width :=
  rfl

/-- Lift a semantic Montgomery--Kaliski workspace step over the staged public
fields and VBE carry work. -/
def stageWithWorkspaceKaliskiStep {n counterWidth : Nat}
    (step : MK.RegistersWithComparisonWork n counterWidth ->
      MK.RegistersWithComparisonWork n counterWidth) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  fun x => (x.1, step x.2)

@[simp] lemma stageWithWorkspaceKaliskiStep_left
    {n counterWidth : Nat}
    (step : MK.RegistersWithComparisonWork n counterWidth ->
      MK.RegistersWithComparisonWork n counterWidth)
    (x : StageWithWorkspace n counterWidth) :
    (stageWithWorkspaceKaliskiStep step x).1 = x.1 := by
  cases x
  rfl

@[simp] lemma stageWithWorkspaceKaliskiStep_right
    {n counterWidth : Nat}
    (step : MK.RegistersWithComparisonWork n counterWidth ->
      MK.RegistersWithComparisonWork n counterWidth)
    (x : StageWithWorkspace n counterWidth) :
    (stageWithWorkspaceKaliskiStep step x).2 = step x.2 := by
  cases x
  rfl

/-- Lift an actual Montgomery--Kaliski workspace program over the staged
public fields and VBE carry work. -/
def stageWithWorkspaceKaliskiProgram {n counterWidth : Nat}
    (program : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithComparisonWorkEncoding n counterWidth).width)).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinarySuffix (stageWithWorkEncoding n).width program

/-- Semantic realization of a lifted Montgomery--Kaliski workspace program. -/
lemma stageWithWorkspaceKaliski_realizes {n counterWidth : Nat}
    {step : MK.RegistersWithComparisonWork n counterWidth ->
      MK.RegistersWithComparisonWork n counterWidth}
    {program : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithComparisonWorkEncoding n counterWidth).width)).toQuantum}
    (h : UnitaryCircuit.Realizes
      (MK.registersWithComparisonWorkEncoding n counterWidth) program environment step) :
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
      (stageWithWorkspaceKaliskiProgram program) environment
      (stageWithWorkspaceKaliskiStep step) :=
  UnitaryCircuit.Realizes.onBinarySuffix (left := stageWithWorkEncoding n) h

/-- Full-workspace semantic step for the `uEven` branch-history write, lifted
over the staged public fields and VBE carry work [RNSL17,
ECDLP.tex:468-475]. -/
def uEvenBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MK.liftedUEvenBranchHistoryWriteStep
      n counterWidth bit historyIndex)

/-- Actual `uEven` branch-history program inside the full staged workspace. -/
def uEvenBranchHistoryWithWorkspaceProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum :=
  stageWithWorkspaceKaliskiProgram
    (MK.liftedUEvenBranchHistoryWriteProgram
      n counterWidth bit historyIndex)

/-- Realization of the lifted `uEven` branch-history program. -/
lemma uEvenBranchHistoryWithWorkspace_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
      (uEvenBranchHistoryWithWorkspaceProgram n counterWidth bit historyIndex) environment
      (uEvenBranchHistoryWithWorkspaceStep n counterWidth bit historyIndex) :=
  stageWithWorkspaceKaliski_realizes
    (MK.liftedUEvenBranchHistoryWrite_realizes (environment := environment)
      n counterWidth bit historyIndex)

/-- Full-workspace semantic step for the `vEven` branch-history write, lifted
over the staged public fields and VBE carry work [RNSL17,
ECDLP.tex:468-475]. -/
def vEvenBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MK.liftedVEvenBranchHistoryWriteStep
      n counterWidth uIndex vIndex historyIndex)

/-- Actual `vEven` branch-history program inside the full staged workspace. -/
def vEvenBranchHistoryWithWorkspaceProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum :=
  stageWithWorkspaceKaliskiProgram
    (MK.liftedVEvenBranchHistoryWriteProgram
      n counterWidth uIndex vIndex historyIndex)

/-- Realization of the lifted `vEven` branch-history program. -/
lemma vEvenBranchHistoryWithWorkspace_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
      (vEvenBranchHistoryWithWorkspaceProgram
        n counterWidth uIndex vIndex historyIndex) environment
      (vEvenBranchHistoryWithWorkspaceStep
        n counterWidth uIndex vIndex historyIndex) :=
  stageWithWorkspaceKaliski_realizes
    (MK.liftedVEvenBranchHistoryWrite_realizes (environment := environment)
      n counterWidth uIndex vIndex historyIndex)

/-- Full-workspace semantic step for the `uGreater` selector/history-write
slice, lifted over the staged public fields and VBE carry work. -/
def uGreaterSelectorBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MK.uGreaterSelectorBranchHistoryWriteStep
      n counterWidth bit historyIndex)

/-- Actual `uGreater` selector/history-write program in the full workspace. -/
def uGreaterSelectorBranchHistoryWithWorkspaceProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum :=
  stageWithWorkspaceKaliskiProgram
    (MK.uGreaterSelectorBranchHistoryWriteProgram
      n counterWidth bit historyIndex)

/-- Realization of the lifted `uGreater` selector/history-write program. -/
lemma uGreaterSelectorBranchHistoryWithWorkspace_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
      (uGreaterSelectorBranchHistoryWithWorkspaceProgram
        n counterWidth bit historyIndex) environment
      (uGreaterSelectorBranchHistoryWithWorkspaceStep
        n counterWidth bit historyIndex) :=
  stageWithWorkspaceKaliski_realizes
    (MK.uGreaterSelectorBranchHistoryWrite_realizes (environment := environment)
      n counterWidth bit historyIndex)

/-- Full-workspace semantic step for the `vLe` selector/history-write slice,
lifted over the staged public fields and VBE carry work. -/
def vLeSelectorBranchHistoryWithWorkspaceStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    StageWithWorkspace n counterWidth -> StageWithWorkspace n counterWidth :=
  stageWithWorkspaceKaliskiStep
    (MK.vLeSelectorBranchHistoryWriteStep
      n counterWidth bit historyIndex)

/-- Actual `vLe` selector/history-write program in the full workspace. -/
def vLeSelectorBranchHistoryWithWorkspaceProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum :=
  stageWithWorkspaceKaliskiProgram
    (MK.vLeSelectorBranchHistoryWriteProgram
      n counterWidth bit historyIndex)

/-- Realization of the lifted `vLe` selector/history-write program. -/
lemma vLeSelectorBranchHistoryWithWorkspace_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
      (vLeSelectorBranchHistoryWithWorkspaceProgram
        n counterWidth bit historyIndex) environment
      (vLeSelectorBranchHistoryWithWorkspaceStep
        n counterWidth bit historyIndex) :=
  stageWithWorkspaceKaliski_realizes
    (MK.vLeSelectorBranchHistoryWrite_realizes (environment := environment)
      n counterWidth bit historyIndex)



/-- Clean endpoint for the target-add leg after lifting it over the finite
Montgomery--Kaliski compute workspace. -/
lemma addScratchToTargetWithWorkspace_cleanEndpoint
    (n counterWidth : Nat) (s : StageState (2 ^ n))
    (hflag : s.flag = false)
    (workspace :
      MK.RegistersWithComparisonWork n counterWidth) :
    addScratchToTargetWithWorkspace n counterWidth ((s, cleanWork n), workspace) =
      ((StageState.addScratchToTarget s, cleanWork n), workspace) := by
  simp [addScratchToTargetWithWorkspace,
    addScratchToTargetWithWork_cleanEndpoint n s hflag]

/-- The target-add leg preserves the Montgomery--Kaliski register/comparison
workspace pointwise. -/
lemma addScratchToTargetWithWorkspace_preservesWorkspace
    (n counterWidth : Nat) (x : StageWithWorkspace n counterWidth) :
    (addScratchToTargetWithWorkspace n counterWidth x).2 = x.2 := by
  cases x
  rfl

/-- Staged inversion state with VBE target-add carry work and the full
Montgomery--Kaliski fixed-round workspace: registers, comparison work,
coefficient-adder work, and padding-counter increment work. -/
abbrev StageWithFullRoundWorkspace (n counterWidth : Nat) : Type :=
  StageWithWork n ×
    MK.RegistersWithFullRoundWork n counterWidth

/-- Encoding for the staged public fields, VBE carry work, and the full finite
Montgomery--Kaliski fixed-round workspace. -/
def stageWithFullRoundWorkspaceEncoding (n counterWidth : Nat) :
    BinaryLabelEncoding (StageWithFullRoundWorkspace n counterWidth) :=
  BinaryLabelEncoding.prod (stageWithWorkEncoding n)
    (MK.registersWithFullRoundWorkEncoding n counterWidth)

/-- Target-add lifted over the full fixed-round workspace.  This is still only
the target-add leg; the concrete Montgomery--Kaliski round program remains a
separate compute obligation [RNSL17, ECDLP.tex:390-465; VBE95,
9511018.tex:237-264,591-618]. -/
def addScratchToTargetWithFullRoundWorkspace (n counterWidth : Nat) :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth
  | (stage, workspace) => (addScratchToTargetWithWork n stage, workspace)

/-- Actual target-add program over the full fixed-round workspace. -/
def stageWithFullRoundWorkspaceTargetAddProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundWorkspaceEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryPrefix
    (MK.registersWithFullRoundWorkEncoding n counterWidth).width
    (stageWithWorkProgram n)

/-- Realization of the lifted full-round-workspace target-add program. -/
lemma stageWithFullRoundWorkspaceTargetAdd_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (stageWithFullRoundWorkspaceEncoding n counterWidth)
      (stageWithFullRoundWorkspaceTargetAddProgram n counterWidth) environment
      (addScratchToTargetWithFullRoundWorkspace n counterWidth) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := MK.registersWithFullRoundWorkEncoding n counterWidth)
    (stageWithWork_realizes n)

@[simp] lemma stageWithFullRoundWorkspaceEncoding_width
    (n counterWidth : Nat) :
    (stageWithFullRoundWorkspaceEncoding n counterWidth).width =
      (stageWithWorkEncoding n).width +
        (MK.registersWithFullRoundWorkEncoding
          n counterWidth).width :=
  rfl

/-- Lift a semantic Montgomery--Kaliski full-workspace step over the staged
public fields and VBE carry work. -/
def stageWithFullRoundWorkspaceKaliskiStep {n counterWidth : Nat}
    (step : MK.RegistersWithFullRoundWork n counterWidth ->
      MK.RegistersWithFullRoundWork n counterWidth) :
    StageWithFullRoundWorkspace n counterWidth ->
      StageWithFullRoundWorkspace n counterWidth :=
  fun x => (x.1, step x.2)

@[simp] lemma stageWithFullRoundWorkspaceKaliskiStep_left
    {n counterWidth : Nat}
    (step : MK.RegistersWithFullRoundWork n counterWidth ->
      MK.RegistersWithFullRoundWork n counterWidth)
    (x : StageWithFullRoundWorkspace n counterWidth) :
    (stageWithFullRoundWorkspaceKaliskiStep step x).1 = x.1 := by
  cases x
  rfl

@[simp] lemma stageWithFullRoundWorkspaceKaliskiStep_right
    {n counterWidth : Nat}
    (step : MK.RegistersWithFullRoundWork n counterWidth ->
      MK.RegistersWithFullRoundWork n counterWidth)
    (x : StageWithFullRoundWorkspace n counterWidth) :
    (stageWithFullRoundWorkspaceKaliskiStep step x).2 = step x.2 := by
  cases x
  rfl

/-- Lift an actual Montgomery--Kaliski full-workspace program over the staged
public fields and VBE carry work. -/
def stageWithFullRoundWorkspaceKaliskiProgram {n counterWidth : Nat}
    (program : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithFullRoundWorkEncoding n counterWidth).width)).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundWorkspaceEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinarySuffix (stageWithWorkEncoding n).width program

/-- Realization of a lifted Montgomery--Kaliski full-workspace program. -/
lemma stageWithFullRoundWorkspaceKaliski_realizes {n counterWidth : Nat}
    {step : MK.RegistersWithFullRoundWork n counterWidth ->
      MK.RegistersWithFullRoundWork n counterWidth}
    {program : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithFullRoundWorkEncoding n counterWidth).width)).toQuantum}
    (h : UnitaryCircuit.Realizes
      (MK.registersWithFullRoundWorkEncoding n counterWidth) program environment step) :
    UnitaryCircuit.Realizes (stageWithFullRoundWorkspaceEncoding n counterWidth)
      (stageWithFullRoundWorkspaceKaliskiProgram program) environment
      (stageWithFullRoundWorkspaceKaliskiStep step) :=
  UnitaryCircuit.Realizes.onBinarySuffix (left := stageWithWorkEncoding n) h

/-- Clean endpoint for the target-add leg after lifting it over the full
fixed-round workspace. -/
lemma addScratchToTargetWithFullRoundWorkspace_cleanEndpoint
    (n counterWidth : Nat) (s : StageState (2 ^ n))
    (hflag : s.flag = false)
    (workspace :
      MK.RegistersWithFullRoundWork n counterWidth) :
    addScratchToTargetWithFullRoundWorkspace n counterWidth
        ((s, cleanWork n), workspace) =
      ((StageState.addScratchToTarget s, cleanWork n), workspace) := by
  simp [addScratchToTargetWithFullRoundWorkspace,
    addScratchToTargetWithWork_cleanEndpoint n s hflag]

/-- The target-add leg preserves the full Montgomery--Kaliski fixed-round
workspace pointwise. -/
lemma addScratchToTargetWithFullRoundWorkspace_preservesWorkspace
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
    MK.RegistersWithFullRoundPathControlWork n counterWidth

/-- Encoding for the staged public fields, VBE carry work, and the
path/control fixed-round workspace. -/
def stageWithFullRoundPathControlWorkspaceEncoding
    (n counterWidth : Nat) :
    BinaryLabelEncoding
      (StageWithFullRoundPathControlWorkspace n counterWidth) :=
  BinaryLabelEncoding.prod (stageWithWorkEncoding n)
    (MK.registersWithFullRoundPathControlWorkEncoding n counterWidth)

/-- Target-add lifted over the path/control fixed-round workspace. -/
def addScratchToTargetWithFullRoundPathControlWorkspace
    (n counterWidth : Nat) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth
  | (stage, workspace) => (addScratchToTargetWithWork n stage, workspace)

/-- Actual target-add program over the path/control fixed-round workspace. -/
def stageWithFullRoundPathControlWorkspaceTargetAddProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryPrefix
    (MK.registersWithFullRoundPathControlWorkEncoding n counterWidth).width
    (stageWithWorkProgram n)

/-- Realization of the lifted path/control-workspace target-add program. -/
lemma stageWithFullRoundPathControlWorkspaceTargetAdd_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
      (stageWithFullRoundPathControlWorkspaceTargetAddProgram n counterWidth) environment
      (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := MK.registersWithFullRoundPathControlWorkEncoding
      n counterWidth)
    (stageWithWork_realizes n)

@[simp] lemma stageWithFullRoundPathControlWorkspaceEncoding_width
    (n counterWidth : Nat) :
    (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width =
      (stageWithWorkEncoding n).width +
        (MK.registersWithFullRoundPathControlWorkEncoding
          n counterWidth).width :=
  rfl

/-- Lift a path/control Montgomery--Kaliski workspace step over the staged
public fields and VBE carry work. -/
def stageWithFullRoundPathControlWorkspaceKaliskiStep
    {n counterWidth : Nat}
    (step :
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth) :
    StageWithFullRoundPathControlWorkspace n counterWidth ->
      StageWithFullRoundPathControlWorkspace n counterWidth :=
  fun x => (x.1, step x.2)

@[simp] lemma stageWithFullRoundPathControlWorkspaceKaliskiStep_left
    {n counterWidth : Nat}
    (step :
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceKaliskiStep step x).1 = x.1 := by
  cases x
  rfl

@[simp] lemma stageWithFullRoundPathControlWorkspaceKaliskiStep_right
    {n counterWidth : Nat}
    (step :
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (stageWithFullRoundPathControlWorkspaceKaliskiStep step x).2 =
      step x.2 := by
  cases x
  rfl

/-- Lift an actual path/control Montgomery--Kaliski program over the staged
public fields and VBE carry work. -/
def stageWithFullRoundPathControlWorkspaceKaliskiProgram
    {n counterWidth : Nat}
    (program : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithFullRoundPathControlWorkEncoding
        n counterWidth).width)).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinarySuffix (stageWithWorkEncoding n).width program

/-- Realization of a lifted path/control Montgomery--Kaliski program. -/
lemma stageWithFullRoundPathControlWorkspaceKaliski_realizes
    {n counterWidth : Nat}
    {step :
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth ->
      MK.RegistersWithFullRoundPathControlWork
        n counterWidth}
    {program : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithFullRoundPathControlWorkEncoding
        n counterWidth).width)).toQuantum}
    (h : UnitaryCircuit.Realizes
      (MK.registersWithFullRoundPathControlWorkEncoding n counterWidth)
      program environment step) :
    UnitaryCircuit.Realizes
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
      (stageWithFullRoundPathControlWorkspaceKaliskiProgram program) environment
      (stageWithFullRoundPathControlWorkspaceKaliskiStep step) :=
  UnitaryCircuit.Realizes.onBinarySuffix (left := stageWithWorkEncoding n) h

/-- Clean endpoint for the target-add leg after lifting it over the
path/control fixed-round workspace. -/
lemma addScratchToTargetWithFullRoundPathControlWorkspace_cleanEndpoint
    (n counterWidth : Nat) (s : StageState (2 ^ n))
    (hflag : s.flag = false)
    (workspace :
      MK.RegistersWithFullRoundPathControlWork n counterWidth) :
    addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth
        ((s, cleanWork n), workspace) =
      ((StageState.addScratchToTarget s, cleanWork n), workspace) := by
  simp [addScratchToTargetWithFullRoundPathControlWorkspace,
    addScratchToTargetWithWork_cleanEndpoint n s hflag]

/-- The target-add leg preserves the path/control fixed-round workspace
pointwise. -/
lemma addScratchToTargetWithFullRoundPathControlWorkspace_preservesWorkspace
    (n counterWidth : Nat)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    (addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth x).2 =
      x.2 := by
  cases x
  rfl

/-- Workspace-aware compute/add/uncompute schedule.  The compute leg may leave
the Montgomery--Kaliski finite workspace dirty; the daggered actual circuit
must clean it through the supplied semantic right inverse.
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
  computeProgram :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum
  /-- Correctness of the compute program on full workspace labels. -/
  computeRealizes : ∀ environment : OracleModel.empty.Interpretation,
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
      computeProgram environment computeStep
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
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical ((stageWithWorkspaceEncoding n
      counterWidth).width)).toQuantum :=
  UnitaryCircuit.seq w.computeProgram
    (UnitaryCircuit.seq (stageWithWorkspaceTargetAddProgram n counterWidth)
      (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

/-- The decomposed full-workspace program realizes the selected
compute/add/uncompute semantic update. -/
lemma realizes {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth) w.program environment
      w.step := by
  have htarget :
      UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
        (stageWithWorkspaceTargetAddProgram n counterWidth) environment
        (addScratchToTargetWithWorkspace n counterWidth) :=
    stageWithWorkspaceTargetAdd_realizes n counterWidth
  have huncompute :
      UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
        (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty))
          environment w.uncomputeStep :=
    UnitaryCircuit.Realizes.dagger_of_rightInverse (w.computeRealizes environment)
      (by
        rw [UnitaryCircuit.dagger_matrix]
        rw [Subsingleton.elim
          ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment) environment]
        exact Unitary.star_eq_inv _)
      w.compute_rightInverse
  have htail :
      UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
        (UnitaryCircuit.seq (stageWithWorkspaceTargetAddProgram n counterWidth)
          (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty))) environment
        (fun x : StageWithWorkspace n counterWidth =>
          w.uncomputeStep (addScratchToTargetWithWorkspace n counterWidth x)) :=
    UnitaryCircuit.Realizes.seq
      (firstStep := addScratchToTargetWithWorkspace n counterWidth)
      (secondStep := w.uncomputeStep)
      htarget huncompute
  have hfull :
      UnitaryCircuit.Realizes (stageWithWorkspaceEncoding n counterWidth)
        w.program environment w.step :=
    UnitaryCircuit.Realizes.seq
      (firstStep := w.computeStep)
      (secondStep := fun x : StageWithWorkspace n counterWidth =>
        w.uncomputeStep (addScratchToTargetWithWorkspace n counterWidth x))
      (w.computeRealizes environment) htail
  simpa [program, step, reversibleScheduleStepWithWorkspace] using hfull

/-- Running the reversed compute semantics after the compute leg restores the
full semantic workspace.  The proof uses injectivity of the realized base-gate
program, so the cleanup fact stays tied to the same concrete program that
supplies correctness and resource accounting. -/
lemma compute_leftInverse {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    ∀ x, w.uncomputeStep (w.computeStep x) = x := by
  intro x
  have hinj := UnitaryCircuit.Realizes.injective
    (w.computeRealizes OracleModel.emptyInterpretation)
  apply hinj
  exact w.compute_rightInverse (w.computeStep x)

/-- Encoded-basis correctness for all full-workspace staged inversion labels. -/
lemma apply_ket {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth)
    (x : StageWithWorkspace n counterWidth) :
    UnitaryCircuit.applyVec w.program environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (stageWithWorkspaceEncoding n counterWidth).width).basisEquiv.symm
            ((stageWithWorkspaceEncoding n counterWidth).encode x)) :
          HilbertVector (QubitLayout.canonical
            (stageWithWorkspaceEncoding n counterWidth).width).toQuantum.register) =
      (NormalizedVector.ket
        ((QubitLayout.canonical
            (stageWithWorkspaceEncoding n counterWidth).width).basisEquiv.symm
          ((stageWithWorkspaceEncoding n counterWidth).encode (w.step x))) :
        HilbertVector (QubitLayout.canonical
          (stageWithWorkspaceEncoding n counterWidth).width).toQuantum.register) := by
  exact applyVec_encoded_ket_of_realizes w.realizes x



end DecomposedStageWithWorkspaceWitness

/-- Workspace-aware compute/add/uncompute schedule over the full finite
Montgomery--Kaliski fixed-round workspace.  The compute leg may leave that
workspace dirty; the daggered actual circuit must clean it through the
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
fixed-round workspace.  The target-add leg is fixed to the lifted VBE actual
circuit; the compute program must supply the concrete
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
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundWorkspaceEncoding n counterWidth).width)).toQuantum
  /-- Correctness of the compute program on full workspace labels. -/
  computeRealizes : ∀ environment : OracleModel.empty.Interpretation,
    UnitaryCircuit.Realizes
      (stageWithFullRoundWorkspaceEncoding n counterWidth)
      computeProgram environment computeStep
  /-- The supplied uncompute semantic action is a right inverse of compute. -/
  compute_rightInverse : ∀ x, computeStep (uncomputeStep x) = x

namespace DecomposedStageWithFullRoundWorkspaceWitness

/-- Package a Montgomery--Kaliski full-workspace compute witness as the compute
leg of the staged decomposed inversion wrapper.  The supplied compute witness
must use the standard full-round work encoding; data-dependent selected-branch
round dispatch remains a separate obligation. -/
def ofKaliski {n counterWidth : Nat}
    {computeStep uncomputeStep :
      MK.RegistersWithFullRoundWork n counterWidth ->
        MK.RegistersWithFullRoundWork n counterWidth}
    (computeProgram : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithFullRoundWorkEncoding n counterWidth).width)).toQuantum)
    (computeRealizes : ∀ environment : OracleModel.empty.Interpretation, UnitaryCircuit.Realizes
      (MK.registersWithFullRoundWorkEncoding n counterWidth)
      computeProgram environment computeStep)
    (hright : ∀ x, computeStep (uncomputeStep x) = x) :
    DecomposedStageWithFullRoundWorkspaceWitness n counterWidth where
  computeStep := stageWithFullRoundWorkspaceKaliskiStep computeStep
  uncomputeStep := stageWithFullRoundWorkspaceKaliskiStep uncomputeStep
  computeProgram := stageWithFullRoundWorkspaceKaliskiProgram computeProgram
  computeRealizes := fun environment =>
    stageWithFullRoundWorkspaceKaliski_realizes (computeRealizes environment)
  compute_rightInverse := by
    intro x
    cases x
    simp [stageWithFullRoundWorkspaceKaliskiStep, hright]

/-- Package one explicit Montgomery--Kaliski active-branch full-round witness
as the compute leg of the staged decomposed inversion wrapper.  This exposes
the fixed-branch family through the standard full-round work encoding; the
data-dependent branch selector remains a separate compute obligation. -/
def ofKaliskiActiveBranch {n counterWidth : Nat}
    (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : NumberTheory.BinaryGCD.Branch)
    (uncomputeStep :
      MK.RegistersWithFullRoundWork n counterWidth ->
        MK.RegistersWithFullRoundWork n counterWidth)
    (hright :
      ∀ x,
        MK.fullRoundWorkKaliskiActiveBranchRoundStep
          n counterWidth uIndex vIndex comparisonIndex historyIndex branch
          (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness n counterWidth :=
  ofKaliski
    (MK.fullRoundWorkKaliskiActiveBranchRoundProgram
      n counterWidth uIndex vIndex comparisonIndex historyIndex branch)
    (fun environment => (MK.fullRoundWorkKaliskiActiveBranchRound_realizes
      (environment := environment)
      n counterWidth uIndex vIndex comparisonIndex historyIndex branch))
    hright

/-- Package the terminating counter-mode full-round witness as the compute leg
of the staged decomposed inversion wrapper.  The witness uses the standard
full-round work encoding, so it can be consumed by the same adapter as the
active branch routes. -/
def ofKaliskiTerminating {tail counterWidth : Nat}
    (uncomputeStep :
      MK.RegistersWithFullRoundWork tail.succ counterWidth ->
        MK.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MK.fullRoundWorkTerminatingStep tail counterWidth
          (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliski
    (MK.fullRoundWorkTerminatingStandardLayoutProgram
      tail counterWidth)
    (fun environment => (MK.fullRoundWorkTerminatingStandardLayout_realizes
      (environment := environment)
      tail counterWidth))
    hright

/-- Package the inactive padding full-round witness as the compute leg of the
staged decomposed inversion wrapper.  This covers the inactive fixed-round
padding route under the standard full-round work encoding. -/
def ofKaliskiInactivePadding {tail counterWidth : Nat}
    (uncomputeStep :
      MK.RegistersWithFullRoundWork tail.succ counterWidth ->
        MK.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MK.fullRoundWorkInactivePaddingStep tail counterWidth
          (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliski
    (MK.fullRoundWorkInactivePaddingProgram
      tail counterWidth)
    (fun environment => (MK.fullRoundWorkInactivePadding_realizes (environment := environment)
      tail counterWidth))
    hright

/-- Package the selected branch-code/history/aux-shift full-round dispatch as
the compute leg of the staged decomposed inversion wrapper.  This is the
gate-level selected branch-code dispatch used by the even nonzero cases; the
odd carried dispatch and outer data-dependent selector remain separate
obligations. -/
def ofKaliskiSelectedBranchCodeDispatch
    {tail counterWidth : Nat}
    (tempIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (uncomputeStep :
      MK.RegistersWithFullRoundWork tail.succ counterWidth ->
        MK.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MK.fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliski
    (MK.fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchProgram
      tail counterWidth tempIndex historyIndex)
    (fun environment => (MK.fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatch_realizes
      (environment := environment)
      tail counterWidth tempIndex historyIndex))
    hright

/-- Package the compare-conditioned carried odd dispatch as the compute leg of
the staged decomposed inversion wrapper.  This supplies a concrete gate-level
route for the odd carried branch code; the outer active-round selector and full
compute instantiation remain separate obligations. -/
def ofKaliskiCompareCarriedDispatch
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (uncomputeStep :
      MK.RegistersWithFullRoundWork tail.succ counterWidth ->
        MK.RegistersWithFullRoundWork tail.succ counterWidth)
    (hright :
      ∀ x,
        MK.fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex (uncomputeStep x) =
          x) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  ofKaliski
    (MK.fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchProgram
      tail counterWidth comparisonIndex historyIndex)
    (fun environment =>
      MK.fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatch_realizes
      (environment := environment) tail counterWidth comparisonIndex historyIndex)
    hright

/-- Package the odd-odd latch-then-body full-round dispatch as the compute leg
of the staged decomposed inversion wrapper.  The supplied compute leg carries
its own reversed uncompute witness, so the latched counter carry-in bit is
cleaned by reversing the same wire-addressed program rather than by
recomputing branch predicates after the data path mutates source words. -/
def ofKaliskiOddOddLatchThenBody
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  open MK in
  ofKaliski
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fun environment => fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatch_realizes
      (environment := environment) tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkOddOddLatchThenBody_compute_rightInverse
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Package the active-guarded odd-odd latch-then-body full-round dispatch as
the compute leg of the staged decomposed inversion wrapper.  The compute leg
carries its reversed uncompute witness, so the active-guarded counter carry-in
latch is cleaned by reversing the same wire-addressed program. -/
def ofKaliskiActiveOddOddLatchThenBody
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    DecomposedStageWithFullRoundWorkspaceWitness tail.succ counterWidth :=
  open MK in
  ofKaliski
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fun environment => fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatch_realizes
      (environment := environment) tail counterWidth comparisonIndex historyIndex workIndex)
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
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundWorkspaceEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.seq w.computeProgram
    (UnitaryCircuit.seq
      (stageWithFullRoundWorkspaceTargetAddProgram n counterWidth)
      (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

/-- The decomposed full-round-workspace program realizes the selected
compute/add/uncompute semantic update. -/
lemma realizes {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    UnitaryCircuit.Realizes
      (stageWithFullRoundWorkspaceEncoding n counterWidth)
      w.program environment w.step := by
  have htarget :
      UnitaryCircuit.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        (stageWithFullRoundWorkspaceTargetAddProgram n counterWidth) environment
        (addScratchToTargetWithFullRoundWorkspace n counterWidth) :=
    stageWithFullRoundWorkspaceTargetAdd_realizes n counterWidth
  have huncompute :
      UnitaryCircuit.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty))
          environment w.uncomputeStep :=
    UnitaryCircuit.Realizes.dagger_of_rightInverse (w.computeRealizes environment)
      (by
        rw [UnitaryCircuit.dagger_matrix]
        rw [Subsingleton.elim
          ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment) environment]
        exact Unitary.star_eq_inv _)
      w.compute_rightInverse
  have htail :
      UnitaryCircuit.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        (UnitaryCircuit.seq
          (stageWithFullRoundWorkspaceTargetAddProgram n counterWidth)
          (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty))) environment
        (fun x : StageWithFullRoundWorkspace n counterWidth =>
          w.uncomputeStep
            (addScratchToTargetWithFullRoundWorkspace n counterWidth x)) :=
    UnitaryCircuit.Realizes.seq
      (firstStep := addScratchToTargetWithFullRoundWorkspace n counterWidth)
      (secondStep := w.uncomputeStep)
      htarget huncompute
  have hfull :
      UnitaryCircuit.Realizes
        (stageWithFullRoundWorkspaceEncoding n counterWidth)
        w.program environment w.step :=
    UnitaryCircuit.Realizes.seq
      (firstStep := w.computeStep)
      (secondStep := fun x : StageWithFullRoundWorkspace n counterWidth =>
        w.uncomputeStep
          (addScratchToTargetWithFullRoundWorkspace n counterWidth x))
      (w.computeRealizes environment) htail
  simpa [program, step, reversibleScheduleStepWithFullRoundWorkspace] using
    hfull

/-- Running the reversed compute semantics after the compute leg restores the
full fixed-round workspace.  This derives the forward cleanup projection from
the realized reversible program plus the supplied semantic right inverse. -/
lemma compute_leftInverse {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    ∀ x, w.uncomputeStep (w.computeStep x) = x := by
  intro x
  have hinj := UnitaryCircuit.Realizes.injective
    (w.computeRealizes OracleModel.emptyInterpretation)
  apply hinj
  exact w.compute_rightInverse (w.computeStep x)

/-- Encoded-basis correctness for all full-round-workspace staged inversion
labels. -/
lemma apply_ket {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth)
    (x : StageWithFullRoundWorkspace n counterWidth) :
    UnitaryCircuit.applyVec w.program environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (stageWithFullRoundWorkspaceEncoding n
                counterWidth).width).basisEquiv.symm
            ((stageWithFullRoundWorkspaceEncoding n counterWidth).encode x)) :
          HilbertVector (QubitLayout.canonical
            (stageWithFullRoundWorkspaceEncoding n
              counterWidth).width).toQuantum.register) =
      (NormalizedVector.ket
        ((QubitLayout.canonical
            (stageWithFullRoundWorkspaceEncoding n
              counterWidth).width).basisEquiv.symm
          ((stageWithFullRoundWorkspaceEncoding n counterWidth).encode
            (w.step x))) :
        HilbertVector (QubitLayout.canonical
          (stageWithFullRoundWorkspaceEncoding n
            counterWidth).width).toQuantum.register) := by
  exact applyVec_encoded_ket_of_realizes w.realizes x



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
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width)).toQuantum
  /-- Correctness of the compute program on path/control workspace labels. -/
  computeRealizes : ∀ environment : OracleModel.empty.Interpretation,
    UnitaryCircuit.Realizes
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
      computeProgram environment computeStep
  /-- The supplied uncompute semantic action is a right inverse of compute. -/
  compute_rightInverse : ∀ x, computeStep (uncomputeStep x) = x

namespace DecomposedStageWithFullRoundPathControlWorkspaceWitness

/-- Package a path/control Montgomery--Kaliski compute witness as the compute
leg of the staged decomposed inversion wrapper. -/
def ofKaliski {n counterWidth : Nat}
    {computeStep uncomputeStep :
      MK.RegistersWithFullRoundPathControlWork
          n counterWidth ->
        MK.RegistersWithFullRoundPathControlWork
          n counterWidth}
    (computeProgram : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((MK.registersWithFullRoundPathControlWorkEncoding
        n counterWidth).width)).toQuantum)
    (computeRealizes : ∀ environment : OracleModel.empty.Interpretation, UnitaryCircuit.Realizes
      (MK.registersWithFullRoundPathControlWorkEncoding n counterWidth)
      computeProgram environment computeStep)
    (hright : ∀ x, computeStep (uncomputeStep x) = x) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth where
  computeStep :=
    stageWithFullRoundPathControlWorkspaceKaliskiStep computeStep
  uncomputeStep :=
    stageWithFullRoundPathControlWorkspaceKaliskiStep uncomputeStep
  computeProgram :=
    stageWithFullRoundPathControlWorkspaceKaliskiProgram computeProgram
  computeRealizes := fun environment =>
    stageWithFullRoundPathControlWorkspaceKaliski_realizes (computeRealizes environment)
  compute_rightInverse := by
    intro x
    cases x
    simp [stageWithFullRoundPathControlWorkspaceKaliskiStep, hright]

/-- Package the folded fixed-round path/control route as the compute leg of the
staged decomposed inversion wrapper.  The supplied uncompute step is kept
explicit so callers can use the reversed same program once a semantic inverse
for the folded route is available. -/
def ofKaliskiFixedRoundPathControl
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (uncomputeStep :
      MK.RegistersWithFullRoundPathControlWork
          tail.succ counterWidth ->
        MK.RegistersWithFullRoundPathControlWork
          tail.succ counterWidth)
    (hright :
      ∀ x,
        MK.fixedRoundPathControlWorkKaliskiRoundFoldStep
          tail counterWidth comparisonIndex workIndex (uncomputeStep x) =
        x) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness
      tail.succ counterWidth :=
  ofKaliski
    (MK.fixedRoundPathControlWorkKaliskiRoundFoldProgram
      tail counterWidth comparisonIndex workIndex)
    (fun environment => MK.fixedRoundPathControlWorkKaliskiRoundFold_realizes
      (environment := environment) tail counterWidth comparisonIndex workIndex)
    hright

/-- Package the folded fixed-round path/control route using the semantic
inverse selected from the finite reversible workspace.  The concrete uncompute
program remains the inverse of the same folded path/control compute program. -/
noncomputable def ofKaliskiFixedRoundPathControlFiniteInverse
    {tail counterWidth : Nat}
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    DecomposedStageWithFullRoundPathControlWorkspaceWitness
      tail.succ counterWidth :=
  ofKaliskiFixedRoundPathControl comparisonIndex workIndex
    (MK.fixedRoundPathControlWorkKaliskiRoundFoldUncomputeStep
      tail counterWidth comparisonIndex workIndex)
    (MK.fixedRoundPathControlWorkKaliskiRoundFold_compute_rightInverse
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
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((stageWithFullRoundPathControlWorkspaceEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.seq w.computeProgram
    (UnitaryCircuit.seq
      (stageWithFullRoundPathControlWorkspaceTargetAddProgram n counterWidth)
      (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

/-- The decomposed path/control workspace program realizes the selected
compute/add/uncompute semantic update. -/
lemma realizes {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    UnitaryCircuit.Realizes
      (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
      w.program environment w.step := by
  have htarget :
      UnitaryCircuit.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        (stageWithFullRoundPathControlWorkspaceTargetAddProgram
          n counterWidth) environment
        (addScratchToTargetWithFullRoundPathControlWorkspace
          n counterWidth) :=
    stageWithFullRoundPathControlWorkspaceTargetAdd_realizes
      n counterWidth
  have huncompute :
      UnitaryCircuit.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty))
          environment w.uncomputeStep :=
    UnitaryCircuit.Realizes.dagger_of_rightInverse (w.computeRealizes environment)
      (by
        rw [UnitaryCircuit.dagger_matrix]
        rw [Subsingleton.elim
          ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment) environment]
        exact Unitary.star_eq_inv _)
      w.compute_rightInverse
  have htail :
      UnitaryCircuit.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        (UnitaryCircuit.seq
          (stageWithFullRoundPathControlWorkspaceTargetAddProgram
            n counterWidth)
          (w.computeProgram.dagger (AlgorithmGate.oracleFreeAdjoints .empty))) environment
        (fun x : StageWithFullRoundPathControlWorkspace n counterWidth =>
          w.uncomputeStep
            (addScratchToTargetWithFullRoundPathControlWorkspace
              n counterWidth x)) :=
    UnitaryCircuit.Realizes.seq
      (firstStep :=
        addScratchToTargetWithFullRoundPathControlWorkspace n counterWidth)
      (secondStep := w.uncomputeStep)
      htarget huncompute
  have hfull :
      UnitaryCircuit.Realizes
        (stageWithFullRoundPathControlWorkspaceEncoding n counterWidth)
        w.program environment w.step :=
    UnitaryCircuit.Realizes.seq
      (firstStep := w.computeStep)
      (secondStep :=
        fun x : StageWithFullRoundPathControlWorkspace n counterWidth =>
          w.uncomputeStep
            (addScratchToTargetWithFullRoundPathControlWorkspace
              n counterWidth x))
      (w.computeRealizes environment) htail
  simpa [program, step,
    reversibleScheduleStepWithFullRoundPathControlWorkspace] using hfull

/-- Running the reversed compute semantics after the path/control compute leg
restores the full staged workspace. -/
lemma compute_leftInverse {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    ∀ x, w.uncomputeStep (w.computeStep x) = x := by
  intro x
  have hinj := UnitaryCircuit.Realizes.injective
    (w.computeRealizes OracleModel.emptyInterpretation)
  apply hinj
  exact w.compute_rightInverse (w.computeStep x)

/-- Encoded-basis correctness for all path/control full-workspace staged
inversion labels. -/
lemma apply_ket {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth)
    (x : StageWithFullRoundPathControlWorkspace n counterWidth) :
    UnitaryCircuit.applyVec w.program environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (stageWithFullRoundPathControlWorkspaceEncoding
                n counterWidth).width).basisEquiv.symm
            ((stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).encode x)) :
          HilbertVector (QubitLayout.canonical
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width).toQuantum.register) =
      (NormalizedVector.ket
        ((QubitLayout.canonical
            (stageWithFullRoundPathControlWorkspaceEncoding
              n counterWidth).width).basisEquiv.symm
          ((stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).encode (w.step x))) :
        HilbertVector (QubitLayout.canonical
          (stageWithFullRoundPathControlWorkspaceEncoding
            n counterWidth).width).toQuantum.register) := by
  exact applyVec_encoded_ket_of_realizes w.realizes x

end DecomposedStageWithFullRoundPathControlWorkspaceWitness

end
end StructuredWitness
end MK
end MAU.Inversion
end QuantumAlg

end
