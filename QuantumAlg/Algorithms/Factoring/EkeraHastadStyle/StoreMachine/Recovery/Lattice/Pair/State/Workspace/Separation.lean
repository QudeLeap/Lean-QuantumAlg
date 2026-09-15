/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Views

/-!
# Persistent pair-state workspace separation

The 25-cell state inventory directly supplies the key injectivity of the LLL
machine and the local and cross-invocation separation of both terminal
decoders.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairStateWorkspaceSeparation

open ClassicalRoutines
open Execution

noncomputable section

private theorem stateKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) (left right : LatticePairStateWorkspaceLayout.Cell)
    (different : left ≠ right) :
    (LatticePairStateWorkspaceLayout.cellRef state left).toCStorageRef.key ≠
      (LatticePairStateWorkspaceLayout.cellRef state right).toCStorageRef.key := by
  intro equal
  exact different
    (LatticePairStateWorkspaceLayout.cellRef_key_injective state distinct equal)

/-- A physical destination is outside the exact support of every distinct stored source. -/
private theorem stateInput_avoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) (source target : LatticePairStateWorkspaceLayout.Cell)
    (different : source ≠ target) :
    (LatticePairStateWorkspaceLayout.cellRef state target).key ∉
      (CInputRef.storage
        (LatticePairStateWorkspaceLayout.cellRef state source).toCStorageRef).storageKeys := by
  change (LatticePairStateWorkspaceLayout.cellRef state target).key ∉
    [(LatticePairStateWorkspaceLayout.cellRef state source).key]
  simpa only [List.mem_singleton] using (stateKey_ne state distinct source target different).symm

/-- Physical state cell underlying one semantic LLL machine cell. -/
def machineCell : LatticeState.MachineCell → LatticePairStateWorkspaceLayout.Cell
  | .firstFirst => .basis11
  | .firstSecond => .basis12
  | .firstThird => .basis13
  | .secondFirst => .basis21
  | .secondSecond => .basis22
  | .secondThird => .basis23
  | .thirdFirst => .basis31
  | .thirdSecond => .basis32
  | .thirdThird => .basis33
  | .secondPhase => .secondPhase
  | .done => .done

/-- The semantic-to-physical machine-cell projection is injective. -/
theorem machineCell_injective : Function.Injective machineCell := by
  intro left right equal
  cases left <;> cases right <;> simp [machineCell] at equal ⊢

/-- Machine keys are exactly the corresponding physical state keys. -/
theorem machineKey_eq_cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (cell : LatticeState.MachineCell) :
    (LatticePairStateWorkspaceViews.machineRefs state).keyOf cell =
      (LatticePairStateWorkspaceLayout.cellRef state
        (machineCell cell)).toCStorageRef.key := by
  cases cell <;> rfl

/-- State-layout distinctness supplies the fixed-fuel machine key invariant. -/
theorem machineSeparated {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) :
    (LatticePairStateWorkspaceViews.machineRefs state).Separated := by
  intro left right equal
  apply machineCell_injective
  apply LatticePairStateWorkspaceLayout.cellRef_key_injective state distinct
  simpa only [machineKey_eq_cellRef] using equal

/-- Physical state cell underlying one output of the first decoder. -/
def firstOutputCell : BatchMachine.PairOutputSlot →
    LatticePairStateWorkspaceLayout.Cell
  | .full => .firstFull
  | .scratch => .firstScratch
  | .j => .firstJ
  | .k => .firstK

/-- Physical state cell underlying one output of the second decoder. -/
def secondOutputCell : BatchMachine.PairOutputSlot →
    LatticePairStateWorkspaceLayout.Cell
  | .full => .secondFull
  | .scratch => .secondScratch
  | .j => .secondJ
  | .k => .secondK

private theorem firstOutputKey_eq {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (input : CInputRef ctx (.bits (measurementBits N)))
    (slot : BatchMachine.PairOutputSlot) :
    BatchMachine.pairOutputKey
        (LatticePairStateWorkspaceViews.firstDecoderRefs state input) slot =
      (LatticePairStateWorkspaceLayout.cellRef state
        (firstOutputCell slot)).toCStorageRef.key := by
  cases slot <;> rfl

private theorem secondOutputKey_eq {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (input : CInputRef ctx (.bits (measurementBits N)))
    (slot : BatchMachine.PairOutputSlot) :
    BatchMachine.pairOutputKey
        (LatticePairStateWorkspaceViews.secondDecoderRefs state input) slot =
      (LatticePairStateWorkspaceLayout.cellRef state
        (secondOutputCell slot)).toCStorageRef.key := by
  cases slot <;> rfl

private theorem liftedInput_avoids_stateCell {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (transport : ClassicalWorkspace.Transport outer ctx)
    (separated : state.TransportSeparated transport)
    (input : CInputRef outer (.bits (measurementBits N)))
    (cell : LatticePairStateWorkspaceLayout.Cell) :
    (LatticePairStateWorkspaceLayout.cellRef state cell).key ∉
      (transport.liftInput input).storageKeys := by
  exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
    state transport separated input
    (LatticePairStateWorkspaceLayout.cellIndex N cell)

private theorem firstDecoderSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) (transport : ClassicalWorkspace.Transport outer ctx)
    (separated : state.TransportSeparated transport)
    (input : CInputRef outer (.bits (measurementBits N))) :
    BatchMachine.Separation
      (LatticePairStateWorkspaceViews.firstDecoderRefs state
        (transport.liftInput input)) := by
  refine {
    inputAvoidsFull := liftedInput_avoids_stateCell state transport separated
      input .firstFull
    inputAvoidsScratch := liftedInput_avoids_stateCell state transport separated
      input .firstScratch
    inputAvoidsJ := liftedInput_avoids_stateCell state transport separated
      input .firstJ
    inputAvoidsK := liftedInput_avoids_stateCell state transport separated
      input .firstK
    fullAvoidsScratch := stateKey_ne state distinct .firstScratch .firstFull
      (by decide)
    fullAvoidsJ := stateKey_ne state distinct .firstJ .firstFull (by decide)
    fullAvoidsK := stateKey_ne state distinct .firstK .firstFull (by decide)
    scratchAvoidsJ := stateKey_ne state distinct .firstJ .firstScratch
      (by decide)
    scratchAvoidsK := stateKey_ne state distinct .firstK .firstScratch
      (by decide)
    jAvoidsK := stateKey_ne state distinct .firstK .firstJ (by decide) }

private theorem secondDecoderSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) (transport : ClassicalWorkspace.Transport outer ctx)
    (separated : state.TransportSeparated transport)
    (input : CInputRef outer (.bits (measurementBits N))) :
    BatchMachine.Separation
      (LatticePairStateWorkspaceViews.secondDecoderRefs state
        (transport.liftInput input)) := by
  refine {
    inputAvoidsFull := liftedInput_avoids_stateCell state transport separated
      input .secondFull
    inputAvoidsScratch := liftedInput_avoids_stateCell state transport separated
      input .secondScratch
    inputAvoidsJ := liftedInput_avoids_stateCell state transport separated
      input .secondJ
    inputAvoidsK := liftedInput_avoids_stateCell state transport separated
      input .secondK
    fullAvoidsScratch := stateKey_ne state distinct .secondScratch .secondFull
      (by decide)
    fullAvoidsJ := stateKey_ne state distinct .secondJ .secondFull (by decide)
    fullAvoidsK := stateKey_ne state distinct .secondK .secondFull (by decide)
    scratchAvoidsJ := stateKey_ne state distinct .secondJ .secondScratch
      (by decide)
    scratchAvoidsK := stateKey_ne state distinct .secondK .secondScratch
      (by decide)
    jAvoidsK := stateKey_ne state distinct .secondK .secondJ (by decide) }

/-- Physical state distinctness and caller transport supply the complete
two-decoder separation package. -/
theorem pairSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) (transport : ClassicalWorkspace.Transport outer ctx)
    (separated : state.TransportSeparated transport)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    BatchMachine.PairSeparation
      (LatticePairStateWorkspaceViews.pairRefs state
        (transport.liftInput firstTerminal)
        (transport.liftInput secondTerminal)) := by
  refine {
    first := firstDecoderSeparation state distinct transport separated
      firstTerminal
    second := secondDecoderSeparation state distinct transport separated
      secondTerminal
    firstInputAvoidsSecond := ?_
    secondInputAvoidsFirst := ?_
    firstOutputsAvoidSecond := ?_ }
  · intro slot
    change BatchMachine.pairOutputKey
      (LatticePairStateWorkspaceViews.secondDecoderRefs state
        (transport.liftInput secondTerminal)) slot ∉ (transport.liftInput firstTerminal).storageKeys
    rw [secondOutputKey_eq]
    exact liftedInput_avoids_stateCell state transport separated firstTerminal
      (secondOutputCell slot)
  · intro slot
    change BatchMachine.pairOutputKey
      (LatticePairStateWorkspaceViews.firstDecoderRefs state
        (transport.liftInput firstTerminal)) slot ∉ (transport.liftInput secondTerminal).storageKeys
    rw [firstOutputKey_eq]
    exact liftedInput_avoids_stateCell state transport separated secondTerminal
      (firstOutputCell slot)
  · intro firstSlot secondSlot
    change
      BatchMachine.pairOutputKey
          (LatticePairStateWorkspaceViews.firstDecoderRefs state
            (transport.liftInput firstTerminal)) firstSlot ≠
        BatchMachine.pairOutputKey
          (LatticePairStateWorkspaceViews.secondDecoderRefs state
            (transport.liftInput secondTerminal)) secondSlot
    rw [firstOutputKey_eq, secondOutputKey_eq]
    apply stateKey_ne state distinct
    cases firstSlot <;> cases secondSlot <;> decide

/-- Physical state cell underlying one first-row basis name. -/
def firstRowCell : LatticeBasis.FirstRowCell →
    LatticePairStateWorkspaceLayout.Cell
  | .b11 => .basis11
  | .b12 => .basis12
  | .b13 => .basis13

/-- Physical state cell underlying one caller-initialized zero basis name. -/
def zeroCell : LatticeBasis.ZeroCell → LatticePairStateWorkspaceLayout.Cell
  | .b22 => .basis22
  | .b23 => .basis23
  | .b31 => .basis31
  | .b33 => .basis33

/-- The physical state inventory supplies the complete sequential basis-loader
separation. -/
theorem basisSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct)
    (firstTerminal secondTerminal : CInputRef ctx (.bits (measurementBits N))) :
    LatticeBasis.Separation
      (LatticePairStateWorkspaceViews.pairRefs state firstTerminal secondTerminal)
      (LatticePairStateWorkspaceViews.rawRefs state) := by
  refine {
    first := {
      firstJAvoidsB11 := stateKey_ne state distinct .basis11 .firstJ (by decide)
      firstJAvoidsB12 := stateKey_ne state distinct .basis12 .firstJ (by decide)
      firstJAvoidsB13 := stateKey_ne state distinct .basis13 .firstJ (by decide)
      secondJAvoidsB11 := stateKey_ne state distinct .basis11 .secondJ
        (by decide)
      secondJAvoidsB12 := stateKey_ne state distinct .basis12 .secondJ
        (by decide)
      secondJAvoidsB13 := stateKey_ne state distinct .basis13 .secondJ
        (by decide)
      b11AvoidsB12 := stateKey_ne state distinct .basis12 .basis11 (by decide)
      b11AvoidsB13 := stateKey_ne state distinct .basis13 .basis11 (by decide)
      b12AvoidsB13 := stateKey_ne state distinct .basis13 .basis12 (by decide) }
    b21AvoidsFirstRow := ?_
    b32AvoidsFirstRow := ?_
    firstRowAvoidsB21 := ?_
    firstRowAvoidsB32 := ?_
    b32AvoidsB21 := stateInput_avoids state distinct .basis32 .basis21 (by decide)
    b21AvoidsB32 := stateInput_avoids state distinct .basis21 .basis32 (by decide)
    zeroCellAvoidsFirstRow := ?_
    zeroCellAvoidsB21 := ?_
    zeroCellAvoidsB32 := ?_ }
  · intro cell
    cases cell with
    | b11 => exact stateInput_avoids state distinct .basis21 .basis11 (by decide)
    | b12 => exact stateInput_avoids state distinct .basis21 .basis12 (by decide)
    | b13 => exact stateInput_avoids state distinct .basis21 .basis13 (by decide)
  · intro cell
    cases cell with
    | b11 => exact stateInput_avoids state distinct .basis32 .basis11 (by decide)
    | b12 => exact stateInput_avoids state distinct .basis32 .basis12 (by decide)
    | b13 => exact stateInput_avoids state distinct .basis32 .basis13 (by decide)
  · intro cell
    cases cell with
    | b11 => exact stateInput_avoids state distinct .basis11 .basis21 (by decide)
    | b12 => exact stateInput_avoids state distinct .basis12 .basis21 (by decide)
    | b13 => exact stateInput_avoids state distinct .basis13 .basis21 (by decide)
  · intro cell
    cases cell with
    | b11 => exact stateInput_avoids state distinct .basis11 .basis32 (by decide)
    | b12 => exact stateInput_avoids state distinct .basis12 .basis32 (by decide)
    | b13 => exact stateInput_avoids state distinct .basis13 .basis32 (by decide)
  · intro cell
    cases cell with
    | b22 => exact ⟨stateInput_avoids state distinct .basis22 .basis11 (by decide),
        stateInput_avoids state distinct .basis22 .basis12 (by decide),
        stateInput_avoids state distinct .basis22 .basis13 (by decide)⟩
    | b23 => exact ⟨stateInput_avoids state distinct .basis23 .basis11 (by decide),
        stateInput_avoids state distinct .basis23 .basis12 (by decide),
        stateInput_avoids state distinct .basis23 .basis13 (by decide)⟩
    | b31 => exact ⟨stateInput_avoids state distinct .basis31 .basis11 (by decide),
        stateInput_avoids state distinct .basis31 .basis12 (by decide),
        stateInput_avoids state distinct .basis31 .basis13 (by decide)⟩
    | b33 => exact ⟨stateInput_avoids state distinct .basis33 .basis11 (by decide),
        stateInput_avoids state distinct .basis33 .basis12 (by decide),
        stateInput_avoids state distinct .basis33 .basis13 (by decide)⟩
  · intro cell
    cases cell with
    | b22 => exact stateInput_avoids state distinct .basis22 .basis21 (by decide)
    | b23 => exact stateInput_avoids state distinct .basis23 .basis21 (by decide)
    | b31 => exact stateInput_avoids state distinct .basis31 .basis21 (by decide)
    | b33 => exact stateInput_avoids state distinct .basis33 .basis21 (by decide)
  · intro cell
    cases cell with
    | b22 => exact stateInput_avoids state distinct .basis22 .basis32 (by decide)
    | b23 => exact stateInput_avoids state distinct .basis23 .basis32 (by decide)
    | b31 => exact stateInput_avoids state distinct .basis31 .basis32 (by decide)
    | b33 => exact stateInput_avoids state distinct .basis33 .basis32 (by decide)

/-- The eight decoder cells in physical layout order. -/
def decoderCells : List LatticePairStateWorkspaceLayout.Cell :=
  [.firstFull, .firstScratch, .firstJ, .firstK,
    .secondFull, .secondScratch, .secondJ, .secondK]

/-- The nine raw basis cells in semantic key-list order. -/
def rawBasisCells : List LatticePairStateWorkspaceLayout.Cell :=
  [.basis11, .basis12, .basis13, .basis21, .basis22,
    .basis23, .basis31, .basis32, .basis33]

private theorem decoderKeys_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (firstTerminal secondTerminal : CInputRef ctx (.bits (measurementBits N))) :
    LatticeWideInitializationPrefix.decoderKeys
        (LatticePairStateWorkspaceViews.pairRefs state
          firstTerminal secondTerminal) =
      decoderCells.map fun cell =>
        (LatticePairStateWorkspaceLayout.cellRef state cell).toCStorageRef.key := by
  rfl

private theorem rawKeys_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : LatticePairStateWorkspaceLayout.Cells ctx N) :
    LatticeWideInitializationPrefix.rawKeys
        (LatticePairStateWorkspaceViews.rawRefs state) =
      rawBasisCells.map fun cell =>
        (LatticePairStateWorkspaceLayout.cellRef state cell).toCStorageRef.key := by
  rfl

/-- Exact physical decoder--basis prefix view over the state package. -/
def prefixRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (firstTerminal secondTerminal : CInputRef ctx (.bits (measurementBits N))) :
    LatticeWideInitializationPrefix.Refs ctx N where
  pair := LatticePairStateWorkspaceViews.pairRefs state
    firstTerminal secondTerminal
  raw := LatticePairStateWorkspaceViews.rawRefs state
  roles := LatticePairStateWorkspaceViews.rawRoles state

/-- State distinctness and caller transport supply the complete decoder--basis
prefix separation. -/
theorem prefixSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) (transport : ClassicalWorkspace.Transport outer ctx)
    (separated : state.TransportSeparated transport)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideInitializationPrefix.Separation
      (prefixRefs state (transport.liftInput firstTerminal)
        (transport.liftInput secondTerminal)) := by
  let firstAt := transport.liftInput firstTerminal
  let secondAt := transport.liftInput secondTerminal
  refine {
    decoder := pairSeparation state distinct transport separated
      firstTerminal secondTerminal
    basis := basisSeparation state distinct firstAt secondAt
    decoderRaw := ?_ }
  intro decoderKey decoderMember rawKey rawMember
  change decoderKey ∈
    LatticeWideInitializationPrefix.decoderKeys
      (LatticePairStateWorkspaceViews.pairRefs state firstAt secondAt) at decoderMember
  change rawKey ∈ LatticeWideInitializationPrefix.rawKeys
    (LatticePairStateWorkspaceViews.rawRefs state) at rawMember
  rw [decoderKeys_eq] at decoderMember
  rw [rawKeys_eq] at rawMember
  rcases List.mem_map.mp decoderMember with
    ⟨decoderCell, decoderCellMember, rfl⟩
  rcases List.mem_map.mp rawMember with ⟨rawCell, rawCellMember, rfl⟩
  intro equal
  have cellEqual :=
    LatticePairStateWorkspaceLayout.cellRef_key_injective state distinct equal
  have disjoint : List.Disjoint decoderCells rawBasisCells := by
    simp [decoderCells, rawBasisCells, List.disjoint_left]
  rw [List.disjoint_left] at disjoint
  rw [← cellEqual] at rawCellMember
  exact disjoint decoderCellMember rawCellMember

end

end LatticePairStateWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
