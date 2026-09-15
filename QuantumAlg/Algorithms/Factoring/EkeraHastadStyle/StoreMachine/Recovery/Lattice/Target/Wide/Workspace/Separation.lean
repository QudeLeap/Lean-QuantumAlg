/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Workspace.Views

/-!
# Wide-target workspace separation

Distinct persistent and scratch inventories, together with transport separation
of the earlier inputs, supply the complete `LatticeWideTargetMachine`
separation contract.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeWideTargetWorkspaceSeparation

open Execution

noncomputable section

namespace Scratch

/-- Abbreviation for the local cell interface. -/
abbrev Cell := LatticeWideTargetWorkspaceLayout.Cell

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeWideTargetWorkspaceViews.Scratch.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  LatticeWideTargetWorkspaceViews.Scratch.cellRef cells cell

end Scratch

namespace State

/-- Abbreviation for the local cell interface. -/
abbrev Cell := LatticePairStateWorkspaceLayout.Cell

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeWideTargetWorkspaceViews.State.Cells ctx N

end State

/-- Shape of one named mutable wide-target scratch cell. -/
def mutableShape (width : Nat) : Scratch.Cell → CShape
  | .firstScaled | .secondScaled | .firstScratch | .secondScratch =>
      .unsignedWord width
  | .firstIsZero | .firstBelowHalf | .secondIsZero | .secondBelowHalf => .bit

/-- Resolve one semantic mutable name to its writable target-machine cell. -/
def mutableRef {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width) :
    (cell : Scratch.Cell) → CWriteRef ctx (mutableShape width cell)
  | .firstScaled => refs.first.scaled
  | .secondScaled => refs.second.scaled
  | .firstScratch => refs.target.first.scratch
  | .firstIsZero => refs.target.first.isZero
  | .firstBelowHalf => refs.target.first.belowHalf
  | .secondScratch => refs.target.second.scratch
  | .secondIsZero => refs.target.second.isZero
  | .secondBelowHalf => refs.target.second.belowHalf

/-- Physical storage identity of one mutable wide-target scratch cell. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width)
    (cell : Scratch.Cell) : StorageKey :=
  (mutableRef refs cell).toCStorageRef.key

/-- Earlier reads that must remain outside every wide-target scratch cell. -/
inductive ExternalSourceCell where
  | firstK | secondK | modulus
  | firstOutput | secondOutput | third
deriving DecidableEq

/-- Shape of one named earlier source read. -/
def externalSourceShape (ell width : Nat) : ExternalSourceCell → CShape
  | .firstK | .secondK => .unsignedWord ell
  | .modulus | .firstOutput | .secondOutput | .third => .unsignedWord width

/-- Resolve one named earlier source to its structural input. -/
def externalSourceInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width) :
    (source : ExternalSourceCell) →
      CInputRef ctx (externalSourceShape ell width source)
  | .firstK => refs.first.k
  | .secondK => refs.second.k
  | .modulus => refs.modulus
  | .firstOutput => LatticeTarget.writeInput refs.target.first.output
  | .secondOutput => LatticeTarget.writeInput refs.target.second.output
  | .third => LatticeState.coordinateInput refs.target.point.third

/-- Compact frame contract spanning persistent and phase-local storage. -/
structure FrameSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width) : Prop where
  mutableKeyInjective : Function.Injective (mutableKey refs)
  externalAvoidsMutable : ∀ source target,
    mutableKey refs target ∉ (externalSourceInput refs source).storageKeys
  modulusAvoidsFirstOutput :
    refs.target.first.output.key ∉ refs.modulus.storageKeys
  modulusAvoidsSecondOutput :
    refs.target.second.output.key ∉ refs.modulus.storageKeys
  firstOutputAvoidsSecondOutput :
    refs.target.second.output.key ∉
      (LatticeTarget.writeInput refs.target.first.output).storageKeys
  thirdAvoidsFirstOutput :
    refs.target.first.output.key ∉
      (LatticeState.coordinateInput refs.target.point.third).storageKeys
  thirdAvoidsSecondOutput :
    refs.target.second.output.key ∉
      (LatticeState.coordinateInput refs.target.point.third).storageKeys

/-- Different named mutable cells have different storage identities. -/
theorem FrameSeparation.mutableKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} {refs : LatticeWideTargetMachine.Refs ctx m ell width}
    (separation : FrameSeparation refs) {left right : Scratch.Cell}
    (different : left ≠ right) : mutableKey refs left ≠ mutableKey refs right := by
  intro equal
  exact different (separation.mutableKeyInjective equal)

/-- One earlier source avoids one named mutable scratch cell. -/
theorem FrameSeparation.externalAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} {refs : LatticeWideTargetMachine.Refs ctx m ell width}
    (separation : FrameSeparation refs) (source : ExternalSourceCell)
    (target : Scratch.Cell) :
    mutableKey refs target ∉ (externalSourceInput refs source).storageKeys :=
  separation.externalAvoidsMutable source target

/-- Exact key projection of one mutable view through the physical inventory. -/
theorem mutableKey_eq_cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N)
    (pair : BatchMachine.PairRefs ctx N) (cell : Scratch.Cell) :
    mutableKey (LatticeWideTargetWorkspaceViews.targetRefs state scratch pair) cell =
      (Scratch.cellRef scratch cell).toCStorageRef.key := by
  cases cell <;> rfl

/-- Earlier inputs avoid every physical scratch cell. -/
def ExternalAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N)
    (refs : LatticeWideTargetMachine.Refs ctx (shortLogBits N)
      (tradeoffBits N) (LatticeWideTargetWorkspaceViews.Scratch.Width N)) : Prop :=
  ∀ source cell,
    (Scratch.cellRef scratch cell).key ∉ (externalSourceInput refs source).storageKeys

private theorem storage_read_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

private theorem storage_read_key_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (avoids : key ∉ (CInputRef.storage source).storageKeys) : source.key ≠ key := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using avoids

private theorem stateKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : State.Cells ctx N) (distinct : state.Distinct)
    (left right : State.Cell) (different : left ≠ right) :
    (LatticePairStateWorkspaceLayout.cellRef state left).toCStorageRef.key ≠
      (LatticePairStateWorkspaceLayout.cellRef state right).toCStorageRef.key := by
  intro equal
  exact different
    (LatticePairStateWorkspaceLayout.cellRef_key_injective state distinct equal)

/-- The two physical inventories supply the compact target frame contract. -/
theorem frameSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (stateDistinct : state.Distinct)
    (scratch : Scratch.Cells ctx N) (scratchDistinct : scratch.Distinct)
    (pair : BatchMachine.PairRefs ctx N)
    (externalAvoids : ExternalAvoids scratch
      (LatticeWideTargetWorkspaceViews.targetRefs state scratch pair)) :
    FrameSeparation
      (LatticeWideTargetWorkspaceViews.targetRefs state scratch pair) := by
  let refs := LatticeWideTargetWorkspaceViews.targetRefs state scratch pair
  refine {
    mutableKeyInjective := ?_
    externalAvoidsMutable := ?_
    modulusAvoidsFirstOutput := ?_
    modulusAvoidsSecondOutput := ?_
    firstOutputAvoidsSecondOutput := ?_
    thirdAvoidsFirstOutput := ?_
    thirdAvoidsSecondOutput := ?_ }
  · intro left right equal
    apply LatticeWideTargetWorkspaceLayout.cellRef_key_injective scratch scratchDistinct
    simpa only [refs, mutableKey_eq_cellRef] using equal
  · intro source target
    rw [mutableKey_eq_cellRef]
    exact externalAvoids source target
  · apply storage_read_not_mem
    change
      (LatticePairStateWorkspaceLayout.cellRef state .basis21).toCStorageRef.key ≠
        (LatticePairStateWorkspaceLayout.cellRef state .targetFirst).toCStorageRef.key
    exact stateKey_ne state stateDistinct .basis21 .targetFirst (by decide)
  · apply storage_read_not_mem
    change
      (LatticePairStateWorkspaceLayout.cellRef state .basis21).toCStorageRef.key ≠
        (LatticePairStateWorkspaceLayout.cellRef state .targetSecond).toCStorageRef.key
    exact stateKey_ne state stateDistinct .basis21 .targetSecond (by decide)
  · apply storage_read_not_mem
    change
      (LatticePairStateWorkspaceLayout.cellRef state .targetFirst).toCStorageRef.key ≠
        (LatticePairStateWorkspaceLayout.cellRef state .targetSecond).toCStorageRef.key
    exact stateKey_ne state stateDistinct .targetFirst .targetSecond (by decide)
  · apply storage_read_not_mem
    change
      (LatticePairStateWorkspaceLayout.cellRef state .targetThird).toCStorageRef.key ≠
        (LatticePairStateWorkspaceLayout.cellRef state .targetFirst).toCStorageRef.key
    exact stateKey_ne state stateDistinct .targetThird .targetFirst (by decide)
  · apply storage_read_not_mem
    change
      (LatticePairStateWorkspaceLayout.cellRef state .targetThird).toCStorageRef.key ≠
        (LatticePairStateWorkspaceLayout.cellRef state .targetSecond).toCStorageRef.key
    exact stateKey_ne state stateDistinct .targetThird .targetSecond (by decide)

private theorem firstTargetSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width)
    (separation : FrameSeparation refs) :
    LatticeTarget.Separation refs.target.first := by
  refine {
    aAvoidsIsZero := ?_
    modulusAvoidsIsZero := ?_
    scratchAvoidsIsZero := ?_
    aAvoidsScratch := ?_
    modulusAvoidsScratch := ?_
    isZeroAvoidsScratch := ?_
    aAvoidsBelowHalf := ?_
    modulusAvoidsBelowHalf := ?_
    scratchAvoidsBelowHalf := ?_
    isZeroAvoidsBelowHalf := ?_
    aAvoidsOutput := ?_
    modulusAvoidsOutput := by
      rw [refs.firstModulus]
      exact separation.modulusAvoidsFirstOutput
    scratchAvoidsOutput := ?_
    isZeroAvoidsOutput := ?_
    belowHalfAvoidsOutput := ?_ }
  · rw [refs.firstInput]
    apply storage_read_not_mem
    change mutableKey refs .firstScaled ≠ mutableKey refs .firstIsZero
    exact separation.mutableKey_ne (by decide)
  · rw [refs.firstModulus]
    simpa only [externalSourceShape, externalSourceInput,
      mutableKey, mutableRef] using
      separation.externalAvoids .modulus .firstIsZero
  · apply storage_read_not_mem
    change mutableKey refs .firstScratch ≠ mutableKey refs .firstIsZero
    exact separation.mutableKey_ne (by decide)
  · rw [refs.firstInput]
    apply storage_read_not_mem
    change mutableKey refs .firstScaled ≠ mutableKey refs .firstScratch
    exact separation.mutableKey_ne (by decide)
  · rw [refs.firstModulus]
    simpa only [externalSourceShape, externalSourceInput,
      mutableKey, mutableRef] using
      separation.externalAvoids .modulus .firstScratch
  · apply storage_read_not_mem
    change mutableKey refs .firstIsZero ≠ mutableKey refs .firstScratch
    exact separation.mutableKey_ne (by decide)
  · rw [refs.firstInput]
    apply storage_read_not_mem
    change mutableKey refs .firstScaled ≠ mutableKey refs .firstBelowHalf
    exact separation.mutableKey_ne (by decide)
  · rw [refs.firstModulus]
    simpa only [externalSourceShape, externalSourceInput,
      mutableKey, mutableRef] using
      separation.externalAvoids .modulus .firstBelowHalf
  · apply storage_read_not_mem
    change mutableKey refs .firstScratch ≠ mutableKey refs .firstBelowHalf
    exact separation.mutableKey_ne (by decide)
  · apply storage_read_not_mem
    change mutableKey refs .firstIsZero ≠ mutableKey refs .firstBelowHalf
    exact separation.mutableKey_ne (by decide)
  · have avoided := separation.externalAvoids .firstOutput .firstScaled
    rw [refs.firstInput]
    have avoided := storage_read_key_ne avoided
    change refs.target.first.output.toCStorageRef.key ≠
      refs.first.scaled.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm
  · have avoided := separation.externalAvoids .firstOutput .firstScratch
    have avoided := storage_read_key_ne avoided
    change refs.target.first.output.toCStorageRef.key ≠
      refs.target.first.scratch.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm
  · have avoided := separation.externalAvoids .firstOutput .firstIsZero
    have avoided := storage_read_key_ne avoided
    change refs.target.first.output.toCStorageRef.key ≠
      refs.target.first.isZero.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm
  · have avoided := separation.externalAvoids .firstOutput .firstBelowHalf
    have avoided := storage_read_key_ne avoided
    change refs.target.first.output.toCStorageRef.key ≠
      refs.target.first.belowHalf.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm

private theorem secondTargetSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width)
    (separation : FrameSeparation refs) :
    LatticeTarget.Separation refs.target.second := by
  refine {
    aAvoidsIsZero := ?_
    modulusAvoidsIsZero := ?_
    scratchAvoidsIsZero := ?_
    aAvoidsScratch := ?_
    modulusAvoidsScratch := ?_
    isZeroAvoidsScratch := ?_
    aAvoidsBelowHalf := ?_
    modulusAvoidsBelowHalf := ?_
    scratchAvoidsBelowHalf := ?_
    isZeroAvoidsBelowHalf := ?_
    aAvoidsOutput := ?_
    modulusAvoidsOutput := by
      rw [refs.secondModulus]
      exact separation.modulusAvoidsSecondOutput
    scratchAvoidsOutput := ?_
    isZeroAvoidsOutput := ?_
    belowHalfAvoidsOutput := ?_ }
  · rw [refs.secondInput]
    apply storage_read_not_mem
    change mutableKey refs .secondScaled ≠ mutableKey refs .secondIsZero
    exact separation.mutableKey_ne (by decide)
  · rw [refs.secondModulus]
    simpa only [externalSourceShape, externalSourceInput,
      mutableKey, mutableRef] using
      separation.externalAvoids .modulus .secondIsZero
  · apply storage_read_not_mem
    change mutableKey refs .secondScratch ≠ mutableKey refs .secondIsZero
    exact separation.mutableKey_ne (by decide)
  · rw [refs.secondInput]
    apply storage_read_not_mem
    change mutableKey refs .secondScaled ≠ mutableKey refs .secondScratch
    exact separation.mutableKey_ne (by decide)
  · rw [refs.secondModulus]
    simpa only [externalSourceShape, externalSourceInput,
      mutableKey, mutableRef] using
      separation.externalAvoids .modulus .secondScratch
  · apply storage_read_not_mem
    change mutableKey refs .secondIsZero ≠ mutableKey refs .secondScratch
    exact separation.mutableKey_ne (by decide)
  · rw [refs.secondInput]
    apply storage_read_not_mem
    change mutableKey refs .secondScaled ≠ mutableKey refs .secondBelowHalf
    exact separation.mutableKey_ne (by decide)
  · rw [refs.secondModulus]
    simpa only [externalSourceShape, externalSourceInput,
      mutableKey, mutableRef] using
      separation.externalAvoids .modulus .secondBelowHalf
  · apply storage_read_not_mem
    change mutableKey refs .secondScratch ≠ mutableKey refs .secondBelowHalf
    exact separation.mutableKey_ne (by decide)
  · apply storage_read_not_mem
    change mutableKey refs .secondIsZero ≠ mutableKey refs .secondBelowHalf
    exact separation.mutableKey_ne (by decide)
  · have avoided := separation.externalAvoids .secondOutput .secondScaled
    rw [refs.secondInput]
    have avoided := storage_read_key_ne avoided
    change refs.target.second.output.toCStorageRef.key ≠
      refs.second.scaled.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm
  · have avoided := separation.externalAvoids .secondOutput .secondScratch
    have avoided := storage_read_key_ne avoided
    change refs.target.second.output.toCStorageRef.key ≠
      refs.target.second.scratch.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm
  · have avoided := separation.externalAvoids .secondOutput .secondIsZero
    have avoided := storage_read_key_ne avoided
    change refs.target.second.output.toCStorageRef.key ≠
      refs.target.second.isZero.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm
  · have avoided := separation.externalAvoids .secondOutput .secondBelowHalf
    have avoided := storage_read_key_ne avoided
    change refs.target.second.output.toCStorageRef.key ≠
      refs.target.second.belowHalf.toCStorageRef.key at avoided
    apply storage_read_not_mem
    exact avoided.symm

private theorem targetPointSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width)
    (separation : FrameSeparation refs) :
    LatticeTargetPoint.Separation refs.target := by
  refine {
    first := firstTargetSeparation refs separation
    second := secondTargetSeparation refs separation
    secondAAvoidsFirst := ?_
    secondModulusAvoidsFirst := ?_
    secondScratchAvoidsFirst := ?_
    secondIsZeroAvoidsFirst := ?_
    secondBelowHalfAvoidsFirst := ?_
    secondOutputAvoidsFirst := ?_
    firstOutputAvoidsSecond := ?_
    thirdAvoidsFirst := ?_
    thirdAvoidsSecond := ?_ }
  · rw [refs.secondInput]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply storage_read_not_mem
      change mutableKey refs .secondScaled ≠ mutableKey refs .firstScratch
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondScaled ≠ mutableKey refs .firstIsZero
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondScaled ≠ mutableKey refs .firstBelowHalf
      exact separation.mutableKey_ne (by decide)
    · have avoided := separation.externalAvoids .firstOutput .secondScaled
      have avoided := storage_read_key_ne avoided
      change refs.target.first.output.toCStorageRef.key ≠
        refs.second.scaled.toCStorageRef.key at avoided
      apply storage_read_not_mem
      exact avoided.symm
  · rw [refs.secondModulus]
    refine ⟨?_, ?_, ?_, separation.modulusAvoidsFirstOutput⟩
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .modulus .firstScratch
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .modulus .firstIsZero
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .modulus .firstBelowHalf
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply storage_read_not_mem
      change mutableKey refs .secondScratch ≠ mutableKey refs .firstScratch
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondScratch ≠ mutableKey refs .firstIsZero
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondScratch ≠ mutableKey refs .firstBelowHalf
      exact separation.mutableKey_ne (by decide)
    · have avoided := separation.externalAvoids .firstOutput .secondScratch
      have avoided := storage_read_key_ne avoided
      change refs.target.first.output.toCStorageRef.key ≠
        refs.target.second.scratch.toCStorageRef.key at avoided
      apply storage_read_not_mem
      exact avoided.symm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply storage_read_not_mem
      change mutableKey refs .secondIsZero ≠ mutableKey refs .firstScratch
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondIsZero ≠ mutableKey refs .firstIsZero
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondIsZero ≠ mutableKey refs .firstBelowHalf
      exact separation.mutableKey_ne (by decide)
    · have avoided := separation.externalAvoids .firstOutput .secondIsZero
      have avoided := storage_read_key_ne avoided
      change refs.target.first.output.toCStorageRef.key ≠
        refs.target.second.isZero.toCStorageRef.key at avoided
      apply storage_read_not_mem
      exact avoided.symm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply storage_read_not_mem
      change mutableKey refs .secondBelowHalf ≠ mutableKey refs .firstScratch
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondBelowHalf ≠ mutableKey refs .firstIsZero
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondBelowHalf ≠ mutableKey refs .firstBelowHalf
      exact separation.mutableKey_ne (by decide)
    · have avoided := separation.externalAvoids .firstOutput .secondBelowHalf
      have avoided := storage_read_key_ne avoided
      change refs.target.first.output.toCStorageRef.key ≠
        refs.target.second.belowHalf.toCStorageRef.key at avoided
      apply storage_read_not_mem
      exact avoided.symm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .secondOutput .firstScratch
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .secondOutput .firstIsZero
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .secondOutput .firstBelowHalf
    · apply storage_read_not_mem
      exact (storage_read_key_ne separation.firstOutputAvoidsSecondOutput).symm
  · refine ⟨?_, ?_, ?_, separation.firstOutputAvoidsSecondOutput⟩
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .firstOutput .secondScratch
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .firstOutput .secondIsZero
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .firstOutput .secondBelowHalf
  · refine ⟨?_, ?_, ?_, separation.thirdAvoidsFirstOutput⟩
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .firstScratch
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .firstIsZero
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .firstBelowHalf
  · refine ⟨?_, ?_, ?_, separation.thirdAvoidsSecondOutput⟩
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .secondScratch
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .secondIsZero
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .secondBelowHalf

/-- Physical target storage supplies the full wide-target separation package. -/
theorem targetSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : LatticeWideTargetMachine.Refs ctx m ell width)
    (separation : FrameSeparation refs) :
    LatticeWideTargetMachine.Separation refs := by
  refine {
    target := targetPointSeparation refs separation
    secondKAvoidsFirst := ?_
    firstScaledAvoidsSecond := ?_
    modulusAvoidsPreimages := ?_
    firstScratchAvoidsPreimages := ?_
    secondScratchAvoidsPreimages := ?_
    thirdAvoidsPreimages := ?_ }
  · simpa only [externalSourceShape, externalSourceInput,
      mutableKey, mutableRef] using
      separation.externalAvoids .secondK .firstScaled
  · apply storage_read_not_mem
    change mutableKey refs .firstScaled ≠ mutableKey refs .secondScaled
    exact separation.mutableKey_ne (by decide)
  · refine ⟨?_, ?_⟩
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .modulus .firstScaled
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .modulus .secondScaled
  · constructor
    · apply storage_read_not_mem
      change mutableKey refs .firstScratch ≠ mutableKey refs .firstScaled
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .firstScratch ≠ mutableKey refs .secondScaled
      exact separation.mutableKey_ne (by decide)
  · constructor
    · apply storage_read_not_mem
      change mutableKey refs .secondScratch ≠ mutableKey refs .firstScaled
      exact separation.mutableKey_ne (by decide)
    · apply storage_read_not_mem
      change mutableKey refs .secondScratch ≠ mutableKey refs .secondScaled
      exact separation.mutableKey_ne (by decide)
  · refine ⟨?_, ?_⟩
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .firstScaled
    · simpa only [externalSourceShape, externalSourceInput,
        mutableKey, mutableRef] using
        separation.externalAvoids .third .secondScaled

end

end LatticeWideTargetWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
