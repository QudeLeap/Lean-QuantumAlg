/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Scale
import all QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Program.Resources

/-!
# Actual short-log target loading at the original source width

The original `ell + m + 1` target layout specializes the verified common-width
loader without duplicating its arithmetic. All original physical references
and role witnesses are retained, and no scratch initialization premise remains.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The decoded raw `k` word agrees with one pure short-log sample. -/
def SampleKRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}
    (store : Store ctx) (k : CInputRef ctx (.unsignedWord ell))
    (sample : RSA.ShortLogSample m ell) : Prop :=
  (store.read k).toNat = sample.2.val

/-- Caller-owned raw cells for two preimages and their centered target point. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (m ell : Nat) where
  /-- References used to prepare the first scaled preimage. -/
  first : LatticeTargetPreimage.Refs ctx m ell
  /-- References used to prepare the second scaled preimage. -/
  second : LatticeTargetPreimage.Refs ctx m ell
  /-- References used to center the two prepared coordinates. -/
  target : LatticeTargetPoint.Refs ctx (ell + m + 1)
  /-- Shared unsigned modulus read by both centering routines. -/
  modulus : CInputRef ctx (.unsignedWord (ell + m + 1))
  firstInput : target.first.a = LatticeTargetPreimage.writeInput first.scaled
  secondInput : target.second.a = LatticeTargetPreimage.writeInput second.scaled
  firstModulus : target.first.modulus = modulus
  secondModulus : target.second.modulus = modulus

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {m ell : Nat}

/-- The original narrow target layout has the exact common-width view of the same physical cells. -/
def wideRefs (refs : Refs ctx m ell) : LatticeWideTargetMachine.Refs ctx m ell (ell + m + 1) where
  first := ⟨refs.first.k, refs.first.scaled, refs.first.scaledWritable⟩
  second := ⟨refs.second.k, refs.second.scaled, refs.second.scaledWritable⟩
  target := refs.target
  modulus := refs.modulus
  firstInput := refs.firstInput
  secondInput := refs.secondInput
  firstModulus := refs.firstModulus
  secondModulus := refs.secondModulus

/-- Structural avoidance of the two original actual preimage writes. -/
abbrev AvoidsPreimageWrites {shape : CShape} (input : CInputRef ctx shape) (refs : Refs ctx m ell) :
    Prop := LatticeWideTargetMachine.AvoidsPreimageWrites input (wideRefs refs)

/-- The original source-width target needs precisely the common-width actual separation facts. -/
abbrev Separation (refs : Refs ctx m ell) : Prop :=
  LatticeWideTargetMachine.Separation (wideRefs refs)

/-- Actual original-width preimage loading and stored-comparison target centering. -/
def loadTargetMachineInto (refs : Refs ctx m ell) : Circuit model ctx ctx :=
  LatticeWideTargetMachine.loadTargetInto (wideRefs refs)

/-- Complete actual store and chronological native path of the original-width target call. -/
def targetMachineStep (refs : Refs ctx m ell) (store : Store ctx) :
    Store ctx × (loadTargetMachineInto refs).Path :=
  LatticeWideTargetMachine.targetStep (wideRefs refs) store

/-- Actual original-width target loading retains every original state block and incoming history. -/
theorem loadTargetMachineInto_execute (refs : Refs ctx m ell) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (loadTargetMachineInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((targetMachineStep refs entry.1).1,
        (entry.2.1, (entry.2.2, (targetMachineStep refs entry.1).2)))) :=
  LatticeWideTargetMachine.loadTargetInto_execute (wideRefs refs) Reference state

/-- Exact original pure target and complete actual caller frame of the original-width layout. -/
abbrev TargetMachineOutcome (refs : Refs ctx m ell)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (before after : Store ctx) : Prop :=
  LatticeWideTargetMachine.TargetOutcome (wideRefs refs) samples before after

/-- Actual source-width scaling and centering produce the original sample lattice target. -/
theorem loadTargetMachineInto_correct (refs : Refs ctx m ell) (separation : Separation refs)
    (store : Store ctx) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (first : SampleKRepresents store refs.first.k samples.1)
    (second : SampleKRepresents store refs.second.k samples.2)
    (modulus : (store.read refs.modulus).toNat = 2 ^ (ell + m))
    (thirdZero : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.target.point.third)) 0) :
    TargetMachineOutcome refs samples store (targetMachineStep refs store).1 :=
  LatticeWideTargetMachine.loadTargetInto_correct (wideRefs refs) separation store samples
    le_rfl first second modulus thirdZero

/-- Actual original-width target loading retains every read outside its original ten write cells. -/
theorem loadTargetMachineInto_callerFrame (refs : Refs ctx m ell) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (preimages : AvoidsPreimageWrites other refs)
    (first : LatticeTargetPoint.AvoidsTargetWrites other refs.target.first)
    (second : LatticeTargetPoint.AvoidsTargetWrites other refs.target.second) :
    (targetMachineStep refs store).1.read other = store.read other :=
  LatticeWideTargetMachine.loadTargetInto_callerFrame (wideRefs refs) store other
    preimages first second

/-- The original-width path emits the independent native formula for its selected arithmetic. -/
theorem loadTargetMachineInto_events (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) :
    (loadTargetMachineInto refs).eventTrace path =
      LatticeWideTargetMachine.targetTrace m ell (ell + m + 1)
        (LatticeTarget.selectedNegation refs.target.first path.2.1.2)
        (LatticeTarget.selectedNegation refs.target.second path.2.2.2) :=
  LatticeWideTargetMachine.loadTargetInto_events (wideRefs refs) path

/-- Actual original-width native multiplicities equal the independently selected target formula. -/
theorem loadTargetMachineInto_resourcePool (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) :
    (loadTargetMachineInto refs).resourcePool path = ResourcePool.ofList
      (LatticeWideTargetMachine.targetTrace m ell (ell + m + 1)
        (LatticeTarget.selectedNegation refs.target.first path.2.1.2)
        (LatticeTarget.selectedNegation refs.target.second path.2.2.2)) :=
  congrArg ResourcePool.ofList (loadTargetMachineInto_events refs path)

/-- Independent coordinate envelope at the original target width. -/
def targetMachineEventEnvelope (m ell : Nat) : ResourcePool model :=
  LatticeWideTargetMachine.eventEnvelope m ell (ell + m + 1)

/-- The actual original-width target obeys its complete independent coordinate envelope. -/
theorem loadTargetMachineInto_resourcePool_le (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) :
    (loadTargetMachineInto refs).resourcePool path ≤ targetMachineEventEnvelope m ell :=
  LatticeWideTargetMachine.loadTargetInto_resourcePool_le (wideRefs refs) path

/-- The actual source-width target uses at most two shifts per bit and sixteen other operations. -/
theorem loadTargetMachineInto_eventCount_le (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) :
    ((loadTargetMachineInto refs).eventTrace path).length ≤ 2 * m + 16 :=
  LatticeWideTargetMachine.loadTargetInto_eventCount_le (wideRefs refs) path

/-- Actual original-width depth includes both preimages and both selected centered coordinates. -/
theorem loadTargetMachineInto_depth_le (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) :
    (loadTargetMachineInto refs).depth (fun _ => 1) path ≤ 2 * m + 16 :=
  LatticeWideTargetMachine.loadTargetInto_depth_le (wideRefs refs) path

/-- Actual original-width target loading preserves all original borrowed-reference correlations. -/
theorem loadTargetMachineInto_borrowedRestored (refs : Refs ctx m ell) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (loadTargetMachineInto refs).BorrowedRestored Reference state
      ((loadTargetMachineInto refs).execute Reference state) :=
  LatticeWideTargetMachine.loadTargetInto_borrowedRestored (wideRefs refs) Reference state

/-- Every actual original-width target instruction retains the complete supplied context. -/
theorem loadTargetMachineInto_visited (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (loadTargetMachineInto refs).visitedContexts path) : visited = ctx :=
  LatticeWideTargetMachine.loadTargetInto_visited (wideRefs refs) path visited present

/-- Actual original-width resident accounting retains every supplied runtime entry. -/
theorem loadTargetMachineInto_resident_le (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) :
    (loadTargetMachineInto refs).peakResidentSpace path ≤ ctx.residentSpace :=
  LatticeWideTargetMachine.loadTargetInto_resident_le (wideRefs refs) path

/-- Actual original-width auxiliary accounting retains every original workspace role. -/
theorem loadTargetMachineInto_auxiliary_le (refs : Refs ctx m ell)
    (path : (loadTargetMachineInto refs).Path) :
    (loadTargetMachineInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  LatticeWideTargetMachine.loadTargetInto_auxiliary_le (wideRefs refs) path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetMachine
