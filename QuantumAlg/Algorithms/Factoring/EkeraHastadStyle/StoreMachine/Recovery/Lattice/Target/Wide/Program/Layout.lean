/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Point.Resources
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Scale.Resources

/-!
# Original wide target cells and actual structural separation

The original common-width cells host both scaled sample coordinates and the
centered target. Structural disjointness refers directly to actual store keys.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- Read one writable raw cell through the common lattice input language. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Caller-owned cells for one wide no-wrap preimage `2^m * k`. -/
structure PreimageRefs {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (m ell width : Nat) where
  /-- Input reference for the k value. -/
  k : CInputRef ctx (.unsignedWord ell)
  /-- Writable cell for the scaled value. -/
  scaled : CWriteRef ctx (.unsignedWord width)
  scaledWritable : scaled.toCStorageRef.role = .workspace ∨
    scaled.toCStorageRef.role = .retained

/-- The original sample component is represented by the actual supplied source word. -/
def SampleKRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell : Nat} (store : Store ctx)
    (k : CInputRef ctx (.unsignedWord ell))
    (sample : RSA.ShortLogSample m ell) : Prop :=
  (store.read k).toNat = sample.2.val

/-- Caller-owned data for two wide preimages and one centered target point. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (m ell width : Nat) where
  /-- Nested references for the first stage. -/
  first : PreimageRefs ctx m ell width
  /-- Nested references for the second stage. -/
  second : PreimageRefs ctx m ell width
  /-- Nested references for the target stage. -/
  target : LatticeTargetPoint.Refs ctx width
  /-- Input reference for the modulus value. -/
  modulus : CInputRef ctx (.unsignedWord width)
  firstInput : target.first.a = writeInput first.scaled
  secondInput : target.second.a = writeInput second.scaled
  firstModulus : target.first.modulus = modulus
  secondModulus : target.second.modulus = modulus

/-- An input avoids both preimage cells written before target centering. -/
def AvoidsPreimageWrites {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} {shape : CShape} (input : CInputRef ctx shape)
    (refs : Refs ctx m ell width) : Prop :=
  refs.first.scaled.key ∉ input.storageKeys ∧
    refs.second.scaled.key ∉ input.storageKeys

/-- Cross-call separation for the two preimages and centered target loader. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} (refs : Refs ctx m ell width) : Prop where
  target : LatticeTargetPoint.Separation refs.target
  secondKAvoidsFirst : refs.first.scaled.key ∉ refs.second.k.storageKeys
  firstScaledAvoidsSecond :
    refs.second.scaled.key ∉ (writeInput refs.first.scaled).storageKeys
  modulusAvoidsPreimages : AvoidsPreimageWrites refs.modulus refs
  firstScratchAvoidsPreimages :
    AvoidsPreimageWrites (LatticeTarget.writeInput refs.target.first.scratch) refs
  secondScratchAvoidsPreimages :
    AvoidsPreimageWrites (LatticeTarget.writeInput refs.target.second.scratch) refs
  thirdAvoidsPreimages :
    AvoidsPreimageWrites (LatticeState.coordinateInput refs.target.point.third) refs

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine
