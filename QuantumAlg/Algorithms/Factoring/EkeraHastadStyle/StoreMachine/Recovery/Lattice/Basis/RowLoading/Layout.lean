/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program.Layout
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources

/-!
# Original actual raw lattice-loading allocation

The original twelve writable word identities and their roles remain explicit.
First-row loading reads both original decoded sample words and writes only its
three original destinations, with structural separation at the real store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- Read the actual caller-owned word named by one writable reference. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- The twelve independently writable raw cells of a three-row basis and target. -/
structure RawOutputRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Writable cell for the b 11 value. -/
  b11 : CWriteRef ctx (.unsignedWord width)
  b11Writable : b11.toCStorageRef.role = .workspace ∨
    b11.toCStorageRef.role = .retained
  /-- Writable cell for the b 12 value. -/
  b12 : CWriteRef ctx (.unsignedWord width)
  b12Writable : b12.toCStorageRef.role = .workspace ∨
    b12.toCStorageRef.role = .retained
  /-- Writable cell for the b 13 value. -/
  b13 : CWriteRef ctx (.unsignedWord width)
  b13Writable : b13.toCStorageRef.role = .workspace ∨
    b13.toCStorageRef.role = .retained
  /-- Writable cell for the b 21 value. -/
  b21 : CWriteRef ctx (.unsignedWord width)
  b21Writable : b21.toCStorageRef.role = .workspace ∨
    b21.toCStorageRef.role = .retained
  /-- Writable cell for the b 22 value. -/
  b22 : CWriteRef ctx (.unsignedWord width)
  b22Writable : b22.toCStorageRef.role = .workspace ∨
    b22.toCStorageRef.role = .retained
  /-- Writable cell for the b 23 value. -/
  b23 : CWriteRef ctx (.unsignedWord width)
  b23Writable : b23.toCStorageRef.role = .workspace ∨
    b23.toCStorageRef.role = .retained
  /-- Writable cell for the b 31 value. -/
  b31 : CWriteRef ctx (.unsignedWord width)
  b31Writable : b31.toCStorageRef.role = .workspace ∨
    b31.toCStorageRef.role = .retained
  /-- Writable cell for the b 32 value. -/
  b32 : CWriteRef ctx (.unsignedWord width)
  b32Writable : b32.toCStorageRef.role = .workspace ∨
    b32.toCStorageRef.role = .retained
  /-- Writable cell for the b 33 value. -/
  b33 : CWriteRef ctx (.unsignedWord width)
  b33Writable : b33.toCStorageRef.role = .workspace ∨
    b33.toCStorageRef.role = .retained
  /-- Writable cell for the t 1 value. -/
  t1 : CWriteRef ctx (.unsignedWord width)
  t1Writable : t1.toCStorageRef.role = .workspace ∨
    t1.toCStorageRef.role = .retained
  /-- Writable cell for the t 2 value. -/
  t2 : CWriteRef ctx (.unsignedWord width)
  t2Writable : t2.toCStorageRef.role = .workspace ∨
    t2.toCStorageRef.role = .retained
  /-- Writable cell for the t 3 value. -/
  t3 : CWriteRef ctx (.unsignedWord width)
  t3Writable : t3.toCStorageRef.role = .workspace ∨
    t3.toCStorageRef.role = .retained

/-- The original first-row source/write exclusions and distinct destination identities. -/
structure FirstBasisRowSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N width : Nat} (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) : Prop where
  firstJAvoidsB11 : output.b11.key ≠ pair.first.j.key
  firstJAvoidsB12 : output.b12.key ≠ pair.first.j.key
  firstJAvoidsB13 : output.b13.key ≠ pair.first.j.key
  secondJAvoidsB11 : output.b11.key ≠ pair.second.j.key
  secondJAvoidsB12 : output.b12.key ≠ pair.second.j.key
  secondJAvoidsB13 : output.b13.key ≠ pair.second.j.key
  b11AvoidsB12 : output.b12.key ≠ output.b11.key
  b11AvoidsB13 : output.b13.key ≠ output.b11.key
  b12AvoidsB13 : output.b13.key ≠ output.b12.key

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading
