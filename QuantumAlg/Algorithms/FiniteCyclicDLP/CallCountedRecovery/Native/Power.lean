/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Model
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Actual declared group-power scan

Each original MSB tail position executes the declared square, then reads its
stored candidate bit to select the declared generator multiplication. Both
calls use the original common encoder and declaration-owned labels. A fresh
accumulator scope remains live through its caller continuation.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace

noncomputable section

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

/-- Read the actual accumulator storage used by both declared calls. -/
def powerRead (accumulator : CWriteRef ctx (.unsignedWord width)) :
    CInputRef ctx (.unsignedWord width) :=
  .storage accumulator.toCStorageRef

/-- The original sealed square is placed at the actual accumulator. -/
def squareDeclaration (A : Access G width)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained) :
    DeclaredClassicalCall ctx (.unsignedWord width) (.unsignedWord width) :=
  DeclaredClassicalCall.place
    (A.groupPowerAccess.sealedSquareAccess A.squareLabel id id)
    (powerRead accumulator) accumulator writable

/-- Generator multiplication captures the original mathematical generator in its declaration. -/
def multiplyDeclaration (A : Access G width) (generator : G)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained) :
    DeclaredClassicalCall ctx (.unsignedWord width) (.unsignedWord width) :=
  DeclaredClassicalCall.place (A.sealedMultiplyGeneratorAccess generator)
    (powerRead accumulator) accumulator writable

/-- One actual square call emits its declaration-owned classical subroutine event. -/
def squareCall (A : Access G width) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained) :
    Circuit ctx ctx :=
  .declaredCall (squareDeclaration A accumulator writable)

/-- One actual multiplication emits the original distinct multiplication event. -/
def multiplyCall (A : Access G width) (generator : G)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained) :
    Circuit ctx ctx :=
  .declaredCall (multiplyDeclaration A generator accumulator writable)

/-- The stored Boolean selects the real multiplication or the unchanged context. -/
def powerChoice (A : Access G width) (generator : G)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained)
    (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then multiplyCall A generator accumulator writable else .id ctx

/-- Each original position squares before reading its candidate bit and choosing multiplication. -/
def powerStep (A : Access G width) (generator : G) (bit : CInputRef ctx .bit)
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained) :
    Circuit ctx ctx :=
  .seq (squareCall A accumulator writable)
    (.branch bit (powerChoice A generator accumulator writable))

/-- Traverse the supplied original bit positions in increasing finite-index order. -/
def powerRange (A : Access G width) (generator : G) (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained) :
    Circuit ctx ctx :=
  Circuit.forRange count fun index => powerStep A generator (bits index) accumulator writable

/-- Read precisely the original word positions after its omitted leading MSB. -/
def powerScan (A : Access G width) (generator : G)
    (candidate : CInputRef ctx (.unsignedWord width))
    (accumulator : CWriteRef ctx (.unsignedWord width))
    (writable : accumulator.role = .workspace ∨ accumulator.role = .retained) :
    Circuit ctx ctx :=
  powerRange A generator (width - 1)
    (fun index => .wordBitGet candidate (tailIndex width index)) accumulator writable

/-- The original fresh word remains live through its caller, then its lexical scope ends. -/
def withPowerAccumulator (A : Access G width) (generator : G)
    (candidate : CInputRef ctx (.unsignedWord width))
    (body : ∀ {inner : RuntimeCtx .quantum}, CInputRef inner (.unsignedWord width) →
      Transport ctx inner → Circuit inner inner) : Circuit ctx ctx :=
  withCells ctx [.unsignedWord width] fun cells _ transport _ =>
    let cell := cells.head
    .seq (powerScan A generator (transport.liftInput candidate) cell.ref (Or.inl cell.role))
      (body (powerRead cell.ref) transport)

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
