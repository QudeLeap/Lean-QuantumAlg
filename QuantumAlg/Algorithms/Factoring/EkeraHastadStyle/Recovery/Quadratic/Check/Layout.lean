/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Pair
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Five actual lexical cells for the two quadratic validity checks

One real zero word and four real Boolean cells support both complete checks.
The old center and root are supplied as the actual one and remainder cells
once both candidate words have been materialized. Upper comparison and
remainder-equality scratch bits are reused between the checks; both final
validity bits coexist until the original left-priority selection consumes them.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout

open ClassicalRoutines

variable {kind : ProblemKind}

/-- Actual existing operands, reusable arithmetic cell and the local first-factor latches. -/
structure Operands (ctx : RuntimeCtx kind) (width : Nat) where
  modulus : CInputRef ctx (.unsignedWord width)
  one : CInputRef ctx (.unsignedWord width)
  remainder : CWriteRef ctx (.unsignedWord width)
  first : CInputRef ctx (.unsignedWord width)
  second : CInputRef ctx (.unsignedWord width)
  selection : FirstAccepted.Refs ctx width

/-- The actual fresh zero workspace entry. -/
def zeroCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The actual fresh upper workspace entry. -/
def upperCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (zeroCtx ctx width).addWorkspace (zeroCtx ctx width).canonicalFreshKey
    .bit (zeroCtx ctx width).canonicalFreshKey_fresh

/-- The actual fresh divides workspace entry. -/
def dividesCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (upperCtx ctx width).addWorkspace (upperCtx ctx width).canonicalFreshKey
    .bit (upperCtx ctx width).canonicalFreshKey_fresh

/-- The actual fresh firstValid workspace entry. -/
def firstCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (dividesCtx ctx width).addWorkspace (dividesCtx ctx width).canonicalFreshKey
    .bit (dividesCtx ctx width).canonicalFreshKey_fresh

/-- The actual fresh secondValid workspace entry. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (firstCtx ctx width).addWorkspace (firstCtx ctx width).canonicalFreshKey
    .bit (firstCtx ctx width).canonicalFreshKey_fresh

/-- The actual zero cell at its intrinsic position in the final workspace. -/
def zero (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) where
  key := ctx.canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there .here)))
  writable := by decide

/-- The actual upper cell at its intrinsic position in the final workspace. -/
def upper (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (zeroCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there .here))
  writable := by decide

/-- The actual divides cell at its intrinsic position in the final workspace. -/
def divides (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (upperCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there .here)
  writable := by decide

/-- The actual firstValid cell at its intrinsic position in the final workspace. -/
def firstValid (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (dividesCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there .here
  writable := by decide

/-- The actual secondValid cell at its intrinsic position in the final workspace. -/
def secondValid (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (firstCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .here
  writable := by decide

/-- Lift the same physical read through all five actual workspace entries. -/
def underRead {ctx : RuntimeCtx kind} {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) : CInputRef (context ctx width) shape :=
  let ref1 : CInputRef (zeroCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (upperCtx ctx width) shape :=
    ref1.underWorkspace (zeroCtx ctx width).canonicalFreshKey
      .bit (zeroCtx ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (dividesCtx ctx width) shape :=
    ref2.underWorkspace (upperCtx ctx width).canonicalFreshKey
      .bit (upperCtx ctx width).canonicalFreshKey_fresh
  let ref4 : CInputRef (firstCtx ctx width) shape :=
    ref3.underWorkspace (dividesCtx ctx width).canonicalFreshKey
      .bit (dividesCtx ctx width).canonicalFreshKey_fresh
  ref4.underWorkspace (firstCtx ctx width).canonicalFreshKey
    .bit (firstCtx ctx width).canonicalFreshKey_fresh

/-- Lift the same physical write through all five actual workspace entries. -/
def underWrite {ctx : RuntimeCtx kind} {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) : CWriteRef (context ctx width) shape :=
  let ref1 : CWriteRef (zeroCtx ctx width) shape :=
    output.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let ref2 : CWriteRef (upperCtx ctx width) shape :=
    ref1.underWorkspace (zeroCtx ctx width).canonicalFreshKey
      .bit (zeroCtx ctx width).canonicalFreshKey_fresh
  let ref3 : CWriteRef (dividesCtx ctx width) shape :=
    ref2.underWorkspace (upperCtx ctx width).canonicalFreshKey
      .bit (upperCtx ctx width).canonicalFreshKey_fresh
  let ref4 : CWriteRef (firstCtx ctx width) shape :=
    ref3.underWorkspace (dividesCtx ctx width).canonicalFreshKey
      .bit (dividesCtx ctx width).canonicalFreshKey_fresh
  ref4.underWorkspace (firstCtx ctx width).canonicalFreshKey
    .bit (firstCtx ctx width).canonicalFreshKey_fresh

/-- Shared selector latches remain their original cells below all five check entries. -/
def selectorRefs {ctx : RuntimeCtx kind} {width : Nat} (refs : FirstAccepted.Refs ctx width) :
    FirstAccepted.Refs (context ctx width) width where
  accepted := underWrite refs.accepted width
  selected := underWrite refs.selected width
  available := underWrite refs.available width
  take := underWrite refs.take width

/-- Both checks use the same actual scratch cells and distinct persistent validity cells. -/
def pairRefs {ctx : RuntimeCtx kind} {width : Nat} (inputs : Operands ctx width) :
    Pair.Refs (context ctx width) width where
  first := {
    divisor := {
      modulus := underRead inputs.modulus width
      candidate := underRead inputs.first width
      zero := .storage (zero ctx width).toCStorageRef
      remainder := underWrite inputs.remainder width
      divides := divides ctx width
      valid := firstValid ctx width }
    one := underRead inputs.one width
    upper := upper ctx width }
  second := {
    divisor := {
      modulus := underRead inputs.modulus width
      candidate := underRead inputs.second width
      zero := .storage (zero ctx width).toCStorageRef
      remainder := underWrite inputs.remainder width
      divides := divides ctx width
      valid := secondValid ctx width }
    one := underRead inputs.one width
    upper := upper ctx width }
  selection := selectorRefs inputs.selection

/-- The five actual new cells in their final intrinsic stack order. -/
def internalKeys (ctx : RuntimeCtx kind) (width : Nat) : List StorageKey :=
  [(secondValid ctx width).key, (firstValid ctx width).key, (divides ctx width).key,
    (upper ctx width).key, (zero ctx width).key]

/-- No other entry is introduced by this actual check layout. -/
theorem nativeQuadratic_checkLayout_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).keys = internalKeys ctx width ++ ctx.keys := rfl

/-- Intrinsic context uniqueness makes all five actual workspace cells distinct. -/
theorem nativeQuadratic_checkLayout_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    (internalKeys ctx width).Nodup := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeQuadratic_checkLayout_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- Every actual new cell is outside all original operand and selector storage. -/
theorem nativeQuadratic_checkLayout_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint (internalKeys ctx width) ctx.keys := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeQuadratic_checkLayout_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- These five actual allocations retain precisely the same physical quantum systems. -/
theorem nativeQuadratic_checkLayout_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := rfl

/-- Actual five-cell allocation encloses both checks and consumes their bits before release. -/
def scopes (ctx : RuntimeCtx kind) (width : Nat)
    (inner : Circuit (context ctx width) (context ctx width)) : Circuit ctx ctx :=
  let lastScope := Circuit.workspace (firstCtx ctx width) (firstCtx ctx width).canonicalFreshKey
    .bit (firstCtx ctx width).canonicalFreshKey_fresh inner
  let firstScope := Circuit.workspace (dividesCtx ctx width)
    (dividesCtx ctx width).canonicalFreshKey .bit
    (dividesCtx ctx width).canonicalFreshKey_fresh lastScope
  let dividesScope := Circuit.workspace (upperCtx ctx width)
    (upperCtx ctx width).canonicalFreshKey .bit
    (upperCtx ctx width).canonicalFreshKey_fresh firstScope
  let upperScope := Circuit.workspace (zeroCtx ctx width)
    (zeroCtx ctx width).canonicalFreshKey .bit
    (zeroCtx ctx width).canonicalFreshKey_fresh dividesScope
  Circuit.workspace ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh upperScope

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout
