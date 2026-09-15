/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Row.Layout

/-!
# Actual nine-word basis and three-word target layout

Four real three-coordinate scopes hold the three basis rows followed by the
target. Every coordinate is its own native writable word. The original
sample references and persistent result cells remain in the enclosing
context, and all twelve temporary coordinates are released after the pair
recovery computation. No new quantum system is introduced by this layout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout

open Execution

variable {kind : ProblemKind}

private def context1 (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  RowLayout.context ctx width

private def context2 (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  RowLayout.context (context1 ctx width) width

private def context3 (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  RowLayout.context (context2 ctx width) width

/-- Twelve actual native words contain the basis rows and target, in that allocation order. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  RowLayout.context (context3 ctx width) width

private def liftRow {ctx : RuntimeCtx kind} {width : Nat} (refs : FirstRow.Refs ctx width) :
    FirstRow.Refs (RowLayout.context ctx width) width where
  first := RowLayout.underWrite refs.first width
  second := RowLayout.underWrite refs.second width
  third := RowLayout.underWrite refs.third width

/-- The first basis row is the oldest three actual cells beneath the other rows and target. -/
def firstRow (ctx : RuntimeCtx kind) (width : Nat) : FirstRow.Refs (context ctx width) width :=
  liftRow (liftRow (liftRow (RowLayout.refs ctx width)))

/-- The second basis row keeps its actual positions below the third row and target. -/
def secondRow (ctx : RuntimeCtx kind) (width : Nat) : FirstRow.Refs (context ctx width) width :=
  liftRow (liftRow (RowLayout.refs (context1 ctx width) width))

/-- The third basis row is the existing three-cell row immediately below the target. -/
def thirdRow (ctx : RuntimeCtx kind) (width : Nat) : FirstRow.Refs (context ctx width) width :=
  liftRow (RowLayout.refs (context2 ctx width) width)

/-- The target is the newest actual three-coordinate row. -/
def target (ctx : RuntimeCtx kind) (width : Nat) : FirstRow.Refs (context ctx width) width :=
  RowLayout.refs (context3 ctx width) width

/-- Structural input references preserve their actual identities beneath the twelve cells. -/
def underRead {ctx : RuntimeCtx kind} {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) : CInputRef (context ctx width) shape :=
  RowLayout.underRead (RowLayout.underRead
    (RowLayout.underRead (RowLayout.underRead input width) width) width) width

/-- Persistent writable references remain the same actual enclosing cells. -/
def underWrite {ctx : RuntimeCtx kind} {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) : CWriteRef (context ctx width) shape :=
  RowLayout.underWrite (RowLayout.underWrite
    (RowLayout.underWrite (RowLayout.underWrite output width) width) width) width

/-- Entry initializes precisely the twelve basis and target words through their actual scopes. -/
def pushStore {ctx : RuntimeCtx kind} (width : Nat) (store : Store ctx) :
    Store (context ctx width) :=
  RowLayout.pushStore width (RowLayout.pushStore width
    (RowLayout.pushStore width (RowLayout.pushStore width store)))

/-- Release removes the target, third, second and first rows in the reverse actual order. -/
def popStore {ctx : RuntimeCtx kind} (width : Nat) (store : Store (context ctx width)) :
    Store ctx :=
  RowLayout.popStore width (RowLayout.popStore width
    (RowLayout.popStore width (RowLayout.popStore width store)))

/-- The actual twelve lexical constructors supply and release the complete pair work layout. -/
def scopes (ctx : RuntimeCtx kind) (width : Nat)
    (body : Circuit (context ctx width) (context ctx width)) : Circuit ctx ctx :=
  RowLayout.scopes ctx width (RowLayout.scopes (context1 ctx width) width
    (RowLayout.scopes (context2 ctx width) width
      (RowLayout.scopes (context3 ctx width) width body)))

/-- The complete original quantum bank retains the same physical systems throughout entry. -/
theorem nativeLattice_basis_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires :=
  (RowLayout.nativeLattice_row_quantumWires (context3 ctx width) width).trans
    ((RowLayout.nativeLattice_row_quantumWires (context2 ctx width) width).trans
      ((RowLayout.nativeLattice_row_quantumWires (context1 ctx width) width).trans
        (RowLayout.nativeLattice_row_quantumWires ctx width)))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout
