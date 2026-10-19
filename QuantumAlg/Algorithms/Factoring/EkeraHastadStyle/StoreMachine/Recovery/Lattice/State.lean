/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Util.Classical.NumberTheory.Basic
import all QuantumAlg.Util.RSA.ShortLog.Widths

/-!
# Fixed-width Ekerå–Håstad lattice state

This module fixes the nominal storage representation of the exact
three-dimensional short-log lattice input.  It contains no reduction routine,
candidate search, resource account, or executable recovery claim.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeState

noncomputable section

/-! ## Closed shapes and pure values -/

/-- Generic raw two's-complement shape used by the executable lattice cells. -/
abbrev RawSignedWordShape (width : Nat) : CShape :=
  .unsignedWord width

/-- Generic right-nested three-dimensional raw signed point. -/
abbrev RawPointShape (width : Nat) : CShape :=
  .product (RawSignedWordShape width)
    (.product (RawSignedWordShape width) (RawSignedWordShape width))

/-- Generic ordered three-row raw signed basis. -/
abbrev RawBasisShape (width : Nat) : CShape :=
  .fixedVector 3 (RawPointShape width)

/-- Interpret one raw word as a two's-complement integer. -/
def decodeRawCoordinate {width : Nat}
    (encoded : CShape.Value (RawSignedWordShape width)) : Int :=
  (ClassicalAlgorithms.NumberTheory.BoundedSigned.decode
    (ClassicalRoutines.decodeWord encoded)).toInt

/-- Interpret one right-nested raw point. -/
def decodeRawPoint {width : Nat}
    (encoded : CShape.Value (RawPointShape width)) :
    NumberTheory.IntegerPoint3 :=
  (decodeRawCoordinate encoded.first,
    decodeRawCoordinate encoded.second.first,
    decodeRawCoordinate encoded.second.second)

/-- Interpret one fixed-vector raw basis. -/
def decodeRawBasis {width : Nat}
    (encoded : CShape.Value (RawBasisShape width)) :
    NumberTheory.IntegerBasis3 :=
  match encoded with
  | .fixedVector entries =>
      { first := decodeRawPoint (entries 0)
        second := decodeRawPoint (entries 1)
        third := decodeRawPoint (entries 2) }

/-- Nominal shape of one signed lattice coordinate. -/
abbrev SignedWordShape (N m ell : Nat) : CShape :=
  RawSignedWordShape (RSA.ShortLogWidths.coordinateWidth N m ell)

/-- Nominal shape of one right-nested three-dimensional signed point. -/
abbrev PointShape (N m ell : Nat) : CShape :=
  RawPointShape (RSA.ShortLogWidths.coordinateWidth N m ell)

/-- Nominal shape of an ordered three-row lattice basis. -/
abbrev BasisShape (N m ell : Nat) : CShape :=
  RawBasisShape (RSA.ShortLogWidths.coordinateWidth N m ell)

/-- Pure basis-plus-target state used as the input to reduction and
nearest-plane search. -/
structure State where
  /-- The basis component of this typed record. -/
  basis : NumberTheory.IntegerBasis3
  /-- The target component of this typed record. -/
  target : NumberTheory.IntegerPoint3

/-- Nominal shape of the basis-plus-target lattice state. -/
abbrev StateShape (N m ell : Nat) : CShape :=
  .product (BasisShape N m ell) (PointShape N m ell)

/-- The current basis-plus-target state is the complete workspace payload of
this representation seam. -/
abbrev WorkspaceShape (N m ell : Nat) : CShape :=
  StateShape N m ell

/-- Closed number of workspace bits for one basis-plus-target state. -/
def workspaceBitCount (N m ell : Nat) : Nat :=
  12 * RSA.ShortLogWidths.coordinateWidth N m ell

/-- The closed workspace shape has exactly twelve signed coordinates. -/
lemma workspaceShape_bitWidth (N m ell : Nat) :
  CShape.bitWidth (WorkspaceShape N m ell) = workspaceBitCount N m ell := by
  simp only [WorkspaceShape, StateShape, BasisShape, PointShape,
    CShape.bitWidth_product, CShape.bitWidth_fixedVector,
    CShape.bitWidth_unsignedWord, workspaceBitCount]
  omega

/-- Exact source lattice state for two decoded short-log samples. -/
def initialState (m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) : State where
  basis := RSA.shortLogLatticeBasis m ell samples
  target := RSA.shortLogLatticeTarget m ell samples

/-! ## Representation relations -/

/-- Decode one nominal signed word through Core's fixed two's-complement
carrier. -/
def decodeCoordinate {N m ell : Nat}
    (encoded : CShape.Value (SignedWordShape N m ell)) : Int :=
  decodeRawCoordinate encoded

/-- Decode one right-nested nominal point to the pure integer point carrier. -/
def decodePoint {N m ell : Nat}
    (encoded : CShape.Value (PointShape N m ell)) : NumberTheory.IntegerPoint3 :=
  decodeRawPoint encoded

/-- Decode an ordered nominal basis to the pure three-row basis carrier. -/
def decodeBasis {N m ell : Nat}
    (encoded : CShape.Value (BasisShape N m ell)) : NumberTheory.IntegerBasis3 :=
  decodeRawBasis encoded

/-- Decode the nominal workspace payload to its pure basis-plus-target state. -/
def decodeState {N m ell : Nat}
    (encoded : CShape.Value (StateShape N m ell)) : State where
  basis := decodeBasis encoded.first
  target := decodePoint encoded.second

/-- Exact representation of one nominal signed coordinate. -/
def CoordinateRepresents {N m ell : Nat}
    (encoded : CShape.Value (SignedWordShape N m ell)) (value : Int) : Prop :=
  decodeCoordinate encoded = value

/-- Exact representation of one nominal three-dimensional point. -/
def PointRepresents {N m ell : Nat}
    (encoded : CShape.Value (PointShape N m ell))
    (point : NumberTheory.IntegerPoint3) : Prop :=
  decodePoint encoded = point

/-- Exact representation of one nominal ordered basis. -/
def BasisRepresents {N m ell : Nat}
    (encoded : CShape.Value (BasisShape N m ell))
    (basis : NumberTheory.IntegerBasis3) : Prop :=
  decodeBasis encoded = basis

/-- Exact representation of one nominal basis-plus-target state. -/
def StateRepresents {N m ell : Nat}
    (encoded : CShape.Value (StateShape N m ell)) (state : State) : Prop :=
  decodeState encoded = state

/-! ## Mutable reducer cells -/

/-- Three independently writable raw coordinates of one reducer row. -/
structure PointRefs {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) where
  /-- Writable cell for the first value. -/
  first : CWriteRef ctx (RawSignedWordShape width)
  firstRole : first.toCStorageRef.role = .workspace
  /-- Writable cell for the second value. -/
  second : CWriteRef ctx (RawSignedWordShape width)
  secondRole : second.toCStorageRef.role = .workspace
  /-- Writable cell for the third value. -/
  third : CWriteRef ctx (RawSignedWordShape width)
  thirdRole : third.toCStorageRef.role = .workspace

/-- Nine independently writable raw coordinates of one ordered basis. -/
structure BasisRefs {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) where
  /-- Nested references for the first stage. -/
  first : PointRefs ctx width
  /-- Nested references for the second stage. -/
  second : PointRefs ctx width
  /-- Nested references for the third stage. -/
  third : PointRefs ctx width

/-- Writable reducer state: one basis and the two monotone phase flags. -/
structure MachineRefs {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : BasisRefs ctx width
  /-- Writable cell for the second phase value. -/
  secondPhase : CWriteRef ctx .bit
  secondPhaseRole : secondPhase.toCStorageRef.role = .workspace
  /-- Writable cell for the done value. -/
  done : CWriteRef ctx .bit
  doneRole : done.toCStorageRef.role = .workspace

/-- Names of all eleven independently writable reducer cells. -/
inductive MachineCell where
  | firstFirst
  | firstSecond
  | firstThird
  | secondFirst
  | secondSecond
  | secondThird
  | thirdFirst
  | thirdSecond
  | thirdThird
  | secondPhase
  | done
deriving DecidableEq

/-- Storage key of one named reducer cell. -/
def MachineRefs.keyOf {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (refs : MachineRefs ctx width) : MachineCell → StorageKey
  | .firstFirst => refs.basis.first.first.toCStorageRef.key
  | .firstSecond => refs.basis.first.second.toCStorageRef.key
  | .firstThird => refs.basis.first.third.toCStorageRef.key
  | .secondFirst => refs.basis.second.first.toCStorageRef.key
  | .secondSecond => refs.basis.second.second.toCStorageRef.key
  | .secondThird => refs.basis.second.third.toCStorageRef.key
  | .thirdFirst => refs.basis.third.first.toCStorageRef.key
  | .thirdSecond => refs.basis.third.second.toCStorageRef.key
  | .thirdThird => refs.basis.third.third.toCStorageRef.key
  | .secondPhase => refs.secondPhase.toCStorageRef.key
  | .done => refs.done.toCStorageRef.key

/-- All mutable reducer cells have distinct storage identities. -/
def MachineRefs.Separated {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (refs : MachineRefs ctx width) : Prop :=
  Function.Injective refs.keyOf

/-- Structural read of one mutable raw coordinate. -/
def coordinateInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (coordinate : CWriteRef ctx (RawSignedWordShape width)) :
    CInputRef ctx (RawSignedWordShape width) :=
  .storage coordinate.toCStorageRef

/-- Decode the three independently stored coordinates of one row. -/
def PointRefs.value {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (observation : Execution.Store ctx)
    (refs : PointRefs ctx width) : NumberTheory.IntegerPoint3 :=
  (decodeRawCoordinate (observation.read (coordinateInput refs.first)),
    decodeRawCoordinate (observation.read (coordinateInput refs.second)),
    decodeRawCoordinate (observation.read (coordinateInput refs.third)))

/-- Decode the nine independently stored coordinates of one basis. -/
def BasisRefs.value {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (observation : Execution.Store ctx)
    (refs : BasisRefs ctx width) : NumberTheory.IntegerBasis3 where
  first := refs.first.value observation
  second := refs.second.value observation
  third := refs.third.value observation

/-- Read the three real coordinate cells as one closed structural point. -/
def PointRefs.input {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : PointRefs ctx width) : CInputRef ctx (RawPointShape width) :=
  .product (coordinateInput refs.first)
    (.product (coordinateInput refs.second) (coordinateInput refs.third))

/-- Read the nine real basis cells in their source row order. -/
def BasisRefs.input {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : BasisRefs ctx width) : CInputRef ctx (RawBasisShape width) :=
  .fixedVector (Fin.cases refs.first.input
    (Fin.cases refs.second.input (fun _ => refs.third.input)))

/-- The point interpretation is the decoder applied to its actual structural store read. -/
lemma PointRefs.value_eq_read {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : PointRefs ctx width) (store : Execution.Store ctx) :
    refs.value store = decodeRawPoint (store.read refs.input) := rfl

/-- The basis interpretation reads exactly the nine stored coordinates. -/
lemma BasisRefs.value_eq_read {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : BasisRefs ctx width) (store : Execution.Store ctx) :
    refs.value store = decodeRawBasis (store.read refs.input) := rfl

/-- An actual write outside a point's three cells preserves its decoded value. -/
lemma PointRefs.value_write {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {shape : CShape} (refs : PointRefs ctx width)
    (store : Execution.Store ctx) (output : CWriteRef ctx shape) (value : shape.Value)
    (separate : output.key ∉ refs.input.storageKeys) :
    refs.value (store.write output value) = refs.value store := by
  rw [refs.value_eq_read, refs.value_eq_read]
  exact congrArg decodeRawPoint
    (Execution.Store.read_write_of_not_mem_storageKeys store output value refs.input separate)

/-- An actual write outside a basis's nine cells preserves its decoded value. -/
lemma BasisRefs.value_write {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {shape : CShape} (refs : BasisRefs ctx width)
    (store : Execution.Store ctx) (output : CWriteRef ctx shape) (value : shape.Value)
    (separate : output.key ∉ refs.input.storageKeys) :
    refs.value (store.write output value) = refs.value store := by
  rw [refs.value_eq_read, refs.value_eq_read]
  exact congrArg decodeRawBasis
    (Execution.Store.read_write_of_not_mem_storageKeys store output value refs.input separate)

/-- Exact two-bit encoding of the three LLL phases. -/
def MachineRefs.PhaseRepresents {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (observation : Execution.Store ctx)
    (refs : MachineRefs ctx width) (phase : NumberTheory.LLLPhase3) : Prop :=
  match phase with
  | .first =>
      (observation.read (.storage refs.secondPhase.toCStorageRef)).toBool = false ∧
        (observation.read (.storage refs.done.toCStorageRef)).toBool = false
  | .second =>
      (observation.read (.storage refs.secondPhase.toCStorageRef)).toBool = true ∧
        (observation.read (.storage refs.done.toCStorageRef)).toBool = false
  | .done =>
      (observation.read (.storage refs.secondPhase.toCStorageRef)).toBool = true ∧
        (observation.read (.storage refs.done.toCStorageRef)).toBool = true

/-- Store-level representation of the executable LLL basis and phase. -/
def MachineRefs.Represented {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (observation : Execution.Store ctx)
    (refs : MachineRefs ctx width) (state : NumberTheory.LLLState3) : Prop :=
  refs.basis.value observation = state.basis ∧
    refs.PhaseRepresents observation state.phase

/-! ## Typed storage references -/

/-- Caller-owned cells for one future fixed-width lattice reduction state. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N m ell : Nat) where
  /-- Retained source basis assembled from one decoded terminal pair. -/
  basis : CStorageRef ctx (BasisShape N m ell)
  basisRole : basis.role = .retained
  /-- Retained centered target assembled from the same decoded terminal pair. -/
  target : CStorageRef ctx (PointShape N m ell)
  targetRole : target.role = .retained
  /-- Workspace cell holding the mutable basis-plus-target state. -/
  state : CWriteRef ctx (StateShape N m ell)
  stateRole : state.toCStorageRef.role = .workspace

/-- Structural read of the retained source basis. -/
def basisInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (refs : Refs ctx N m ell) : CInputRef ctx (BasisShape N m ell) :=
  .storage refs.basis

/-- Structural read of the retained source target. -/
def targetInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (refs : Refs ctx N m ell) : CInputRef ctx (PointShape N m ell) :=
  .storage refs.target

/-- Structural read of the mutable lattice workspace payload. -/
def stateInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (refs : Refs ctx N m ell) : CInputRef ctx (StateShape N m ell) :=
  .storage refs.state.toCStorageRef

/-- The input basis, input target, and mutable workspace have distinct
storage identities. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (refs : Refs ctx N m ell) : Prop where
  basisAvoidsTarget : refs.target.key ∉ (basisInput refs).storageKeys
  basisAvoidsState : refs.state.key ∉ (basisInput refs).storageKeys
  targetAvoidsState : refs.state.key ∉ (targetInput refs).storageKeys

/-- Representation of the retained source basis in the actual store. -/
def BasisRefRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (observation : Execution.Store ctx) (refs : Refs ctx N m ell)
    (basis : NumberTheory.IntegerBasis3) : Prop :=
  BasisRepresents (observation.read (basisInput refs)) basis

/-- Representation of the retained source target in the actual store. -/
def TargetRefRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (observation : Execution.Store ctx) (refs : Refs ctx N m ell)
    (target : NumberTheory.IntegerPoint3) : Prop :=
  PointRepresents (observation.read (targetInput refs)) target

/-- Representation of the mutable basis-plus-target workspace in the actual
store. -/
def StateRefRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (observation : Execution.Store ctx) (refs : Refs ctx N m ell)
    (state : State) : Prop :=
  StateRepresents (observation.read (stateInput refs)) state

/-- A complete store representation records the two retained inputs and the
workspace state under the same fixed coordinate width. -/
def Refs.Represented {kind : ProblemKind} {ctx : RuntimeCtx kind} {N m ell : Nat}
    (observation : Execution.Store ctx) (refs : Refs ctx N m ell)
    (state : State) : Prop :=
  BasisRefRepresents observation refs state.basis ∧
    TargetRefRepresents observation refs state.target ∧
      StateRefRepresents observation refs state

end

end LatticeState
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
