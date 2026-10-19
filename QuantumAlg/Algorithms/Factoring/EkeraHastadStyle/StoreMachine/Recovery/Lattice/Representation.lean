/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.RowLoading.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Layout

/-!
# Raw-cell representation bridge for the canonical lattice

The original independently stored raw coordinates are read from the actual
execution store. Their workspace views preserve the original cell identities;
signed-range premises justify exact integer decoding from those actual words.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeRepresentation

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- Workspace-role witnesses needed to view raw loader cells as reducer cells. -/
structure WorkspaceRoles {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : LatticeLoading.RawOutputRefs ctx width) : Prop where
  b11 : output.b11.toCStorageRef.role = .workspace
  b12 : output.b12.toCStorageRef.role = .workspace
  b13 : output.b13.toCStorageRef.role = .workspace
  b21 : output.b21.toCStorageRef.role = .workspace
  b22 : output.b22.toCStorageRef.role = .workspace
  b23 : output.b23.toCStorageRef.role = .workspace
  b31 : output.b31.toCStorageRef.role = .workspace
  b32 : output.b32.toCStorageRef.role = .workspace
  b33 : output.b33.toCStorageRef.role = .workspace
  t1 : output.t1.toCStorageRef.role = .workspace
  t2 : output.t2.toCStorageRef.role = .workspace
  t3 : output.t3.toCStorageRef.role = .workspace

/-- View the first nine raw loader cells as the mutable reducer basis. -/
def basisRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : LatticeLoading.RawOutputRefs ctx width) (roles : WorkspaceRoles output) :
    LatticeState.BasisRefs ctx width where
  first :=
    { first := output.b11
      firstRole := roles.b11
      second := output.b12
      secondRole := roles.b12
      third := output.b13
      thirdRole := roles.b13 }
  second :=
    { first := output.b21
      firstRole := roles.b21
      second := output.b22
      secondRole := roles.b22
      third := output.b23
      thirdRole := roles.b23 }
  third :=
    { first := output.b31
      firstRole := roles.b31
      second := output.b32
      secondRole := roles.b32
      third := output.b33
      thirdRole := roles.b33 }

/-- View the final three raw loader cells as the mutable reducer target. -/
def targetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : LatticeLoading.RawOutputRefs ctx width) (roles : WorkspaceRoles output) :
    LatticeState.PointRefs ctx width where
  first := output.t1
  firstRole := roles.t1
  second := output.t2
  secondRole := roles.t2
  third := output.t3
  thirdRole := roles.t3

/-- The two structural readers for one writable raw cell are definitionally equal. -/
private lemma coordinateInput_eq_loadingWriteInput {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (output : CWriteRef ctx (LatticeState.RawSignedWordShape width)) :
    LatticeState.coordinateInput output = LatticeLoading.writeInput output := rfl

/-- Nine independent raw signed representations of one ordered basis. -/
def BasisRawRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (store : Store ctx)
    (output : LatticeLoading.RawOutputRefs ctx width)
    (basis : NumberTheory.IntegerBasis3) : Prop :=
  RawSignedRepresents (store.read (LatticeLoading.writeInput output.b11)) basis.first.1 ∧
    RawSignedRepresents (store.read (LatticeLoading.writeInput output.b12)) basis.first.2.1 ∧
      RawSignedRepresents (store.read (LatticeLoading.writeInput output.b13)) basis.first.2.2 ∧
        RawSignedRepresents (store.read (LatticeLoading.writeInput output.b21)) basis.second.1 ∧
          RawSignedRepresents (store.read (LatticeLoading.writeInput output.b22))
            basis.second.2.1 ∧
            RawSignedRepresents (store.read (LatticeLoading.writeInput output.b23))
              basis.second.2.2 ∧
              RawSignedRepresents (store.read (LatticeLoading.writeInput output.b31))
                basis.third.1 ∧
                RawSignedRepresents (store.read (LatticeLoading.writeInput output.b32))
                  basis.third.2.1 ∧
                  RawSignedRepresents (store.read (LatticeLoading.writeInput output.b33))
                    basis.third.2.2

/-- Three independent raw signed representations of one target point. -/
def TargetRawRepresents {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (store : Store ctx)
    (output : LatticeLoading.RawOutputRefs ctx width)
    (target : NumberTheory.IntegerPoint3) : Prop :=
  RawSignedRepresents (store.read (LatticeLoading.writeInput output.t1)) target.1 ∧
    RawSignedRepresents (store.read (LatticeLoading.writeInput output.t2)) target.2.1 ∧
      RawSignedRepresents (store.read (LatticeLoading.writeInput output.t3)) target.2.2

/-- Convert three raw cells into the reducer's three-coordinate raw relation. -/
lemma pointRawRepresents_of_raw {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (store : Store ctx)
    (refs : LatticeState.PointRefs ctx width) (point : NumberTheory.IntegerPoint3)
    (firstRep : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.first)) point.1)
    (secondRep : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.second)) point.2.1)
    (thirdRep : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.third)) point.2.2) :
    LatticeArithmetic.PointRawRepresents store refs point :=
  ⟨firstRep, secondRep, thirdRep⟩

/-- The nine basis-cell representations are exactly the three point relations. -/
lemma basisRawRepresents_iff_pointRawRepresents {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (store : Store ctx)
    (output : LatticeLoading.RawOutputRefs ctx width) (roles : WorkspaceRoles output)
    (basis : NumberTheory.IntegerBasis3) :
    BasisRawRepresents store output basis ↔
      LatticeArithmetic.PointRawRepresents store (basisRefs output roles).first basis.first ∧
        LatticeArithmetic.PointRawRepresents store (basisRefs output roles).second
          basis.second ∧
          LatticeArithmetic.PointRawRepresents store (basisRefs output roles).third
            basis.third := by
  constructor
  · intro represents
    rcases represents with ⟨b11, b12, b13, b21, b22, b23, b31, b32, b33⟩
    refine ⟨?_, ?_, ?_⟩
    · exact pointRawRepresents_of_raw store (basisRefs output roles).first basis.first
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b11)
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b12)
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b13)
    · exact pointRawRepresents_of_raw store (basisRefs output roles).second basis.second
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b21)
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b22)
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b23)
    · exact pointRawRepresents_of_raw store (basisRefs output roles).third basis.third
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b31)
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b32)
        (by simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b33)
  · intro represents
    rcases represents with ⟨first, second, third⟩
    rcases first with ⟨b11, b12, b13⟩
    rcases second with ⟨b21, b22, b23⟩
    rcases third with ⟨b31, b32, b33⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b11
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b12
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b13
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b21
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b22
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b23
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b31
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b32
    · simpa only [basisRefs, coordinateInput_eq_loadingWriteInput] using b33

/-- The original nine raw cells are exactly the actual basis relation consumed by Gram and LLL. -/
lemma basisRawRepresents_iff_metricBasis {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (store : Store ctx) (output : LatticeLoading.RawOutputRefs ctx width)
    (roles : WorkspaceRoles output) (basis : NumberTheory.IntegerBasis3) :
    BasisRawRepresents store output basis ↔
      LatticeMetricMachine.BasisRawRepresents store (basisRefs output roles) basis := by
  constructor
  · intro represents row
    have points := (basisRawRepresents_iff_pointRawRepresents store output roles basis).mp
      represents
    cases row with
    | first => exact points.1
    | second => exact points.2.1
    | third => exact points.2.2
  · intro represents
    apply (basisRawRepresents_iff_pointRawRepresents store output roles basis).mpr
    exact ⟨represents .first, represents .second, represents .third⟩

/-- The three target-cell representations are exactly one point relation. -/
lemma targetRawRepresents_iff_pointRawRepresents {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (store : Store ctx)
    (output : LatticeLoading.RawOutputRefs ctx width) (roles : WorkspaceRoles output)
    (target : NumberTheory.IntegerPoint3) :
    TargetRawRepresents store output target ↔
      LatticeArithmetic.PointRawRepresents store (targetRefs output roles) target := by
  constructor
  · intro represents
    rcases represents with ⟨t1, t2, t3⟩
    exact pointRawRepresents_of_raw store (targetRefs output roles) target
      (by simpa only [targetRefs, coordinateInput_eq_loadingWriteInput] using t1)
      (by simpa only [targetRefs, coordinateInput_eq_loadingWriteInput] using t2)
      (by simpa only [targetRefs, coordinateInput_eq_loadingWriteInput] using t3)
  · intro represents
    rcases represents with ⟨t1, t2, t3⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [targetRefs, coordinateInput_eq_loadingWriteInput] using t1
    · simpa only [targetRefs, coordinateInput_eq_loadingWriteInput] using t2
    · simpa only [targetRefs, coordinateInput_eq_loadingWriteInput] using t3

/-- Signed-range premises that make the raw decoder exact for one point. -/
def PointDecodeRange (width : Nat) (point : NumberTheory.IntegerPoint3) : Prop :=
  ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width point.1 ∧
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width point.2.1 ∧
      ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width point.2.2

/-- Signed-range premises that make all nine raw basis decoders exact. -/
def BasisDecodeRange (width : Nat) (basis : NumberTheory.IntegerBasis3) : Prop :=
  PointDecodeRange width basis.first ∧
    PointDecodeRange width basis.second ∧
      PointDecodeRange width basis.third

/-- Raw signed representation decodes to its integer under the existing signed range. -/
lemma decodeRawCoordinate_eq_of_rawSignedRepresents {width : Nat}
    (encoded : CShape.Word width) (value : Int) (widthPositive : 0 < width)
    (represents : RawSignedRepresents encoded value)
    (range : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width value) :
    LatticeState.decodeRawCoordinate encoded = value := by
  change decodeRawSignedWord encoded = value
  exact rawSignedRepresents_decode_eq encoded value widthPositive represents range

/-- One raw reducer point decodes to its represented integer point. -/
lemma pointValue_eq_of_pointRawRepresents {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (store : Store ctx)
    (refs : LatticeState.PointRefs ctx width) (point : NumberTheory.IntegerPoint3)
    (widthPositive : 0 < width)
    (represents : LatticeArithmetic.PointRawRepresents store refs point)
    (range : PointDecodeRange width point) :
    refs.value store = point := by
  rcases represents with ⟨firstRep, secondRep, thirdRep⟩
  rcases range with ⟨firstRange, secondRange, thirdRange⟩
  unfold LatticeState.PointRefs.value
  apply Prod.ext
  · exact decodeRawCoordinate_eq_of_rawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.first)) point.1 widthPositive firstRep
      firstRange
  · apply Prod.ext
    · exact decodeRawCoordinate_eq_of_rawSignedRepresents
        (store.read (LatticeState.coordinateInput refs.second)) point.2.1 widthPositive secondRep
        secondRange
    · exact decodeRawCoordinate_eq_of_rawSignedRepresents
        (store.read (LatticeState.coordinateInput refs.third)) point.2.2 widthPositive thirdRep
        thirdRange

/-- The nine raw cells decode to the displayed ordered integer basis. -/
lemma basisValue_eq_of_rawSignedRepresents {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (store : Store ctx)
    (output : LatticeLoading.RawOutputRefs ctx width) (roles : WorkspaceRoles output)
    (basis : NumberTheory.IntegerBasis3) (widthPositive : 0 < width)
    (represents : BasisRawRepresents store output basis)
    (range : BasisDecodeRange width basis) :
    (basisRefs output roles).value store = basis := by
  have points := (basisRawRepresents_iff_pointRawRepresents store output roles basis).mp
    represents
  have firstValue := pointValue_eq_of_pointRawRepresents store
    (basisRefs output roles).first basis.first widthPositive points.1 range.1
  have secondValue := pointValue_eq_of_pointRawRepresents store
    (basisRefs output roles).second basis.second widthPositive points.2.1 range.2.1
  have thirdValue := pointValue_eq_of_pointRawRepresents store
    (basisRefs output roles).third basis.third widthPositive points.2.2 range.2.2
  change
    { first := (basisRefs output roles).first.value store
      second := (basisRefs output roles).second.value store
      third := (basisRefs output roles).third.value store } = basis
  rw [firstValue, secondValue, thirdValue]

/-- The three raw target cells decode to the displayed integer target. -/
lemma targetValue_eq_of_rawSignedRepresents {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (store : Store ctx)
    (output : LatticeLoading.RawOutputRefs ctx width) (roles : WorkspaceRoles output)
    (target : NumberTheory.IntegerPoint3) (widthPositive : 0 < width)
    (represents : TargetRawRepresents store output target)
    (range : PointDecodeRange width target) :
    (targetRefs output roles).value store = target := by
  apply pointValue_eq_of_pointRawRepresents store (targetRefs output roles) target
    widthPositive
  · exact (targetRawRepresents_iff_pointRawRepresents store output roles target).mp
      represents
  · exact range

/-- The raw basis and target cells decode jointly to the displayed pair of values. -/
lemma basisTargetValue_eq_of_rawSignedRepresents {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (store : Store ctx)
    (output : LatticeLoading.RawOutputRefs ctx width) (roles : WorkspaceRoles output)
    (basis : NumberTheory.IntegerBasis3) (target : NumberTheory.IntegerPoint3)
    (widthPositive : 0 < width)
    (basisRepresents : BasisRawRepresents store output basis)
    (targetRepresents : TargetRawRepresents store output target)
    (basisRange : BasisDecodeRange width basis)
    (targetRange : PointDecodeRange width target) :
    (basisRefs output roles).value store = basis ∧
      (targetRefs output roles).value store = target := by
  exact ⟨basisValue_eq_of_rawSignedRepresents store output roles basis widthPositive
      basisRepresents basisRange,
    targetValue_eq_of_rawSignedRepresents store output roles target widthPositive
      targetRepresents targetRange⟩

end

end LatticeRepresentation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
