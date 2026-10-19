/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Semantics

/-!
# Original complete-addition predicates of the actual stored classifier

Case selection preserves both infinity arms, inverse and vertical inputs,
finite doubling and distinct-X addition. These are the original raw branch
predicates; no admissible-trajectory restriction is imposed on recovery inputs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Read exactly the actual predicate cells consulted by the native dispatch tree. -/
def classifyStored (classifier : Classifier ctx width) (store : Store ctx) : Case :=
  if (store.read (.first (classifierRead classifier.leftRaw))).toBool then .leftInfinity
  else if (store.read (.first (classifierRead classifier.rightRaw))).toBool then .rightInfinity
  else if (store.read (classifierRead classifier.xEqual)).toBool then
    if (store.read (classifierRead classifier.yEqual)).toBool then
      if (store.read (classifierRead classifier.yZero)).toBool then .vertical else .doubling
    else .vertical
  else .generic

/-- Complete actual predicates select exactly the original case on the input point values. -/
lemma classifyStored_eq_classifyValues (classifier : Classifier ctx width) (store : Store ctx)
    (left right : CShape.Value (PointShape width)) (ready : classifier.Ready store left right) :
    classifyStored classifier store = classifyValues left right := by
  simp only [classifyStored, read_first, ready.leftRaw, ready.rightRaw,
    ready.xEqual, ready.yEqual, ready.yZero]
  cases left
  cases right
  simp [classifyValues, CShape.unpackEllipticCurvePoint, CShape.Value.first,
    CShape.Value.ellipticCurvePointInfinityTag, CShape.Value.ellipticCurvePointX,
    CShape.Value.ellipticCurvePointY, CShape.Value.toBool]

/-- Every original case has its complete tag and coordinate predicate. -/
def Case.Matches (selected : Case) (left right : CShape.Value (PointShape width)) : Prop :=
  match selected with
  | .leftInfinity => left.ellipticCurvePointInfinityTag = true
  | .rightInfinity => left.ellipticCurvePointInfinityTag = false ∧
      right.ellipticCurvePointInfinityTag = true
  | .vertical => left.ellipticCurvePointInfinityTag = false ∧
      right.ellipticCurvePointInfinityTag = false ∧
      left.ellipticCurvePointX = right.ellipticCurvePointX ∧
      (left.ellipticCurvePointY ≠ right.ellipticCurvePointY ∨ left.ellipticCurvePointY = 0)
  | .doubling => left.ellipticCurvePointInfinityTag = false ∧
      right.ellipticCurvePointInfinityTag = false ∧
      left.ellipticCurvePointX = right.ellipticCurvePointX ∧
      left.ellipticCurvePointY = right.ellipticCurvePointY ∧ left.ellipticCurvePointY ≠ 0
  | .generic => left.ellipticCurvePointInfinityTag = false ∧
      right.ellipticCurvePointInfinityTag = false ∧
      left.ellipticCurvePointX ≠ right.ellipticCurvePointX

/-- The total original selector establishes its selected complete branch predicate. -/
lemma classifyValues_matches (left right : CShape.Value (PointShape width)) :
    (classifyValues left right).Matches left right := by
  unfold classifyValues
  split
  · assumption
  · split
    · simp_all [Case.Matches]
    · split
      · split
        · split <;> simp_all [Case.Matches]
        · simp_all [Case.Matches]
      · simp_all [Case.Matches]

/-- The actual stored branch choice satisfies the original complete predicate. -/
lemma classifyStored_matches (classifier : Classifier ctx width) (store : Store ctx)
    (left right : CShape.Value (PointShape width)) (ready : classifier.Ready store left right) :
    (classifyStored classifier store).Matches left right := by
  rw [classifyStored_eq_classifyValues classifier store left right ready]
  exact classifyValues_matches left right

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
