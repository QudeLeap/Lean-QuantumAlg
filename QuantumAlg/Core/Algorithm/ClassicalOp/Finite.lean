/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Finite values in typed classical storage

Every closed classical storage shape admits finitely many values. The
enumerations below follow its actual constructors and payloads. They allow the
execution interpreter to retain correlations between stored classical values
and quantum poststates without replacing a typed register by an unbounded
integer or charging the mathematical enumeration as a runtime operation.
-/

namespace QuantumAlg.CShape.Value

noncomputable section

local instance (shape : CShape) : DecidableEq (Value shape) := Classical.decEq _

@[instance_reducible]
private def finiteValues : (shape : CShape) → Fintype (Value shape)
  | .unit => Fintype.ofSurjective (fun _ : Unit => Value.unit) (by
      intro value
      cases value
      exact ⟨(), rfl⟩)
  | .bit => Fintype.ofSurjective Value.bit (by
      intro value
      cases value with
      | bit value => exact ⟨value, rfl⟩)
  | .finite cardinality => Fintype.ofSurjective (@Value.finite cardinality) (by
      intro value
      cases value with
      | finite value => exact ⟨value, rfl⟩)
  | .bits count => Fintype.ofSurjective (@Value.bits count) (by
      intro value
      cases value with
      | bits get => exact ⟨get, rfl⟩)
  | .unsignedWord width => Fintype.ofSurjective (@Value.unsignedWord width) (by
      intro value
      cases value with
      | unsignedWord value => exact ⟨value, rfl⟩)
  | .boundedSignedWord width => Fintype.ofSurjective (@Value.boundedSignedWord width) (by
      intro value
      cases value with
      | boundedSignedWord value => exact ⟨value, rfl⟩)
  | .option payload =>
      letI := finiteValues payload
      Fintype.ofSurjective
        (fun value : Option (Value payload) => match value with
          | none => Value.optionNone
          | some value => Value.optionSome value) (by
            intro value
            cases value with
            | optionNone => exact ⟨none, rfl⟩
            | optionSome value => exact ⟨some value, rfl⟩)
  | .product left right =>
      letI := finiteValues left
      letI := finiteValues right
      Fintype.ofSurjective
        (fun pair : Value left × Value right => Value.product pair.1 pair.2) (by
          intro value
          cases value with
          | product first second => exact ⟨(first, second), rfl⟩)
  | .fixedVector length element =>
      letI := finiteValues element
      Fintype.ofSurjective (@Value.fixedVector length element) (by
        intro value
        cases value with
        | fixedVector get => exact ⟨get, rfl⟩)
  | .canonicalResidue width => Fintype.ofSurjective (@Value.canonicalResidue width) (by
      intro value
      cases value with
      | canonicalResidue value => exact ⟨value, rfl⟩)
  | .unitResidue width => Fintype.ofSurjective (@Value.unitResidue width) (by
      intro value
      cases value with
      | unitResidue value => exact ⟨value, rfl⟩)
  | .ellipticCurvePoint width => Fintype.ofSurjective
      (fun point : Bool × Fin (2 ^ width) × Fin (2 ^ width) =>
        Value.ellipticCurvePoint point.1 point.2.1 point.2.2) (by
          intro value
          cases value with
          | ellipticCurvePoint tag x y => exact ⟨(tag, x, y), rfl⟩)

/-- Closed classical shapes have finite actual value spaces. Specialized
enumerations, including the finite-register encoding, retain priority. -/
@[no_expose]
public instance (priority := 100) (shape : CShape) : Fintype (Value shape) := finiteValues shape

end

end QuantumAlg.CShape.Value
