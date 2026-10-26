/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Point

/-!
# Coverage of every actual point-program outcome

The six query paths and two arithmetic paths remain arbitrary. Only the
twelve unit-valued outcomes of native fragments are eliminated. This
structural product argument does not enumerate any measurement bit family.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus QueryOutcome

private def sixQueryPaths
    (p0 : parameters.QueryOutcome (services := services) 0)
    (p1 : parameters.QueryOutcome (services := services) 1)
    (p2 : parameters.QueryOutcome (services := services) 2)
    (p3 : parameters.QueryOutcome (services := services) 3)
    (p4 : parameters.QueryOutcome (services := services) 4)
    (p5 : parameters.QueryOutcome (services := services) 5) :
    (index : Fin 6) → parameters.QueryOutcome (services := services) index :=
  Fin.cases p0 (Fin.cases p1 (Fin.cases p2
    (Fin.cases p3 (Fin.cases p4 (Fin.cases p5 (fun index => Fin.elim0 index))))))

/-- The field trace covers all actual outcomes, retaining each measured path. -/
lemma pointFieldPaths_complete_surjective :
    Function.Surjective (PointFieldPaths.complete (services := services) parameters) := by
  intro outcome
  rcases outcome with ⟨⟨u0, p0, p1⟩,
    ⟨⟨u1, division, u2⟩, ⟨⟨p2, u3, u4, u5, product, u6⟩,
      ⟨⟨p3, u7, u8, u9, u10⟩, p4, p5, u11⟩⟩⟩⟩
  cases u0
  cases u1
  cases u2
  cases u3
  cases u4
  cases u5
  cases u6
  cases u7
  cases u8
  cases u9
  cases u10
  cases u11
  refine ⟨⟨parameters.sixQueryPaths p0 p1 p2 p3 p4 p5, division, product⟩, ?_⟩
  rfl

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
