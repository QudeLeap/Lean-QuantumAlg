/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prefix
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Address
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Row
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Remaining
import all QuantumAlg.Core.Base.State.Normalized

/-!
# The original coherent good component at each physical source boundary

These are the same raw state definitions used by the actual action proof.
They retain every original admissible branch and external Reference amplitude,
without importing a theorem about the point instrument or its action.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The original admissible source branches, without changing their amplitudes or support. -/
abbrev GoodBranch (I : DomainParameters.PublicKeyInstance) :=
  {branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) // branchGood I branch}

/-- A classical enumeration of the same finite subtype of original admissible branches. -/
noncomputable instance goodBranchFintype (I : DomainParameters.PublicKeyInstance) :
    Fintype (GoodBranch I) := Fintype.ofFinite (GoodBranch I)

variable {ctx : RuntimeCtx .quantum}

attribute [local irreducible] branchGood prefixAffine

/-- The complete physical, remaining-source, and Reference label of one original branch. -/
def coherentLabel (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (processed : Nat) (within : processed ≤ 34)
    (consumed : Nat) (branch : GoodBranch I) {Reference : Register} (ref : Reference.Index) :
    (ctx.register.prod (Sampling.SourceRegister.prod Reference)).Index :=
  (parameters.physicalLabel
    (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
      (prefixAffine I branch.val branch.property processed within) (false, false, false) 0),
    Sampling.remainingSource consumed (sourceBranch I branch.val), ref)

/-- The complete raw coherent boundary with its consumed-source cursor and arbitrary phases. -/
def coherentPrefix (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (processed : Nat) (within : processed ≤ 34)
    (consumed : Nat) (amplitude : GoodBranch I → Complex)
    {Reference : Register} (reference : HilbertVector Reference) :
    HilbertVector (ctx.register.prod (Sampling.SourceRegister.prod Reference)) :=
  ∑ branch : GoodBranch I, ∑ ref : Reference.Index,
    (amplitude branch * reference ref) •
      (NormalizedVector.ket
        (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (coherentLabel parameters I processed within consumed branch ref)).vec

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
