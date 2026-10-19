/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.FullOutcomeFibers

/-!
# Exact finite sums over the full actual legal path fibers

The existing full-protocol equivalence retains the complete old Store and
division labels. These finite-sum laws transport any additive contribution
through that equivalence, without removing zero contributions or identifying
different original paths. The original and final Stores are arbitrary.

An operator sandwich can be used as the contribution. These laws alone do not
assert that the contribution is an actual execution density, or establish a
common positive output density, initialization, success or resource bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.LegalPathSums

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open TerminalStoreCoordinates LegalPathFibers FullOutcomeFibers
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma conditional_sum_subtype {Label Value : Type}
    [Fintype Label] [AddCommMonoid Value]
    (predicate : Label → Prop) (term : Label → Value) :
    (∑ label, if predicate label then term label else 0) =
      ∑ label : Subtype predicate, term label.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun _ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]) term

/-- Every legal old label occurs exactly once in the full new path fiber, including zero terms. -/
lemma full_legal_sum {Value : Type} [AddCommMonoid Value]
    (modulus m : Nat) (original final : Store (Recovery.Layout.terminal modulus.size m))
    (term : (Fin (2 * m) → Recovery.Reference.Measured.Branch modulus.size (2 * m)) → Value) :
    (∑ path : Fin (2 * m) → Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.Branch
        modulus.size m,
      if Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.traceValid
          modulus.size m (2 * m) id path original final then
        term (Recovery.Layout.BankWords.oldPath modulus m (2 * m) path) else 0) =
      ∑ path : Fin (2 * m) → Recovery.Reference.Measured.Branch modulus.size (2 * m),
        if Recovery.Reference.Measured.traceValid modulus.size (2 * m) id path
            (instantStore modulus m original).1 (instantStore modulus m final).1 then
          term path else 0 := by
  rw [conditional_sum_subtype, conditional_sum_subtype]
  exact Fintype.sum_equiv (fullLegalPathEquiv modulus m original final) _ _
    (fun path => congrArg term (fullLegalPathEquiv_oldPath modulus m original final path).symm)

/-- Branchwise additive identities transfer under the same exact complete legal-path equivalence. -/
lemma full_legal_sum_of_agree {Value : Type} [AddCommMonoid Value]
    (modulus m : Nat) (original final : Store (Recovery.Layout.terminal modulus.size m))
    (newTerm : (Fin (2 * m) →
      Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.Branch modulus.size m) → Value)
    (oldTerm : (Fin (2 * m) → Recovery.Reference.Measured.Branch modulus.size (2 * m)) → Value)
    (agree : ∀ path,
      Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.traceValid
          modulus.size m (2 * m) id path original final →
        newTerm path = oldTerm (Recovery.Layout.BankWords.oldPath modulus m (2 * m) path)) :
    (∑ path, if Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.traceValid
        modulus.size m (2 * m) id path original final then newTerm path else 0) =
      ∑ path, if Recovery.Reference.Measured.traceValid modulus.size (2 * m) id path
          (instantStore modulus m original).1 (instantStore modulus m final).1 then
        oldTerm path else 0 := by
  refine Eq.trans ?_ (full_legal_sum modulus m original final oldTerm)
  apply Finset.sum_congr rfl
  intro path _
  by_cases valid : Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.traceValid
      modulus.size m (2 * m) id path original final
  · rw [if_pos valid, if_pos valid, agree path valid]
  · rw [if_neg valid, if_neg valid]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.LegalPathSums
