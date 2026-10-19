/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.FreeSourceGram
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Completeness of ordered finite Kraus words

The list records families in execution order. Its head acts first, so the head
operator is the rightmost factor of the resulting word. The paths here are
abstract outcome tuples; no identification with stored execution traces is made.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace OrderedKrausWords

noncomputable section

open scoped BigOperators

variable {Outcome Bank : Type} [Fintype Bank] [DecidableEq Bank]

/-- The ordered word acts by the head family first and then by the tail word. -/
def word : (families : List (Outcome → Matrix Bank Bank ℂ)) →
    (Fin families.length → Outcome) → Matrix Bank Bank ℂ
  | [], _ => 1
  | first :: rest, path => word rest (fun index => path index.succ) * first (path 0)

/-- The empty sequence has exactly the identity word. -/
@[simp] lemma word_nil (path : Fin 0 → Outcome) :
    word ([] : List (Outcome → Matrix Bank Bank ℂ)) path = 1 := rfl

/-- The first outcome selects the rightmost factor. -/
@[simp] lemma word_cons (first : Outcome → Matrix Bank Bank ℂ)
    (rest : List (Outcome → Matrix Bank Bank ℂ)) (path : Fin (rest.length + 1) → Outcome) :
    word (first :: rest) path =
      word rest (fun index => path index.succ) * first (path 0) := rfl

/-- Local completeness of every family implies completeness of all ordered words. -/
lemma word_complete [Fintype Outcome]
    (families : List (Outcome → Matrix Bank Bank ℂ))
    (complete : ∀ family ∈ families,
      ∑ label, (family label).conjTranspose * family label = 1) :
    ∑ path : Fin families.length → Outcome,
      (word families path).conjTranspose * word families path = 1 := by
  classical
  revert complete
  induction families with
  | nil =>
      intro _
      simp only [word_nil, Matrix.conjTranspose_one, Matrix.one_mul]
      let _ : Unique (Fin 0 → Outcome) :=
        { default := fun index => Fin.elim0 index
          uniq := fun path => by funext index; exact Fin.elim0 index }
      exact Fintype.sum_unique (fun _ : Fin 0 → Outcome => (1 : Matrix Bank Bank ℂ))
  | cons first rest ih =>
      intro complete
      have firstComplete := complete first List.mem_cons_self
      have restComplete : ∀ family ∈ rest,
          ∑ label, (family label).conjTranspose * family label = 1 := by
        intro family member
        exact complete family (List.mem_cons_of_mem first member)
      calc
        _ = ∑ label : Outcome, ∑ tail : Fin rest.length → Outcome,
            (word rest tail * first label).conjTranspose * (word rest tail * first label) := by
          calc
            _ = ∑ pair : Outcome × (Fin rest.length → Outcome),
                (word (first :: rest)
                  (Fin.consEquiv (fun _ : Fin (rest.length + 1) => Outcome) pair)).conjTranspose *
                  word (first :: rest)
                    (Fin.consEquiv (fun _ : Fin (rest.length + 1) => Outcome) pair) :=
              ((Fin.consEquiv (fun _ : Fin (rest.length + 1) => Outcome)).sum_comp
                (fun path : Fin (rest.length + 1) → Outcome =>
                  (word (first :: rest) path).conjTranspose *
                    word (first :: rest) path)).symm
            _ = _ := by
              rw [Fintype.sum_prod_type]
              simp only [word_cons, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        _ = 1 := FreeSourceGram.composed_complete first (word rest)
          firstComplete (ih restComplete)

end

end OrderedKrausWords
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
