/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability

/-!
# Concrete target-verification soundness for finite-cyclic DLP

The concrete endpoint stores candidate residues at `orderWidth` and stores
the corresponding clean implementation states at the actual tail width.  The
two encodings are intentionally kept separate: equality of two image words
is first lifted through the tail encoding and the clean-tail embedding, and
only then reduced to equality of generator powers modulo the known order.
-/

section

namespace QuantumAlg

noncomputable section

namespace FiniteCyclicDLP
namespace Concrete
namespace TargetSoundness

universe u

variable {G : Type u} [Group G]

/-! ## Concrete verifier table values -/

/-- Static candidate encodings in canonical residue order. -/
abbrev CandidateTableShape (P : KnownOrderProblem G) : CShape :=
  .fixedVector P.order (.unsignedWord (orderWidth P))

/-- Static clean-tail encodings aligned with the candidate table. -/
abbrev ImageTableShape (P : KnownOrderProblem G)
    (A : ConcreteCircuitAccess P) : CShape :=
  .fixedVector P.order (.unsignedWord A.tailEncoding.width)

/-- The candidate table stores each canonical residue at its own index. -/
def candidateTableValue (P : KnownOrderProblem G) :
    CShape.Value (CandidateTableShape P) :=
  .fixedVector fun index => CShape.wordOfNat (orderWidth P) index.val

/-- The image table stores the clean-tail encoding of the matching power. -/
def imageTableValue {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P) :
    CShape.Value (ImageTableShape P A) :=
  .fixedVector fun index =>
    .unsignedWord (A.tailEncoding.encode
      (A.cleanTail (P.generator ^ index.val)))

/-- The target word uses the same concrete clean-tail encoding as the table. -/
def targetValue {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P) :
    CShape.Value (.unsignedWord A.tailEncoding.width) :=
  .unsignedWord (A.tailEncoding.encode (A.cleanTail P.target))

/-- A candidate-table entry does not truncate: the source order fits the
oversampled Fourier word width. -/
theorem candidateTableValue_get_toNat (P : KnownOrderProblem G)
    (index : Fin P.order) :
    ((candidateTableValue P).get index).toNat = index.val := by
  change (CShape.wordOfNat (orderWidth P) index.val).toNat = index.val
  rw [CShape.wordOfNat_val]
  exact Nat.mod_eq_of_lt (by
    simpa only [CShape.wordModulus, fourierModulus] using
      index.isLt.trans_le (order_le_fourierModulus P))

/-- The encoded image stored at a static row is its matching clean-tail value. -/
theorem imageTableValue_get {P : KnownOrderProblem G}
    (A : ConcreteCircuitAccess P) (index : Fin P.order) :
    (imageTableValue A).get index =
      .unsignedWord (A.tailEncoding.encode
        (A.cleanTail (P.generator ^ index.val))) :=
  rfl

/-- An image-table word equal to the concrete target identifies the secret
index.  The two injectivity hypotheses are applied in their storage order:
tail encoding first, then the clean-tail representation. -/
theorem imageTableEntry_eq_target_implies_index_eq_secret
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P)
    (input : Input P) (index : Fin P.order)
    (imageTarget : (imageTableValue A).get index = targetValue A) :
    index.val = input.secret.val := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  have encodedValues := congrArg CShape.Value.toNat imageTarget
  change (A.tailEncoding.encode
      (A.cleanTail (P.generator ^ index.val))).val =
      (A.tailEncoding.encode (A.cleanTail P.target)).val at encodedValues
  have encoded : A.tailEncoding.encode
      (A.cleanTail (P.generator ^ index.val)) =
      A.tailEncoding.encode (A.cleanTail P.target) :=
    Fin.ext encodedValues
  have clean : A.cleanTail (P.generator ^ index.val) =
      A.cleanTail P.target :=
    A.tailEncoding.encode_injective encoded
  have power : P.generator ^ index.val = P.target :=
    A.cleanTail_injective clean
  have samePower : P.generator ^ index.val =
      P.generator ^ input.secret.val :=
    power.trans input.target_eq_generator_pow.symm
  have sameResidue := (pow_inj_mod).mp samePower
  simpa [P.order_eq_orderOf.symm,
    Nat.mod_eq_of_lt index.isLt,
    Nat.mod_eq_of_lt (ZMod.val_lt input.secret)] using sameResidue

/-- A recovered candidate word matching a concrete candidate row and its
image target is the advertised secret. -/
theorem recoveredWord_eq_secret_of_candidate_row_and_image_target
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P)
    (input : Input P) (index : Fin P.order)
    (recovered : CShape.Word (orderWidth P))
    (candidateRow : recovered.toNat =
      ((candidateTableValue P).get index).toNat)
    (imageTarget : (imageTableValue A).get index = targetValue A) :
    recovered.toNat = input.secret.val := by
  calc
    recovered.toNat = ((candidateTableValue P).get index).toNat := candidateRow
    _ = index.val := candidateTableValue_get_toNat P index
    _ = input.secret.val :=
      imageTableEntry_eq_target_implies_index_eq_secret A input index imageTarget

/-- Observation-level form used by the closed table scanner: image equality
is exposed through the `toNat` values of the two concrete tail words. -/
theorem recoveredWord_eq_secret_of_row_toNat
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P)
    (input : Input P) (index : Fin P.order)
    (recovered : CShape.Word (orderWidth P))
    (candidateRow : recovered.toNat =
      ((candidateTableValue P).get index).toNat)
    (imageTarget : ((imageTableValue A).get index).toNat =
      (targetValue A).toNat) :
    recovered.toNat = input.secret.val := by
  apply recoveredWord_eq_secret_of_candidate_row_and_image_target A input index
    recovered candidateRow
  change (A.tailEncoding.encode
      (A.cleanTail (P.generator ^ index.val))).val =
      (A.tailEncoding.encode (A.cleanTail P.target)).val at imageTarget
  exact congrArg CShape.Value.unsignedWord (Fin.ext imageTarget)

/-- The row indexed by the advertised secret is a complete concrete target
match for the advertised candidate word. -/
theorem secret_row_matches
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P)
    (input : Input P) (recovered : CShape.Word (orderWidth P))
    (recoveredSecret : recovered.toNat = input.secret.val) :
    recovered.toNat =
        ((candidateTableValue P).get
          (Probability.residueIndex P input.secret)).toNat ∧
      ((imageTableValue A).get
          (Probability.residueIndex P input.secret)).toNat =
        (targetValue A).toNat := by
  constructor
  · rw [candidateTableValue_get_toNat]
    exact recoveredSecret
  · change (A.tailEncoding.encode
      (A.cleanTail (P.generator ^ input.secret.val))).val =
      (A.tailEncoding.encode (A.cleanTail P.target)).val
    rw [input.target_eq_generator_pow]

end TargetSoundness
end Concrete
end FiniteCyclicDLP

end

end QuantumAlg

end
