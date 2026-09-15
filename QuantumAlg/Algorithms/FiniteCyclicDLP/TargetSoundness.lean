/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base
import all QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Core.Algorithm.QuantumState
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Util.Complex
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.PMF
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Access
import all QuantumAlg.Algorithms.FiniteCyclicDLP.BornBridge
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.HiddenLine

/-!
# Canonical target-verification soundness for finite-cyclic DLP

The endpoint-owned target verifier scans an explicit table of canonical
residue words and an equally explicit table of encoded generator powers.
This module proves the mathematical contract of those fixed inputs: a row
whose image matches the encoded target identifies the advertised secret.
The result is stated independently of the verifier's mutable scan state so it
can be used directly at the endpoint's closed routine boundary.
-/

section

namespace QuantumAlg

noncomputable section

namespace FiniteCyclicDLP
namespace Canonical
namespace TargetSoundness

universe u

variable {G : Type u} [Group G]

/-- Static candidate encodings in canonical residue order. -/
abbrev CandidateTableShape (P : KnownOrderProblem G) : CShape :=
  .fixedVector P.order (.unsignedWord (orderWidth P))

/-- Static encoded generator-power values aligned with the candidate table. -/
abbrev ImageTableShape (P : KnownOrderProblem G) : CShape :=
  .fixedVector P.order (.unsignedWord (orderWidth P))

/-- The candidate table stores each canonical residue at its own index. -/
def candidateTableValue (P : KnownOrderProblem G) :
    CShape.Value (CandidateTableShape P) :=
  .fixedVector fun index => CShape.wordOfNat (orderWidth P) index.val

/-- The image table stores the oracle encoding of the matching generator power. -/
def imageTableValue {P : KnownOrderProblem G} (A : Access P) :
    CShape.Value (ImageTableShape P) :=
  .fixedVector fun index =>
    .unsignedWord (A.ux.encode (P.generator ^ index.val))

/-- The target word uses exactly the same encoding as the image table. -/
def targetValue {P : KnownOrderProblem G} (A : Access P) :
    CShape.Value (.unsignedWord (orderWidth P)) :=
  .unsignedWord (A.ux.encode P.target)

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

/-- The encoded image stored at a static row is the matching generator power. -/
theorem imageTableValue_get {P : KnownOrderProblem G} (A : Access P)
    (index : Fin P.order) :
    (imageTableValue A).get index =
      .unsignedWord (A.ux.encode (P.generator ^ index.val)) :=
  rfl

/-- If a row's encoded generator power equals the encoded target, its index is
the advertised secret's canonical representative. -/
theorem imageTableEntry_eq_target_implies_index_eq_secret
    {P : KnownOrderProblem G} (A : Access P) (input : Probability.SecretInput P)
    (index : Fin P.order)
    (imageTarget : (imageTableValue A).get index = targetValue A) :
    index.val = input.secret.val := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  have encodedValues := congrArg CShape.Value.toNat imageTarget
  change (A.ux.encode (P.generator ^ index.val)).val =
      (A.ux.encode P.target).val at encodedValues
  have encoded : A.ux.encode (P.generator ^ index.val) = A.ux.encode P.target :=
    Fin.ext encodedValues
  have power : P.generator ^ index.val = P.target :=
    A.ux.encode_injective encoded
  have samePower : P.generator ^ index.val = P.generator ^ input.secret.val :=
    power.trans input.target_eq_generator_pow.symm
  have sameResidue := (pow_inj_mod).mp samePower
  simpa [P.order_eq_orderOf.symm,
    Nat.mod_eq_of_lt index.isLt,
    Nat.mod_eq_of_lt (ZMod.val_lt input.secret)] using sameResidue

/-- A recovered word matching a canonical candidate row whose image matches
the encoded target is the advertised secret.  This is the endpoint-facing
soundness bridge for one accepted target-verifier row. -/
theorem recoveredWord_eq_secret_of_candidate_row_and_image_target
    {P : KnownOrderProblem G} (A : Access P) (input : Probability.SecretInput P)
    (index : Fin P.order) (recovered : CShape.Word (orderWidth P))
    (candidateRow : recovered.toNat = ((candidateTableValue P).get index).toNat)
    (imageTarget : (imageTableValue A).get index = targetValue A) :
    recovered.toNat = input.secret.val := by
  calc
    recovered.toNat = ((candidateTableValue P).get index).toNat := candidateRow
    _ = index.val := candidateTableValue_get_toNat P index
    _ = input.secret.val :=
      imageTableEntry_eq_target_implies_index_eq_secret A input index imageTarget

/-- Observation-level form used by the closed table scanner: equality of the
two encoded words is exposed through `toNat`, exactly as
`TargetVerification.RowMatches` states it. -/
theorem recoveredWord_eq_secret_of_row_toNat
    {P : KnownOrderProblem G} (A : Access P) (input : Probability.SecretInput P)
    (index : Fin P.order) (recovered : CShape.Word (orderWidth P))
    (candidateRow : recovered.toNat = ((candidateTableValue P).get index).toNat)
    (imageTarget : ((imageTableValue A).get index).toNat = (targetValue A).toNat) :
    recovered.toNat = input.secret.val := by
  apply recoveredWord_eq_secret_of_candidate_row_and_image_target A input index
    recovered candidateRow
  change (A.ux.encode (P.generator ^ index.val)).val =
      (A.ux.encode P.target).val at imageTarget
  exact congrArg CShape.Value.unsignedWord (Fin.ext imageTarget)

/-- The canonical row indexed by the advertised secret is a complete target
match for the advertised candidate word. -/
theorem secret_row_matches
    {P : KnownOrderProblem G} (A : Access P) (input : Probability.SecretInput P)
    (recovered : CShape.Word (orderWidth P))
    (recoveredSecret : recovered.toNat = input.secret.val) :
    recovered.toNat =
        ((candidateTableValue P).get (Probability.residueIndex P input.secret)).toNat ∧
      ((imageTableValue A).get (Probability.residueIndex P input.secret)).toNat =
        (targetValue A).toNat := by
  constructor
  · rw [candidateTableValue_get_toNat]
    exact recoveredSecret
  · change
      (A.ux.encode (P.generator ^ input.secret.val)).val =
        (A.ux.encode P.target).val
    rw [input.target_eq_generator_pow]

end TargetSoundness
end Canonical
end FiniteCyclicDLP

end

end QuantumAlg

end
