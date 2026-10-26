/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Bases

/-!
# Affine prefixes of the original admissible chronological branches

The mathematical prefix keeps the original fixed seed, all unsigned digits,
and the two certified row families. Its order and exclusions are independent
of the physical sampling implementation.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open PrimeFieldShortWeierstrass

private lemma admissible_prefix_nonidentity {G Branch : Type*} [Group G]
    (count : Nat) (selected : Branch → Fin count → Bool) (addend : Fin count → G)
    (seed : G) (branch : Branch) (seedNonidentity : seed ≠ 1)
    (good : ExceptionalOffsetAveraging.Admissible count selected addend seed branch) :
    ∀ processed : Nat, processed ≤ count →
      seed * ExceptionalOffsetAveraging.prefixMultiplier count selected addend branch processed ≠
        1 := by
  intro processed
  induction processed with
  | zero =>
      intro _
      simpa only [ExceptionalOffsetAveraging.prefixMultiplier, List.take_zero,
        List.foldl_nil, mul_one] using seedNonidentity
  | succ processed ih =>
      intro within
      have indexLt : processed < count := by omega
      rw [ExceptionalOffsetAveraging.prefixMultiplier_succ count selected addend branch
        processed indexLt]
      by_cases active : selected branch ⟨processed, indexLt⟩ = true
      · rw [if_pos active]
        intro same
        apply (good ⟨processed, indexLt⟩ active).2
        have appended :
            (seed * ExceptionalOffsetAveraging.prefixMultiplier count selected addend branch
              processed) * addend ⟨processed, indexLt⟩ = 1 := by
          simpa only [mul_assoc] using same
        have cancelled := congrArg
          (fun point : G => point * (addend ⟨processed, indexLt⟩)⁻¹) appended
        simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using cancelled
      · rw [if_neg active]
        exact ih (Nat.le_of_succ_le within)

private lemma admissible_of_mem {G : Type*} [Group G] (width count : Nat)
    (selected : EllipticCurve.FullRange.Branch width → Fin count → Bool)
    (addend : EllipticCurve.FullRange.Branch width → Fin count → G) (seed : G)
    (branch : EllipticCurve.FullRange.Branch width)
    (good : branch ∈ EllipticCurve.FullRange.admissibleBranches width count selected addend seed) :
    ExceptionalOffsetAveraging.Admissible count selected (addend branch) seed branch := by
  classical
  exact (Finset.mem_filter.mp good).2

def branchGood (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) : Prop :=
  branch ∈ EllipticCurve.FullRange.admissibleBranches (Cascade.exponentWidth I) 34
    (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
    (FullRange.chronologicalFixedSeed I).toGroupPoint

private lemma branchGood_implication (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    branch ∈ EllipticCurve.FullRange.admissibleBranches (Cascade.exponentWidth I) 34
      (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
      (FullRange.chronologicalFixedSeed I).toGroupPoint →
    ExceptionalOffsetAveraging.Admissible 34 (FullRange.chronologicalSelected I)
      (FullRange.chronologicalAddend I branch)
      (FullRange.chronologicalFixedSeed I).toGroupPoint branch :=
  admissible_of_mem (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
    (FullRange.chronologicalAddend I) (FullRange.chronologicalFixedSeed I).toGroupPoint branch

attribute [local irreducible] EllipticCurve.FullRange.admissibleBranches

lemma branchGood_admissible (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) :
    ExceptionalOffsetAveraging.Admissible 34 (FullRange.chronologicalSelected I)
      (FullRange.chronologicalAddend I branch)
      (FullRange.chronologicalFixedSeed I).toGroupPoint branch := by
  unfold branchGood at good
  exact branchGood_implication I branch good

attribute [local irreducible] branchGood

def prefixGroup (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (processed : Nat) :
    (DomainParameters.curve I.curveCert).GroupPoint :=
  (FullRange.chronologicalFixedSeed I).toGroupPoint *
    ExceptionalOffsetAveraging.prefixMultiplier 34 (FullRange.chronologicalSelected I)
      (FullRange.chronologicalAddend I branch) branch processed

lemma prefixGroup_nonidentity (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch)
    (processed : Nat) (within : processed ≤ 34) : prefixGroup I branch processed ≠ 1 :=
  admissible_prefix_nonidentity 34 (FullRange.chronologicalSelected I)
    (FullRange.chronologicalAddend I branch) (FullRange.chronologicalFixedSeed I).toGroupPoint
    branch (FullRange.chronologicalFixedSeed_original_subgroup I).2
    (branchGood_admissible I branch good) processed within

def prefixAffine (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch)
    (processed : Nat) (within : processed ≤ 34) :
    PrimeFieldShortWeierstrass.AffinePoint (DomainParameters.curve I.curveCert) :=
  Cascade.affineRepresentative (prefixGroup I branch processed)
    (prefixGroup_nonidentity I branch good processed within)

lemma prefixAffine_group (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch)
    (processed : Nat) (within : processed ≤ 34) :
    (prefixAffine I branch good processed within).toGroupPoint = prefixGroup I branch processed :=
  Cascade.affineRepresentative_toGroupPoint _ _

lemma groupPoint_mul_toMathlib {p : Nat}
    (curve : PrimeFieldShortWeierstrass p) (first last : curve.GroupPoint) :
    letI : Fact p.Prime := ⟨curve.prime⟩
    (first * last).toMathlib = first.toMathlib + last.toMathlib := by
  let : Fact p.Prime := ⟨curve.prime⟩
  have same := (groupPointEquiv curve).mulEquiv.map_mul first last
  change (first * last).toMathlib = first.toMathlib + last.toMathlib at same
  exact same

lemma groupPoint_inv_toMathlib {p : Nat}
    (curve : PrimeFieldShortWeierstrass p) (point : curve.GroupPoint) :
    letI : Fact p.Prime := ⟨curve.prime⟩
    (point⁻¹).toMathlib = -point.toMathlib := by
  let : Fact p.Prime := ⟨curve.prime⟩
  have same := (groupPointEquiv curve).mulEquiv.map_inv point
  change (point⁻¹).toMathlib = -point.toMathlib at same
  exact same

lemma groupPoint_mathlib_injective {p : Nat}
    (curve : PrimeFieldShortWeierstrass p) :
    Function.Injective (GroupPoint.toMathlib (E := curve)) := by
  intro first last same
  cases first
  cases last
  cases same
  rfl

lemma prefixGroup_next (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 34) :
    prefixGroup I branch (position.val + 1) =
      prefixGroup I branch position.val * FullRange.chronologicalAddend I branch position := by
  unfold prefixGroup
  rw [ExceptionalOffsetAveraging.prefixMultiplier_succ 34
    (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I branch)
    branch position.val position.isLt]
  cases selected : FullRange.chronologicalSelected I branch position with
  | true => rw [if_pos rfl, mul_assoc]
  | false =>
      rw [if_neg (by decide),
        FullRange.chronologicalAddend_zero I branch position selected, mul_one]

lemma prefixAffine_toMathlib (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (processed : Nat) (within : processed ≤ 34) :
    (prefixAffine I branch good processed within).toMathlib =
      (prefixGroup I branch processed).toMathlib :=
  congrArg GroupPoint.toMathlib (prefixAffine_group I branch good processed within)

def chronologicalBasePoint (I : DomainParameters.PublicKeyInstance)
    (position : Fin 34) : (DomainParameters.curve I.curveCert).MathlibPoint := by
  letI : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  exact Fin.addCases (m := 17) (n := 17)
    (fun row => (2 ^ (16 * row.rev.val)) •
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib)
    (fun row => (2 ^ (16 * row.rev.val)) • (-I.publicKey.toMathlib)) position

lemma chronologicalBasePoint_addend (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 34) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (FullRange.chronologicalAddend I branch position).toMathlib =
      FullRange.chronologicalAddress I branch position • chronologicalBasePoint I position := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  refine Fin.addCases (m := 17) (n := 17) (fun row => ?_) (fun row => ?_) position
  · simpa only [chronologicalBasePoint, Fin.addCases_left] using
      chronologicalAddend_first_toMathlib I branch row
  · simpa only [chronologicalBasePoint, Fin.addCases_right] using
      chronologicalAddend_second_toMathlib I branch row

lemma chronologicalBasePoint_order (I : DomainParameters.PublicKeyInstance)
    (position : Fin 34) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    addOrderOf (chronologicalBasePoint I position) = DomainParameters.subgroupOrder := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  refine Fin.addCases (m := 17) (n := 17) (fun row => ?_) (fun row => ?_) position
  · simpa only [chronologicalBasePoint, Fin.addCases_left] using
      baseRow_addOrderOf I row.rev.val
  · simpa only [chronologicalBasePoint, Fin.addCases_right] using
      inverseTargetRow_addOrderOf I row.rev.val

lemma prefixAffine_next (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (position : Fin 34) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (prefixAffine I branch good (position.val + 1)
      (Nat.succ_le_of_lt position.isLt)).toMathlib =
      (prefixAffine I branch good position.val position.isLt.le).toMathlib +
        FullRange.chronologicalAddress I branch position •
          chronologicalBasePoint I position := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  rw [prefixAffine_toMathlib, prefixAffine_toMathlib, prefixGroup_next,
    groupPoint_mul_toMathlib, chronologicalBasePoint_addend]

lemma prefixAffine_exclusions (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (position : Fin 34)
    (enabled : FullRange.chronologicalSelected I branch position = true) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (prefixAffine I branch good position.val position.isLt.le).toMathlib ≠
        FullRange.chronologicalAddress I branch position • chronologicalBasePoint I position ∧
      (prefixAffine I branch good position.val position.isLt.le).toMathlib ≠
        -(FullRange.chronologicalAddress I branch position •
          chronologicalBasePoint I position) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  have admissible := branchGood_admissible I branch good
  have exclusions := admissible position enabled
  change prefixGroup I branch position.val ≠ _ ∧
    prefixGroup I branch position.val ≠ _ at exclusions
  rw [prefixAffine_toMathlib, ← chronologicalBasePoint_addend]
  constructor
  · intro same
    exact exclusions.1 (groupPoint_mathlib_injective _ same)
  · intro same
    apply exclusions.2
    apply groupPoint_mathlib_injective (DomainParameters.curve I.curveCert)
    exact same.trans (groupPoint_inv_toMathlib _ _).symm

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
