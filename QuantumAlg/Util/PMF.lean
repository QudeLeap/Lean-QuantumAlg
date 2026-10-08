/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Combinatorics
import all QuantumAlg.Util.Combinatorics
public import Mathlib.Data.Vector.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Uniform

/-!
# Probability-mass combinatorics

Algorithm-independent constructions and event-mass identities for independent
sampling. This module has no dependency on an algorithm-specific execution
layer.
-/

section

namespace QuantumAlg

namespace PMF

noncomputable section

/-- Independently sample one PMF a fixed number of times. -/
public def independentReplicate {Sample : Type} (distribution : PMF Sample) :
    Nat → PMF (List Sample)
  | 0 => PMF.pure []
  | count + 1 =>
      distribution.bind fun sample =>
        (independentReplicate distribution count).map (List.cons sample)

/-- Independently sample one PMF while retaining the sample count in its type. -/
public def independentReplicateVector {Sample : Type} (distribution : PMF Sample) :
    (count : Nat) → PMF (List.Vector Sample count)
  | 0 => PMF.pure List.Vector.nil
  | count + 1 =>
      distribution.bind fun sample =>
        (independentReplicateVector distribution count).map
          (List.Vector.cons sample)

public theorem independentReplicateVector_toList {Sample : Type}
    (distribution : PMF Sample) (count : Nat) :
    (independentReplicateVector distribution count).map List.Vector.toList =
      independentReplicate distribution count := by
  induction count with
  | zero =>
      simpa [independentReplicateVector, independentReplicate] using
        (PMF.pure_map (f := List.Vector.toList) List.Vector.nil)
  | succ count ih =>
      simp only [independentReplicateVector, independentReplicate, PMF.map_bind]
      apply congrArg (PMF.bind distribution)
      funext sample
      calc
        ((independentReplicateVector distribution count).map
            (List.Vector.cons sample)).map List.Vector.toList =
            (independentReplicateVector distribution count).map
              (List.Vector.toList ∘ List.Vector.cons sample) :=
          PMF.map_comp _ _ _
        _ = (independentReplicateVector distribution count).map
              (List.cons sample ∘ List.Vector.toList) := by
          congr 1
        _ = ((independentReplicateVector distribution count).map
              List.Vector.toList).map (List.cons sample) :=
          (PMF.map_comp _ _ _).symm
        _ = (independentReplicate distribution count).map
              (List.cons sample) := by rw [ih]

public theorem independentReplicateVector_map_toList {Sample Target : Type}
    (distribution : PMF Sample) (count : Nat)
    (projection : List Sample → Target) :
    (independentReplicateVector distribution count).map
        (projection ∘ List.Vector.toList) =
      (independentReplicate distribution count).map projection := by
  rw [← PMF.map_comp, independentReplicateVector_toList]

public theorem independentReplicateVector_map {Sample Target : Type}
    (distribution : PMF Sample) (projection : Sample → Target) :
    ∀ count,
      (independentReplicateVector distribution count).map
          (fun samples => samples.map projection) =
        independentReplicateVector (distribution.map projection) count
  | 0 => by
      simpa [independentReplicateVector] using
        (PMF.pure_map (f := fun samples : List.Vector Sample 0 =>
          samples.map projection) List.Vector.nil)
  | count + 1 => by
      simp only [independentReplicateVector, PMF.map_bind, PMF.bind_map]
      apply congrArg (PMF.bind distribution)
      funext sample
      calc
        ((independentReplicateVector distribution count).map
            (List.Vector.cons sample)).map
              (fun samples => samples.map projection) =
            (independentReplicateVector distribution count).map
              (List.Vector.cons (projection sample) ∘
                fun samples => samples.map projection) := by
          rw [PMF.map_comp]
          congr 1
        _ = ((independentReplicateVector distribution count).map
              (fun samples => samples.map projection)).map
                (List.Vector.cons (projection sample)) := by
          rw [PMF.map_comp]
        _ = (independentReplicateVector
              (distribution.map projection) count).map
              (List.Vector.cons (projection sample)) := by
          rw [independentReplicateVector_map distribution projection count]

/-- An injective relabeling preserves the point mass of every source atom. -/
public theorem map_apply_of_injective {Sample Target : Type}
    (distribution : PMF Sample) (embedding : Sample → Target)
    (hinjective : Function.Injective embedding) (sample : Sample) :
    (distribution.map embedding) (embedding sample) = distribution sample := by
  rw [PMF.map_apply]
  refine (tsum_eq_single sample ?_).trans ?_
  · intro candidate hcandidate
    rw [if_neg]
    exact hinjective.ne hcandidate.symm
  · simp

/-- A list of independent samples contains a successful draw. -/
public def ContainsEvent {Sample : Type} (event : Sample → Prop)
    (samples : List Sample) : Prop :=
  ∃ sample ∈ samples, event sample

/-- Number of samples satisfying one event. -/
noncomputable def EventCount {Sample : Type} (event : Sample → Prop)
    (samples : List Sample) : Nat := by
  classical
  exact (samples.filter event).length

@[simp] theorem eventCount_nil {Sample : Type} (event : Sample → Prop) :
    EventCount event [] = 0 := by
  simp [EventCount]

theorem eventCount_cons_of_true {Sample : Type} (event : Sample → Prop)
    (sample : Sample) (samples : List Sample) (hsample : event sample) :
    EventCount event (sample :: samples) = EventCount event samples + 1 := by
  classical
  simp [EventCount, hsample]

theorem eventCount_cons_of_false {Sample : Type} (event : Sample → Prop)
    (sample : Sample) (samples : List Sample) (hsample : ¬ event sample) :
    EventCount event (sample :: samples) = EventCount event samples := by
  classical
  simp [EventCount, hsample]

/-- A transcript contains at least two event occurrences. -/
def AtLeastTwoEvents {Sample : Type} (event : Sample → Prop)
    (samples : List Sample) : Prop :=
  2 ≤ EventCount event samples

/-- Two independent draws from one probability mass function. -/
def independentPair {Sample : Type} (distribution : PMF Sample) :
    PMF (Sample × Sample) :=
  distribution.bind fun first => distribution.map fun second => (first, second)

/-- Point mass of two independent draws on an arbitrary sample space. -/
theorem independentPair_apply {Sample : Type}
    (distribution : PMF Sample) (pair : Sample × Sample) :
    independentPair distribution pair =
      distribution pair.1 * distribution pair.2 := by
  rcases pair with ⟨first, second⟩
  rw [independentPair, PMF.bind_apply]
  refine (tsum_eq_single first ?_).trans ?_
  · intro candidate hcandidate
    have hmap :
        (distribution.map fun value => (candidate, value)) (first, second) = 0 := by
      rw [PMF.map_apply]
      simp [hcandidate.symm]
    rw [hmap, mul_zero]
  · rw [PMF.map_apply_of_injective distribution
      (fun value => (first, value))]
    intro left right heq
    exact congrArg Prod.snd heq

/-- Point mass of two independent draws on a finite sample space. -/
theorem independentPair_apply_fintype {Sample : Type} [Finite Sample]
    (distribution : PMF Sample) (pair : Sample × Sample) :
    independentPair distribution pair =
      distribution pair.1 * distribution pair.2 := by
  classical
  let _ := Fintype.ofFinite Sample
  rcases pair with ⟨first, second⟩
  rw [independentPair, PMF.bind_apply]
  simp only [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single first]
  · rw [Finset.sum_eq_single second]
    · simp
    · intro candidate _hcandidate hne
      simp [hne.symm]
    · simp
  · intro candidate _hcandidate hne
    simp [hne.symm]
  · simp

/-- Exact integral form of a relation event under two independent draws. -/
theorem independentPair_eventProbability_eq {Sample : Type}
    (distribution : PMF Sample) (relation : Sample × Sample → Prop) :
    (independentPair distribution).toOuterMeasure {pair | relation pair} =
      ∑' first, distribution first *
        distribution.toOuterMeasure {second | relation (first, second)} := by
  rw [independentPair, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro first
  congr 1
  rw [PMF.toOuterMeasure_map_apply]
  apply congrArg distribution.toOuterMeasure
  ext second
  simp

/-- Mapping both coordinates of an independent pair is the independent pair
of the mapped distribution. -/
theorem independentPair_map {Sample Target : Type}
    (distribution : PMF Sample) (projection : Sample → Target) :
    (independentPair distribution).map
        (fun pair => (projection pair.1, projection pair.2)) =
      independentPair (distribution.map projection) := by
  simp [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- A transcript contains an unordered pair satisfying `relation`. -/
def HasPair {Sample : Type} (relation : Sample × Sample → Prop)
    (samples : List Sample) : Prop :=
  ∃ pair ∈ samples.unorderedPairs, relation pair

theorem hasPair_cons {Sample : Type} (relation : Sample × Sample → Prop)
    (head : Sample) (tail : List Sample) :
    HasPair relation (head :: tail) ↔
      ContainsEvent (fun second => relation (head, second)) tail ∨
        HasPair relation tail := by
  constructor
  · rintro ⟨pair, hpair, hrelation⟩
    rw [List.unorderedPairs_cons, List.mem_append] at hpair
    rcases hpair with hhead | htail
    · rcases List.mem_map.mp hhead with ⟨second, hsecond, rfl⟩
      exact Or.inl ⟨second, hsecond, hrelation⟩
    · exact Or.inr ⟨pair, htail, hrelation⟩
  · rintro (⟨second, hsecond, hrelation⟩ | ⟨pair, hpair, hrelation⟩)
    · refine ⟨(head, second), ?_, hrelation⟩
      rw [List.unorderedPairs_cons, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨second, hsecond, rfl⟩)
    · refine ⟨pair, ?_, hrelation⟩
      rw [List.unorderedPairs_cons, List.mem_append]
      exact Or.inr hpair

/-- At least two event occurrences determine an unordered transcript pair
whose two coordinates both satisfy the event. -/
theorem hasPair_sameEvent_of_atLeastTwo {Sample : Type}
    (event : Sample → Prop) (samples : List Sample)
    (htwo : AtLeastTwoEvents event samples) :
    HasPair (fun pair => event pair.1 ∧ event pair.2) samples := by
  classical
  induction samples with
  | nil =>
      simp [AtLeastTwoEvents, EventCount] at htwo
  | cons head tail ih =>
      rw [hasPair_cons]
      by_cases hhead : event head
      · left
        have htailPos : 0 < EventCount event tail := by
          unfold AtLeastTwoEvents at htwo
          rw [eventCount_cons_of_true event head tail hhead] at htwo
          omega
        have htailEvent : ContainsEvent event tail := by
          by_contra hnone
          have hzero : EventCount event tail = 0 := by
            simpa [EventCount, ContainsEvent] using hnone
          omega
        rcases htailEvent with ⟨second, hmem, hsecond⟩
        exact ⟨second, hmem, hhead, hsecond⟩
      · right
        apply ih
        unfold AtLeastTwoEvents at htwo ⊢
        rw [eventCount_cons_of_false event head tail hhead] at htwo
        exact htwo

/-- Relabeling every entry of an iid transcript is the iid transcript of the
relabelled one-draw distribution. -/
theorem independentReplicate_map {Sample Target : Type}
    (distribution : PMF Sample) (projection : Sample → Target) : ∀ count,
    (independentReplicate distribution count).map (List.map projection) =
      independentReplicate (distribution.map projection) count
  | 0 => by
      simpa [independentReplicate] using
        (PMF.pure_map (f := List.map projection) ([] : List Sample))
  | count + 1 => by
      simp only [independentReplicate, PMF.map_bind, PMF.bind_map]
      apply congrArg (PMF.bind distribution)
      funext sample
      calc
        ((independentReplicate distribution count).map
            (List.cons sample)).map (List.map projection) =
          (independentReplicate distribution count).map
            (List.cons (projection sample) ∘ List.map projection) := by
              rw [PMF.map_comp]
              congr 1
        _ = ((independentReplicate distribution count).map
              (List.map projection)).map
                (List.cons (projection sample)) := by
              rw [PMF.map_comp]
        _ = (independentReplicate (distribution.map projection) count).map
              (List.cons (projection sample)) := by
                rw [independentReplicate_map distribution projection count]

/-- The probability that both coordinates of an independent pair satisfy one
event is the square of the one-draw event mass. -/
theorem independentPair_sameEventProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) :
    (independentPair distribution).toOuterMeasure
        {pair | event pair.1 ∧ event pair.2} =
      distribution.toOuterMeasure {sample | event sample} ^ 2 := by
  classical
  rw [independentPair, PMF.toOuterMeasure_bind_apply]
  have hsecond (first : Sample) :
      (distribution.map fun second => (first, second)).toOuterMeasure
          {pair | event pair.1 ∧ event pair.2} =
        if event first then distribution.toOuterMeasure {sample | event sample}
        else 0 := by
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hfirst : event first
    · rw [if_pos hfirst]
      apply congrArg distribution.toOuterMeasure
      ext second
      simp [hfirst]
    · rw [if_neg hfirst]
      simp [hfirst]
  simp_rw [hsecond]
  rw [pow_two]
  calc
    (∑' first, distribution first *
        if event first then distribution.toOuterMeasure {sample | event sample}
        else 0) =
      ∑' first, (if event first then distribution first else 0) *
        distribution.toOuterMeasure {sample | event sample} := by
          apply tsum_congr
          intro first
          by_cases hfirst : event first <;> simp [hfirst]
    _ = (∑' first, if event first then distribution first else 0) *
        distribution.toOuterMeasure {sample | event sample} := by
          rw [ENNReal.tsum_mul_right]
    _ = distribution.toOuterMeasure {sample | event sample} *
        distribution.toOuterMeasure {sample | event sample} := by
          rw [PMF.toOuterMeasure_apply]
          congr 1

/-- Point mass of two independent draws from the finite uniform PMF. -/
theorem independentPair_uniformOfFintype_apply (Sample : Type)
    [Fintype Sample] [Nonempty Sample] (pair : Sample × Sample) :
    independentPair (PMF.uniformOfFintype Sample) pair =
      (Fintype.card Sample : ENNReal)⁻¹ *
        (Fintype.card Sample : ENNReal)⁻¹ := by
  classical
  rcases pair with ⟨first, second⟩
  rw [independentPair, PMF.bind_apply]
  simp only [PMF.uniformOfFintype_apply, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single first]
  · rw [Finset.sum_eq_single second]
    · simp
    · intro candidate _hmem hne
      simp [hne.symm]
    · simp
  · intro candidate _hmem hne
    simp [hne.symm]
  · simp

/-- Exact mass of a finite event under two independent finite-uniform draws. -/
theorem independentPair_uniformOfFintype_finset (Sample : Type)
    [Fintype Sample] [Nonempty Sample]
    (event : Finset (Sample × Sample)) :
    (independentPair (PMF.uniformOfFintype Sample)).toOuterMeasure event =
      event.card * ((Fintype.card Sample : ENNReal)⁻¹ *
        (Fintype.card Sample : ENNReal)⁻¹) := by
  classical
  rw [PMF.toOuterMeasure_apply_finset]
  simp_rw [independentPair_uniformOfFintype_apply]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Every element of a supported independent-retry transcript belongs to the
support of the one-attempt distribution. -/
theorem independentReplicate_support_forall {Sample : Type}
    (distribution : PMF Sample) (count : Nat) {samples : List Sample}
    (hsupport : samples ∈ (independentReplicate distribution count).support) :
    ∀ sample ∈ samples, sample ∈ distribution.support := by
  induction count generalizing samples with
  | zero =>
      simp [independentReplicate] at hsupport
      subst samples
      simp
  | succ count ih =>
      rw [independentReplicate, PMF.mem_support_bind_iff] at hsupport
      rcases hsupport with ⟨head, hhead, htailMap⟩
      rw [PMF.mem_support_map_iff] at htailMap
      rcases htailMap with ⟨tail, htail, hcons⟩
      subst samples
      intro sample hmem
      rcases List.mem_cons.mp hmem with hsample | hsample
      · subst sample
        exact hhead
      · exact ih htail sample hsample

/-- Every supported transcript of `count` independent draws has exactly
`count` entries. -/
theorem independentReplicate_support_length {Sample : Type}
    (distribution : PMF Sample) (count : Nat) {samples : List Sample}
    (hsupport : samples ∈ (independentReplicate distribution count).support) :
    samples.length = count := by
  induction count generalizing samples with
  | zero =>
      simp [independentReplicate] at hsupport
      subst samples
      rfl
  | succ count ih =>
      rw [independentReplicate, PMF.mem_support_bind_iff] at hsupport
      rcases hsupport with ⟨head, _hhead, htailMap⟩
      rw [PMF.mem_support_map_iff] at htailMap
      rcases htailMap with ⟨tail, htail, hcons⟩
      subst samples
      simp [ih htail]

/-- A bind inherits a conditional event floor from every nonexceptional input
branch, weighted by the input mass outside the exceptional event. -/
theorem bind_eventProbability_ge_goodMass_mul
    {Input Output : Type} (distribution : PMF Input)
    (kernel : Input → PMF Output) (exceptional : Input → Prop)
    (event : Output → Prop) (floor : ENNReal)
    (hbranch : ∀ input, ¬ exceptional input →
      floor ≤ (kernel input).toOuterMeasure {output | event output}) :
    distribution.toOuterMeasure {input | ¬ exceptional input} * floor ≤
      (distribution.bind kernel).toOuterMeasure {output | event output} := by
  classical
  calc
    distribution.toOuterMeasure {input | ¬ exceptional input} * floor =
        (∑' input, if ¬ exceptional input then distribution input else 0) *
          floor := by
      rw [PMF.toOuterMeasure_apply]
      congr 1
      apply tsum_congr
      intro input
      simp [Set.indicator]
    _ = ∑' input,
        (if ¬ exceptional input then distribution input else 0) * floor := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ ∑' input, distribution input *
        (kernel input).toOuterMeasure {output | event output} := by
      apply ENNReal.tsum_le_tsum
      intro input
      by_cases hexceptional : exceptional input
      · simp [hexceptional]
      · simp only [hexceptional, not_false_eq_true, if_true]
        exact mul_le_mul_right (hbranch input hexceptional) _
    _ = (distribution.bind kernel).toOuterMeasure
        {output | event output} :=
      (PMF.toOuterMeasure_bind_apply
        distribution kernel {output | event output}).symm

/-- A union-bound lower success estimate is no larger than the product of two
independent complement estimates.  This form is useful when one failure event
is outside a retry loop and the other is amplified inside it. -/
theorem one_sub_add_le_mul_one_sub (firstFailure secondFailure : ENNReal) :
    1 - (firstFailure + secondFailure) ≤
      (1 - firstFailure) * (1 - secondFailure) := by
  rw [tsub_add_eq_tsub_tsub]
  calc
    1 - firstFailure - secondFailure ≤
        1 - firstFailure - ((1 - firstFailure) * secondFailure) := by
      apply tsub_le_tsub_left
      simpa [mul_comm] using
        mul_le_mul_right (tsub_le_self : 1 - firstFailure ≤ 1)
          secondFailure
    _ = (1 - firstFailure) * (1 - secondFailure) := by
      rw [ENNReal.mul_sub (by
        intro _ _
        exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
      simp

/-- The probability that one PMF satisfies an event is one minus the
probability of its complement. -/
theorem eventProbability_eq_one_sub_complement {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) :
    distribution.toOuterMeasure {sample | event sample} =
      1 - distribution.toOuterMeasure {sample | ¬ event sample} := by
  let _ : MeasurableSpace Sample := ⊤
  have hevent : MeasurableSet {sample | event sample} := by
    exact MeasurableSet.of_discrete
  have hfailure : MeasurableSet {sample | ¬ event sample} := by
    exact MeasurableSet.of_discrete
  have hcomplement :
      {sample | event sample} = {sample | ¬ event sample}ᶜ := by
    ext sample
    simp
  rw [← distribution.toMeasure_apply_eq_toOuterMeasure_apply hevent,
    hcomplement, MeasureTheory.measure_compl hfailure (by simp),
    MeasureTheory.measure_univ,
    distribution.toMeasure_apply_eq_toOuterMeasure_apply hfailure]

/-- A finite union of events under a PMF has mass at most the sum of the
individual event masses. This uses outer-measure subadditivity, so it needs
no measurability assumptions on the events. -/
theorem toOuterMeasure_exists_le_sum {Sample Index : Type}
    [Fintype Index] (distribution : PMF Sample)
    (event : Index → Sample → Prop) :
    distribution.toOuterMeasure {sample | ∃ index, event index sample} ≤
      ∑ index, distribution.toOuterMeasure {sample | event index sample} := by
  classical
  simpa only [Set.ofPred_exists] using
    (MeasureTheory.measure_iUnion_fintype_le distribution.toOuterMeasure
      (fun index => {sample | event index sample}))

/-- Union bound for seeing an event in a fixed number of independent draws. -/
theorem independentReplicate_containsEventProbability_le {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | ContainsEvent event samples} ≤
      (count : ENNReal) *
        distribution.toOuterMeasure {sample | event sample} := by
  classical
  induction count with
  | zero =>
      simp [independentReplicate, ContainsEvent]
  | succ count ih =>
      rw [independentReplicate, PMF.toOuterMeasure_bind_apply]
      let tailMass :=
        (independentReplicate distribution count).toOuterMeasure
          {samples | ContainsEvent event samples}
      let successMass :=
        distribution.toOuterMeasure {sample | event sample}
      have hmap (sample : Sample) :
          ((independentReplicate distribution count).map
              (List.cons sample)).toOuterMeasure
              {samples | ContainsEvent event samples} =
            if event sample then 1 else tailMass := by
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hsample : event sample
        · rw [if_pos hsample]
          exact ((independentReplicate distribution count).toOuterMeasure_apply_eq_one_iff
            _).2 (by simp [ContainsEvent, hsample])
        · rw [if_neg hsample]
          apply congrArg (fun set : Set (List Sample) =>
            (independentReplicate distribution count).toOuterMeasure set)
          ext samples
          simp [ContainsEvent, hsample]
      simp_rw [hmap]
      have hsuccessTsum :
          (∑' sample, if event sample then distribution sample else 0) =
            successMass := by
        dsimp [successMass]
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro sample
        simp [Set.indicator]
      have hfailureTsum :
          (∑' sample, if ¬ event sample then distribution sample else 0) =
            distribution.toOuterMeasure {sample | ¬ event sample} := by
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro sample
        simp [Set.indicator]
      have hfailureLeOne :
          distribution.toOuterMeasure {sample | ¬ event sample} ≤ 1 := by
        calc
          distribution.toOuterMeasure {sample | ¬ event sample} ≤
              distribution.toOuterMeasure Set.univ :=
            distribution.toOuterMeasure.mono (Set.subset_univ _)
          _ = 1 := by
            rw [PMF.toOuterMeasure_apply]
            simp
      calc
        (∑' sample, distribution sample *
            if event sample then 1 else tailMass) =
            (∑' sample, if event sample then distribution sample else 0) +
              (∑' sample, if ¬ event sample then distribution sample else 0) *
                tailMass := by
          rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          apply tsum_congr
          intro sample
          by_cases hsample : event sample <;> simp [hsample]
        _ = successMass +
              distribution.toOuterMeasure {sample | ¬ event sample} *
                tailMass := by
          rw [hsuccessTsum, hfailureTsum]
        _ ≤ successMass + tailMass := by
          simpa [add_comm, mul_comm] using add_le_add_left
            (mul_le_mul_right hfailureLeOne tailMass) successMass
        _ ≤ successMass + (count : ENNReal) * successMass := by
          simpa [tailMass, successMass, add_comm] using
            add_le_add_left ih successMass
        _ = ((count + 1 : Nat) : ENNReal) * successMass := by
          push_cast
          ring

/-- Pair-union bound for a fixed number of independent draws.  Every
unordered position pair has the same `independentPair` marginal. -/
theorem independentReplicate_hasPairProbability_le {Sample : Type}
    (distribution : PMF Sample) (relation : Sample × Sample → Prop)
    (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | HasPair relation samples} ≤
      (count.choose 2 : ENNReal) *
        (independentPair distribution).toOuterMeasure
          {pair | relation pair} := by
  classical
  induction count with
  | zero =>
      simp [independentReplicate, HasPair]
  | succ count ih =>
      rw [independentReplicate, PMF.toOuterMeasure_bind_apply]
      let tailPairMass :=
        (independentReplicate distribution count).toOuterMeasure
          {samples | HasPair relation samples}
      let pairMass :=
        (independentPair distribution).toOuterMeasure
          {pair | relation pair}
      let secondMass (head : Sample) :=
        distribution.toOuterMeasure {second | relation (head, second)}
      have hmapLe (head : Sample) :
          ((independentReplicate distribution count).map
              (List.cons head)).toOuterMeasure
              {samples | HasPair relation samples} ≤
            (independentReplicate distribution count).toOuterMeasure
                {samples |
                  ContainsEvent (fun second => relation (head, second)) samples} +
              tailPairMass := by
        rw [PMF.toOuterMeasure_map_apply]
        have hevent :
            List.cons head ⁻¹' {samples | HasPair relation samples} =
              {samples |
                ContainsEvent (fun second => relation (head, second)) samples} ∪
                {samples | HasPair relation samples} := by
          ext samples
          exact hasPair_cons relation head samples
        rw [hevent]
        exact MeasureTheory.measure_union_le _ _
      have hsecond (head : Sample) :
          (independentReplicate distribution count).toOuterMeasure
              {samples |
                ContainsEvent (fun second => relation (head, second)) samples} ≤
            (count : ENNReal) * secondMass head :=
        independentReplicate_containsEventProbability_le distribution
          (fun second => relation (head, second)) count
      calc
        (∑' head, distribution head *
            ((independentReplicate distribution count).map
              (List.cons head)).toOuterMeasure
                {samples | HasPair relation samples}) ≤
            ∑' head, distribution head *
              ((count : ENNReal) * secondMass head + tailPairMass) := by
          apply ENNReal.tsum_le_tsum
          intro head
          exact mul_le_mul_right ((hmapLe head).trans (by
            simpa [add_comm] using
              add_le_add_right (hsecond head) tailPairMass)) _
        _ = (count : ENNReal) * pairMass + tailPairMass := by
          have hfirst :
              (∑' head, distribution head *
                  ((count : ENNReal) * secondMass head)) =
                (count : ENNReal) * pairMass := by
            calc
              (∑' head, distribution head *
                  ((count : ENNReal) * secondMass head)) =
                  ∑' head, (count : ENNReal) *
                    (distribution head * secondMass head) := by
                apply tsum_congr
                intro head
                ring
              _ = (count : ENNReal) *
                    ∑' head, distribution head * secondMass head := by
                rw [ENNReal.tsum_mul_left]
              _ = (count : ENNReal) * pairMass := by
                dsimp [pairMass, secondMass]
                rw [independentPair_eventProbability_eq]
          have htail :
              (∑' head, distribution head * tailPairMass) =
                tailPairMass := by
            rw [ENNReal.tsum_mul_right, distribution.tsum_coe, one_mul]
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, hfirst, htail]
        _ ≤ (count : ENNReal) * pairMass +
              (count.choose 2 : ENNReal) * pairMass := by
          simpa [tailPairMass, pairMass] using
            add_le_add_right ih ((count : ENNReal) * pairMass)
        _ = ((count + 1).choose 2 : ENNReal) * pairMass := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          push_cast
          ring

/-- Exact failure probability for a fixed number of independent samples. -/
theorem independentReplicate_failureProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | ¬ ContainsEvent event samples} =
      (distribution.toOuterMeasure {sample | ¬ event sample}) ^ count := by
  classical
  induction count with
  | zero =>
      simp [independentReplicate, ContainsEvent]
  | succ count ih =>
      rw [independentReplicate, PMF.toOuterMeasure_bind_apply]
      have hmap (sample : Sample) :
          ((independentReplicate distribution count).map
              (List.cons sample)).toOuterMeasure
              {samples | ¬ ContainsEvent event samples} =
            if event sample then 0
            else
              (independentReplicate distribution count).toOuterMeasure
                {samples | ¬ ContainsEvent event samples} := by
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hsample : event sample
        · simp [ContainsEvent, hsample]
        · rw [if_neg hsample]
          apply congrArg (fun set : Set (List Sample) =>
            (independentReplicate distribution count).toOuterMeasure set)
          ext samples
          simp [ContainsEvent, hsample]
      simp_rw [hmap]
      have hfailure_tsum :
          (∑' sample, if ¬ event sample then distribution sample else 0) =
            distribution.toOuterMeasure {sample | ¬ event sample} := by
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro sample
        simp [Set.indicator]
      calc
        (∑' sample, distribution sample *
            if event sample then 0
            else
              (independentReplicate distribution count).toOuterMeasure
                {samples | ¬ ContainsEvent event samples}) =
            ∑' sample,
              (if ¬ event sample then distribution sample else 0) *
                (independentReplicate distribution count).toOuterMeasure
                  {samples | ¬ ContainsEvent event samples} := by
              apply tsum_congr
              intro sample
              by_cases hsample : event sample <;> simp [hsample]
        _ = (∑' sample, if ¬ event sample then distribution sample else 0) *
              (independentReplicate distribution count).toOuterMeasure
                {samples | ¬ ContainsEvent event samples} := by
              rw [ENNReal.tsum_mul_right]
        _ = distribution.toOuterMeasure {sample | ¬ event sample} *
              (independentReplicate distribution count).toOuterMeasure
                {samples | ¬ ContainsEvent event samples} := by
              rw [hfailure_tsum]
        _ = (distribution.toOuterMeasure {sample | ¬ event sample}) ^
              (count + 1) := by
              rw [ih, pow_succ]
              ac_rfl

/-- The mass of fixed-count independent sample vectors whose every coordinate
satisfies an event is the corresponding one-draw event mass to that count. -/
theorem independentReplicateVector_allEventProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicateVector distribution count).toOuterMeasure
        {samples | ∀ sample ∈ samples.toList, event sample} =
      (distribution.toOuterMeasure {sample | event sample}) ^ count := by
  classical
  calc
    (independentReplicateVector distribution count).toOuterMeasure
        {samples | ∀ sample ∈ samples.toList, event sample} =
        (independentReplicateVector distribution count).toOuterMeasure
          (List.Vector.toList ⁻¹'
            {samples | ¬ ContainsEvent (fun sample => ¬ event sample) samples}) := by
          apply congrArg (fun set : Set (List.Vector Sample count) =>
            (independentReplicateVector distribution count).toOuterMeasure set)
          ext samples
          simp [ContainsEvent]
    _ = ((independentReplicateVector distribution count).map List.Vector.toList).toOuterMeasure
          {samples | ¬ ContainsEvent (fun sample => ¬ event sample) samples} := by
          rw [PMF.toOuterMeasure_map_apply]
    _ = (independentReplicate distribution count).toOuterMeasure
          {samples | ¬ ContainsEvent (fun sample => ¬ event sample) samples} := by
          rw [independentReplicateVector_toList]
    _ = (distribution.toOuterMeasure {sample | event sample}) ^ count := by
          simpa using
            (independentReplicate_failureProbability_eq distribution
              (fun sample => ¬ event sample) count)

/-- Exact probability that an independent transcript contains no occurrence
of the selected event. -/
theorem independentReplicate_zeroEventProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | EventCount event samples = 0} =
      (distribution.toOuterMeasure {sample | ¬ event sample}) ^ count := by
  rw [← independentReplicate_failureProbability_eq distribution event count]
  apply congrArg
  ext samples
  classical
  simp [EventCount, ContainsEvent]

/-- Exact probability that an independent transcript contains exactly one
occurrence of the selected event. -/
theorem independentReplicate_exactlyOneProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | EventCount event samples = 1} =
      (count : ENNReal) *
        distribution.toOuterMeasure {sample | event sample} *
        (distribution.toOuterMeasure {sample | ¬ event sample}) ^
          (count - 1) := by
  classical
  let successMass :=
    distribution.toOuterMeasure {sample | event sample}
  let failureMass :=
    distribution.toOuterMeasure {sample | ¬ event sample}
  induction count with
  | zero =>
      simp [independentReplicate, EventCount]
  | succ count ih =>
      rw [independentReplicate, PMF.toOuterMeasure_bind_apply]
      have hmap (sample : Sample) :
          ((independentReplicate distribution count).map
              (List.cons sample)).toOuterMeasure
              {samples | EventCount event samples = 1} =
            if event sample then failureMass ^ count
            else
              (count : ENNReal) * successMass *
                failureMass ^ (count - 1) := by
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hsample : event sample
        · rw [if_pos hsample,
            ← independentReplicate_zeroEventProbability_eq
              distribution event count]
          apply congrArg
          ext samples
          change EventCount event (sample :: samples) = 1 ↔
            EventCount event samples = 0
          rw [eventCount_cons_of_true event sample samples hsample]
          omega
        · rw [if_neg hsample, ← ih]
          apply congrArg
          ext samples
          change EventCount event (sample :: samples) = 1 ↔
            EventCount event samples = 1
          rw [eventCount_cons_of_false event sample samples hsample]
      simp_rw [hmap]
      have hsuccessTsum :
          (∑' sample, if event sample then distribution sample else 0) =
            successMass := by
        dsimp [successMass]
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro sample
        simp [Set.indicator]
      have hfailureTsum :
          (∑' sample, if ¬ event sample then distribution sample else 0) =
            failureMass := by
        dsimp [failureMass]
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro sample
        simp [Set.indicator]
      calc
        (∑' sample, distribution sample *
            if event sample then failureMass ^ count
            else
              (count : ENNReal) * successMass *
                failureMass ^ (count - 1)) =
            ∑' sample, (
              (if event sample then distribution sample else 0) *
                  failureMass ^ count +
                (if ¬ event sample then distribution sample else 0) *
                  ((count : ENNReal) * successMass *
                    failureMass ^ (count - 1))) := by
              apply tsum_congr
              intro sample
              by_cases hsample : event sample <;> simp [hsample]
        _ =
            (∑' sample, if event sample then distribution sample else 0) *
                failureMass ^ count +
              (∑' sample, if ¬ event sample then distribution sample else 0) *
                ((count : ENNReal) * successMass *
                  failureMass ^ (count - 1)) := by
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                ENNReal.tsum_mul_right]
        _ = successMass * failureMass ^ count +
              failureMass * ((count : ENNReal) * successMass *
                failureMass ^ (count - 1)) := by
              rw [hsuccessTsum, hfailureTsum]
        _ = ((count + 1 : Nat) : ENNReal) * successMass *
              failureMass ^ (count + 1 - 1) := by
              cases count with
              | zero => simp
              | succ count =>
                  simp [pow_succ]
                  ring

/-- Exact probability that an independent transcript contains fewer than two
occurrences of the selected event. -/
theorem independentReplicate_lessThanTwoProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | ¬ AtLeastTwoEvents event samples} =
      (distribution.toOuterMeasure {sample | ¬ event sample}) ^ count +
        (count : ENNReal) *
          distribution.toOuterMeasure {sample | event sample} *
          (distribution.toOuterMeasure {sample | ¬ event sample}) ^
            (count - 1) := by
  classical
  calc
    (independentReplicate distribution count).toOuterMeasure
        {samples | ¬ AtLeastTwoEvents event samples} =
      (independentReplicate distribution count).toOuterMeasure
          {samples | EventCount event samples = 0} +
        (independentReplicate distribution count).toOuterMeasure
          {samples | EventCount event samples = 1} := by
      simp only [PMF.toOuterMeasure_apply]
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro samples
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      by_cases hzero : EventCount event samples = 0
      · simp [AtLeastTwoEvents, hzero]
      · by_cases hone : EventCount event samples = 1
        · simp [AtLeastTwoEvents, hone]
        · have htwo : 2 ≤ EventCount event samples := by omega
          simp [AtLeastTwoEvents, hzero, hone, htwo]
    _ = _ := by
      rw [independentReplicate_zeroEventProbability_eq,
        independentReplicate_exactlyOneProbability_eq]

/-- Exact probability that an independent transcript contains at least two
occurrences of the selected event. -/
theorem independentReplicate_atLeastTwoProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | AtLeastTwoEvents event samples} =
      1 -
        ((distribution.toOuterMeasure {sample | ¬ event sample}) ^ count +
          (count : ENNReal) *
            distribution.toOuterMeasure {sample | event sample} *
            (distribution.toOuterMeasure {sample | ¬ event sample}) ^
              (count - 1)) := by
  rw [eventProbability_eq_one_sub_complement
    (independentReplicate distribution count) (AtLeastTwoEvents event)]
  rw [independentReplicate_lessThanTwoProbability_eq]

/-- Exact success probability for a fixed number of independent samples. -/
theorem independentReplicate_successProbability_eq {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat) :
    (independentReplicate distribution count).toOuterMeasure
        {samples | ContainsEvent event samples} =
      1 - (distribution.toOuterMeasure {sample | ¬ event sample}) ^ count := by
  let _ : MeasurableSpace (List Sample) := ⊤
  have hsuccess : MeasurableSet {samples | ContainsEvent event samples} := by
    exact MeasurableSet.of_discrete
  have hfailure :
      MeasurableSet {samples | ¬ ContainsEvent event samples} := by
    exact MeasurableSet.of_discrete
  have hcomplement :
      {samples | ContainsEvent event samples} =
        {samples | ¬ ContainsEvent event samples}ᶜ := by
    ext samples
    simp
  rw [← (independentReplicate distribution count).toMeasure_apply_eq_toOuterMeasure_apply
      hsuccess,
    hcomplement, MeasureTheory.measure_compl hfailure (by simp),
    MeasureTheory.measure_univ,
    (independentReplicate distribution count).toMeasure_apply_eq_toOuterMeasure_apply
      hfailure,
    independentReplicate_failureProbability_eq]

/-- Independent repetition amplifies a one-attempt success floor to any target
below the corresponding geometric failure bound. -/
public theorem independentReplicate_successProbability_ge {Sample : Type}
    (distribution : PMF Sample) (event : Sample → Prop) (count : Nat)
    (attemptFloor target : ENNReal)
    (hattempt : attemptFloor ≤
      distribution.toOuterMeasure {sample | event sample})
    (htarget : target ≤ 1 - (1 - attemptFloor) ^ count) :
    target ≤
      (independentReplicate distribution count).toOuterMeasure
        {samples | ContainsEvent event samples} := by
  rw [independentReplicate_successProbability_eq]
  apply htarget.trans
  apply tsub_le_tsub_left
  apply pow_le_pow_left'
  have hfailure :
      distribution.toOuterMeasure {sample | ¬ event sample} =
        1 - distribution.toOuterMeasure {sample | event sample} := by
    rw [eventProbability_eq_one_sub_complement distribution
      (fun sample => ¬ event sample)]
    congr 2
    ext sample
    simp
  rw [hfailure]
  exact tsub_le_tsub_left hattempt 1

end

end PMF

end QuantumAlg

end
