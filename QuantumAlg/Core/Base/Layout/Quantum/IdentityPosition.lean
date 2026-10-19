/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Layout.Quantum

/-!
# Locate the same physical systems in two layouts

Containment of physical identities selects the unique actual position of each
source system in a target layout. The resulting injection does not infer a
correspondence from Hilbert-space dimensions or rename any physical address.
-/

namespace QuantumAlg.QuantumLayout

noncomputable section

variable {small large : Nat} (source : QuantumLayout small) (target : QuantumLayout large)
  (contained : source.identities ⊆ target.identities)

include contained

private lemma position_exists (index : Fin small) :
    ∃ located : Fin large,
      (target.wire located).identity = (source.wire index).identity := by
  have sourceMember : (source.wire index).identity ∈ source.identities := by
    change _ ∈ List.ofFn (fun position : Fin small => (source.wire position).identity)
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  have targetMember := contained sourceMember
  change (source.wire index).identity ∈
    List.ofFn (fun position : Fin large => (target.wire position).identity) at targetMember
  exact List.mem_ofFn.mp targetMember

/-- Each source identity has exactly one target position. -/
def positionOfIdentity : Fin small ↪ Fin large where
  toFun index := (position_exists source target contained index).choose
  inj' := by
    intro left right same
    apply source.identityInjective
    have leftIdentity := (position_exists source target contained left).choose_spec
    have rightIdentity := (position_exists source target contained right).choose_spec
    exact leftIdentity.symm.trans ((congrArg (fun index : Fin large =>
      (target.wire index).identity) same).trans rightIdentity)

/-- The selected target wire has the literal physical identity of its source. -/
lemma positionOfIdentity_identity (index : Fin small) :
    (target.wire (positionOfIdentity source target contained index)).identity =
      (source.wire index).identity :=
  (position_exists source target contained index).choose_spec

/-- When both layouts contain the same identities, every target wire is selected. -/
lemma positionOfIdentity_surjective
    (reverse : target.identities ⊆ source.identities) :
    Function.Surjective (positionOfIdentity source target contained) := by
  intro targetIndex
  have targetMember : (target.wire targetIndex).identity ∈ target.identities := by
    change _ ∈ List.ofFn (fun position : Fin large => (target.wire position).identity)
    exact List.mem_ofFn.mpr ⟨targetIndex, rfl⟩
  have sourceMember := reverse targetMember
  change (target.wire targetIndex).identity ∈
    List.ofFn (fun position : Fin small => (source.wire position).identity) at sourceMember
  obtain ⟨sourceIndex, same⟩ := List.mem_ofFn.mp sourceMember
  refine ⟨sourceIndex, target.identityInjective ?_⟩
  exact (positionOfIdentity_identity source target contained sourceIndex).trans same

end

end QuantumAlg.QuantumLayout
