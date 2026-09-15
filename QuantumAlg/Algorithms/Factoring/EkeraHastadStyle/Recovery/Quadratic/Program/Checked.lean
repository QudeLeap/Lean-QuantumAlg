/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Exact execution after candidate initialization

The two complete checks and local first-accepted selection run before the
actual narrowed update of the original result. This equation composes those
same circuits on the complete incoming state and records their true paths;
it does not replace either stage with a predicate or store-only executor.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width resultWidth : Nat}

/-- The actual checked pair runs before the actual converted persistent selection. -/
def checkedBodyStep (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (store : Store (LocalLayout.context ctx width)) :
    Store (LocalLayout.context ctx width) × (checkedBody modulus original).Path :=
  let pair := LocalLayout.pairRefs modulus
  let checked := Pair.step pair store
  let narrowed := NarrowSelection.step (FirstAccepted.cellRead pair.selection.accepted)
    (FirstAccepted.cellRead pair.selection.selected) (LocalLayout.persistentRefs original width)
    checked.1
  (narrowed.1, (checked.2, narrowed.2))

/-- The exact checked body preserves every full incoming quantum-reference block. -/
theorem nativeQuadratic_checkedBody_execute
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (LocalLayout.context ctx width) Reference History) :
    (checkedBody modulus original).execute Reference state = state.mapClassical (fun entry =>
      ((checkedBodyStep modulus original entry.1).1,
        (entry.2, (checkedBodyStep modulus original entry.1).2))) := by
  let pair := LocalLayout.pairRefs modulus
  let eligible := FirstAccepted.cellRead pair.selection.accepted
  let candidate := FirstAccepted.cellRead pair.selection.selected
  let persistent := LocalLayout.persistentRefs original width
  refine (Circuit.execute_seq_mapClassical (Pair.code pair)
    (NarrowSelection.code eligible candidate persistent) (Pair.step pair)
    (NarrowSelection.step eligible candidate persistent)
    (Pair.nativeQuadratic_pair_execute pair)
    (NarrowSelection.nativeQuadratic_narrow_execute eligible candidate persistent)
    Reference state).trans ?_
  dsimp only [checkedBodyStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (LocalLayout.context ctx width) × History)
    (D := Store (LocalLayout.context ctx width) ×
      (History × (checkedBody modulus original).Path))
    (R := Register.prod (LocalLayout.context ctx width).register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (LocalLayout.context ctx width) × History)
    (D := Store (LocalLayout.context ctx width) ×
      (History × (checkedBody modulus original).Path))
    (R := Register.prod (LocalLayout.context ctx width).register Reference) _ state _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
