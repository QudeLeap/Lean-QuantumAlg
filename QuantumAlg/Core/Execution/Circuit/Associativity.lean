/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit.History
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Trace

/-!
# Exact reassociation of three actual circuit sections

Rebracketing changes the type of the recorded path, but not the ordered
instructions, weighted output state, actual event list, depth or live-space
peaks. The record equivalence retains every measurement and branch outcome.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

variable {model : ExecutionModel} {allowAllocation : Bool}
  {pre middle₁ middle₂ post : RuntimeCtx model.kind}
  (first : Circuit model pre middle₁ allowAllocation)
  (middle : Circuit model middle₁ middle₂ allowAllocation)
  (last : Circuit model middle₂ post allowAllocation)

/-- Reassociate only the complete path record of three unchanged sections. -/
def seqAssocPath : ((first.seq middle).seq last).Path ≃
    (first.seq (middle.seq last)).Path :=
  Equiv.prodAssoc _ _ _

/-- Relabel only the newly recorded path, leaving service and incoming history intact. -/
def seqAssocHistory {H : Type} :
    model.HiddenState × (H × (first.seq (middle.seq last)).Path) →
      model.HiddenState × (H × ((first.seq middle).seq last).Path) :=
  fun history => (history.1,
    (history.2.1, (seqAssocPath first middle last).symm history.2.2))

/-- The chronological native-event list is unchanged under reassociation. -/
lemma seqAssoc_eventTrace
    (path : ((first.seq middle).seq last).Path) :
    ((first.seq middle).seq last).eventTrace path =
      (first.seq (middle.seq last)).eventTrace
        (seqAssocPath first middle last path) := by
  rcases path with ⟨⟨left, center⟩, right⟩
  simp [seqAssocPath, Equiv.prodAssoc, Circuit.eventTrace, List.append_assoc]

/-- Reassociation preserves the actual visited contexts and their order. -/
lemma seqAssoc_visitedContexts
    (path : ((first.seq middle).seq last).Path) :
    ((first.seq middle).seq last).visitedContexts path =
      (first.seq (middle.seq last)).visitedContexts
        (seqAssocPath first middle last path) := by
  rcases path with ⟨⟨left, center⟩, right⟩
  simp [seqAssocPath, Equiv.prodAssoc, Circuit.visitedContexts, List.append_assoc]

/-- The same path has the same chronological dependency depth. -/
lemma seqAssoc_depth
    (duration : Resource.Event model → Nat)
    (path : ((first.seq middle).seq last).Path) :
    ((first.seq middle).seq last).depth duration path =
      (first.seq (middle.seq last)).depth duration
        (seqAssocPath first middle last path) := by
  rcases path with ⟨⟨left, center⟩, right⟩
  change (first.depth duration left + middle.depth duration center) +
    last.depth duration right =
      first.depth duration left + (middle.depth duration center + last.depth duration right)
  exact Nat.add_assoc _ _ _

/-- No resident storage is lost when a cycle boundary changes parentheses. -/
lemma seqAssoc_peakResidentSpace
    (path : ((first.seq middle).seq last).Path) :
    ((first.seq middle).seq last).peakResidentSpace path =
      (first.seq (middle.seq last)).peakResidentSpace
        (seqAssocPath first middle last path) := by
  unfold Circuit.peakResidentSpace
  rw [seqAssoc_visitedContexts first middle last path]

/-- The auxiliary peak is likewise unchanged on every actual path. -/
lemma seqAssoc_peakAuxiliarySpace
    (path : ((first.seq middle).seq last).Path) :
    ((first.seq middle).seq last).peakAuxiliarySpace path =
      (first.seq (middle.seq last)).peakAuxiliarySpace
        (seqAssocPath first middle last path) := by
  unfold Circuit.peakAuxiliarySpace
  rw [seqAssoc_visitedContexts first middle last path]

/-- The complete weighted output state, including store, service, reference
and every path outcome, changes only by the explicit path reassociation. -/
lemma seqAssoc_execute (environment : model.Environment) (Reference : Register)
    {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × H)) :
    ((first.seq middle).seq last).execute environment Reference state =
      ((first.seq (middle.seq last)).execute environment Reference state).mapHistory
        (seqAssocHistory first middle last) := by
  simp only [Circuit.execute_seq]
  let intermediate :=
    middle.execute environment Reference (first.execute environment Reference state)
  have natural := Circuit.execute_mapHistory last environment Reference intermediate
    (fun history : (H × first.Path) × middle.Path =>
      (history.1.1, (history.1.2, history.2)))
  rw [natural]
  simp only [State.mapHistory_comp, Function.comp_def]
  rfl

/-- Two circuit trees execute the same weighted physical process after a
bijection of mathematical path records. The certificate retains exact native
events, chronological depth, and both live-space peaks on every path. -/
structure OperationalEquiv {pre post : RuntimeCtx model.kind}
    (source target : Circuit model pre post allowAllocation) where
  path : source.Path ≃ target.Path
  execute : ∀ (environment : model.Environment) (Reference : Register) {H : Type} [Fintype H]
      (state : State pre Reference (model.HiddenState × H)),
      source.execute environment Reference state =
        (target.execute environment Reference state).mapHistory
          (fun history => (history.1, (history.2.1, path.symm history.2.2)))
  events : ∀ sourcePath : source.Path,
    source.eventTrace sourcePath = target.eventTrace (path sourcePath)
  depth : ∀ (duration : Resource.Event model → Nat) (sourcePath : source.Path),
    source.depth duration sourcePath = target.depth duration (path sourcePath)
  resident : ∀ sourcePath : source.Path,
    source.peakResidentSpace sourcePath = target.peakResidentSpace (path sourcePath)
  auxiliary : ∀ sourcePath : source.Path,
    source.peakAuxiliarySpace sourcePath = target.peakAuxiliarySpace (path sourcePath)

/-- Three unchanged sections satisfy the full operational equivalence contract. -/
def seqAssocOperationalEquiv :
    OperationalEquiv ((first.seq middle).seq last)
      (first.seq (middle.seq last)) where
  path := seqAssocPath first middle last
  execute := by
    intro environment Reference H _ state
    exact seqAssoc_execute first middle last environment Reference state
  events := seqAssoc_eventTrace first middle last
  depth := seqAssoc_depth first middle last
  resident := seqAssoc_peakResidentSpace first middle last
  auxiliary := seqAssoc_peakAuxiliarySpace first middle last

end

end QuantumAlg.Circuit
