/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit.Associativity
import all QuantumAlg.Core.Execution.Circuit.Associativity
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Composition of exact circuit execution equivalences

Each equivalence retains the full weighted state, ordered native events,
chronological depth and live-space peaks. Composing these certificates does
not identify or drop mathematical history records.
-/

namespace QuantumAlg.Circuit.OperationalEquiv

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem mapHistory_id {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference H) : state.mapHistory _root_.id = state := by
  change state.mapClassical (fun value => (value.1, value.2)) = state
  have same : (fun value : Store ctx × H => (value.1, value.2)) = _root_.id := by
    funext value
    rcases value with ⟨store, history⟩
    rfl
  rw [same]
  exact ExecutionState.mapClassical_id state

/-- Every circuit is equivalent to itself with exactly the same path. -/
def refl {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) : OperationalEquiv code code where
  path := Equiv.refl _
  execute := by
    intro Reference H _ state
    have same : (fun history : model.HiddenState × (H × code.Path) =>
        (history.1, (history.2.1, (Equiv.refl code.Path).symm history.2.2))) =
        _root_.id := by
      funext history
      rcases history with ⟨hidden, old, path⟩
      rfl
    rw [same]
    exact (mapHistory_id (code.execute Reference state)).symm
  events := by intro path; rfl
  depth := by intro duration path; rfl
  resident := by intro path; rfl
  auxiliary := by intro path; rfl

/-- Compose complete execution equivalences without changing the native run. -/
def trans {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {first middle last : Circuit model pre post}
    (left : OperationalEquiv first middle) (right : OperationalEquiv middle last) :
    OperationalEquiv first last where
  path := left.path.trans right.path
  execute := by
    intro Reference H _ state
    calc
      first.execute Reference state =
          (middle.execute Reference state).mapHistory
            (fun history => (history.1, (history.2.1, left.path.symm history.2.2))) :=
        left.execute Reference state
      _ = (((last.execute Reference state).mapHistory
            (fun history => (history.1, (history.2.1, right.path.symm history.2.2)))).mapHistory
            (fun history => (history.1, (history.2.1, left.path.symm history.2.2)))) :=
        congrArg (fun output => output.mapHistory
          (fun history => (history.1, (history.2.1, left.path.symm history.2.2))))
          (right.execute Reference state)
      _ = (last.execute Reference state).mapHistory
          (fun history => (history.1,
            (history.2.1, (left.path.trans right.path).symm history.2.2))) := by
        rw [State.mapHistory_comp]
        congr 1
  events := by
    intro path
    exact (left.events path).trans (right.events (left.path path))
  depth := by
    intro duration path
    exact (left.depth duration path).trans (right.depth duration (left.path path))
  resident := by
    intro path
    exact (left.resident path).trans (right.resident (left.path path))
  auxiliary := by
    intro path
    exact (left.auxiliary path).trans (right.auxiliary (left.path path))

/-- Reverse an exact path equivalence without changing the physical execution. -/
def symm {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {source target : Circuit model pre post}
    (certificate : OperationalEquiv source target) :
    OperationalEquiv target source where
  path := certificate.path.symm
  execute := by
    intro Reference H _ state
    let forward : model.HiddenState × (H × source.Path) →
        model.HiddenState × (H × target.Path) :=
      fun history => (history.1, (history.2.1, certificate.path history.2.2))
    let backward : model.HiddenState × (H × target.Path) →
        model.HiddenState × (H × source.Path) :=
      fun history => (history.1, (history.2.1, certificate.path.symm history.2.2))
    have identity : (((target.execute Reference state).mapHistory backward).mapHistory
        forward) = target.execute Reference state := by
      rw [State.mapHistory_comp]
      have same : (forward ∘ backward) = _root_.id := by
        funext history
        rcases history with ⟨hidden, old, path⟩
        simp [forward, backward]
      rw [same]
      exact mapHistory_id _
    have original := certificate.execute Reference state
    change source.execute Reference state =
      (target.execute Reference state).mapHistory backward at original
    rw [← original] at identity
    exact identity.symm
  events := by
    intro path
    simpa only [Equiv.apply_symm_apply] using
      (certificate.events (certificate.path.symm path)).symm
  depth := by
    intro duration path
    simpa only [Equiv.apply_symm_apply] using
      (certificate.depth duration (certificate.path.symm path)).symm
  resident := by
    intro path
    simpa only [Equiv.apply_symm_apply] using
      (certificate.resident (certificate.path.symm path)).symm
  auxiliary := by
    intro path
    simpa only [Equiv.apply_symm_apply] using
      (certificate.auxiliary (certificate.path.symm path)).symm

/-- The same preceding physical section preserves an exact equivalence of
the complete suffix execution, including the preceding path history. -/
def prepend {model : ExecutionModel} {pre middle post : RuntimeCtx model.kind}
    (initial : Circuit model pre middle) {source target : Circuit model middle post}
    (certificate : OperationalEquiv source target) :
    OperationalEquiv (initial.seq source) (initial.seq target) where
  path := (Equiv.refl initial.Path).prodCongr certificate.path
  execute := by
    intro Reference H _ state
    let prior := initial.execute Reference state
    have step := certificate.execute Reference prior
    simp only [Circuit.execute_seq]
    rw [step]
    simp only [State.mapHistory_comp, Function.comp_def]
    rfl
  events := by
    intro path
    rcases path with ⟨initialPath, sourcePath⟩
    change initial.eventTrace initialPath ++ source.eventTrace sourcePath =
      initial.eventTrace initialPath ++ target.eventTrace (certificate.path sourcePath)
    rw [certificate.events sourcePath]
  depth := by
    intro duration path
    rcases path with ⟨initialPath, sourcePath⟩
    change initial.depth duration initialPath + source.depth duration sourcePath =
      initial.depth duration initialPath + target.depth duration
        (certificate.path sourcePath)
    rw [certificate.depth duration sourcePath]
  resident := by
    intro path
    rcases path with ⟨initialPath, sourcePath⟩
    simp only [Circuit.peakResidentSpace_seq]
    change SpacePool.max (initial.peakResidentSpace initialPath)
      (source.peakResidentSpace sourcePath) =
        SpacePool.max (initial.peakResidentSpace initialPath)
          (target.peakResidentSpace (certificate.path sourcePath))
    rw [certificate.resident sourcePath]
  auxiliary := by
    intro path
    rcases path with ⟨initialPath, sourcePath⟩
    simp only [Circuit.peakAuxiliarySpace_seq]
    change SpacePool.max (initial.peakAuxiliarySpace initialPath)
      (source.peakAuxiliarySpace sourcePath) =
        SpacePool.max (initial.peakAuxiliarySpace initialPath)
          (target.peakAuxiliarySpace (certificate.path sourcePath))
    rw [certificate.auxiliary sourcePath]

/-- The same following physical section preserves an exact equivalence of
the complete prefix execution and every resulting history. -/
def append {model : ExecutionModel} {pre middle post : RuntimeCtx model.kind}
    {source target : Circuit model pre middle}
    (certificate : OperationalEquiv source target) (suffix : Circuit model middle post) :
    OperationalEquiv (source.seq suffix) (target.seq suffix) where
  path := certificate.path.prodCongr (Equiv.refl suffix.Path)
  execute := by
    intro Reference H _ state
    have step := certificate.execute Reference state
    simp only [Circuit.execute_seq]
    rw [step]
    rw [Circuit.execute_mapHistory suffix Reference (target.execute Reference state)
      (fun history : H × target.Path => (history.1, certificate.path.symm history.2))]
    simp only [State.mapHistory_comp, Function.comp_def]
    rfl
  events := by
    intro path
    rcases path with ⟨sourcePath, suffixPath⟩
    change source.eventTrace sourcePath ++ suffix.eventTrace suffixPath =
      target.eventTrace (certificate.path sourcePath) ++ suffix.eventTrace suffixPath
    rw [certificate.events sourcePath]
  depth := by
    intro duration path
    rcases path with ⟨sourcePath, suffixPath⟩
    change source.depth duration sourcePath + suffix.depth duration suffixPath =
      target.depth duration (certificate.path sourcePath) + suffix.depth duration suffixPath
    rw [certificate.depth duration sourcePath]
  resident := by
    intro path
    rcases path with ⟨sourcePath, suffixPath⟩
    simp only [Circuit.peakResidentSpace_seq]
    change SpacePool.max (source.peakResidentSpace sourcePath)
      (suffix.peakResidentSpace suffixPath) =
        SpacePool.max (target.peakResidentSpace (certificate.path sourcePath))
          (suffix.peakResidentSpace suffixPath)
    rw [certificate.resident sourcePath]
  auxiliary := by
    intro path
    rcases path with ⟨sourcePath, suffixPath⟩
    simp only [Circuit.peakAuxiliarySpace_seq]
    change SpacePool.max (source.peakAuxiliarySpace sourcePath)
      (suffix.peakAuxiliarySpace suffixPath) =
        SpacePool.max (target.peakAuxiliarySpace (certificate.path sourcePath))
          (suffix.peakAuxiliarySpace suffixPath)
    rw [certificate.auxiliary sourcePath]

end

end QuantumAlg.Circuit.OperationalEquiv
