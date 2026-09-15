/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scan
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Semantics

/-!
# Native residue preparation in its actual eleven classical scopes

The public modulus loader, original ordered proposal scan and expanded GCD
decision share the declared cells. Each cell is allocated by a real lexical
workspace constructor and released in reverse order. The packed sample and
complete parameter output remain in the caller's context. There are no new
quantum systems or hidden external scratch cells in this construction.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Load, scan, decide and pack within the real eleven-cell sampler context. -/
def inner (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) :
    Circuit (Layout.context ctx (modulusBits N)) (Layout.context ctx (modulusBits N)) :=
  .seq (Scan.circuit N sample)
    (Decision.circuit (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N)))

/-- Exact store and actual path of the complete inner instruction sequence. -/
def innerStep (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (store : Store (Layout.context ctx (modulusBits N))) :
    Store (Layout.context ctx (modulusBits N)) × (inner N sample output).Path :=
  let scanned := Scan.step N sample store
  let prepared := Decision.step (Layout.shared ctx (modulusBits N))
    (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
    (Layout.underWrite output (modulusBits N)) scanned.1
  (prepared.1, (scanned.2, prepared.2))

/-- The complete inner program follows its literal full-state instruction semantics. -/
theorem samplerInner_execute (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Layout.context ctx (modulusBits N)) Reference History) :
    (inner N sample output).execute Reference state =
      state.mapClassical (fun entry => ((innerStep N sample output entry.1).1,
        (entry.2, (innerStep N sample output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (Scan.circuit N sample) _ (Scan.step N sample)
    (Decision.step (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
      (Layout.gcdResultCell ctx (modulusBits N)) (Layout.underWrite output (modulusBits N)))
    (Scan.samplerScan_execute N sample)
    (Decision.decision_execute (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N))) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Enclose an actual inner program in precisely the layout's eleven workspace constructors. -/
def scopes (ctx : RuntimeCtx kind) (width : Nat)
    (body : Circuit (Layout.context ctx width) (Layout.context ctx width)) : Circuit ctx ctx :=
  let stage10 := Circuit.workspace (Layout.availableCtx ctx width)
    (Layout.availableCtx ctx width).canonicalFreshKey .bit
    (Layout.availableCtx ctx width).canonicalFreshKey_fresh body
  let stage9 := Circuit.workspace (Layout.selectedCtx ctx width)
    (Layout.selectedCtx ctx width).canonicalFreshKey .bit
    (Layout.selectedCtx ctx width).canonicalFreshKey_fresh stage10
  let stage8 := Circuit.workspace (Layout.acceptedCtx ctx width)
    (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh stage9
  let stage7 := Circuit.workspace (Layout.eligibleCtx ctx width)
    (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
    (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh stage8
  let stage6 := Circuit.workspace (Layout.belowCtx ctx width)
    (Layout.belowCtx ctx width).canonicalFreshKey .bit
    (Layout.belowCtx ctx width).canonicalFreshKey_fresh stage7
  let stage5 := Circuit.workspace (Layout.positiveCtx ctx width)
    (Layout.positiveCtx ctx width).canonicalFreshKey .bit
    (Layout.positiveCtx ctx width).canonicalFreshKey_fresh stage6
  let stage4 := Circuit.workspace (Layout.extendedCtx ctx width)
    (Layout.extendedCtx ctx width).canonicalFreshKey .bit
    (Layout.extendedCtx ctx width).canonicalFreshKey_fresh stage5
  let stage3 := Circuit.workspace (Layout.candidateCtx ctx width)
    (Layout.candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
    (Layout.candidateCtx ctx width).canonicalFreshKey_fresh stage4
  let stage2 := Circuit.workspace (Layout.gcdCtx ctx width)
    (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (Layout.gcdCtx ctx width).canonicalFreshKey_fresh stage3
  let stage1 := Circuit.workspace (Layout.modulusCtx ctx width)
    (Layout.modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
    (Layout.modulusCtx ctx width).canonicalFreshKey_fresh stage2
  Circuit.workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh stage1

/-- The actual scoped residue program takes a stored sample and writes its complete parameter. -/
def circuit (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) : Circuit ctx ctx :=
  scopes ctx (modulusBits N) (inner N sample output)

/-- Enter all real cells, execute the inner program and remove exactly those cells. -/
def step (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (store : Store ctx) :
    Store ctx × (circuit N sample output).Path :=
  let prepared := innerStep N sample output (Layout.pushStore (modulusBits N) store)
  (Layout.popStore (modulusBits N) prepared.1, prepared.2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
