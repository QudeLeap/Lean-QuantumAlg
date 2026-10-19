/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Initialized.Paths
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Word
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback

/-!
# Actual initialized raw streaming execution at every complete final Store

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.InitializedPaths

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open StoredRecursion PathDensity
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

-- Keep the base arithmetic layout abstract when composing complete-state laws.
attribute [local irreducible] NumeratorMeasurement.context

/-- An explicit physical initialized input family yields the actual legal-path bank sandwiches.
The premise fixes only the private C/M inclusion in each complete original Store fiber;
it does not assume old/new equivalence, a common output density, or a clean bank. -/
lemma actual_initialized_store_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (density : Store (Recovery.Layout.terminal p.size m) →
      Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ)
    (initialized : ∀ original : Store (Recovery.Layout.terminal p.size m),
      storeDensity state original =
        initializedColumns p.size m Reference * density original *
          (initializedColumns p.size m Reference).conjTranspose)
    (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity ((stages E r points (Recovery.Layout.order m)).execute environment Reference
      state) final =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m (2 * m) id path original final then
            initializedColumns p.size m Reference *
              (bankWord (environment := environment) E r points Reference path * density original *
                (bankWord (environment := environment) E r points Reference path).conjTranspose) *
              (initializedColumns p.size m Reference).conjTranspose
          else 0 := by
  have input := funext initialized
  have actual := actual_trace_density (environment := environment) E r points Reference (2 * m) id
    state final
  have transported := congrArg
    (fun initial => traceDensity (environment := environment) E r points Reference (2 * m) id
      initial final) input
  exact actual.trans (transported.trans
    (initialized_trace_density E r points Reference positive fits density final))

end

end PointCoordinates.StageWord.PathWord.InitializedPaths
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
