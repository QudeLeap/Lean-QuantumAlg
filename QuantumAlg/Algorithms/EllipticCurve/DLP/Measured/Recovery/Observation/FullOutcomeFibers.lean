/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.LegalPath.Fibers
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.BareStores

/-!
# Exact full-protocol outcome fibers of the original legal Store paths

The actual full schedule writes each of the 2*m indexed result cells once, in
its original id order. The complete final history therefore determines every
actual outcome label even when the original history is dirty. Composing this
fact with the existing legal-path equivalence retains exactly the original old
Store and division labels. No zero CP branch is removed.

All operations below are on the literal existing historyRun. This is a finite
label equivalence, not a circuit operation, bit reversal, CP-sum equality,
initialization law or complete instrument statement. Zero width is included.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace FullOutcomeFibers

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open TerminalStoreCoordinates LegalPathFibers

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A result slot avoided by an arbitrary chronological schedule keeps its original value. -/
private lemma historyRun_values_unwritten (modulus m length : Nat) :
    ∀ (indices : Fin length → Fin (2 * m)) (outcomes : Fin length → Fin 2)
    (history : Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m))
    (observed : Fin (2 * m)) (_avoids : ∀ position, observed ≠ indices position),
    BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (historyRun modulus m length indices outcomes history) observed =
      BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        history observed := by
  induction length with
  | zero => intro indices outcomes history observed avoids; rfl
  | succ length ih =>
      intro indices outcomes history observed avoids
      change BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
          (historyRun modulus m length (Fin.tail indices) (Fin.tail outcomes)
            (BareStores.historyWrite (Allocation.after modulus.size (2 * m)) 2 (2 * m)
              history (indices 0) (outcomes 0))) observed = _
      rw [ih (Fin.tail indices) (Fin.tail outcomes) _ observed
        (fun position => avoids position.succ)]
      exact (congrFun (BareStores.historyValues_write
        (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        history (indices 0) (outcomes 0)) observed).trans
          (Function.update_of_ne (avoids 0) (outcomes 0)
            (BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
              history))

/-- In a schedule with distinct destinations, each actual write survives every subsequent write. -/
private lemma historyRun_values_written (modulus m length : Nat) :
    ∀ (indices : Fin length → Fin (2 * m)) (outcomes : Fin length → Fin 2)
    (history : Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m))
    (_distinct : Function.Injective indices) (position : Fin length),
    BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (historyRun modulus m length indices outcomes history) (indices position) =
      outcomes position := by
  induction length with
  | zero => intro indices outcomes history distinct position; exact Fin.elim0 position
  | succ length ih =>
      intro indices outcomes history distinct position
      refine Fin.cases ?_ (fun previous => ?_) position
      · change BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
            (historyRun modulus m length (Fin.tail indices) (Fin.tail outcomes)
              (BareStores.historyWrite (Allocation.after modulus.size (2 * m)) 2 (2 * m)
                history (indices 0) (outcomes 0))) (indices 0) = outcomes 0
        rw [historyRun_values_unwritten modulus m length
          (Fin.tail indices) (Fin.tail outcomes) _ (indices 0)
          (fun previous equality => Fin.succ_ne_zero previous (distinct equality).symm)]
        exact (congrFun (BareStores.historyValues_write
          (Allocation.after modulus.size (2 * m)) 2 (2 * m)
          history (indices 0) (outcomes 0)) (indices 0)).trans
            (Function.update_self (indices 0) (outcomes 0)
              (BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
                history))
      · exact ih (Fin.tail indices) (Fin.tail outcomes) _
          (fun first second equality => Fin.succ_injective length (distinct equality)) previous

/-- Every actual full-protocol result value is its original outcome, from any dirty history. -/
lemma historyRun_full_values (modulus m : Nat) (outcomes : Fin (2 * m) → Fin 2)
    (history : Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m)) :
    BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
      (historyRun modulus m (2 * m) id outcomes history) = outcomes := by
  funext position
  exact historyRun_values_written modulus m (2 * m) id outcomes history
    (fun _ _ equality => equality) position

/-- Writing all actual indexed cells reconstructs any prescribed complete final history. -/
lemma historyRun_full_target (modulus m : Nat)
    (original final : Circuit.measurementCellsHistory
      (Allocation.after modulus.size (2 * m)) 2 (2 * m)) :
    historyRun modulus m (2 * m) id
        (BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m) final)
        original = final := by
  apply (BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)).injective
  exact historyRun_full_values modulus m
    (BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m) final) original

/-- At fixed complete final Store, the actual full-protocol outcome tuple is forced exactly. -/
lemma fullOutcome_values (modulus m : Nat)
    (original final : Store (Recovery.Layout.terminal modulus.size m))
    (choices : OutcomeFiber modulus m (2 * m) id original final) :
    choices.val = BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
      (instantStore modulus m final).2 := by
  have values := congrArg
    (BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m))
    choices.property
  rw [historyRun_full_values] at values
  exact values

/-- The complete actual id schedule has one outcome fiber, including zero result width. -/
def fullOutcomeEquiv (modulus m : Nat)
    (original final : Store (Recovery.Layout.terminal modulus.size m)) :
    OutcomeFiber modulus m (2 * m) id original final ≃ Unit where
  toFun _ := ()
  invFun _ :=
    ⟨BareStores.historyValues (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (instantStore modulus m final).2,
      historyRun_full_target modulus m
        (instantStore modulus m original).2 (instantStore modulus m final).2⟩
  left_inv choices := Subtype.ext (fullOutcome_values modulus m original final choices).symm
  right_inv value := by cases value; rfl

/-- Exact full-protocol legal paths, retaining all original old Store and division labels. -/
def fullLegalPathEquiv (modulus m : Nat)
    (original final : Store (Recovery.Layout.terminal modulus.size m)) :
    NewLegalPaths modulus m (2 * m) id original final ≃
      ReferenceLegalPaths modulus m (2 * m) id original final :=
  (legalPathEquiv modulus m (2 * m) id original final).trans
    (((Equiv.refl _).prodCongr (fullOutcomeEquiv modulus m original final)).trans
      (Equiv.prodUnique _ Unit))

/-- Eliminating the forced outcome coordinate keeps exactly the previous actual oldPath map. -/
lemma fullLegalPathEquiv_oldPath (modulus m : Nat)
    (original final : Store (Recovery.Layout.terminal modulus.size m))
    (path : NewLegalPaths modulus m (2 * m) id original final) :
    (fullLegalPathEquiv modulus m original final path).val =
      Recovery.Layout.BankWords.oldPath modulus m (2 * m) path.val := rfl

end

end FullOutcomeFibers
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
