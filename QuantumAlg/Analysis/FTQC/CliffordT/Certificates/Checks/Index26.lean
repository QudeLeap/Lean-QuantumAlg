/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word26Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word26State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word26Step0 :
    word26Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word26State1 := by decide +kernel

private def word26Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word26State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word26Step1 :
    word26Chunk1.foldl (fun acc a => a.applyPacked acc)
      word26State1 = word26State2 := by decide +kernel

private def word26Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word26State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word26Step2 :
    word26Chunk2.foldl (fun acc a => a.applyPacked acc)
      word26State2 = word26State3 := by decide +kernel

private def word26Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word26State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word26Step3 :
    word26Chunk3.foldl (fun acc a => a.applyPacked acc)
      word26State3 = word26State4 := by decide +kernel

private def word26Chunk4 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word26State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word26Step4 :
    word26Chunk4.foldl (fun acc a => a.applyPacked acc)
      word26State4 = word26State5 := by decide +kernel

private def word26Chunk5 : List Letter := [.h, .s, .s, .s, .h, .s, .t, .h]
private def word26State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word26Step5 :
    word26Chunk5.foldl (fun acc a => a.applyPacked acc)
      word26State5 = word26State6 := by decide +kernel

private def word26Chunk6 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word26State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word26Step6 :
    word26Chunk6.foldl (fun acc a => a.applyPacked acc)
      word26State6 = word26State7 := by decide +kernel

private def word26Chunk7 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State8 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word26Step7 :
    word26Chunk7.foldl (fun acc a => a.applyPacked acc)
      word26State7 = word26State8 := by decide +kernel

private def word26Chunk8 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word26State9 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word26Step8 :
    word26Chunk8.foldl (fun acc a => a.applyPacked acc)
      word26State8 = word26State9 := by decide +kernel

private def word26Chunk9 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word26State10 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((15 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word26Step9 :
    word26Chunk9.foldl (fun acc a => a.applyPacked acc)
      word26State9 = word26State10 := by decide +kernel

private def word26Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word26State11 : PackedMat2 :=
    ⟨⟨⟨((23 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-17 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((23 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word26Step10 :
    word26Chunk10.foldl (fun acc a => a.applyPacked acc)
      word26State10 = word26State11 := by decide +kernel

private def word26Chunk11 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word26State12 : PackedMat2 :=
    ⟨⟨⟨((15 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩⟩
private lemma word26Step11 :
    word26Chunk11.foldl (fun acc a => a.applyPacked acc)
      word26State11 = word26State12 := by decide +kernel

private def word26Chunk12 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word26State13 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 6),
        ((-33 : Dyadic) * half ^ 7)⟩,
       ⟨((-31 : Dyadic) * half ^ 6),
        ((-37 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 6),
        ((37 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 6),
        ((33 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((13 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word26Step12 :
    word26Chunk12.foldl (fun acc a => a.applyPacked acc)
      word26State12 = word26State13 := by decide +kernel

private def word26Chunk13 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word26State14 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 6),
        ((-31 : Dyadic) * half ^ 6)⟩,
       ⟨((17 : Dyadic) * half ^ 5),
        ((25 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-27 : Dyadic) * half ^ 7)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 6)⟩,
       ⟨((35 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((87 : Dyadic) * half ^ 7),
        ((27 : Dyadic) * half ^ 7)⟩,
       ⟨((-37 : Dyadic) * half ^ 7),
        ((41 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word26Step13 :
    word26Chunk13.foldl (fun acc a => a.applyPacked acc)
      word26State13 = word26State14 := by decide +kernel

private def word26Chunk14 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word26State15 : PackedMat2 :=
    ⟨⟨⟨((-165 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 7)⟩,
       ⟨((-123 : Dyadic) * half ^ 8),
        ((-19 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 8),
        ((39 : Dyadic) * half ^ 7)⟩,
       ⟨((15 : Dyadic) * half ^ 8),
        ((-67 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-145 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 8)⟩,
       ⟨((11 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((37 : Dyadic) * half ^ 8),
        ((-21 : Dyadic) * half ^ 8)⟩,
       ⟨((1 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word26Step14 :
    word26Chunk14.foldl (fun acc a => a.applyPacked acc)
      word26State14 = word26State15 := by decide +kernel

private def word26Chunk15 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word26State16 : PackedMat2 :=
    ⟨⟨⟨((-27 : Dyadic) * half ^ 8),
        ((-125 : Dyadic) * half ^ 9)⟩,
       ⟨((-235 : Dyadic) * half ^ 8),
        ((17 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 9)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 8),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 7),
        ((-131 : Dyadic) * half ^ 8)⟩,
       ⟨((-71 : Dyadic) * half ^ 8),
        ((13 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word26Step15 :
    word26Chunk15.foldl (fun acc a => a.applyPacked acc)
      word26State15 = word26State16 := by decide +kernel

private def word26Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word26State17 : PackedMat2 :=
    ⟨⟨⟨((113 : Dyadic) * half ^ 9),
        ((-99 : Dyadic) * half ^ 10)⟩,
       ⟨((3 : Dyadic) * half ^ 8),
        ((-551 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((109 : Dyadic) * half ^ 9),
        ((291 : Dyadic) * half ^ 10)⟩,
       ⟨((33 : Dyadic) * half ^ 8),
        ((-261 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((109 : Dyadic) * half ^ 9),
        ((291 : Dyadic) * half ^ 10)⟩,
       ⟨((-33 : Dyadic) * half ^ 8),
        ((261 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-113 : Dyadic) * half ^ 9),
        ((99 : Dyadic) * half ^ 10)⟩,
       ⟨((3 : Dyadic) * half ^ 8),
        ((-551 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word26Step16 :
    word26Chunk16.foldl (fun acc a => a.applyPacked acc)
      word26State16 = word26State17 := by decide +kernel

private def word26Chunk17 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State18 : PackedMat2 :=
    ⟨⟨⟨((383 : Dyadic) * half ^ 10),
        ((25 : Dyadic) * half ^ 6)⟩,
       ⟨((-233 : Dyadic) * half ^ 10),
        ((99 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-125 : Dyadic) * half ^ 10),
        ((-47 : Dyadic) * half ^ 10)⟩,
       ⟨((-267 : Dyadic) * half ^ 10),
        ((423 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((235 : Dyadic) * half ^ 9),
        ((-71 : Dyadic) * half ^ 10)⟩,
       ⟨((47 : Dyadic) * half ^ 7),
        ((-49 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((101 : Dyadic) * half ^ 9),
        ((77 : Dyadic) * half ^ 8)⟩,
       ⟨((-299 : Dyadic) * half ^ 9),
        ((-75 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word26Step17 :
    word26Chunk17.foldl (fun acc a => a.applyPacked acc)
      word26State17 = word26State18 := by decide +kernel

private def word26Chunk18 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word26State19 : PackedMat2 :=
    ⟨⟨⟨((431 : Dyadic) * half ^ 11),
        ((825 : Dyadic) * half ^ 11)⟩,
       ⟨((447 : Dyadic) * half ^ 11),
        ((291 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-979 : Dyadic) * half ^ 11),
        ((305 : Dyadic) * half ^ 10)⟩,
       ⟨((-217 : Dyadic) * half ^ 11),
        ((-257 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((281 : Dyadic) * half ^ 9),
        ((-381 : Dyadic) * half ^ 11)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((299 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-267 : Dyadic) * half ^ 10),
        ((1 : Dyadic) * half ^ 8)⟩,
       ⟨((279 : Dyadic) * half ^ 9),
        ((439 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word26Step18 :
    word26Chunk18.foldl (fun acc a => a.applyPacked acc)
      word26State18 = word26State19 := by decide +kernel

private def word26Chunk19 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word26State20 : PackedMat2 :=
    ⟨⟨⟨((-127 : Dyadic) * half ^ 12),
        ((-305 : Dyadic) * half ^ 11)⟩,
       ⟨((2079 : Dyadic) * half ^ 12),
        ((363 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((2767 : Dyadic) * half ^ 12),
        ((-93 : Dyadic) * half ^ 11)⟩,
       ⟨((-235 : Dyadic) * half ^ 12),
        ((1351 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1537 : Dyadic) * half ^ 12),
        ((-1501 : Dyadic) * half ^ 12)⟩,
       ⟨((1165 : Dyadic) * half ^ 12),
        ((633 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-973 : Dyadic) * half ^ 12),
        ((-1103 : Dyadic) * half ^ 12)⟩,
       ⟨((247 : Dyadic) * half ^ 12),
        ((-61 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word26Step19 :
    word26Chunk19.foldl (fun acc a => a.applyPacked acc)
      word26State19 = word26State20 := by decide +kernel

private def word26Chunk20 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word26State21 : PackedMat2 :=
    ⟨⟨⟨((-347 : Dyadic) * half ^ 11),
        ((-2357 : Dyadic) * half ^ 13)⟩,
       ⟨((-161 : Dyadic) * half ^ 10),
        ((1269 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2521 : Dyadic) * half ^ 12),
        ((-767 : Dyadic) * half ^ 13)⟩,
       ⟨((2207 : Dyadic) * half ^ 12),
        ((-1247 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2207 : Dyadic) * half ^ 12),
        ((1247 : Dyadic) * half ^ 13)⟩,
       ⟨((2521 : Dyadic) * half ^ 12),
        ((767 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-161 : Dyadic) * half ^ 10),
        ((1269 : Dyadic) * half ^ 13)⟩,
       ⟨((-347 : Dyadic) * half ^ 11),
        ((-2357 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word26Step20 :
    word26Chunk20.foldl (fun acc a => a.applyPacked acc)
      word26State20 = word26State21 := by decide +kernel

private def word26Chunk21 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word26State22 : PackedMat2 :=
    ⟨⟨⟨((-1953 : Dyadic) * half ^ 13),
        ((2071 : Dyadic) * half ^ 14)⟩,
       ⟨((-27 : Dyadic) * half ^ 9),
        ((-3959 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4787 : Dyadic) * half ^ 13),
        ((-3845 : Dyadic) * half ^ 14)⟩,
       ⟨((-403 : Dyadic) * half ^ 10),
        ((4985 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4787 : Dyadic) * half ^ 13),
        ((-3845 : Dyadic) * half ^ 14)⟩,
       ⟨((403 : Dyadic) * half ^ 10),
        ((-4985 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1953 : Dyadic) * half ^ 13),
        ((-2071 : Dyadic) * half ^ 14)⟩,
       ⟨((-27 : Dyadic) * half ^ 9),
        ((-3959 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word26Step21 :
    word26Chunk21.foldl (fun acc a => a.applyPacked acc)
      word26State21 = word26State22 := by decide +kernel

private def word26Chunk22 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word26State23 : PackedMat2 :=
    ⟨⟨⟨((3645 : Dyadic) * half ^ 13),
        ((1949 : Dyadic) * half ^ 14)⟩,
       ⟨((-571 : Dyadic) * half ^ 10),
        ((387 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1287 : Dyadic) * half ^ 13),
        ((-1561 : Dyadic) * half ^ 12)⟩,
       ⟨((315 : Dyadic) * half ^ 13),
        ((-3167 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((3077 : Dyadic) * half ^ 14),
        ((801 : Dyadic) * half ^ 13)⟩,
       ⟨((-9411 : Dyadic) * half ^ 14),
        ((-243 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1147 : Dyadic) * half ^ 14),
        ((8213 : Dyadic) * half ^ 14)⟩,
       ⟨((-5045 : Dyadic) * half ^ 14),
        ((923 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word26Step22 :
    word26Chunk22.foldl (fun acc a => a.applyPacked acc)
      word26State22 = word26State23 := by decide +kernel

private def word26Chunk23 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State24 : PackedMat2 :=
    ⟨⟨⟨((1329 : Dyadic) * half ^ 15),
        ((1 : Dyadic) * half ^ 15)⟩,
       ⟨((18897 : Dyadic) * half ^ 15),
        ((-4157 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((8003 : Dyadic) * half ^ 15),
        ((4713 : Dyadic) * half ^ 15)⟩,
       ⟨((-19905 : Dyadic) * half ^ 15),
        ((-2999 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((19905 : Dyadic) * half ^ 15),
        ((2999 : Dyadic) * half ^ 14)⟩,
       ⟨((-8003 : Dyadic) * half ^ 15),
        ((-4713 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((18897 : Dyadic) * half ^ 15),
        ((-4157 : Dyadic) * half ^ 14)⟩,
       ⟨((1329 : Dyadic) * half ^ 15),
        ((1 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word26Step23 :
    word26Chunk23.foldl (fun acc a => a.applyPacked acc)
      word26State23 = word26State24 := by decide +kernel

private def word26Chunk24 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word26State25 : PackedMat2 :=
    ⟨⟨⟨((56999 : Dyadic) * half ^ 16),
        ((875 : Dyadic) * half ^ 15)⟩,
       ⟨((12731 : Dyadic) * half ^ 16),
        ((2389 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((27727 : Dyadic) * half ^ 16),
        ((-1913 : Dyadic) * half ^ 15)⟩,
       ⟨((-6113 : Dyadic) * half ^ 16),
        ((3939 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((7765 : Dyadic) * half ^ 16),
        ((-2115 : Dyadic) * half ^ 13)⟩,
       ⟨((113 : Dyadic) * half ^ 16),
        ((10807 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-639 : Dyadic) * half ^ 16),
        ((11067 : Dyadic) * half ^ 15)⟩,
       ⟨((-4139 : Dyadic) * half ^ 16),
        ((-34865 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word26Step24 :
    word26Chunk24.foldl (fun acc a => a.applyPacked acc)
      word26State24 = word26State25 := by decide +kernel

private def word26Chunk25 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word26State26 : PackedMat2 :=
    ⟨⟨⟨((-959 : Dyadic) * half ^ 13),
        ((58549 : Dyadic) * half ^ 17)⟩,
       ⟨((2797 : Dyadic) * half ^ 12),
        ((10655 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-7135 : Dyadic) * half ^ 16),
        ((21399 : Dyadic) * half ^ 17)⟩,
       ⟨((-10697 : Dyadic) * half ^ 16),
        ((-11689 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((10697 : Dyadic) * half ^ 16),
        ((11689 : Dyadic) * half ^ 17)⟩,
       ⟨((7135 : Dyadic) * half ^ 16),
        ((-21399 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((2797 : Dyadic) * half ^ 12),
        ((10655 : Dyadic) * half ^ 17)⟩,
       ⟨((-959 : Dyadic) * half ^ 13),
        ((58549 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word26Step25 :
    word26Chunk25.foldl (fun acc a => a.applyPacked acc)
      word26State25 = word26State26 := by decide +kernel

private def word26Chunk26 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word26State27 : PackedMat2 :=
    ⟨⟨⟨((-2747 : Dyadic) * half ^ 17),
        ((-29561 : Dyadic) * half ^ 18)⟩,
       ⟨((3919 : Dyadic) * half ^ 16),
        ((130221 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((56043 : Dyadic) * half ^ 17),
        ((-55005 : Dyadic) * half ^ 18)⟩,
       ⟨((-26713 : Dyadic) * half ^ 16),
        ((-37075 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((56043 : Dyadic) * half ^ 17),
        ((-55005 : Dyadic) * half ^ 18)⟩,
       ⟨((26713 : Dyadic) * half ^ 16),
        ((37075 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((2747 : Dyadic) * half ^ 17),
        ((29561 : Dyadic) * half ^ 18)⟩,
       ⟨((3919 : Dyadic) * half ^ 16),
        ((130221 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word26Step26 :
    word26Chunk26.foldl (fun acc a => a.applyPacked acc)
      word26State26 = word26State27 := by decide +kernel

private def word26Chunk27 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word26State28 : PackedMat2 :=
    ⟨⟨⟨((-46721 : Dyadic) * half ^ 17),
        ((-40355 : Dyadic) * half ^ 18)⟩,
       ⟨((1157 : Dyadic) * half ^ 12),
        ((-3185 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2163 : Dyadic) * half ^ 17),
        ((7475 : Dyadic) * half ^ 15)⟩,
       ⟨((5565 : Dyadic) * half ^ 17),
        ((-146039 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-205839 : Dyadic) * half ^ 18),
        ((483 : Dyadic) * half ^ 14)⟩,
       ⟨((-86239 : Dyadic) * half ^ 18),
        ((1701 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-14875 : Dyadic) * half ^ 18),
        ((-83745 : Dyadic) * half ^ 18)⟩,
       ⟨((65835 : Dyadic) * half ^ 18),
        ((9697 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word26Step27 :
    word26Chunk27.foldl (fun acc a => a.applyPacked acc)
      word26State27 = word26State28 := by decide +kernel

private def word26Chunk28 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word26State29 : PackedMat2 :=
    ⟨⟨⟨((51081 : Dyadic) * half ^ 19),
        ((-37845 : Dyadic) * half ^ 18)⟩,
       ⟨((-58163 : Dyadic) * half ^ 19),
        ((30291 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((123345 : Dyadic) * half ^ 19),
        ((112729 : Dyadic) * half ^ 18)⟩,
       ⟨((-362239 : Dyadic) * half ^ 19),
        ((61233 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((362239 : Dyadic) * half ^ 19),
        ((-61233 : Dyadic) * half ^ 19)⟩,
       ⟨((-123345 : Dyadic) * half ^ 19),
        ((-112729 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-58163 : Dyadic) * half ^ 19),
        ((30291 : Dyadic) * half ^ 19)⟩,
       ⟨((51081 : Dyadic) * half ^ 19),
        ((-37845 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word26Step28 :
    word26Chunk28.foldl (fun acc a => a.applyPacked acc)
      word26State28 = word26State29 := by decide +kernel

private def word26Chunk29 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State30 : PackedMat2 :=
    ⟨⟨⟨((-192795 : Dyadic) * half ^ 19),
        ((54867 : Dyadic) * half ^ 18)⟩,
       ⟨((-25095 : Dyadic) * half ^ 18),
        ((-176157 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((44715 : Dyadic) * half ^ 17),
        ((-2965 : Dyadic) * half ^ 16)⟩,
       ⟨((333147 : Dyadic) * half ^ 19),
        ((12425 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((6495 : Dyadic) * half ^ 17),
        ((512007 : Dyadic) * half ^ 20)⟩,
       ⟨((-18355 : Dyadic) * half ^ 17),
        ((-154287 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((66423 : Dyadic) * half ^ 19),
        ((242985 : Dyadic) * half ^ 20)⟩,
       ⟨((-285891 : Dyadic) * half ^ 19),
        ((142605 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word26Step29 :
    word26Chunk29.foldl (fun acc a => a.applyPacked acc)
      word26State29 = word26State30 := by decide +kernel

private def word26Chunk30 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word26State31 : PackedMat2 :=
    ⟨⟨⟨((572839 : Dyadic) * half ^ 20),
        ((23001 : Dyadic) * half ^ 20)⟩,
       ⟨((-6115 : Dyadic) * half ^ 19),
        ((-564119 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((72321 : Dyadic) * half ^ 19),
        ((-50559 : Dyadic) * half ^ 19)⟩,
       ⟨((-25451 : Dyadic) * half ^ 20),
        ((214103 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((25451 : Dyadic) * half ^ 20),
        ((-214103 : Dyadic) * half ^ 20)⟩,
       ⟨((-72321 : Dyadic) * half ^ 19),
        ((50559 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-6115 : Dyadic) * half ^ 19),
        ((-564119 : Dyadic) * half ^ 20)⟩,
       ⟨((572839 : Dyadic) * half ^ 20),
        ((23001 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word26Step30 :
    word26Chunk30.foldl (fun acc a => a.applyPacked acc)
      word26State30 = word26State31 := by decide +kernel

private def word26Chunk31 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word26State32 : PackedMat2 :=
    ⟨⟨⟨((373453 : Dyadic) * half ^ 21),
        ((2103823 : Dyadic) * half ^ 22)⟩,
       ⟨((-221207 : Dyadic) * half ^ 20),
        ((140733 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((410335 : Dyadic) * half ^ 21),
        ((446147 : Dyadic) * half ^ 22)⟩,
       ⟨((556983 : Dyadic) * half ^ 20),
        ((-813747 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((410335 : Dyadic) * half ^ 21),
        ((446147 : Dyadic) * half ^ 22)⟩,
       ⟨((-556983 : Dyadic) * half ^ 20),
        ((813747 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-373453 : Dyadic) * half ^ 21),
        ((-2103823 : Dyadic) * half ^ 22)⟩,
       ⟨((-221207 : Dyadic) * half ^ 20),
        ((140733 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word26Step31 :
    word26Chunk31.foldl (fun acc a => a.applyPacked acc)
      word26State31 = word26State32 := by decide +kernel

private def word26Chunk32 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word26State33 : PackedMat2 :=
    ⟨⟨⟨((-47669 : Dyadic) * half ^ 22),
        ((5271695 : Dyadic) * half ^ 23)⟩,
       ⟨((8985 : Dyadic) * half ^ 20),
        ((2230599 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-12907 : Dyadic) * half ^ 22),
        ((-577003 : Dyadic) * half ^ 23)⟩,
       ⟨((506399 : Dyadic) * half ^ 21),
        ((161613 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((207695 : Dyadic) * half ^ 22),
        ((-999891 : Dyadic) * half ^ 23)⟩,
       ⟨((92327 : Dyadic) * half ^ 20),
        ((1025705 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3751147 : Dyadic) * half ^ 22),
        ((-11729 : Dyadic) * half ^ 23)⟩,
       ⟨((380137 : Dyadic) * half ^ 20),
        ((-83609 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word26Step32 :
    word26Chunk32.foldl (fun acc a => a.applyPacked acc)
      word26State32 = word26State33 := by decide +kernel

private def word26Chunk33 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word26State34 : PackedMat2 :=
    ⟨⟨⟨((3459843 : Dyadic) * half ^ 23),
        ((2014629 : Dyadic) * half ^ 23)⟩,
       ⟨((-1901585 : Dyadic) * half ^ 23),
        ((3280099 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-4984547 : Dyadic) * half ^ 23),
        ((68251 : Dyadic) * half ^ 22)⟩,
       ⟨((-151349 : Dyadic) * half ^ 23),
        ((173481 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-4984547 : Dyadic) * half ^ 23),
        ((68251 : Dyadic) * half ^ 22)⟩,
       ⟨((151349 : Dyadic) * half ^ 23),
        ((-173481 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-3459843 : Dyadic) * half ^ 23),
        ((-2014629 : Dyadic) * half ^ 23)⟩,
       ⟨((-1901585 : Dyadic) * half ^ 23),
        ((3280099 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word26Step33 :
    word26Chunk33.foldl (fun acc a => a.applyPacked acc)
      word26State33 = word26State34 := by decide +kernel

private def word26Chunk34 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word26State35 : PackedMat2 :=
    ⟨⟨⟨((10504807 : Dyadic) * half ^ 24),
        ((-139379 : Dyadic) * half ^ 24)⟩,
       ⟨((-2160819 : Dyadic) * half ^ 24),
        ((687629 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-2448149 : Dyadic) * half ^ 24),
        ((-6058507 : Dyadic) * half ^ 24)⟩,
       ⟨((-8385279 : Dyadic) * half ^ 24),
        ((442717 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-8385279 : Dyadic) * half ^ 24),
        ((442717 : Dyadic) * half ^ 23)⟩,
       ⟨((-2448149 : Dyadic) * half ^ 24),
        ((-6058507 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2160819 : Dyadic) * half ^ 24),
        ((-687629 : Dyadic) * half ^ 22)⟩,
       ⟨((-10504807 : Dyadic) * half ^ 24),
        ((139379 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word26Step34 :
    word26Chunk34.foldl (fun acc a => a.applyPacked acc)
      word26State34 = word26State35 := by decide +kernel

private def word26Chunk35 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word26State36 : PackedMat2 :=
    ⟨⟨⟨((-3251609 : Dyadic) * half ^ 24),
        ((8639725 : Dyadic) * half ^ 25)⟩,
       ⟨((6778845 : Dyadic) * half ^ 24),
        ((-8358705 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-392729 : Dyadic) * half ^ 23),
        ((-6084099 : Dyadic) * half ^ 25)⟩,
       ⟨((-1397761 : Dyadic) * half ^ 22),
        ((-14304407 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((10194253 : Dyadic) * half ^ 24),
        ((3188251 : Dyadic) * half ^ 24)⟩,
       ⟨((-2055077 : Dyadic) * half ^ 23),
        ((-2402793 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((70255 : Dyadic) * half ^ 23),
        ((881809 : Dyadic) * half ^ 23)⟩,
       ⟨((8499215 : Dyadic) * half ^ 24),
        ((-5015227 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word26Step35 :
    word26Chunk35.foldl (fun acc a => a.applyPacked acc)
      word26State35 = word26State36 := by decide +kernel

private def word26Chunk36 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State37 : PackedMat2 :=
    ⟨⟨⟨((5757437 : Dyadic) * half ^ 25),
        ((-4227375 : Dyadic) * half ^ 26)⟩,
       ⟨((-3870247 : Dyadic) * half ^ 23),
        ((6221259 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((7235047 : Dyadic) * half ^ 25),
        ((33833817 : Dyadic) * half ^ 26)⟩,
       ⟨((-1520939 : Dyadic) * half ^ 22),
        ((10202511 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((7235047 : Dyadic) * half ^ 25),
        ((33833817 : Dyadic) * half ^ 26)⟩,
       ⟨((1520939 : Dyadic) * half ^ 22),
        ((-10202511 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-5757437 : Dyadic) * half ^ 25),
        ((4227375 : Dyadic) * half ^ 26)⟩,
       ⟨((-3870247 : Dyadic) * half ^ 23),
        ((6221259 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word26Step36 :
    word26Chunk36.foldl (fun acc a => a.applyPacked acc)
      word26State36 = word26State37 := by decide +kernel

private def word26Chunk37 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word26State38 : PackedMat2 :=
    ⟨⟨⟨((2009283 : Dyadic) * half ^ 25),
        ((-14270101 : Dyadic) * half ^ 26)⟩,
       ⟨((-11801 : Dyadic) * half ^ 22),
        ((-3123355 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((25879383 : Dyadic) * half ^ 25),
        ((2513 : Dyadic) * half ^ 23)⟩,
       ⟨((16459273 : Dyadic) * half ^ 25),
        ((1638767 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((1618663 : Dyadic) * half ^ 26),
        ((-4710055 : Dyadic) * half ^ 25)⟩,
       ⟨((1658871 : Dyadic) * half ^ 26),
        ((1323083 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1776681 : Dyadic) * half ^ 26),
        ((2103691 : Dyadic) * half ^ 26)⟩,
       ⟨((26763521 : Dyadic) * half ^ 26),
        ((-1914875 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word26Step37 :
    word26Chunk37.foldl (fun acc a => a.applyPacked acc)
      word26State37 = word26State38 := by decide +kernel

private def word26Chunk38 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word26State39 : PackedMat2 :=
    ⟨⟨⟨((-26732723 : Dyadic) * half ^ 27),
        ((1772969 : Dyadic) * half ^ 25)⟩,
       ⟨((-19309403 : Dyadic) * half ^ 27),
        ((27879739 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-34655019 : Dyadic) * half ^ 27),
        ((26111845 : Dyadic) * half ^ 26)⟩,
       ⟨((81799821 : Dyadic) * half ^ 27),
        ((31023775 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-81799821 : Dyadic) * half ^ 27),
        ((-31023775 : Dyadic) * half ^ 27)⟩,
       ⟨((34655019 : Dyadic) * half ^ 27),
        ((-26111845 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-19309403 : Dyadic) * half ^ 27),
        ((27879739 : Dyadic) * half ^ 27)⟩,
       ⟨((-26732723 : Dyadic) * half ^ 27),
        ((1772969 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word26Step38 :
    word26Chunk38.foldl (fun acc a => a.applyPacked acc)
      word26State38 = word26State39 := by decide +kernel

private def word26Chunk39 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word26State40 : PackedMat2 :=
    ⟨⟨⟨((-126284841 : Dyadic) * half ^ 28),
        ((-29547397 : Dyadic) * half ^ 27)⟩,
       ⟨((51778881 : Dyadic) * half ^ 28),
        ((-19265941 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((18607217 : Dyadic) * half ^ 28),
        ((-12418123 : Dyadic) * half ^ 26)⟩,
       ⟨((197078791 : Dyadic) * half ^ 28),
        ((-28115359 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((197078791 : Dyadic) * half ^ 28),
        ((-28115359 : Dyadic) * half ^ 28)⟩,
       ⟨((18607217 : Dyadic) * half ^ 28),
        ((-12418123 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-51778881 : Dyadic) * half ^ 28),
        ((19265941 : Dyadic) * half ^ 28)⟩,
       ⟨((126284841 : Dyadic) * half ^ 28),
        ((29547397 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word26Step39 :
    word26Chunk39.foldl (fun acc a => a.applyPacked acc)
      word26State39 = word26State40 := by decide +kernel

private def word26Chunk40 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State41 : PackedMat2 :=
    ⟨⟨⟨((-5388843 : Dyadic) * half ^ 26),
        ((48585939 : Dyadic) * half ^ 28)⟩,
       ⟨((-138990795 : Dyadic) * half ^ 28),
        ((-41579405 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-79441203 : Dyadic) * half ^ 28),
        ((6451261 : Dyadic) * half ^ 27)⟩,
       ⟨((-54107643 : Dyadic) * half ^ 27),
        ((43829433 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-25140347 : Dyadic) * half ^ 26),
        ((187656489 : Dyadic) * half ^ 29)⟩,
       ⟨((9344543 : Dyadic) * half ^ 25),
        ((-28774083 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-34572871 : Dyadic) * half ^ 28),
        ((-160546167 : Dyadic) * half ^ 29)⟩,
       ⟨((131744749 : Dyadic) * half ^ 28),
        ((117435423 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word26Step40 :
    word26Chunk40.foldl (fun acc a => a.applyPacked acc)
      word26State40 = word26State41 := by decide +kernel

private def word26Chunk41 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word26State42 : PackedMat2 :=
    ⟨⟨⟨((-85473743 : Dyadic) * half ^ 28),
        ((325533355 : Dyadic) * half ^ 30)⟩,
       ⟨((72775147 : Dyadic) * half ^ 28),
        ((-203194389 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-357936503 : Dyadic) * half ^ 29),
        ((-222505037 : Dyadic) * half ^ 30)⟩,
       ⟨((98573085 : Dyadic) * half ^ 29),
        ((56622321 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((98573085 : Dyadic) * half ^ 29),
        ((56622321 : Dyadic) * half ^ 30)⟩,
       ⟨((-357936503 : Dyadic) * half ^ 29),
        ((-222505037 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-72775147 : Dyadic) * half ^ 28),
        ((203194389 : Dyadic) * half ^ 30)⟩,
       ⟨((85473743 : Dyadic) * half ^ 28),
        ((-325533355 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word26Step41 :
    word26Chunk41.foldl (fun acc a => a.applyPacked acc)
      word26State41 = word26State42 := by decide +kernel

private def word26Chunk42 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word26State43 : PackedMat2 :=
    ⟨⟨⟨((51304103 : Dyadic) * half ^ 29),
        ((725835589 : Dyadic) * half ^ 31)⟩,
       ⟨((-191187979 : Dyadic) * half ^ 30),
        ((495459067 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-22199951 : Dyadic) * half ^ 25),
        ((-212957421 : Dyadic) * half ^ 31)⟩,
       ⟨((-265350033 : Dyadic) * half ^ 30),
        ((493821261 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((22199951 : Dyadic) * half ^ 25),
        ((212957421 : Dyadic) * half ^ 31)⟩,
       ⟨((-265350033 : Dyadic) * half ^ 30),
        ((493821261 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((51304103 : Dyadic) * half ^ 29),
        ((725835589 : Dyadic) * half ^ 31)⟩,
       ⟨((191187979 : Dyadic) * half ^ 30),
        ((-495459067 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word26Step42 :
    word26Chunk42.foldl (fun acc a => a.applyPacked acc)
      word26State42 = word26State43 := by decide +kernel

private def word26Chunk43 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word26State44 : PackedMat2 :=
    ⟨⟨⟨((12914071 : Dyadic) * half ^ 27),
        ((-125800019 : Dyadic) * half ^ 30)⟩,
       ⟨((431708653 : Dyadic) * half ^ 30),
        ((-75180815 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-25107797 : Dyadic) * half ^ 30),
        ((-1320226857 : Dyadic) * half ^ 31)⟩,
       ⟨((-203882575 : Dyadic) * half ^ 30),
        ((-62049605 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-1196127647 : Dyadic) * half ^ 31),
        ((89387389 : Dyadic) * half ^ 30)⟩,
       ⟨((1444326067 : Dyadic) * half ^ 31),
        ((57247593 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((176419223 : Dyadic) * half ^ 31),
        ((328396085 : Dyadic) * half ^ 31)⟩,
       ⟨((-326780853 : Dyadic) * half ^ 31),
        ((535021221 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word26Step43 :
    word26Chunk43.foldl (fun acc a => a.applyPacked acc)
      word26State43 = word26State44 := by decide +kernel

private def word26Chunk44 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State45 : PackedMat2 :=
    ⟨⟨⟨((-838696515 : Dyadic) * half ^ 32),
        ((61241989 : Dyadic) * half ^ 31)⟩,
       ⟨((-933357429 : Dyadic) * half ^ 32),
        ((1678828855 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((125270403 : Dyadic) * half ^ 32),
        ((773960015 : Dyadic) * half ^ 31)⟩,
       ⟨((-880151375 : Dyadic) * half ^ 32),
        ((-1676718057 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-880151375 : Dyadic) * half ^ 32),
        ((-1676718057 : Dyadic) * half ^ 32)⟩,
       ⟨((125270403 : Dyadic) * half ^ 32),
        ((773960015 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((933357429 : Dyadic) * half ^ 32),
        ((-1678828855 : Dyadic) * half ^ 32)⟩,
       ⟨((838696515 : Dyadic) * half ^ 32),
        ((-61241989 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word26Step44 :
    word26Chunk44.foldl (fun acc a => a.applyPacked acc)
      word26State44 = word26State45 := by decide +kernel

private def word26Chunk45 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word26State46 : PackedMat2 :=
    ⟨⟨⟨((-4395555429 : Dyadic) * half ^ 33),
        ((-316043961 : Dyadic) * half ^ 33)⟩,
       ⟨((-2870907591 : Dyadic) * half ^ 33),
        ((1666190185 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((3313210299 : Dyadic) * half ^ 33),
        ((2280310087 : Dyadic) * half ^ 33)⟩,
       ⟨((-1435831143 : Dyadic) * half ^ 33),
        ((-108407679 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((2713940803 : Dyadic) * half ^ 33),
        ((2374520721 : Dyadic) * half ^ 33)⟩,
       ⟨((-1846679371 : Dyadic) * half ^ 33),
        ((-469344789 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((3648424331 : Dyadic) * half ^ 33),
        ((762323919 : Dyadic) * half ^ 33)⟩,
       ⟨((3016336409 : Dyadic) * half ^ 33),
        ((-1816615755 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word26Step45 :
    word26Chunk45.foldl (fun acc a => a.applyPacked acc)
      word26State45 = word26State46 := by decide +kernel

private def word26Chunk46 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word26State47 : PackedMat2 :=
    ⟨⟨⟨((-3500521805 : Dyadic) * half ^ 33),
        ((3822246411 : Dyadic) * half ^ 34)⟩,
       ⟨((-123045205 : Dyadic) * half ^ 32),
        ((7224887259 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((660551055 : Dyadic) * half ^ 33),
        ((1642471649 : Dyadic) * half ^ 34)⟩,
       ⟨((2330522355 : Dyadic) * half ^ 32),
        ((3019257885 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((660551055 : Dyadic) * half ^ 33),
        ((1642471649 : Dyadic) * half ^ 34)⟩,
       ⟨((-2330522355 : Dyadic) * half ^ 32),
        ((-3019257885 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3500521805 : Dyadic) * half ^ 33),
        ((-3822246411 : Dyadic) * half ^ 34)⟩,
       ⟨((-123045205 : Dyadic) * half ^ 32),
        ((7224887259 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word26Step46 :
    word26Chunk46.foldl (fun acc a => a.applyPacked acc)
      word26State46 = word26State47 := by decide +kernel

private def word26Chunk47 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word26State48 : PackedMat2 :=
    ⟨⟨⟨((1356898673 : Dyadic) * half ^ 34),
        ((-571939335 : Dyadic) * half ^ 30)⟩,
       ⟨((-61729327 : Dyadic) * half ^ 34),
        ((-3117712207 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-4308668459 : Dyadic) * half ^ 34),
        ((-2703895897 : Dyadic) * half ^ 34)⟩,
       ⟨((3853937947 : Dyadic) * half ^ 34),
        ((99098657 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1401497277 : Dyadic) * half ^ 33),
        ((4081303203 : Dyadic) * half ^ 34)⟩,
       ⟨((-325599655 : Dyadic) * half ^ 31),
        ((-28420657 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1457802473 : Dyadic) * half ^ 33),
        ((44332125 : Dyadic) * half ^ 30)⟩,
       ⟨((7693226887 : Dyadic) * half ^ 33),
        ((-647584673 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word26Step47 :
    word26Chunk47.foldl (fun acc a => a.applyPacked acc)
      word26State47 = word26State48 := by decide +kernel

private def word26Chunk48 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word26State49 : PackedMat2 :=
    ⟨⟨⟨((1078512625 : Dyadic) * half ^ 32),
        ((-918574947 : Dyadic) * half ^ 32)⟩,
       ⟨((-1796941677 : Dyadic) * half ^ 33),
        ((-14003038917 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-100378827 : Dyadic) * half ^ 31),
        ((-13694724371 : Dyadic) * half ^ 35)⟩,
       ⟨((5391510077 : Dyadic) * half ^ 34),
        ((-2746943001 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-100378827 : Dyadic) * half ^ 31),
        ((-13694724371 : Dyadic) * half ^ 35)⟩,
       ⟨((-5391510077 : Dyadic) * half ^ 34),
        ((2746943001 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1078512625 : Dyadic) * half ^ 32),
        ((918574947 : Dyadic) * half ^ 32)⟩,
       ⟨((-1796941677 : Dyadic) * half ^ 33),
        ((-14003038917 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word26Step48 :
    word26Chunk48.foldl (fun acc a => a.applyPacked acc)
      word26State48 = word26State49 := by decide +kernel

private def word26Chunk49 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word26State50 : PackedMat2 :=
    ⟨⟨⟨((5247249369 : Dyadic) * half ^ 36),
        ((1880720485 : Dyadic) * half ^ 36)⟩,
       ⟨((-6820166281 : Dyadic) * half ^ 36),
        ((-21477148359 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-24389925051 : Dyadic) * half ^ 36),
        ((10390680009 : Dyadic) * half ^ 36)⟩,
       ⟨((8749696291 : Dyadic) * half ^ 36),
        ((-705683763 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((8749696291 : Dyadic) * half ^ 36),
        ((-705683763 : Dyadic) * half ^ 33)⟩,
       ⟨((-24389925051 : Dyadic) * half ^ 36),
        ((10390680009 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((6820166281 : Dyadic) * half ^ 36),
        ((21477148359 : Dyadic) * half ^ 35)⟩,
       ⟨((-5247249369 : Dyadic) * half ^ 36),
        ((-1880720485 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word26Step49 :
    word26Chunk49.foldl (fun acc a => a.applyPacked acc)
      word26State49 = word26State50 := by decide +kernel

private def word26Chunk50 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word26State51 : PackedMat2 :=
    ⟨⟨⟨((12788286005 : Dyadic) * half ^ 35),
        ((19643584839 : Dyadic) * half ^ 36)⟩,
       ⟨((-6485005235 : Dyadic) * half ^ 36),
        ((6869687019 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((36374977553 : Dyadic) * half ^ 36),
        ((-2566070265 : Dyadic) * half ^ 34)⟩,
       ⟨((-2288419645 : Dyadic) * half ^ 32),
        ((545581977 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((2288419645 : Dyadic) * half ^ 32),
        ((-545581977 : Dyadic) * half ^ 35)⟩,
       ⟨((-36374977553 : Dyadic) * half ^ 36),
        ((2566070265 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-6485005235 : Dyadic) * half ^ 36),
        ((6869687019 : Dyadic) * half ^ 35)⟩,
       ⟨((12788286005 : Dyadic) * half ^ 35),
        ((19643584839 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word26Step50 :
    word26Chunk50.foldl (fun acc a => a.applyPacked acc)
      word26State50 = word26State51 := by decide +kernel

private def word26Chunk51 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word26State52 : PackedMat2 :=
    ⟨⟨⟨((37114302133 : Dyadic) * half ^ 37),
        ((97188810663 : Dyadic) * half ^ 38)⟩,
       ⟨((47379904537 : Dyadic) * half ^ 37),
        ((11562067537 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-464309123 : Dyadic) * half ^ 32),
        ((88042073051 : Dyadic) * half ^ 38)⟩,
       ⟨((-6685718969 : Dyadic) * half ^ 35),
        ((106450216687 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-6685718969 : Dyadic) * half ^ 35),
        ((106450216687 : Dyadic) * half ^ 38)⟩,
       ⟨((-464309123 : Dyadic) * half ^ 32),
        ((88042073051 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-47379904537 : Dyadic) * half ^ 37),
        ((-11562067537 : Dyadic) * half ^ 38)⟩,
       ⟨((-37114302133 : Dyadic) * half ^ 37),
        ((-97188810663 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word26Step51 :
    word26Chunk51.foldl (fun acc a => a.applyPacked acc)
      word26State51 = word26State52 := by decide +kernel

private def word26Chunk52 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word26State53 : PackedMat2 :=
    ⟨⟨⟨((-68423710983 : Dyadic) * half ^ 38),
        ((-12566263917 : Dyadic) * half ^ 39)⟩,
       ⟨((3656493095 : Dyadic) * half ^ 35),
        ((258163022847 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-14983208543 : Dyadic) * half ^ 38),
        ((-194169373335 : Dyadic) * half ^ 39)⟩,
       ⟨((18004206669 : Dyadic) * half ^ 36),
        ((-157197722111 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((175683547723 : Dyadic) * half ^ 38),
        ((-57033618133 : Dyadic) * half ^ 39)⟩,
       ⟨((4621456403 : Dyadic) * half ^ 36),
        ((87000035219 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((122798379465 : Dyadic) * half ^ 38),
        ((-39171766223 : Dyadic) * half ^ 39)⟩,
       ⟨((-67682321691 : Dyadic) * half ^ 37),
        ((-97675655743 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word26Step52 :
    word26Chunk52.foldl (fun acc a => a.applyPacked acc)
      word26State52 = word26State53 := by decide +kernel

private def word26Chunk53 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word26State54 : PackedMat2 :=
    ⟨⟨⟨((-14200354305 : Dyadic) * half ^ 37),
        ((-147294954537 : Dyadic) * half ^ 38)⟩,
       ⟨((29430621297 : Dyadic) * half ^ 37),
        ((101567673857 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-49440622257 : Dyadic) * half ^ 37),
        ((69898784471 : Dyadic) * half ^ 39)⟩,
       ⟨((-71464492947 : Dyadic) * half ^ 38),
        ((13001706429 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-49440622257 : Dyadic) * half ^ 37),
        ((69898784471 : Dyadic) * half ^ 39)⟩,
       ⟨((71464492947 : Dyadic) * half ^ 38),
        ((-13001706429 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((14200354305 : Dyadic) * half ^ 37),
        ((147294954537 : Dyadic) * half ^ 38)⟩,
       ⟨((29430621297 : Dyadic) * half ^ 37),
        ((101567673857 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word26Step53 :
    word26Chunk53.foldl (fun acc a => a.applyPacked acc)
      word26State53 = word26State54 := by decide +kernel

private def word26Chunk54 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word26State55 : PackedMat2 :=
    ⟨⟨⟨((-672787436375 : Dyadic) * half ^ 40),
        ((-65476169755 : Dyadic) * half ^ 39)⟩,
       ⟨((320246366397 : Dyadic) * half ^ 40),
        ((-347213161347 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-113431028095 : Dyadic) * half ^ 40),
        ((-24314880729 : Dyadic) * half ^ 36)⟩,
       ⟨((203287049053 : Dyadic) * half ^ 40),
        ((-103490735407 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((285547356257 : Dyadic) * half ^ 40),
        ((79179519287 : Dyadic) * half ^ 39)⟩,
       ⟨((-492528827071 : Dyadic) * half ^ 40),
        ((44928010479 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((216260821837 : Dyadic) * half ^ 40),
        ((-248258450693 : Dyadic) * half ^ 39)⟩,
       ⟨((478165500857 : Dyadic) * half ^ 40),
        ((176270534989 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word26Step54 :
    word26Chunk54.foldl (fun acc a => a.applyPacked acc)
      word26State54 = word26State55 := by decide +kernel

private def word26Chunk55 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word26State56 : PackedMat2 :=
    ⟨⟨⟨((-878373329943 : Dyadic) * half ^ 40),
        ((-59184375863 : Dyadic) * half ^ 40)⟩,
       ⟨((-9534133093 : Dyadic) * half ^ 38),
        ((-13288304975 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-128188465757 : Dyadic) * half ^ 38),
        ((31987194451 : Dyadic) * half ^ 38)⟩,
       ⟨((-51381061821 : Dyadic) * half ^ 40),
        ((-255220161743 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((127271383939 : Dyadic) * half ^ 40),
        ((564134924849 : Dyadic) * half ^ 41)⟩,
       ⟨((-383168939547 : Dyadic) * half ^ 40),
        ((461372801207 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-36236340419 : Dyadic) * half ^ 39),
        ((-916509862315 : Dyadic) * half ^ 41)⟩,
       ⟨((-5737008861 : Dyadic) * half ^ 37),
        ((-840236797571 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word26Step55 :
    word26Chunk55.foldl (fun acc a => a.applyPacked acc)
      word26State55 = word26State56 := by decide +kernel

private def word26Chunk56 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word26State57 : PackedMat2 :=
    ⟨⟨⟨((-239466879741 : Dyadic) * half ^ 41),
        ((1116129421987 : Dyadic) * half ^ 42)⟩,
       ⟨((849154124811 : Dyadic) * half ^ 41),
        ((-1522924816031 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-291211570037 : Dyadic) * half ^ 40),
        ((-1053312942849 : Dyadic) * half ^ 42)⟩,
       ⟨((-463284122673 : Dyadic) * half ^ 40),
        ((-1022051092817 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-463284122673 : Dyadic) * half ^ 40),
        ((-1022051092817 : Dyadic) * half ^ 42)⟩,
       ⟨((-291211570037 : Dyadic) * half ^ 40),
        ((-1053312942849 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-849154124811 : Dyadic) * half ^ 41),
        ((1522924816031 : Dyadic) * half ^ 42)⟩,
       ⟨((239466879741 : Dyadic) * half ^ 41),
        ((-1116129421987 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word26Step56 :
    word26Chunk56.foldl (fun acc a => a.applyPacked acc)
      word26State56 = word26State57 := by decide +kernel

private def word26Chunk57 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word26State58 : PackedMat2 :=
    ⟨⟨⟨((1304657315009 : Dyadic) * half ^ 42),
        ((2552982441969 : Dyadic) * half ^ 43)⟩,
       ⟨((-436690192689 : Dyadic) * half ^ 40),
        ((2470292566337 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-330142394525 : Dyadic) * half ^ 42),
        ((466892057739 : Dyadic) * half ^ 43)⟩,
       ⟨((-142473556941 : Dyadic) * half ^ 41),
        ((-3995070438093 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((1764089190177 : Dyadic) * half ^ 42),
        ((615089508407 : Dyadic) * half ^ 43)⟩,
       ⟨((-557745311979 : Dyadic) * half ^ 40),
        ((45195280643 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((2511637504153 : Dyadic) * half ^ 42),
        ((-442103455747 : Dyadic) * half ^ 43)⟩,
       ⟨((5168117227 : Dyadic) * half ^ 39),
        ((3051418085765 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word26Step57 :
    word26Chunk57.foldl (fun acc a => a.applyPacked acc)
      word26State57 = word26State58 := by decide +kernel

private def word26Chunk58 : List Letter := [.t, .h, .s]
private def word26State59 : PackedMat2 :=
    ⟨⟨⟨((3274026440031 : Dyadic) * half ^ 42),
        ((1589604428891 : Dyadic) * half ^ 43)⟩,
       ⟨((1001700254299 : Dyadic) * half ^ 42),
        ((-1416618376231 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((734296156019 : Dyadic) * half ^ 41),
        ((-2076903165281 : Dyadic) * half ^ 43)⟩,
       ⟨((-360521999031 : Dyadic) * half ^ 41),
        ((1019710201127 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-734296156019 : Dyadic) * half ^ 41),
        ((2076903165281 : Dyadic) * half ^ 43)⟩,
       ⟨((-360521999031 : Dyadic) * half ^ 41),
        ((1019710201127 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((3274026440031 : Dyadic) * half ^ 42),
        ((1589604428891 : Dyadic) * half ^ 43)⟩,
       ⟨((-1001700254299 : Dyadic) * half ^ 42),
        ((1416618376231 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word26Step58 :
    word26Chunk58.foldl (fun acc a => a.applyPacked acc)
      word26State58 = word26State59 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word26_check : check word26 26 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word26 = word26State59.toMatrix := by
    unfold evalRingPacked
    change ((
      word26Chunk0 ++ word26Chunk1 ++ word26Chunk2 ++ word26Chunk3 ++
      word26Chunk4 ++ word26Chunk5 ++ word26Chunk6 ++ word26Chunk7 ++
      word26Chunk8 ++ word26Chunk9 ++ word26Chunk10 ++ word26Chunk11 ++
      word26Chunk12 ++ word26Chunk13 ++ word26Chunk14 ++ word26Chunk15 ++
      word26Chunk16 ++ word26Chunk17 ++ word26Chunk18 ++ word26Chunk19 ++
      word26Chunk20 ++ word26Chunk21 ++ word26Chunk22 ++ word26Chunk23 ++
      word26Chunk24 ++ word26Chunk25 ++ word26Chunk26 ++ word26Chunk27 ++
      word26Chunk28 ++ word26Chunk29 ++ word26Chunk30 ++ word26Chunk31 ++
      word26Chunk32 ++ word26Chunk33 ++ word26Chunk34 ++ word26Chunk35 ++
      word26Chunk36 ++ word26Chunk37 ++ word26Chunk38 ++ word26Chunk39 ++
      word26Chunk40 ++ word26Chunk41 ++ word26Chunk42 ++ word26Chunk43 ++
      word26Chunk44 ++ word26Chunk45 ++ word26Chunk46 ++ word26Chunk47 ++
      word26Chunk48 ++ word26Chunk49 ++ word26Chunk50 ++ word26Chunk51 ++
      word26Chunk52 ++ word26Chunk53 ++ word26Chunk54 ++ word26Chunk55 ++
      word26Chunk56 ++ word26Chunk57 ++ word26Chunk58
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word26Step0, word26Step1, word26Step2, word26Step3, word26Step4,
      word26Step5, word26Step6, word26Step7, word26Step8, word26Step9,
      word26Step10, word26Step11, word26Step12, word26Step13, word26Step14,
      word26Step15, word26Step16, word26Step17, word26Step18, word26Step19,
      word26Step20, word26Step21, word26Step22, word26Step23, word26Step24,
      word26Step25, word26Step26, word26Step27, word26Step28, word26Step29,
      word26Step30, word26Step31, word26Step32, word26Step33, word26Step34,
      word26Step35, word26Step36, word26Step37, word26Step38, word26Step39,
      word26Step40, word26Step41, word26Step42, word26Step43, word26Step44,
      word26Step45, word26Step46, word26Step47, word26Step48, word26Step49,
      word26Step50, word26Step51, word26Step52, word26Step53, word26Step54,
      word26Step55, word26Step56, word26Step57, word26Step58]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
