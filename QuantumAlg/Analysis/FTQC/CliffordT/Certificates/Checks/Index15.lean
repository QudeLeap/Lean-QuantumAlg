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
private def word15Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word15State1 : PackedMat2 :=
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
private lemma word15Step0 :
    word15Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word15State1 := by decide +kernel

private def word15Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word15State2 : PackedMat2 :=
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
private lemma word15Step1 :
    word15Chunk1.foldl (fun acc a => a.applyPacked acc)
      word15State1 = word15State2 := by decide +kernel

private def word15Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word15State3 : PackedMat2 :=
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
private lemma word15Step2 :
    word15Chunk2.foldl (fun acc a => a.applyPacked acc)
      word15State2 = word15State3 := by decide +kernel

private def word15Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word15State4 : PackedMat2 :=
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
private lemma word15Step3 :
    word15Chunk3.foldl (fun acc a => a.applyPacked acc)
      word15State3 = word15State4 := by decide +kernel

private def word15Chunk4 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word15State5 : PackedMat2 :=
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
private lemma word15Step4 :
    word15Chunk4.foldl (fun acc a => a.applyPacked acc)
      word15State4 = word15State5 := by decide +kernel

private def word15Chunk5 : List Letter := [.h, .s, .s, .s, .h, .s, .s, .h]
private def word15State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word15Step5 :
    word15Chunk5.foldl (fun acc a => a.applyPacked acc)
      word15State5 = word15State6 := by decide +kernel

private def word15Chunk6 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word15State7 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word15Step6 :
    word15Chunk6.foldl (fun acc a => a.applyPacked acc)
      word15State6 = word15State7 := by decide +kernel

private def word15Chunk7 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word15State8 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word15Step7 :
    word15Chunk7.foldl (fun acc a => a.applyPacked acc)
      word15State7 = word15State8 := by decide +kernel

private def word15Chunk8 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word15State9 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word15Step8 :
    word15Chunk8.foldl (fun acc a => a.applyPacked acc)
      word15State8 = word15State9 := by decide +kernel

private def word15Chunk9 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word15State10 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word15Step9 :
    word15Chunk9.foldl (fun acc a => a.applyPacked acc)
      word15State9 = word15State10 := by decide +kernel

private def word15Chunk10 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word15State11 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((17 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word15Step10 :
    word15Chunk10.foldl (fun acc a => a.applyPacked acc)
      word15State10 = word15State11 := by decide +kernel

private def word15Chunk11 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word15State12 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((13 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((29 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word15Step11 :
    word15Chunk11.foldl (fun acc a => a.applyPacked acc)
      word15State11 = word15State12 := by decide +kernel

private def word15Chunk12 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word15State13 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-29 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 5)⟩,
       ⟨((33 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-29 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word15Step12 :
    word15Chunk12.foldl (fun acc a => a.applyPacked acc)
      word15State12 = word15State13 := by decide +kernel

private def word15Chunk13 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word15State14 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-69 : Dyadic) * half ^ 7),
        ((-39 : Dyadic) * half ^ 7)⟩,
       ⟨((-61 : Dyadic) * half ^ 7),
        ((33 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((-65 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((39 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word15Step13 :
    word15Chunk13.foldl (fun acc a => a.applyPacked acc)
      word15State13 = word15State14 := by decide +kernel

private def word15Chunk14 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word15State15 : PackedMat2 :=
    ⟨⟨⟨((49 : Dyadic) * half ^ 8),
        ((49 : Dyadic) * half ^ 8)⟩,
       ⟨((-33 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((75 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((25 : Dyadic) * half ^ 8),
        ((-157 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 8),
        ((157 : Dyadic) * half ^ 8)⟩,
       ⟨((-75 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((49 : Dyadic) * half ^ 8),
        ((49 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word15Step14 :
    word15Chunk14.foldl (fun acc a => a.applyPacked acc)
      word15State14 = word15State15 := by decide +kernel

private def word15Chunk15 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word15State16 : PackedMat2 :=
    ⟨⟨⟨((-17 : Dyadic) * half ^ 8),
        ((13 : Dyadic) * half ^ 7)⟩,
       ⟨((-39 : Dyadic) * half ^ 7),
        ((33 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 7),
        ((273 : Dyadic) * half ^ 9)⟩,
       ⟨((-65 : Dyadic) * half ^ 7),
        ((25 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 7),
        ((273 : Dyadic) * half ^ 9)⟩,
       ⟨((65 : Dyadic) * half ^ 7),
        ((-25 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 8),
        ((-13 : Dyadic) * half ^ 7)⟩,
       ⟨((-39 : Dyadic) * half ^ 7),
        ((33 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word15Step15 :
    word15Chunk15.foldl (fun acc a => a.applyPacked acc)
      word15State15 = word15State16 := by decide +kernel

private def word15Chunk16 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word15State17 : PackedMat2 :=
    ⟨⟨⟨((53 : Dyadic) * half ^ 7),
        ((107 : Dyadic) * half ^ 10)⟩,
       ⟨((-29 : Dyadic) * half ^ 9),
        ((-13 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((227 : Dyadic) * half ^ 9),
        ((-195 : Dyadic) * half ^ 10)⟩,
       ⟨((93 : Dyadic) * half ^ 7),
        ((57 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((63 : Dyadic) * half ^ 8),
        ((145 : Dyadic) * half ^ 10)⟩,
       ⟨((-69 : Dyadic) * half ^ 9),
        ((599 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 7),
        ((241 : Dyadic) * half ^ 10)⟩,
       ⟨((-47 : Dyadic) * half ^ 9),
        ((-183 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word15Step16 :
    word15Chunk16.foldl (fun acc a => a.applyPacked acc)
      word15State16 = word15State17 := by decide +kernel

private def word15Chunk17 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word15State18 : PackedMat2 :=
    ⟨⟨⟨((17 : Dyadic) * half ^ 8),
        ((637 : Dyadic) * half ^ 11)⟩,
       ⟨((91 : Dyadic) * half ^ 10),
        ((599 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((-617 : Dyadic) * half ^ 11)⟩,
       ⟨((641 : Dyadic) * half ^ 10),
        ((63 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((-617 : Dyadic) * half ^ 11)⟩,
       ⟨((-641 : Dyadic) * half ^ 10),
        ((-63 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 8),
        ((-637 : Dyadic) * half ^ 11)⟩,
       ⟨((91 : Dyadic) * half ^ 10),
        ((599 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word15Step17 :
    word15Chunk17.foldl (fun acc a => a.applyPacked acc)
      word15State17 = word15State18 := by decide +kernel

private def word15Chunk18 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word15State19 : PackedMat2 :=
    ⟨⟨⟨((-77 : Dyadic) * half ^ 11),
        ((451 : Dyadic) * half ^ 12)⟩,
       ⟨((177 : Dyadic) * half ^ 9),
        ((-773 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-337 : Dyadic) * half ^ 11),
        ((-2021 : Dyadic) * half ^ 12)⟩,
       ⟨((-33 : Dyadic) * half ^ 10),
        ((1501 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((337 : Dyadic) * half ^ 11),
        ((2021 : Dyadic) * half ^ 12)⟩,
       ⟨((-33 : Dyadic) * half ^ 10),
        ((1501 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-77 : Dyadic) * half ^ 11),
        ((451 : Dyadic) * half ^ 12)⟩,
       ⟨((-177 : Dyadic) * half ^ 9),
        ((773 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word15Step18 :
    word15Chunk18.foldl (fun acc a => a.applyPacked acc)
      word15State18 = word15State19 := by decide +kernel

private def word15Chunk19 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word15State20 : PackedMat2 :=
    ⟨⟨⟨((159 : Dyadic) * half ^ 11),
        ((779 : Dyadic) * half ^ 12)⟩,
       ⟨((-253 : Dyadic) * half ^ 10),
        ((839 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1435 : Dyadic) * half ^ 12),
        ((175 : Dyadic) * half ^ 11)⟩,
       ⟨((-1239 : Dyadic) * half ^ 12),
        ((-197 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((963 : Dyadic) * half ^ 11),
        ((-49 : Dyadic) * half ^ 11)⟩,
       ⟨((613 : Dyadic) * half ^ 11),
        ((1337 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((899 : Dyadic) * half ^ 12),
        ((-665 : Dyadic) * half ^ 12)⟩,
       ⟨((2457 : Dyadic) * half ^ 12),
        ((-347 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word15Step19 :
    word15Chunk19.foldl (fun acc a => a.applyPacked acc)
      word15State19 = word15State20 := by decide +kernel

private def word15Chunk20 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word15State21 : PackedMat2 :=
    ⟨⟨⟨((-1151 : Dyadic) * half ^ 11),
        ((-1787 : Dyadic) * half ^ 13)⟩,
       ⟨((-355 : Dyadic) * half ^ 11),
        ((2595 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-827 : Dyadic) * half ^ 12),
        ((89 : Dyadic) * half ^ 11)⟩,
       ⟨((317 : Dyadic) * half ^ 11),
        ((-1559 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-827 : Dyadic) * half ^ 12),
        ((89 : Dyadic) * half ^ 11)⟩,
       ⟨((-317 : Dyadic) * half ^ 11),
        ((1559 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1151 : Dyadic) * half ^ 11),
        ((1787 : Dyadic) * half ^ 13)⟩,
       ⟨((-355 : Dyadic) * half ^ 11),
        ((2595 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word15Step20 :
    word15Chunk20.foldl (fun acc a => a.applyPacked acc)
      word15State20 = word15State21 := by decide +kernel

private def word15Chunk21 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word15State22 : PackedMat2 :=
    ⟨⟨⟨((1279 : Dyadic) * half ^ 12),
        ((-3861 : Dyadic) * half ^ 14)⟩,
       ⟨((193 : Dyadic) * half ^ 13),
        ((-7201 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4121 : Dyadic) * half ^ 13),
        ((2893 : Dyadic) * half ^ 14)⟩,
       ⟨((-1219 : Dyadic) * half ^ 12),
        ((269 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4121 : Dyadic) * half ^ 13),
        ((-2893 : Dyadic) * half ^ 14)⟩,
       ⟨((-1219 : Dyadic) * half ^ 12),
        ((269 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1279 : Dyadic) * half ^ 12),
        ((-3861 : Dyadic) * half ^ 14)⟩,
       ⟨((-193 : Dyadic) * half ^ 13),
        ((7201 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word15Step21 :
    word15Chunk21.foldl (fun acc a => a.applyPacked acc)
      word15State21 = word15State22 := by decide +kernel

private def word15Chunk22 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word15State23 : PackedMat2 :=
    ⟨⟨⟨((-5635 : Dyadic) * half ^ 14),
        ((5317 : Dyadic) * half ^ 14)⟩,
       ⟨((-5955 : Dyadic) * half ^ 14),
        ((-5017 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 11),
        ((2681 : Dyadic) * half ^ 13)⟩,
       ⟨((1515 : Dyadic) * half ^ 12),
        ((191 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1515 : Dyadic) * half ^ 12),
        ((-191 : Dyadic) * half ^ 14)⟩,
       ⟨((25 : Dyadic) * half ^ 11),
        ((-2681 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-5955 : Dyadic) * half ^ 14),
        ((-5017 : Dyadic) * half ^ 14)⟩,
       ⟨((-5635 : Dyadic) * half ^ 14),
        ((5317 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word15Step22 :
    word15Chunk22.foldl (fun acc a => a.applyPacked acc)
      word15State22 = word15State23 := by decide +kernel

private def word15Chunk23 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word15State24 : PackedMat2 :=
    ⟨⟨⟨((16371 : Dyadic) * half ^ 15),
        ((-1535 : Dyadic) * half ^ 14)⟩,
       ⟨((-4551 : Dyadic) * half ^ 15),
        ((7669 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-389 : Dyadic) * half ^ 15),
        ((-7239 : Dyadic) * half ^ 14)⟩,
       ⟨((9627 : Dyadic) * half ^ 15),
        ((8261 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((9627 : Dyadic) * half ^ 15),
        ((8261 : Dyadic) * half ^ 15)⟩,
       ⟨((-389 : Dyadic) * half ^ 15),
        ((-7239 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4551 : Dyadic) * half ^ 15),
        ((-7669 : Dyadic) * half ^ 15)⟩,
       ⟨((-16371 : Dyadic) * half ^ 15),
        ((1535 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word15Step23 :
    word15Chunk23.foldl (fun acc a => a.applyPacked acc)
      word15State23 = word15State24 := by decide +kernel

private def word15Chunk24 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word15State25 : PackedMat2 :=
    ⟨⟨⟨((12955 : Dyadic) * half ^ 15),
        ((9649 : Dyadic) * half ^ 16)⟩,
       ⟨((16093 : Dyadic) * half ^ 15),
        ((2399 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((69 : Dyadic) * half ^ 15),
        ((-10595 : Dyadic) * half ^ 15)⟩,
       ⟨((2283 : Dyadic) * half ^ 12),
        ((-4439 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-69 : Dyadic) * half ^ 15),
        ((10595 : Dyadic) * half ^ 15)⟩,
       ⟨((2283 : Dyadic) * half ^ 12),
        ((-4439 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((12955 : Dyadic) * half ^ 15),
        ((9649 : Dyadic) * half ^ 16)⟩,
       ⟨((-16093 : Dyadic) * half ^ 15),
        ((-2399 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word15Step24 :
    word15Chunk24.foldl (fun acc a => a.applyPacked acc)
      word15State24 = word15State25 := by decide +kernel

private def word15Chunk25 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word15State26 : PackedMat2 :=
    ⟨⟨⟨((-6513 : Dyadic) * half ^ 16),
        ((44701 : Dyadic) * half ^ 17)⟩,
       ⟨((16809 : Dyadic) * half ^ 15),
        ((32957 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-26499 : Dyadic) * half ^ 16),
        ((18665 : Dyadic) * half ^ 17)⟩,
       ⟨((-12451 : Dyadic) * half ^ 15),
        ((12939 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((2863 : Dyadic) * half ^ 16),
        ((-1597 : Dyadic) * half ^ 17)⟩,
       ⟨((-7901 : Dyadic) * half ^ 15),
        ((51401 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-367 : Dyadic) * half ^ 12),
        ((40131 : Dyadic) * half ^ 17)⟩,
       ⟨((38829 : Dyadic) * half ^ 16),
        ((27105 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word15Step25 :
    word15Chunk25.foldl (fun acc a => a.applyPacked acc)
      word15State25 = word15State26 := by decide +kernel

private def word15Chunk26 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word15State27 : PackedMat2 :=
    ⟨⟨⟨((6973 : Dyadic) * half ^ 16),
        ((-11895 : Dyadic) * half ^ 16)⟩,
       ⟨((5321 : Dyadic) * half ^ 16),
        ((81669 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((37695 : Dyadic) * half ^ 17),
        ((-12903 : Dyadic) * half ^ 17)⟩,
       ⟨((25269 : Dyadic) * half ^ 17),
        ((-2017 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((25269 : Dyadic) * half ^ 17),
        ((-2017 : Dyadic) * half ^ 17)⟩,
       ⟨((37695 : Dyadic) * half ^ 17),
        ((-12903 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-5321 : Dyadic) * half ^ 16),
        ((-81669 : Dyadic) * half ^ 17)⟩,
       ⟨((-6973 : Dyadic) * half ^ 16),
        ((11895 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word15Step26 :
    word15Chunk26.foldl (fun acc a => a.applyPacked acc)
      word15State26 = word15State27 := by decide +kernel

private def word15Chunk27 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word15State28 : PackedMat2 :=
    ⟨⟨⟨((-10843 : Dyadic) * half ^ 17),
        ((-27037 : Dyadic) * half ^ 16)⟩,
       ⟨((1671 : Dyadic) * half ^ 17),
        ((124773 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((9841 : Dyadic) * half ^ 18),
        ((-52947 : Dyadic) * half ^ 18)⟩,
       ⟨((-39473 : Dyadic) * half ^ 18),
        ((56779 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-54863 : Dyadic) * half ^ 17),
        ((24657 : Dyadic) * half ^ 18)⟩,
       ⟨((-479 : Dyadic) * half ^ 15),
        ((463 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((232921 : Dyadic) * half ^ 18),
        ((6257 : Dyadic) * half ^ 17)⟩,
       ⟨((16625 : Dyadic) * half ^ 18),
        ((-2293 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word15Step27 :
    word15Chunk27.foldl (fun acc a => a.applyPacked acc)
      word15State27 = word15State28 := by decide +kernel

private def word15Chunk28 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word15State29 : PackedMat2 :=
    ⟨⟨⟨((-259111 : Dyadic) * half ^ 19),
        ((-5605 : Dyadic) * half ^ 15)⟩,
       ⟨((237701 : Dyadic) * half ^ 19),
        ((-157753 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-69763 : Dyadic) * half ^ 19),
        ((-171711 : Dyadic) * half ^ 19)⟩,
       ⟨((145085 : Dyadic) * half ^ 19),
        ((983 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((145085 : Dyadic) * half ^ 19),
        ((983 : Dyadic) * half ^ 15)⟩,
       ⟨((-69763 : Dyadic) * half ^ 19),
        ((-171711 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-237701 : Dyadic) * half ^ 19),
        ((157753 : Dyadic) * half ^ 19)⟩,
       ⟨((259111 : Dyadic) * half ^ 19),
        ((5605 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word15Step28 :
    word15Chunk28.foldl (fun acc a => a.applyPacked acc)
      word15State28 = word15State29 := by decide +kernel

private def word15Chunk29 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word15State30 : PackedMat2 :=
    ⟨⟨⟨((-444665 : Dyadic) * half ^ 19),
        ((5205 : Dyadic) * half ^ 17)⟩,
       ⟨((-2465 : Dyadic) * half ^ 17),
        ((43171 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-66565 : Dyadic) * half ^ 19),
        ((-307531 : Dyadic) * half ^ 20)⟩,
       ⟨((1825 : Dyadic) * half ^ 19),
        ((-138239 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((222885 : Dyadic) * half ^ 19),
        ((16185 : Dyadic) * half ^ 18)⟩,
       ⟨((42323 : Dyadic) * half ^ 18),
        ((34195 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((53581 : Dyadic) * half ^ 18),
        ((-454525 : Dyadic) * half ^ 20)⟩,
       ⟨((-32761 : Dyadic) * half ^ 18),
        ((-434805 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word15Step29 :
    word15Chunk29.foldl (fun acc a => a.applyPacked acc)
      word15State29 = word15State30 := by decide +kernel

private def word15Chunk30 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word15State31 : PackedMat2 :=
    ⟨⟨⟨((53325 : Dyadic) * half ^ 20),
        ((-1200253 : Dyadic) * half ^ 21)⟩,
       ⟨((-169273 : Dyadic) * half ^ 19),
        ((-285611 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-37437 : Dyadic) * half ^ 17),
        ((-167575 : Dyadic) * half ^ 21)⟩,
       ⟨((239861 : Dyadic) * half ^ 20),
        ((-345521 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-37437 : Dyadic) * half ^ 17),
        ((-167575 : Dyadic) * half ^ 21)⟩,
       ⟨((-239861 : Dyadic) * half ^ 20),
        ((345521 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-53325 : Dyadic) * half ^ 20),
        ((1200253 : Dyadic) * half ^ 21)⟩,
       ⟨((-169273 : Dyadic) * half ^ 19),
        ((-285611 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word15Step30 :
    word15Chunk30.foldl (fun acc a => a.applyPacked acc)
      word15State30 = word15State31 := by decide +kernel

private def word15Chunk31 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word15State32 : PackedMat2 :=
    ⟨⟨⟨((-117899 : Dyadic) * half ^ 19),
        ((106885 : Dyadic) * half ^ 18)⟩,
       ⟨((-295461 : Dyadic) * half ^ 20),
        ((-427171 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((95283 : Dyadic) * half ^ 21),
        ((146749 : Dyadic) * half ^ 19)⟩,
       ⟨((-1134451 : Dyadic) * half ^ 21),
        ((-41825 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-335323 : Dyadic) * half ^ 20),
        ((-614867 : Dyadic) * half ^ 21)⟩,
       ⟨((251673 : Dyadic) * half ^ 20),
        ((-16237 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1282251 : Dyadic) * half ^ 21),
        ((59663 : Dyadic) * half ^ 21)⟩,
       ⟨((-427909 : Dyadic) * half ^ 21),
        ((531259 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word15Step31 :
    word15Chunk31.foldl (fun acc a => a.applyPacked acc)
      word15State31 = word15State32 := by decide +kernel

private def word15Chunk32 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word15State33 : PackedMat2 :=
    ⟨⟨⟨((43889 : Dyadic) * half ^ 22),
        ((79411 : Dyadic) * half ^ 18)⟩,
       ⟨((-3015415 : Dyadic) * half ^ 22),
        ((-246621 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((2160989 : Dyadic) * half ^ 22),
        ((-380197 : Dyadic) * half ^ 22)⟩,
       ⟨((-427563 : Dyadic) * half ^ 22),
        ((-25929 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((432055 : Dyadic) * half ^ 22),
        ((-866713 : Dyadic) * half ^ 22)⟩,
       ⟨((328339 : Dyadic) * half ^ 22),
        ((-323569 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1023955 : Dyadic) * half ^ 22),
        ((-1485763 : Dyadic) * half ^ 22)⟩,
       ⟨((1517197 : Dyadic) * half ^ 22),
        ((382413 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word15Step32 :
    word15Chunk32.foldl (fun acc a => a.applyPacked acc)
      word15State32 = word15State33 := by decide +kernel

private def word15Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word15State34 : PackedMat2 :=
    ⟨⟨⟨((1163867 : Dyadic) * half ^ 22),
        ((442947 : Dyadic) * half ^ 22)⟩,
       ⟨((228481 : Dyadic) * half ^ 19),
        ((-2553 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-504469 : Dyadic) * half ^ 21),
        ((2996907 : Dyadic) * half ^ 23)⟩,
       ⟨((646489 : Dyadic) * half ^ 20),
        ((784995 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-504469 : Dyadic) * half ^ 21),
        ((2996907 : Dyadic) * half ^ 23)⟩,
       ⟨((-646489 : Dyadic) * half ^ 20),
        ((-784995 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1163867 : Dyadic) * half ^ 22),
        ((-442947 : Dyadic) * half ^ 22)⟩,
       ⟨((228481 : Dyadic) * half ^ 19),
        ((-2553 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word15Step33 :
    word15Chunk33.foldl (fun acc a => a.applyPacked acc)
      word15State33 = word15State34 := by decide +kernel

private def word15Chunk34 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word15State35 : PackedMat2 :=
    ⟨⟨⟨((8373 : Dyadic) * half ^ 20),
        ((-648749 : Dyadic) * half ^ 24)⟩,
       ⟨((3729399 : Dyadic) * half ^ 23),
        ((5326585 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((787409 : Dyadic) * half ^ 22),
        ((-1916977 : Dyadic) * half ^ 24)⟩,
       ⟨((-2051791 : Dyadic) * half ^ 23),
        ((8189243 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2526555 : Dyadic) * half ^ 22),
        ((-3626609 : Dyadic) * half ^ 24)⟩,
       ⟨((3136133 : Dyadic) * half ^ 23),
        ((-476973 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2987667 : Dyadic) * half ^ 23),
        ((-3662415 : Dyadic) * half ^ 24)⟩,
       ⟨((-1169459 : Dyadic) * half ^ 22),
        ((-3796383 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word15Step34 :
    word15Chunk34.foldl (fun acc a => a.applyPacked acc)
      word15State34 = word15State35 := by decide +kernel

private def word15Chunk35 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word15State36 : PackedMat2 :=
    ⟨⟨⟨((-8835841 : Dyadic) * half ^ 24),
        ((-4719 : Dyadic) * half ^ 20)⟩,
       ⟨((251321 : Dyadic) * half ^ 24),
        ((-511991 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-64887 : Dyadic) * half ^ 17),
        ((-3986121 : Dyadic) * half ^ 24)⟩,
       ⟨((3347879 : Dyadic) * half ^ 23),
        ((-2483611 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-3347879 : Dyadic) * half ^ 23),
        ((2483611 : Dyadic) * half ^ 23)⟩,
       ⟨((64887 : Dyadic) * half ^ 17),
        ((3986121 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((251321 : Dyadic) * half ^ 24),
        ((-511991 : Dyadic) * half ^ 22)⟩,
       ⟨((-8835841 : Dyadic) * half ^ 24),
        ((-4719 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word15Step35 :
    word15Chunk35.foldl (fun acc a => a.applyPacked acc)
      word15State35 = word15State36 := by decide +kernel

private def word15Chunk36 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word15State37 : PackedMat2 :=
    ⟨⟨⟨((19510323 : Dyadic) * half ^ 25),
        ((-201903 : Dyadic) * half ^ 22)⟩,
       ⟨((-12191731 : Dyadic) * half ^ 25),
        ((5180847 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((467411 : Dyadic) * half ^ 25),
        ((-709891 : Dyadic) * half ^ 23)⟩,
       ⟨((-21982177 : Dyadic) * half ^ 25),
        ((-4367369 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-21982177 : Dyadic) * half ^ 25),
        ((-4367369 : Dyadic) * half ^ 25)⟩,
       ⟨((467411 : Dyadic) * half ^ 25),
        ((-709891 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((12191731 : Dyadic) * half ^ 25),
        ((-5180847 : Dyadic) * half ^ 25)⟩,
       ⟨((-19510323 : Dyadic) * half ^ 25),
        ((201903 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word15Step36 :
    word15Chunk36.foldl (fun acc a => a.applyPacked acc)
      word15State36 = word15State37 := by decide +kernel

private def word15Chunk37 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word15State38 : PackedMat2 :=
    ⟨⟨⟨((40973 : Dyadic) * half ^ 18),
        ((12777135 : Dyadic) * half ^ 25)⟩,
       ⟨((18539475 : Dyadic) * half ^ 25),
        ((-762393 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1443695 : Dyadic) * half ^ 22),
        ((-11016247 : Dyadic) * half ^ 26)⟩,
       ⟨((-587713 : Dyadic) * half ^ 23),
        ((-21162445 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((8044673 : Dyadic) * half ^ 24),
        ((-2299677 : Dyadic) * half ^ 24)⟩,
       ⟨((-5073099 : Dyadic) * half ^ 25),
        ((-3475103 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((11252349 : Dyadic) * half ^ 25),
        ((23784019 : Dyadic) * half ^ 26)⟩,
       ⟨((14301921 : Dyadic) * half ^ 25),
        ((-13294931 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word15Step37 :
    word15Chunk37.foldl (fun acc a => a.applyPacked acc)
      word15State37 = word15State38 := by decide +kernel

private def word15Chunk38 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word15State39 : PackedMat2 :=
    ⟨⟨⟨((3030517 : Dyadic) * half ^ 26),
        ((66288273 : Dyadic) * half ^ 27)⟩,
       ⟨((6392861 : Dyadic) * half ^ 24),
        ((26600921 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-16490855 : Dyadic) * half ^ 26),
        ((32639837 : Dyadic) * half ^ 27)⟩,
       ⟨((7688979 : Dyadic) * half ^ 25),
        ((-22295085 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((27467461 : Dyadic) * half ^ 26),
        ((-31868813 : Dyadic) * half ^ 27)⟩,
       ⟨((-646547 : Dyadic) * half ^ 23),
        ((1112897 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-4960919 : Dyadic) * half ^ 24),
        ((22540927 : Dyadic) * half ^ 27)⟩,
       ⟨((46444597 : Dyadic) * half ^ 26),
        ((28601961 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word15Step38 :
    word15Chunk38.foldl (fun acc a => a.applyPacked acc)
      word15State38 = word15State39 := by decide +kernel

private def word15Chunk39 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word15State40 : PackedMat2 :=
    ⟨⟨⟨((-20277199 : Dyadic) * half ^ 27),
        ((65602493 : Dyadic) * half ^ 28)⟩,
       ⟨((3318293 : Dyadic) * half ^ 25),
        ((16800405 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((32131501 : Dyadic) * half ^ 27),
        ((-70766087 : Dyadic) * half ^ 28)⟩,
       ⟨((52635443 : Dyadic) * half ^ 26),
        ((32117719 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-32131501 : Dyadic) * half ^ 27),
        ((70766087 : Dyadic) * half ^ 28)⟩,
       ⟨((52635443 : Dyadic) * half ^ 26),
        ((32117719 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-20277199 : Dyadic) * half ^ 27),
        ((65602493 : Dyadic) * half ^ 28)⟩,
       ⟨((-3318293 : Dyadic) * half ^ 25),
        ((-16800405 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word15Step39 :
    word15Chunk39.foldl (fun acc a => a.applyPacked acc)
      word15State39 = word15State40 := by decide +kernel

private def word15Chunk40 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word15State41 : PackedMat2 :=
    ⟨⟨⟨((443709 : Dyadic) * half ^ 27),
        ((-32623547 : Dyadic) * half ^ 27)⟩,
       ⟨((7923695 : Dyadic) * half ^ 27),
        ((-22626775 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-200438017 : Dyadic) * half ^ 28),
        ((32847827 : Dyadic) * half ^ 28)⟩,
       ⟨((105450669 : Dyadic) * half ^ 28),
        ((66385829 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-16769001 : Dyadic) * half ^ 27),
        ((-152944343 : Dyadic) * half ^ 28)⟩,
       ⟨((-12404207 : Dyadic) * half ^ 25),
        ((23746837 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((42620319 : Dyadic) * half ^ 28),
        ((3739993 : Dyadic) * half ^ 27)⟩,
       ⟨((-87873869 : Dyadic) * half ^ 28),
        ((2091851 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word15Step40 :
    word15Chunk40.foldl (fun acc a => a.applyPacked acc)
      word15State40 = word15State41 := by decide +kernel

private def word15Chunk41 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word15State42 : PackedMat2 :=
    ⟨⟨⟨((73361403 : Dyadic) * half ^ 27),
        ((-54722343 : Dyadic) * half ^ 29)⟩,
       ⟨((-65187237 : Dyadic) * half ^ 27),
        ((-150203277 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-113822597 : Dyadic) * half ^ 28),
        ((11825109 : Dyadic) * half ^ 26)⟩,
       ⟨((55491 : Dyadic) * half ^ 18),
        ((-6915717 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-113822597 : Dyadic) * half ^ 28),
        ((11825109 : Dyadic) * half ^ 26)⟩,
       ⟨((-55491 : Dyadic) * half ^ 18),
        ((6915717 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-73361403 : Dyadic) * half ^ 27),
        ((54722343 : Dyadic) * half ^ 29)⟩,
       ⟨((-65187237 : Dyadic) * half ^ 27),
        ((-150203277 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word15Step41 :
    word15Chunk41.foldl (fun acc a => a.applyPacked acc)
      word15State41 = word15State42 := by decide +kernel

private def word15Chunk42 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word15State43 : PackedMat2 :=
    ⟨⟨⟨((-4122651 : Dyadic) * half ^ 25),
        ((219720039 : Dyadic) * half ^ 30)⟩,
       ⟨((-130377425 : Dyadic) * half ^ 28),
        ((53207329 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-101379523 : Dyadic) * half ^ 29),
        ((135560781 : Dyadic) * half ^ 29)⟩,
       ⟨((-1702169 : Dyadic) * half ^ 23),
        ((-128176325 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((120791869 : Dyadic) * half ^ 29),
        ((210318339 : Dyadic) * half ^ 30)⟩,
       ⟨((-391913431 : Dyadic) * half ^ 29),
        ((-7559293 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((34115921 : Dyadic) * half ^ 27),
        ((-163358633 : Dyadic) * half ^ 29)⟩,
       ⟨((83256355 : Dyadic) * half ^ 29),
        ((97396217 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word15Step42 :
    word15Chunk42.foldl (fun acc a => a.applyPacked acc)
      word15State42 = word15State43 := by decide +kernel

private def word15Chunk43 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word15State44 : PackedMat2 :=
    ⟨⟨⟨((210464249 : Dyadic) * half ^ 30),
        ((-370522895 : Dyadic) * half ^ 31)⟩,
       ⟨((-9030095 : Dyadic) * half ^ 29),
        ((85694227 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-62424065 : Dyadic) * half ^ 28),
        ((900225789 : Dyadic) * half ^ 31)⟩,
       ⟨((-685488125 : Dyadic) * half ^ 30),
        ((-443935465 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((672080627 : Dyadic) * half ^ 30),
        ((435791865 : Dyadic) * half ^ 31)⟩,
       ⟨((-114072581 : Dyadic) * half ^ 29),
        ((935184385 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((228108561 : Dyadic) * half ^ 30),
        ((-228524439 : Dyadic) * half ^ 31)⟩,
       ⟨((-71207167 : Dyadic) * half ^ 29),
        ((192404059 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word15Step43 :
    word15Chunk43.foldl (fun acc a => a.applyPacked acc)
      word15State43 = word15State44 := by decide +kernel

private def word15Chunk44 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word15State45 : PackedMat2 :=
    ⟨⟨⟨((-256135833 : Dyadic) * half ^ 29),
        ((-50278797 : Dyadic) * half ^ 31)⟩,
       ⟨((262151819 : Dyadic) * half ^ 30),
        ((-335456915 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((1357605353 : Dyadic) * half ^ 31),
        ((21633423 : Dyadic) * half ^ 29)⟩,
       ⟨((-551217391 : Dyadic) * half ^ 31),
        ((-82894315 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-551217391 : Dyadic) * half ^ 31),
        ((-82894315 : Dyadic) * half ^ 29)⟩,
       ⟨((1357605353 : Dyadic) * half ^ 31),
        ((21633423 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-262151819 : Dyadic) * half ^ 30),
        ((335456915 : Dyadic) * half ^ 30)⟩,
       ⟨((256135833 : Dyadic) * half ^ 29),
        ((50278797 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word15Step44 :
    word15Chunk44.foldl (fun acc a => a.applyPacked acc)
      word15State44 = word15State45 := by decide +kernel

private def word15Chunk45 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word15State46 : PackedMat2 :=
    ⟨⟨⟨((-146421059 : Dyadic) * half ^ 29),
        ((-1842183545 : Dyadic) * half ^ 32)⟩,
       ⟨((1076683381 : Dyadic) * half ^ 31),
        ((-567092985 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-614234679 : Dyadic) * half ^ 32),
        ((4859739 : Dyadic) * half ^ 25)⟩,
       ⟨((1077699329 : Dyadic) * half ^ 32),
        ((154617623 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((894025 : Dyadic) * half ^ 30),
        ((-211491751 : Dyadic) * half ^ 30)⟩,
       ⟨((-310129271 : Dyadic) * half ^ 30),
        ((-231732325 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((707997575 : Dyadic) * half ^ 32),
        ((1662367617 : Dyadic) * half ^ 32)⟩,
       ⟨((-2976369515 : Dyadic) * half ^ 32),
        ((490999145 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word15Step45 :
    word15Chunk45.foldl (fun acc a => a.applyPacked acc)
      word15State45 = word15State46 := by decide +kernel

private def word15Chunk46 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word15State47 : PackedMat2 :=
    ⟨⟨⟨((-4760034523 : Dyadic) * half ^ 33),
        ((290643995 : Dyadic) * half ^ 32)⟩,
       ⟨((-4053975091 : Dyadic) * half ^ 33),
        ((933229809 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1986972907 : Dyadic) * half ^ 33),
        ((-98519201 : Dyadic) * half ^ 33)⟩,
       ⟨((1794074777 : Dyadic) * half ^ 33),
        ((1770964733 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1794074777 : Dyadic) * half ^ 33),
        ((1770964733 : Dyadic) * half ^ 32)⟩,
       ⟨((-1986972907 : Dyadic) * half ^ 33),
        ((-98519201 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((4053975091 : Dyadic) * half ^ 33),
        ((-933229809 : Dyadic) * half ^ 33)⟩,
       ⟨((4760034523 : Dyadic) * half ^ 33),
        ((-290643995 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word15Step46 :
    word15Chunk46.foldl (fun acc a => a.applyPacked acc)
      word15State46 = word15State47 := by decide +kernel

private def word15Chunk47 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word15State48 : PackedMat2 :=
    ⟨⟨⟨((2564035643 : Dyadic) * half ^ 32),
        ((1674381951 : Dyadic) * half ^ 34)⟩,
       ⟨((-294628635 : Dyadic) * half ^ 32),
        ((-4857465827 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((303212277 : Dyadic) * half ^ 33),
        ((-1566790979 : Dyadic) * half ^ 32)⟩,
       ⟨((276399819 : Dyadic) * half ^ 30),
        ((-2159092861 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((5292674819 : Dyadic) * half ^ 33),
        ((-2514410829 : Dyadic) * half ^ 34)⟩,
       ⟨((974489097 : Dyadic) * half ^ 33),
        ((1907986275 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-795770969 : Dyadic) * half ^ 32),
        ((70918969 : Dyadic) * half ^ 28)⟩,
       ⟨((3265923889 : Dyadic) * half ^ 33),
        ((1429332139 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word15Step47 :
    word15Chunk47.foldl (fun acc a => a.applyPacked acc)
      word15State47 = word15State48 := by decide +kernel

private def word15Chunk48 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word15State49 : PackedMat2 :=
    ⟨⟨⟨((4474837773 : Dyadic) * half ^ 34),
        ((10795422677 : Dyadic) * half ^ 35)⟩,
       ⟨((71727217 : Dyadic) * half ^ 31),
        ((-5771296505 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3944552599 : Dyadic) * half ^ 33),
        ((9782076103 : Dyadic) * half ^ 35)⟩,
       ⟨((-9143044731 : Dyadic) * half ^ 34),
        ((-3519148763 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((6650612433 : Dyadic) * half ^ 34),
        ((1253939533 : Dyadic) * half ^ 35)⟩,
       ⟨((-1565731835 : Dyadic) * half ^ 33),
        ((17032149929 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-8283359591 : Dyadic) * half ^ 34),
        ((-3901020037 : Dyadic) * half ^ 35)⟩,
       ⟨((1256031543 : Dyadic) * half ^ 33),
        ((5048655509 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word15Step48 :
    word15Chunk48.foldl (fun acc a => a.applyPacked acc)
      word15State48 = word15State49 := by decide +kernel

private def word15Chunk49 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word15State50 : PackedMat2 :=
    ⟨⟨⟨((-92585043 : Dyadic) * half ^ 35),
        ((27513978617 : Dyadic) * half ^ 36)⟩,
       ⟨((4053820741 : Dyadic) * half ^ 33),
        ((4468268473 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-16067496627 : Dyadic) * half ^ 35),
        ((-6230456131 : Dyadic) * half ^ 36)⟩,
       ⟨((6379962557 : Dyadic) * half ^ 34),
        ((-13324113277 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((16067496627 : Dyadic) * half ^ 35),
        ((6230456131 : Dyadic) * half ^ 36)⟩,
       ⟨((6379962557 : Dyadic) * half ^ 34),
        ((-13324113277 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-92585043 : Dyadic) * half ^ 35),
        ((27513978617 : Dyadic) * half ^ 36)⟩,
       ⟨((-4053820741 : Dyadic) * half ^ 33),
        ((-4468268473 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word15Step49 :
    word15Chunk49.foldl (fun acc a => a.applyPacked acc)
      word15State49 = word15State50 := by decide +kernel

private def word15Chunk50 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word15State51 : PackedMat2 :=
    ⟨⟨⟨((11059541809 : Dyadic) * half ^ 35),
        ((9312753905 : Dyadic) * half ^ 37)⟩,
       ⟨((45653701089 : Dyadic) * half ^ 36),
        ((13720354347 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((7593359431 : Dyadic) * half ^ 34),
        ((-35466093057 : Dyadic) * half ^ 37)⟩,
       ⟨((-8866870139 : Dyadic) * half ^ 36),
        ((-27614324605 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((7593359431 : Dyadic) * half ^ 34),
        ((-35466093057 : Dyadic) * half ^ 37)⟩,
       ⟨((8866870139 : Dyadic) * half ^ 36),
        ((27614324605 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-11059541809 : Dyadic) * half ^ 35),
        ((-9312753905 : Dyadic) * half ^ 37)⟩,
       ⟨((45653701089 : Dyadic) * half ^ 36),
        ((13720354347 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word15Step50 :
    word15Chunk50.foldl (fun acc a => a.applyPacked acc)
      word15State50 = word15State51 := by decide +kernel

private def word15Chunk51 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word15State52 : PackedMat2 :=
    ⟨⟨⟨((-9900786801 : Dyadic) * half ^ 35),
        ((-20508454695 : Dyadic) * half ^ 36)⟩,
       ⟨((-1575596603 : Dyadic) * half ^ 36),
        ((45489754435 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-47551535429 : Dyadic) * half ^ 37),
        ((23251992905 : Dyadic) * half ^ 36)⟩,
       ⟨((53353800121 : Dyadic) * half ^ 37),
        ((3421894185 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-16408204535 : Dyadic) * half ^ 36),
        ((50452667775 : Dyadic) * half ^ 37)⟩,
       ⟨((30095781275 : Dyadic) * half ^ 36),
        ((1450566173 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-86506663825 : Dyadic) * half ^ 37),
        ((-18225976999 : Dyadic) * half ^ 37)⟩,
       ⟨((-4472845045 : Dyadic) * half ^ 37),
        ((21377170205 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word15Step51 :
    word15Chunk51.foldl (fun acc a => a.applyPacked acc)
      word15State51 = word15State52 := by decide +kernel

private def word15Chunk52 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word15State53 : PackedMat2 :=
    ⟨⟨⟨((-31331090145 : Dyadic) * half ^ 38),
        ((-131596887449 : Dyadic) * half ^ 38)⟩,
       ⟨((104730161787 : Dyadic) * half ^ 38),
        ((-952516433 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((51024295 : Dyadic) * half ^ 38),
        ((-102256021559 : Dyadic) * half ^ 38)⟩,
       ⟨((-17025188743 : Dyadic) * half ^ 38),
        ((6796003937 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((47887990063 : Dyadic) * half ^ 38),
        ((530442639 : Dyadic) * half ^ 34)⟩,
       ⟨((156624053055 : Dyadic) * half ^ 38),
        ((-8538106519 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-162077413305 : Dyadic) * half ^ 38),
        ((36699535821 : Dyadic) * half ^ 38)⟩,
       ⟨((-101116361593 : Dyadic) * half ^ 38),
        ((-34015312983 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word15Step52 :
    word15Chunk52.foldl (fun acc a => a.applyPacked acc)
      word15State52 = word15State53 := by decide +kernel

private def word15Chunk53 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word15State54 : PackedMat2 :=
    ⟨⟨⟨((41912937823 : Dyadic) * half ^ 39),
        ((-156428843907 : Dyadic) * half ^ 38)⟩,
       ⟨((72687923879 : Dyadic) * half ^ 39),
        ((-111753376921 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-109345162165 : Dyadic) * half ^ 39),
        ((-137162817991 : Dyadic) * half ^ 39)⟩,
       ⟨((-60588230849 : Dyadic) * half ^ 39),
        ((-51477119467 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-60588230849 : Dyadic) * half ^ 39),
        ((-51477119467 : Dyadic) * half ^ 38)⟩,
       ⟨((-109345162165 : Dyadic) * half ^ 39),
        ((-137162817991 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-72687923879 : Dyadic) * half ^ 39),
        ((111753376921 : Dyadic) * half ^ 39)⟩,
       ⟨((-41912937823 : Dyadic) * half ^ 39),
        ((156428843907 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word15Step53 :
    word15Chunk53.foldl (fun acc a => a.applyPacked acc)
      word15State53 = word15State54 := by decide +kernel

private def word15Chunk54 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word15State55 : PackedMat2 :=
    ⟨⟨⟨((-183152969641 : Dyadic) * half ^ 38),
        ((64643924543 : Dyadic) * half ^ 39)⟩,
       ⟨((29261620453 : Dyadic) * half ^ 39),
        ((-38800766857 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-394784195 : Dyadic) * half ^ 35),
        ((8996569797 : Dyadic) * half ^ 40)⟩,
       ⟨((-2890096503 : Dyadic) * half ^ 32),
        ((-140450617989 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((2053969503 : Dyadic) * half ^ 34),
        ((23515556219 : Dyadic) * half ^ 36)⟩,
       ⟨((-74723593893 : Dyadic) * half ^ 39),
        ((-22725987829 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-12957609171 : Dyadic) * half ^ 39),
        ((-337044318829 : Dyadic) * half ^ 40)⟩,
       ⟨((142245458257 : Dyadic) * half ^ 39),
        ((-395567559735 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word15Step54 :
    word15Chunk54.foldl (fun acc a => a.applyPacked acc)
      word15State54 = word15State55 := by decide +kernel

private def word15Chunk55 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word15State56 : PackedMat2 :=
    ⟨⟨⟨((469958581017 : Dyadic) * half ^ 40),
        ((-436958193147 : Dyadic) * half ^ 41)⟩,
       ⟨((-257596229795 : Dyadic) * half ^ 39),
        ((178814520195 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((204095271317 : Dyadic) * half ^ 39),
        ((-27385543679 : Dyadic) * half ^ 41)⟩,
       ⟨((-513073104391 : Dyadic) * half ^ 40),
        ((-601580285885 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((287097371103 : Dyadic) * half ^ 40),
        ((921263647025 : Dyadic) * half ^ 41)⟩,
       ⟨((157241457391 : Dyadic) * half ^ 39),
        ((104882561757 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((307886356671 : Dyadic) * half ^ 40),
        ((-985151040607 : Dyadic) * half ^ 41)⟩,
       ⟨((-32267959119 : Dyadic) * half ^ 38),
        ((-45233878573 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word15Step55 :
    word15Chunk55.foldl (fun acc a => a.applyPacked acc)
      word15State55 = word15State56 := by decide +kernel

private def word15Chunk56 : List Letter := [.h, .s, .t, .h, .s]
private def word15State57 : PackedMat2 :=
    ⟨⟨⟨((1399200892987 : Dyadic) * half ^ 41),
        ((35347488073 : Dyadic) * half ^ 37)⟩,
       ⟨((-916786444113 : Dyadic) * half ^ 41),
        ((648116833119 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((515367354497 : Dyadic) * half ^ 41),
        ((-364419751167 : Dyadic) * half ^ 41)⟩,
       ⟨((114911011253 : Dyadic) * half ^ 41),
        ((-40627177645 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-515367354497 : Dyadic) * half ^ 41),
        ((364419751167 : Dyadic) * half ^ 41)⟩,
       ⟨((114911011253 : Dyadic) * half ^ 41),
        ((-40627177645 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((1399200892987 : Dyadic) * half ^ 41),
        ((35347488073 : Dyadic) * half ^ 37)⟩,
       ⟨((916786444113 : Dyadic) * half ^ 41),
        ((-648116833119 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word15Step56 :
    word15Chunk56.foldl (fun acc a => a.applyPacked acc)
      word15State56 = word15State57 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word15_check : check word15 15 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word15 = word15State57.toMatrix := by
    unfold evalRingPacked
    change ((
      word15Chunk0 ++ word15Chunk1 ++ word15Chunk2 ++ word15Chunk3 ++
      word15Chunk4 ++ word15Chunk5 ++ word15Chunk6 ++ word15Chunk7 ++
      word15Chunk8 ++ word15Chunk9 ++ word15Chunk10 ++ word15Chunk11 ++
      word15Chunk12 ++ word15Chunk13 ++ word15Chunk14 ++ word15Chunk15 ++
      word15Chunk16 ++ word15Chunk17 ++ word15Chunk18 ++ word15Chunk19 ++
      word15Chunk20 ++ word15Chunk21 ++ word15Chunk22 ++ word15Chunk23 ++
      word15Chunk24 ++ word15Chunk25 ++ word15Chunk26 ++ word15Chunk27 ++
      word15Chunk28 ++ word15Chunk29 ++ word15Chunk30 ++ word15Chunk31 ++
      word15Chunk32 ++ word15Chunk33 ++ word15Chunk34 ++ word15Chunk35 ++
      word15Chunk36 ++ word15Chunk37 ++ word15Chunk38 ++ word15Chunk39 ++
      word15Chunk40 ++ word15Chunk41 ++ word15Chunk42 ++ word15Chunk43 ++
      word15Chunk44 ++ word15Chunk45 ++ word15Chunk46 ++ word15Chunk47 ++
      word15Chunk48 ++ word15Chunk49 ++ word15Chunk50 ++ word15Chunk51 ++
      word15Chunk52 ++ word15Chunk53 ++ word15Chunk54 ++ word15Chunk55 ++
      word15Chunk56
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word15Step0, word15Step1, word15Step2, word15Step3, word15Step4,
      word15Step5, word15Step6, word15Step7, word15Step8, word15Step9,
      word15Step10, word15Step11, word15Step12, word15Step13, word15Step14,
      word15Step15, word15Step16, word15Step17, word15Step18, word15Step19,
      word15Step20, word15Step21, word15Step22, word15Step23, word15Step24,
      word15Step25, word15Step26, word15Step27, word15Step28, word15Step29,
      word15Step30, word15Step31, word15Step32, word15Step33, word15Step34,
      word15Step35, word15Step36, word15Step37, word15Step38, word15Step39,
      word15Step40, word15Step41, word15Step42, word15Step43, word15Step44,
      word15Step45, word15Step46, word15Step47, word15Step48, word15Step49,
      word15Step50, word15Step51, word15Step52, word15Step53, word15Step54,
      word15Step55, word15Step56]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
