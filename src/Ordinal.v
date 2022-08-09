(*** Coq coding by choukh, Aug 2022 ***)

Require Export Prelim.

(** 序数 **)
Section Ordinal.

(* 全集 *)
Variable U : Type.
(* X的子集 *)
Implicit Types a b c : 𝒫 U.
(* X的子集族, 可能有⊆良序 *)
Implicit Types A B C : 𝒫 𝒫 U.
(* 上者的等价类 *)
Implicit Types α β : 𝒫 𝒫 𝒫 U.

Section WellOrder.
Variable A : 𝒫 𝒫 U.

Definition 良序 := ∀ B ⊆ A, B ≠ ∅ → ∃ a ∈ B, ∀ b ∈ B, a ⊆ b.
Definition 可及 := Acc (λ a b, a ∈ A ∧ b ∈ A ∧ a ⊂ b).
Definition 良基 := ∀ a ∈ A, 可及 a.

(* 需要排中律 *)
Fact 良序_良基 : 良序 → 良基.
Proof.
  intros wo a aA. 反证.
  destruct (wo (A ∩ 可及⁻)) as [b Hb]. 1-2:firstorder.
  apply Hb. constructor. fold 可及.
  intros c cA. 反证. apply cA. firstorder.
Qed.

Fact 良序_线序 : 良序 → ∀ a b ∈ A, a ⊆ b ∨ b ⊆ a.
Proof.
  intros wo a aA b bA.
  destruct (wo {a, b}) as (c & [->| ->] & Hc).
  - firstorder congruence.
  - exists a. now left.
  - left. apply Hc. now right.
  - right. apply Hc. now left.
Qed.

(* 需要排中律 *)
Fact 良序_强线序 : 良序 → ∀ a b ∈ A, a ⊆ b ∨ b ⊂ a.
Proof.
  intros wo a aA b bA.
  destruct (wo {a, b}) as (c & [->| ->] & Hc).
  - firstorder congruence.
  - exists a. now left.
  - left. apply Hc. now right.
  - destruct (XM (a ⊆ b)) as []. auto.
    right. split; trivial. apply Hc. now left.
Qed.

End WellOrder.

Definition 嵌入性 A B (f : Σ A → Σ B) :=
  ∀ aₛ bₛ : Σ A, π₁ aₛ ⊆ π₁ bₛ ↔ π₁ (f aₛ) ⊆ π₁ (f bₛ).

Definition 嵌入 A B := ∃ f : Σ A → Σ B, 嵌入性 f.
Notation "A ⪯ B" := (嵌入 A B) (at level 70).

Global Instance 嵌入_预序 : PreOrder 嵌入.
Proof. split.
  - intros A. exists (λ xₛ, xₛ). firstorder.
  - intros A B C [f Hf] [g Hg]. exists (λ xₛ, g (f xₛ)).
    intros p q. rewrite (Hf p q). apply Hg.
Qed.

Fact 嵌入_单射 A B f : @嵌入性 A B f → 单射性 f.
Proof.
  intros Hf aₛ bₛ H. apply π_单射.
  apply 外延; apply Hf; congruence.
Qed.

Fact 子集_嵌入 A B : A ⊆ B → A ⪯ B.
Proof.
  intros H. unshelve eexists.
  - intros [a aA]. exists a. now apply H.
  - intros [a aA] [b bA]. now simpl.
Qed.

Fact 嵌入_反推良序 A B : A ⪯ B → 良序 B → 良序 A.
Proof.
  intros [f Hf] wo C CA [a aC].
  destruct (@wo {b ∊ B | bB in ∃ xₛ, (π₁ xₛ) ∈ C ∧ f xₛ = σ B b bB})
    as [b [[bB [xₛ [xC fxₛ]]] H]].
  - firstorder.
  - set (aₛ := σ A a (CA a aC)).
    exists (π₁ (f aₛ)), (π₂ (f aₛ)), aₛ.
    split; trivial. now rewrite σπ_η.
  - exists (π₁ xₛ). split; trivial. intros c cC.
    set (cₛ := σ A c (CA c cC)).
    apply (Hf xₛ cₛ). rewrite fxₛ. simpl. apply H.
    exists (π₂ (f cₛ)), cₛ. split; trivial. now rewrite σπ_η.
Qed.

Definition 同构 A B := A ⪯ B ∧ B ⪯ A.
Notation "'ord' A" := (同构 A) (at level 10).
Notation "A ~ B" := (同构 A B) (at level 70).

Definition 强同构 A B := ∃ f : Σ A → Σ B, 嵌入性 f ∧ ∃ g, 互逆 f g.
Notation "'Ord' A" := (强同构 A) (at level 10).
Notation "A ≈ B" := (强同构 A B) (at level 70).

Lemma 嵌入_逆 A B (f : Σ A → Σ B) g : 嵌入性 f → 互逆 f g → 嵌入性 g.
Proof.
  intros H [fg gf] a b.
  rewrite <- (fg a), <- (fg b), gf, gf. symmetry. apply H.
Qed.

Fact 强同构_同构 A B : A ≈ B → A ~ B.
Proof.
  intros (f & emb & g & inv). split.
  - exists f. apply emb.
  - exists g. now apply (嵌入_逆 emb).
Qed.

Instance 同构_等价关系 : Equivalence 同构.
Proof. split.
  - intros A. split; reflexivity.
  - intros A B H. split; apply H.
  - intros A B C [AB BA] [BC CB]. split; etransitivity; eauto.
Qed.

Instance 同构改写良序 : Proper (同构 ==> iff) 良序.
Proof. intros A B [AB BA]. split; now apply 嵌入_反推良序. Qed.

Instance 同构改写嵌入 : Proper (同构 ==> 同构 ==> iff) 嵌入.
Proof.
  intros A B [AB BA] C D [CD DC].
  split; etransitivity; etransitivity; eauto; reflexivity.
Qed.

Fact ord_函数 A B : A = B → ord A = ord B.
Proof. intros H. apply 外延; intros C <-; now rewrite H. Qed.

(* 序数 *)
Definition Ω α := ∃ A ∈ α, 良序 A ∧ ∀ B, B ∈ α ↔ A ~ B.

Fact 序数等于同构类 α A : α ∈ Ω → A ∈ α → α = ord A.
Proof.
  intros [B HB] Aα. apply 外延; intros C HC.
  - apply HB in HC. rewrite <- HC. symmetry. now apply HB.
  - apply HB. rewrite <- HC. now apply HB.
Qed.

Fact 序数_良序集 α A : α ∈ Ω → A ∈ α → 良序 A.
Proof.
  intros (B & Bα & wo & H) Aα.
  enough (A ~ B) as ->. trivial.
  symmetry. now apply H.
Qed.

Fact 良序集_序数 A : 良序 A → ord A ∈ Ω.
Proof. exists A. firstorder reflexivity. Qed.

Lemma 序数_同构 α A B : α ∈ Ω → A ∈ α → B ∈ α → A ~ B.
Proof.
  intros (C & _ & _ & HC) Aα Bα. etransitivity.
  - symmetry. apply HC, Aα.
  - apply HC, Bα.
Qed.

Lemma 同构_序数 α A B : α ∈ Ω → A ∈ α → A ~ B → B ∈ α.
Proof.
  intros (C & _ & _ & HC) Aα AB. apply HC. etransitivity.
  apply HC, Aα. apply AB.
Qed.

Definition 序 α β := ∃ A B, A ∈ α ∧ B ∈ β ∧ A ⪯ B.
Notation "α ≤ β" := (序 α β) (at level 70).

Fact 序_嵌入 α β A B : α ∈ Ω → β ∈ Ω → α ≤ β → A ∈ α → B ∈ β → A ⪯ B.
Proof.
  intros αΩ βΩ (C & D & Cα & βD & CD) Aα Bβ.
  rewrite (序数_同构 αΩ Aα Cα).
  rewrite (序数_同构 βΩ Bβ βD). apply CD.
Qed.

Lemma 序_自反 α : α ∈ Ω → α ≤ α.
Proof. intros (A & Aα & wo & H). exists A, A. firstorder reflexivity. Qed.

Lemma 序_传递 α β γ : β ∈ Ω → α ≤ β → β ≤ γ → α ≤ γ.
Proof.
  intros βΩ (A & B & Aα & Bβ & AB) (C & D & Cβ & Dγ & CD).
  exists A, D. split; trivial. split; trivial.
  etransitivity. apply AB.
  etransitivity. 2:apply CD.
  apply 序数_同构 with β; trivial.
Qed.

Lemma 序_反自反_引理 α β : α ∈ Ω → β ∈ Ω → α ≤ β → β ≤ α → α ⊆ β.
Proof.
  intros αΩ βΩ (A & B & Aα & Bβ & AB) (C & D & Cβ & Dα & CD) E Eα.
  apply 同构_序数 with B; trivial. split.
  - now rewrite (序数_同构 αΩ Eα Dα), (序数_同构 βΩ Bβ Cβ).
  - now rewrite (序数_同构 αΩ Eα Aα).
Qed.

Lemma 序_反自反 α β : α ∈ Ω → β ∈ Ω → α ≤ β → β ≤ α → α = β.
Proof. intros. apply 外延; now apply 序_反自反_引理. Qed.

End Ordinal.

Notation "'ord' A" := (同构 A) (at level 10).
Notation "A ~ B" := (同构 A B) (at level 70).
Notation "'Ord' A" := (强同构 A) (at level 10).
Notation "A ≈ B" := (强同构 A B) (at level 70).
