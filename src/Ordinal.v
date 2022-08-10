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

Definition 良序 := ∀ B ⊆ A, B ≠ ∅ → ∃ m ∈ B, ∀ x ∈ B, m ⊆ x.
Definition 可及 := Acc (λ a b, a ∈ A ∧ b ∈ A ∧ a ⊂ b).
Definition 良基 := ∀ a ∈ A, 可及 a.

Fact 良序_良基 `{经典} : 良序 → 良基.
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

Lemma 良序_强线序 `{经典} : 良序 → ∀ a b ∈ A, a ⊆ b ∨ b ⊂ a.
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
Notation "A ⋠ B" := (¬ 嵌入 A B) (at level 70).

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

Fact 包含_嵌入 A B : A ⊆ B → A ⪯ B.
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
Notation "A ≃ B" := (同构 A B) (at level 70).

Definition 强同构 A B := ∃ f : Σ A → Σ B, 嵌入性 f ∧ ∃ g, 互逆 f g.
Notation "'Ord' A" := (强同构 A) (at level 10).
Notation "A ≅ B" := (强同构 A B) (at level 70).

Lemma 嵌入_逆 A B (f : Σ A → Σ B) g : 嵌入性 f → 互逆 f g → 嵌入性 g.
Proof.
  intros H [fg gf] a b.
  rewrite <- (fg a), <- (fg b), gf, gf. symmetry. apply H.
Qed.

Fact 强同构_同构 A B : A ≅ B → A ≃ B.
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
Definition Ω α := ∃ A ∈ α, 良序 A ∧ ∀ B, B ∈ α ↔ A ≃ B.

Fact 序数等于同构类 α A : α ∈ Ω → A ∈ α → α = ord A.
Proof.
  intros [B HB] Aα. apply 外延; intros C HC.
  - apply HB in HC. rewrite <- HC. symmetry. now apply HB.
  - apply HB. rewrite <- HC. now apply HB.
Qed.

Fact 序数_良序集 α A : α ∈ Ω → A ∈ α → 良序 A.
Proof.
  intros (B & Bα & wo & H) Aα.
  enough (A ≃ B) as ->. trivial.
  symmetry. now apply H.
Qed.

Fact 良序集_序数 A : 良序 A → ord A ∈ Ω.
Proof. exists A. firstorder reflexivity. Qed.

Lemma 序数_同构 α A B : α ∈ Ω → A ∈ α → B ∈ α → A ≃ B.
Proof.
  intros (C & _ & _ & HC) Aα Bα. etransitivity.
  - symmetry. apply HC, Aα.
  - apply HC, Bα.
Qed.

Lemma 同构_序数 α A B : α ∈ Ω → A ∈ α → A ≃ B → B ∈ α.
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

(** 用关系定义的序嵌入与序同构 **)

Definition 嵌入性ᵣ A B (R : Σ A → Σ B → Prop) :=
  ∀ aₛ bₛ xₛ yₛ, R aₛ bₛ → R xₛ yₛ → π₁ aₛ ⊆ π₁ xₛ ↔ π₁ bₛ ⊆ π₁ yₛ.

Definition 嵌入ᵣ A B := ∃ R : Σ A → Σ B → Prop, 左完全 R ∧ 嵌入性ᵣ R.
Notation "A ⪯ᵣ B" := (嵌入ᵣ A B) (at level 70).

Definition 同构ᵣ A B := ∃ R : Σ A → Σ B → Prop, 左完全 R ∧ 右完全 R ∧ 嵌入性ᵣ R.
Notation "A ≅ᵣ B" := (同构ᵣ A B) (at level 70).

Lemma 嵌入_嵌入ᵣ A B : A ⪯ B → A ⪯ᵣ B.
Proof.
  intros [f Hf]. exists (λ aₛ bₛ, bₛ = f aₛ). split.
  - intros aₛ. exists (f aₛ). reflexivity.
  - intros aₛ bₛ aₛ' bₛ' -> ->. apply Hf.
Qed.

Lemma 强同构_同构ᵣ A B : A ≅ B → A ≅ᵣ B.
Proof.
  intros (f & Hf & g & gf & _).
  exists (λ aₛ bₛ, bₛ = f aₛ). split3.
  - intros aₛ. exists (f aₛ). reflexivity.
  - intros bₛ. exists (g bₛ). now rewrite gf.
  - intros aₛ bₛ aₛ' bₛ' -> ->. apply Hf.
Qed.

Section Relational.

Variable A B : 𝒫 𝒫 U.
Variable R : Σ A → Σ B → Prop.
Hypothesis 全 : 左完全 R.
Hypothesis 满 : 右完全 R.
Hypothesis 嵌 : 嵌入性ᵣ R.

Lemma 嵌入性ᵣ_函数性 : 函数性 R.
Proof.
  intros aₛ bₛ cₛ Rab Rac. apply π_单射, 外延.
  - apply (嵌 Rab Rac). firstorder.
  - apply (嵌 Rac Rab). firstorder.
Qed.

Lemma 嵌入性ᵣ_单射性ᵣ : 单射性ᵣ R.
Proof.
  intros aₛ bₛ cₛ Rab Rac. apply π_单射, 外延.
  - apply (嵌 Rab Rac). firstorder.
  - apply (嵌 Rac Rab). firstorder.
Qed.

(** 序嵌入关系的函数化 **)

Let fπ₁ (aₛ : Σ A) := λ x, ∀ b (bB : b ∈ B), R aₛ (σ B b bB) → x ∈ b.

Local Lemma fπ₁_求值 aₛ bₛ : R aₛ bₛ → fπ₁ aₛ = π₁ bₛ.
Proof.
  intros H. apply 外延.
  - intros x Hx. apply (Hx (π₁ bₛ) (π₂ bₛ)). now rewrite σπ_η.
  - intros x Hx c cB Rac. specialize (嵌入性ᵣ_函数性 H Rac). intros ->. apply Hx.
Qed.

Local Lemma fπ₂ aₛ : fπ₁ aₛ ∈ B.
Proof. destruct (全 aₛ) as [bₛ Rab]. rewrite (fπ₁_求值 Rab). apply π₂. Qed.

Local Definition f (aₛ : Σ A) := σ B (fπ₁ aₛ) (fπ₂ aₛ).

Local Lemma f_求值 aₛ bₛ : R aₛ bₛ → f aₛ = bₛ.
Proof. intros H. now apply π_单射, fπ₁_求值. Qed.

Local Lemma f_关系 aₛ : R aₛ (f aₛ).
Proof. destruct (全 aₛ) as [bₛ Rab]. now rewrite (f_求值 Rab). Qed.

Local Lemma f_嵌入性 : 嵌入性 f.
Proof. intros a b. apply 嵌; apply f_关系. Qed.

Let gπ₁ (bₛ : Σ B) := λ x, ∀ a (aA : a ∈ A), R (σ A a aA) bₛ → x ∈ a.

Local Lemma gπ₁_求值 aₛ bₛ : R aₛ bₛ → gπ₁ bₛ = π₁ aₛ.
Proof.
  intros H. apply 外延.
  - intros x Hx. apply (Hx (π₁ aₛ) (π₂ aₛ)). now rewrite σπ_η.
  - intros x Hx c cB Rac. specialize (嵌入性ᵣ_单射性ᵣ H Rac). intros ->. apply Hx.
Qed.

Local Lemma gπ₂ bₛ : gπ₁ bₛ ∈ A.
Proof. destruct (满 bₛ) as [a Rab]. rewrite (gπ₁_求值 Rab). apply π₂. Qed.

Local Definition g (bₛ : Σ B) := σ A (gπ₁ bₛ) (gπ₂ bₛ).

Local Lemma g_求值 aₛ bₛ : R aₛ bₛ → g bₛ = aₛ.
Proof. intros H. now apply π_单射, gπ₁_求值. Qed.

Local Lemma g_关系 bₛ : R (g bₛ) bₛ.
Proof. destruct (满 bₛ) as [aₛ Rab]. now rewrite (g_求值 Rab). Qed.

Local Lemma fg互逆 : 互逆 f g.
Proof. split.
  - intros bₛ. destruct (满 bₛ) as [a Rab].
    rewrite (g_求值 Rab). now apply f_求值.
  - intros aₛ. destruct (全 aₛ) as [b Rab].
    rewrite (f_求值 Rab). now apply g_求值.
Qed.

Local Fact g_嵌入性 : 嵌入性 g.
Proof. apply 嵌入_逆 with f. apply f_嵌入性. apply fg互逆. Qed.

End Relational.

Lemma 嵌入ᵣ_嵌入 A B : A ⪯ᵣ B → A ⪯ B.
Proof. intros (R & tot & emb). exists (f tot emb). apply f_嵌入性. Qed.

Fact 嵌入_iff_嵌入ᵣ A B : A ⪯ B ↔ A ⪯ᵣ B.
Proof. split. apply 嵌入_嵌入ᵣ. apply 嵌入ᵣ_嵌入. Qed.

Lemma 同构ᵣ_强同构 A B : A ≅ᵣ B → A ≅ B.
Proof.
  intros (R & tot & sur & emb).
  exists (f tot emb). split. apply f_嵌入性.
  exists (g sur emb). apply fg互逆.
Qed.

Fact 强同构_iff_同构ᵣ A B : A ≅ B ↔ A ≅ᵣ B.
Proof. split. apply 强同构_同构ᵣ. apply 同构ᵣ_强同构. Qed.

Definition 前段 A a := {x ∊ A | x ⊂ a}.
Notation "a ⇠ A" := (前段 A a) (at level 55, right associativity).

Fact 前段是子集 A a : a ⇠ A ⊆ A.
Proof. firstorder. Qed.

Lemma 前段之前段 A a b : a ⊆ b → a ⇠ b ⇠ A = a ⇠ A.
Proof. intros H. apply 外延; firstorder. Qed.

Lemma 前段良序 A a : 良序 A → 良序 (a ⇠ A).
Proof.
  intros wo B BS [b bB]. destruct (wo B) as [c Hc].
  firstorder. now exists b. now exists c.
Qed.

Lemma 前段嵌入全段 A a : a ⇠ A ⪯ A.
Proof. unshelve eexists.
  - intros [b bS]. exists b. apply bS.
  - intros [b bS] [c cS]. simpl. easy.
Qed.

Lemma 全段不嵌入前段 A a : 良序 A → a ∈ A → A ⋠ a ⇠ A.
Proof.
  intros wo aA Ea.
  destruct (wo {x ∊ A | A ⪯ x ⇠ A}) as (b & [bA [f Hf]] & min). 1-2:firstorder.
  set (fbₛ := f (σ A b bA)). apply (π₂ fbₛ). apply min.
  split. apply (π₂ fbₛ). unshelve eexists.
  - intros [c cA].
    set (fcₛ := f (σ A c cA)).
    set (ffcₛ := f (σ A (π₁ fcₛ) ltac:(apply (π₂ fcₛ)))).
    exists (π₁ ffcₛ). repeat split.
    + apply (π₂ ffcₛ).
    + apply Hf. simpl. apply (π₂ fcₛ).
    + intros H % Hf. simpl in H. now apply (π₂ fcₛ).
  - intros [c cA] [d dA]; simpl.
    rewrite (Hf (σ A c cA) (σ A d dA)).
    destruct (f (σ A c cA)) as [fc [fcA fcb]].
    destruct (f (σ A d dA)) as [fd [fdA fdb]]. simpl.
    rewrite <- (Hf (σ A fc fcA) (σ A fd fdA)). simpl. easy.
Qed.

Lemma 前段保序_l A a b : a ⊆ b → a ⇠ A ⊆ b ⇠ A.
Proof. firstorder. Qed.

Lemma 前段保序_r `{经典} A a b : 良序 A → a ∈ A → b ∈ A → a ⇠ A ⊆ b ⇠ A → a ⊆ b.
Proof. intros wo aA bA sub. destruct (良序_强线序 wo aA bA); firstorder. Qed.

Lemma 前段保序 `{经典} A a b : 良序 A → a ∈ A → b ∈ A → a ⊆ b ↔ a ⇠ A ⊆ b ⇠ A.
Proof. split. apply 前段保序_l. now apply 前段保序_r. Qed.

Lemma 前段嵌入前段_l A a b : a ⊆ b → a ⇠ A ⪯ b ⇠ A.
Proof. intros. now apply 包含_嵌入, 前段保序_l. Qed.

Lemma 前段嵌入前段_r `{经典} A a b : 良序 A → a ∈ A → b ∈ A → a ⇠ A ⪯ b ⇠ A → a ⊆ b.
Proof.
  intros wo aA bA sub.
  destruct (良序_强线序 wo aA bA) as [|[ba ab]]; trivial.
  exfalso. rewrite <- (前段之前段 _ ba) in sub.
  contradict sub. apply 全段不嵌入前段. now apply 前段良序. firstorder.
Qed.

Lemma 前段嵌入前段 `{经典} A a b : 良序 A → a ∈ A → b ∈ A → a ⊆ b ↔ a ⇠ A ⪯ b ⇠ A.
Proof. split. apply 前段嵌入前段_l. now apply 前段嵌入前段_r. Qed.

(** 考察两个良序集间相同序数位置的元素 **)
Section OrderRelated.


Variable A B : 𝒫 𝒫 U.
Hypothesis HA : 良序 A.
Hypothesis HB : 良序 B.

Definition 序关联 a b := a ∈ A ∧ b ∈ B ∧ a ⇠ A ≅ b ⇠ B.
Notation "a ~ b" := (序关联 a b) (at level 70).

Let Dom a := ∃ b, a ~ b.
Let Ran b := ∃ a, a ~ b.

Local Lemma 关联点保序 `{经典} a b x y : a ~ x → b ~ y → a ⊆ b ↔ x ⊆ y.
Proof.
  intros (aA & xB & ax % 强同构_同构) (bA & yB & b_y % 强同构_同构). split; intros sub.
  - eapply 前段嵌入前段_r. apply HB. 1-2:trivial.
    rewrite <- ax, <- b_y. now apply 前段嵌入前段_l.
  - eapply 前段嵌入前段_r. apply HA. 1-2:trivial.
    rewrite ax, b_y. now apply 前段嵌入前段_l.
Qed.

Local Lemma 关联域同构 `{经典} : Dom ≅ Ran.
Proof.
  apply 同构ᵣ_强同构.
  exists (λ aₛ bₛ, π₁ aₛ ~ π₁ bₛ). split3.
  - intros (a & x & ax). unshelve eexists.
    now exists x, a. now simpl.
  - intros (y & b & b_y). unshelve eexists.
    now exists b, y. now simpl.
  - intros a b x y. apply 关联点保序.
Qed.

Local Lemma 定义域充满 `{经典} : (¬ ∃ a ∈ A, a ∉ Dom) → Dom = A.
Proof.
  intros ne. apply 外延. firstorder.
  intros a aA. destruct (XM (a ∈ Dom)) as []. trivial.
  exfalso. apply ne. eauto.
Qed.

End OrderRelated.

End Ordinal.

Notation "'ord' A" := (同构 A) (at level 10).
Notation "A ≃ B" := (同构 A B) (at level 70).
Notation "'Ord' A" := (强同构 A) (at level 10).
Notation "A ≅ B" := (强同构 A B) (at level 70).
