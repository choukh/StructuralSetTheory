(*** Coq coding by choukh, Aug 2022 ***)

Require Export Utf8_core Setoid Morphisms.
Global Set Implicit Arguments.
Global Unset Strict Implicit.

(** 经典逻辑 **)

(* 命题外延 *)
Axiom PE : ∀ P Q, P ↔ Q → P = Q.
(* 函数外延 *)
Axiom FE : ∀ A B (f g : A → B), (∀ x, f x = g x) → f = g.
(* 排中律 *)
Axiom XM : ∀ P, P ∨ ¬ P.

Tactic Notation "反证" := edestruct XM as []; eauto; exfalso.

Lemma 谓词外延 A (p q : A → Prop) : (∀ x, p x ↔ q x) → p = q.
Proof. intros H. apply FE. intros x. apply PE, H. Qed.

(* 证明无关性 *)
Fact PI (P : Prop) (H H' : P) : H = H'.
Proof.
  enough (P = True) as ->.
  destruct H, H'. reflexivity. apply PE. easy.
Qed.

(** 成员关系 **)

Notation "x ∈ p" := (p x) (only parsing, at level 70).

Notation "∀ x .. y ∈ A , P" :=
  (∀ x, x ∈ A → (.. (∀ y, y ∈ A → P) ..))
  (only parsing, at level 200, x binder, right associativity).

Notation "∃ x .. y ∈ A , P" :=
  (∃ x, x ∈ A ∧ (.. (∃ y, y ∈ A ∧ P) ..))
  (only parsing, at level 200, x binder, right associativity).

(** 子集关系 *)

Notation "p ⊆ q" := (∀ x ∈ p, x ∈ q) (at level 70).
Notation "p ⊂ q" := (p ⊆ q ∧ ¬ q ⊆ p) (at level 70).

Notation "∀ x .. y ⊆ A , P" :=
  (∀ x, x ⊆ A → (.. (∀ y, y ⊆ A → P) ..))
  (only parsing, at level 200, x binder, right associativity).

Notation "∃ x .. y ⊆ A , P" :=
  (∃ x, x ⊆ A ∧ (.. (∃ y, y ⊆ A ∧ P) ..))
  (only parsing, at level 200, x binder, right associativity).

Notation "'𝒫' A" := (A → Prop) (at level 9).

Fact 包含_自反 A (p : 𝒫 A) : p ⊆ p.
Proof. firstorder. Qed.

Fact 包含_传递 A (p q r : 𝒫 A) : p ⊆ q → q ⊆ r → p ⊆ r.
Proof. firstorder. Qed.

(* 集论外延 *)
Lemma 包含_反对称 A (p q : 𝒫 A) : p ⊆ q → q ⊆ p → p = q.
Proof. intros. apply 谓词外延; firstorder. Qed.
Notation 外延 := 包含_反对称.

(** 其他集论记号 **)

Notation "A ≠ ∅" := (∃ x, x ∈ A) (only parsing, at level 70).
Notation "A ⋃ B" := (λ x, x ∈ A ∨ x ∈ B) (at level 60).
Notation "A ∩ B" := (λ x, x ∈ A ∧ x ∈ B) (at level 60).
Notation "A ⁻" := (λ x, ¬ x ∈ A) (format "A ⁻", at level 20).
Notation "{ a , }" := (λ x, x = a) (only parsing).
Notation "{ a , b }" := (λ x, x = a ∨ x = b) (only parsing).
Notation "{ x ∊ A | P }" := (λ x, x ∈ A ∧ P) (only parsing).
Notation "{ x ∊ A | xA 'in' P }" := (λ x, ∃ xA : x ∈ A, P) (only parsing).

(** 子类型 (子集的类型化) **)

Notation Σ := sig.
Notation σ := exist.
Notation π₁ := proj1_sig.
Notation π₂ := proj2_sig.

Fact σ_函数 A (p : 𝒫 A) x y px py : x = y → σ p x px = σ p y py.
Proof. intros ->. now rewrite (PI px py). Qed.

Lemma π_单射 A (p : 𝒫 A) (xₛ yₛ : Σ p) : π₁ xₛ = π₁ yₛ → xₛ = yₛ.
Proof. destruct xₛ as [x px], yₛ as [y py]. apply σ_函数. Qed.

Lemma σπ_η A (p : 𝒫 A) (xₛ : Σ p) : σ p (π₁ xₛ) (π₂ xₛ) = xₛ.
Proof. now destruct xₛ. Qed.

(** 单射 **)

Definition 单射性 A B (f : A → B) := ∀ x y, f x = f y → x = y.
Definition 单射 A B := ∃ f : A → B, 单射性 f.
Notation "| A | ≤ | B |" := (单射 A B) (format "| A |  ≤  | B |", at level 70).

Global Instance 单射_预序 : PreOrder 单射.
Proof. split.
  - intros A. exists (λ x, x). firstorder.
  - intros A B C [f Hf] [g Hg]. exists (λ x, g (f x)). firstorder.
Qed.

Lemma 单射_从子集 A (p : 𝒫 A) : |Σ p| ≤ |A|.
Proof. exists (@π₁ A p). intros x y. apply π_单射. Qed.

Lemma 单射_到幂集 A : |A| ≤ |𝒫 A|.
Proof. exists eq. now intros x y ->. Qed.

(** 双射 **)

Definition 互逆 A B (f : A → B) (g : B → A) := (∀ x, f (g x) = x) ∧ (∀ y, g (f y) = y).
Definition 双射 A B := ∃ (f : A → B) (g : B → A), 互逆 f g.
Notation "| A | = | B |" := (双射 A B) (format "| A |  =  | B |", at level 70).

Global Instance 双射_等价关系 : Equivalence 双射.
Proof. split.
  - intros A. exists (λ x, x), (λ x, x). firstorder.
  - intros A B (f & g & inv). exists g, f. firstorder.
  - intros A B C (f & g & fg & gf) (h & i & hi & ih).
    exists (λ x, h (f x)), (λ x, g (i x)). firstorder congruence.
Qed.

Fact 双射_单射 A B : |A| = |B| → |A| ≤ |B|.
Proof. intros (f & g & fg & gf). exists f. congruence. Qed.

(* 幂迭代 *)
Fixpoint 𝒫ₙ n A :=
  match n with
  | O => A
  | S n => 𝒫ₙ n (𝒫 A)
  end.

Lemma 幂迭代 A n : 𝒫ₙ n (𝒫 A) = 𝒫 (𝒫ₙ n A).
Proof. revert A; induction n; intros A; firstorder congruence. Qed.

Lemma 单射_到幂迭代 A n : |A| ≤ |𝒫ₙ n A|.
Proof. induction n.
  - reflexivity.
  - etransitivity. apply IHn. simpl. rewrite 幂迭代. apply 单射_到幂集.
Qed.

Definition 无穷 A := |nat| ≤ |A|.

Lemma 无穷_单射 A B : 无穷 A → |A| ≤ |B| → 无穷 B.
Proof. unfold 无穷. etransitivity; eauto. Qed.

Fact 无穷_幂迭代 A n : 无穷 A → 无穷 (𝒫ₙ n A).
Proof. intros H. apply 无穷_单射 with A. trivial. apply 单射_到幂迭代. Qed.

(* 广义连续统假设 *)
Definition GCH := ∀ A B, 无穷 A → |A| ≤ |B| → |B| ≤ |𝒫 A| → |B| ≤ |A| ∨ |𝒫 A| ≤ |B|.
