From discprob.basic Require Import base order nify.
Require Import Ranalysis5.
Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import List.
Require Import Psatz.


Local Notation "x ≤ y" := (Rle x y) (at level 70, no associativity).
Local Notation "x ≥ y" := (Rge x y) (at level 70, no associativity).


Lemma Rmult_eq_0_inv_r: ∀ r r1 r2 : R, (r ≠ 0 → r1 = r2) → r * r1 = r * r2.
Proof.
  intros r r1 r2; case (Req_dec r 0).
  - intros ->. by rewrite !Rmult_0_l. 
  - intros Hneq Heq. rewrite Heq //.
Qed.

Lemma Rmult_eq_0_inv_l: ∀ r r1 r2 : R, (r ≠ 0 → r1 = r2) → r1 * r = r2 * r.
Proof.
  intros r r1 r2; case (Req_dec r 0).
  - intros ->. by rewrite !Rmult_0_r.
  - intros Hneq Heq. rewrite Heq //.
Qed.

Lemma Rmult_neq_0_compat: ∀ r1 r2 : R, r1 ≠ 0 → r2 ≠ 0 → r1 * r2 ≠ 0.
Proof. intros r1 r2 ?? [?|?]%Rmult_integral; congruence. Qed.

Lemma Rdiv_le_compat_contra: ∀ r1 r2 r3 r4 : R,
    0 ≤ r1 → 0 < r4 → r1 ≤ r2 → r4 ≤ r3 → r1 / r3 ≤ r2 / r4.
Proof.
  intros. rewrite /Rdiv. apply Rmult_le_compat; auto.
  rewrite -(Rmult_1_l (/ r3)). apply Rle_mult_inv_pos; fourier.
    by apply Rinv_le_contravar.
Qed.

Lemma Rmult_le_0_compat x y: 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof. 
  intros. rewrite -[a in a ≤ _](Rmult_0_l 0).
  apply Rmult_le_compat; eauto; try reflexivity.
Qed.


Lemma fold_right_plus_mult (l: list R) v :
  (fold_right Rplus 0 l) * v = fold_right Rplus 0 (map (λ x, x * v) l).
Proof.
  induction l => //=; first nra.
  ring_simplify. rewrite IHl. done.
Qed.

Lemma fold_right_map_Rmult_le {A} (l: list A) f f':
  (∀ x, In x l → 0 <= f x ∧ f x <= f' x) →
  fold_right Rmult 1 (map f l) <= fold_right Rmult 1 (map f' l).
Proof.
  intros Hin.
  cut (0 <= fold_right Rmult 1 (map f l) ∧
       fold_right Rmult 1 (map f l) <= fold_right Rmult 1 (map f' l)).
  { intros [? ?]; done. }
  induction l.
  - rewrite //=; intros; nra.
  - rewrite //=. destruct IHl.
    { intros a' Hin'. apply Hin. by right. }
    split.
    * apply Rmult_le_0_compat; eauto.
      edestruct (Hin a); eauto; first by left.
    * apply Rmult_le_compat; auto.
      ** edestruct (Hin a); eauto; first by left.
      ** edestruct (Hin a); eauto; first by left.
Qed.

