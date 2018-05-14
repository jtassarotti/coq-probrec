From discprob.basic Require Import base nify.
From mathcomp Require Import ssreflect seq ssrbool eqtype.
Import Omega.

Lemma undup_map {A B: eqType} (l: seq A) (f: A → B):
  undup [seq f x | x <- l] = undup [seq f x | x <- undup l].
Proof.  
  induction l as [| a l] => //=.
  symmetry. case: ifP.
  * intros Hin. apply (map_f f) in Hin.
    rewrite Hin. done.
  * intros Hnin. rewrite //=.
    case: ifP.
    ** intros Hin'.
       move /mapP in Hin'. destruct Hin' as [a' ? ?]; subst.
       case: ifP; auto.
       intros Hfalse. exfalso. move /mapP in Hfalse. apply Hfalse.
       exists a'. 
       *** rewrite -mem_undup; done.
       *** auto.
    ** intros Hnin'.
       case: ifP; last by (intros; f_equal; eauto).
       intros Hfalse. move /mapP in Hnin'. exfalso. apply Hnin'.
       move /mapP in Hfalse. destruct Hfalse as [a' ? ?]. 
       exists a'.
       *** rewrite mem_undup; done.
       *** auto.
Qed.

Lemma nth_legacy {A: Type} (d: A) l x:
  nth d l x = List.nth x l d.
Proof.  
  revert x; induction l => //=; destruct x => /= //.
Qed.

Lemma nth_error_nth1 {A: Type} (d: A) l x:
  x < length l →
  List.nth_error l x = Some (nth d l x).
Proof.  
  revert l.
  induction x.
  - rewrite //=. destruct l; auto. rewrite //=. omega. 
  - intros l Hlt0; destruct l.
      ** rewrite //= in Hlt0. omega.
      ** rewrite //=. eapply IHx. rewrite //= in Hlt0. omega. 
Qed.

Lemma nth_error_nth2 {A: Type} (d: A) l x v:
  List.nth_error l x = Some v → 
  nth d l x = v.
Proof.  
  revert x.
  induction l => //=.
  - destruct x; rewrite //=.
  - destruct x; rewrite //=; first by inversion 1.
    eauto.
Qed.

Lemma size_legacy {A: Type} (l: list A):
  size l = length l.
Proof. induction l => //=. Qed.

Lemma map_legacy {A B: Type} (f: A → B) l:
  map f l = List.map f l.
Proof.  
  induction l => //=.
Qed.

Lemma mem_seq_legacy {A: eqType} (x: A) (l: seq A):
  x \in l ↔ In x l.
Proof.  
  split.
  - induction l.
    * inversion 1.
    * move /orP => [Heq|Htail].
      ** move /eqP in Heq. by left.
      ** right. auto.
  - induction l; inversion 1. 
    * apply /orP; left; subst; auto.
    * apply /orP; right; subst; auto.
Qed.

Require Import Reals Psatz.

Local Open Scope R.
From discprob.basic Require Import base nify order.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.
Import List.

Lemma fold_left_Rmin_init l x:
  fold_left Rmin l x <= x.
Proof.
  revert x. induction l => //=; first reflexivity.
  intros x. etransitivity; first eapply IHl.
  apply Rmin_l.
Qed.

Lemma fold_left_Rmin_mono_init l x x':
  x <= x' →
  fold_left Rmin l x <= fold_left Rmin l x'.
Proof.
  revert x x'. induction l => //=.
  intros. eapply IHl. 
  apply Rle_min_compat_r; auto.
Qed.

Lemma fold_left_Rmin_cons a l x:
  fold_left Rmin (a :: l) x <= fold_left Rmin l x.
Proof.
  revert a x. destruct l.
  - intros; apply Rmin_l.
  - intros => //=. apply fold_left_Rmin_mono_init.
    apply Rle_min_compat_r. apply Rmin_l.
Qed.

Lemma fold_left_ext {A B} (f f': A → B → A) l l' x x':
  (forall a b, f a b = f' a b) → l = l' → x = x' → fold_left f l x = fold_left f' l' x'.
Proof.
  revert x x' l'. induction l => //=.
  - intros.  subst => //=.
  - intros x x' [| a' l']; first by auto.
    intros => //=. eapply IHl; eauto; by congruence.
Qed.

Lemma fold_left_Rmin_glb l r x:
  (∀ r', In r' l → r <= r') → r <= x → r <= fold_left Rmin l x.
Proof.
  revert r x. induction l as [| a l] => //=.
  intros r x Hglb Hinit. eapply IHl.
  - intros. apply Hglb; eauto.
  - apply Rmin_glb; eauto.
Qed.

Lemma fold_left_Rmin_witness1 l x:
  (∃ r, In r l ∧ r = fold_left Rmin l x) ∨ ((∀ r, In r l → x < r) ∧ fold_left Rmin l x = x).
Proof.
  revert x. induction l as [| a l] => //=.
  - right. split; auto; intros ? [].
  - intros x. edestruct (IHl (Rmin x a)) as [(r&Hin&Heq)|Hlt].
    * left. exists r. split; auto.
    * destruct (Rlt_dec x a).
      ** right; split.
         *** intros ? [|]; eauto.
             **** subst. nra.
             **** eapply Rle_lt_trans; last eapply Hlt; eauto.
                  rewrite Rmin_left; nra.
         *** destruct Hlt as (?&->). rewrite Rmin_left; nra.
      ** left. move: Hlt. rewrite Rmin_right; last by nra => Hlt.
         intros. exists a; split; first by left.
         apply Rle_antisym.
         ***  apply fold_left_Rmin_glb; try nra. intros. left. apply Hlt; eauto.
         *** apply fold_left_Rmin_init.
Qed.

Lemma fold_left_Rmax_init l x:
  x <= fold_left Rmax l x.
Proof.
  revert x. induction l => //=; first reflexivity.
  intros x. etransitivity; last eapply IHl.
  apply Rmax_l.
Qed.

Lemma fold_left_Rmax_mono_init l x x':
  x <= x' →
  fold_left Rmax l x <= fold_left Rmax l x'.
Proof.
  revert x x'. induction l => //=.
  intros. eapply IHl. 
  apply Rle_max_compat_r; auto.
Qed.

Lemma fold_left_Rmax_cons a l x:
   fold_left Rmax l x <= fold_left Rmax (a :: l) x.
Proof.
  revert a x. destruct l.
  - intros; apply Rmax_l.
  - intros => //=. apply fold_left_Rmax_mono_init.
    apply Rle_max_compat_r. apply Rmax_l.
Qed.

Lemma fold_left_Rmax_lub l r x:
  (∀ r', In r' l → r' <= r) → x <= r → fold_left Rmax l x <= r.
Proof.
  revert r x. induction l as [| a l] => //=.
  intros r x Hglb Hinit. eapply IHl.
  - intros. apply Hglb; eauto.
  - apply Rmax_lub; eauto.
Qed.

Lemma fold_left_Rmax_witness1 l x:
  (∃ r, In r l ∧ r = fold_left Rmax l x) ∨ ((∀ r, In r l → r < x) ∧ fold_left Rmax l x = x).
Proof.
  revert x. induction l as [| a l] => //=.
  - right. split; auto; intros ? [].
  - intros x. edestruct (IHl (Rmax x a)) as [(r&Hin&Heq)|Hlt].
    * left. exists r. split; auto.
    * destruct (Rgt_dec x a).
      ** right; split.
         *** intros ? [|]; eauto.
             **** subst. nra.
             **** eapply Rge_gt_trans; last eapply Hlt; eauto.
                  rewrite Rmax_left; nra.
         *** destruct Hlt as (?&->). rewrite Rmax_left; nra.
      ** left. move: Hlt. rewrite Rmax_right; last by nra => Hlt.
         intros. exists a; split; first by left.
         apply Rle_antisym.
         *** apply fold_left_Rmax_init.
         *** apply fold_left_Rmax_lub; try nra. intros. left. apply Hlt; eauto.
Qed.


Lemma fold_left_Rmax_Rmin_map {A} (l: list A) (x: R) f:
   fold_left Rmax (map f l) x = - fold_left Rmin (map (λ x, - f x) l) (- x).
Proof.
  revert x.
  induction l => x //=.
  - nra.
  - assert (- Rmax x (f a) = Rmin (- x) (-f a)) as <-; last auto.
    apply Ropp_Rmax.
Qed.

Lemma allpairs_comp {A A' B B'} (f1: A → A') (f2: B → B') l1 l2:
  [seq (f1 x1, f2 x2) | x1 <- l1, x2 <- l2] =
  [seq (x1, x2) | x1 <- [seq f1 i | i <- l1], x2 <- [seq f2 i | i <- l2]].
Proof.
  revert f1 f2 l2; induction l1 => //= f1 f2 l2.
  rewrite ?IHl1.
  rewrite -map_comp //=.
Qed.

Lemma foldl_Rmin l:
  ∀ x, foldl Rmin x l <= x.
Proof.
  induction l; rewrite //=; intros; try nra.
  eapply Rle_trans; first eapply IHl.
  apply Rmin_l.
Qed.
