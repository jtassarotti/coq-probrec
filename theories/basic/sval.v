From mathcomp Require Export ssreflect eqtype ssrbool.

Lemma sval_inj_pred {A: Type} (P: pred A) (a b: {x : A | P x}):
  sval a = sval b -> a = b.
Proof.  
  destruct a, b. rewrite /sval. intros. subst; f_equal. apply bool_irrelevance.
Qed.

Require ProofIrrelevance.

Lemma sval_inj_pi {A: Type} (P: A -> Prop) (a b: {x : A | P x}):
  sval a = sval b -> a = b.
Proof.  
  destruct a, b. rewrite /sval. intros. subst; f_equal. apply ProofIrrelevance.proof_irrelevance.
Qed.