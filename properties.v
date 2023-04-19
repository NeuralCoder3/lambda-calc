Load semantics.
Require Import Lia.

Lemma closed_lift e k n:
  closed k e -> lift e k n = e.
Proof.
  induction e in k,n |- *;intros H.
  - cbn [lift]. cbn in H. now apply PeanoNat.Nat.ltb_lt in H as ->.
  - cbn. destruct H. now rewrite IHe1,IHe2. 
  - cbn. rewrite IHe;easy.
Qed.

Definition closed0_lift e n := closed_lift e 0 n.


Lemma closed_subst e k x:
  closed k e -> subst x k e = e.
Proof.
  induction e in k,x |- *;intros H.
  - cbn [subst]. cbn in H.
    assert(Nat.eqb n k = false) as -> by (apply PeanoNat.Nat.eqb_neq;lia).
    assert(Nat.ltb n k = true) as -> by (now apply PeanoNat.Nat.ltb_lt).
    reflexivity.
  - cbn. destruct H. now rewrite IHe1,IHe2. 
  - cbn. rewrite IHe;easy.
Qed.
Definition closed0_subst e x := closed_subst e 0 x.

Lemma closed_inc e k:
  closed k e -> closed (Datatypes.S k) e.
Proof.
  intros H. induction e in k,H |- *;cbn in *.
  - lia.
  - destruct H. split;eauto.
  - now apply IHe.
Qed.

Lemma closed_add e k l:
  closed k e -> closed (l+k) e.
Proof.
  induction l.
  - easy.
  - intros H%IHl. cbn. now apply closed_inc.
Qed.
    

Lemma fixpoint f:
  closed0 f ->
  (lam_Y ⋅ f) ≡ (f ⋅ (lam_Y ⋅ f)).
Proof.
  eexists;split. 
  - eapply steps_step; [apply step_beta|];cbn.
    eapply steps_step; [apply step_beta|];cbn.
    repeat setoid_rewrite closed_lift.
    repeat setoid_rewrite closed_subst.
    all: (try apply closed_inc;try easy).
    apply steps_refl.
  - eapply steps_step.
    {
      apply step_app_right.
      apply step_beta;cbn.
    }
    cbn.
    repeat setoid_rewrite closed_lift;try easy.
    apply steps_refl.
Qed.

Hint Resolve closed_inc : core.

Ltac resolve_closed :=
  cbn;firstorder;lia;now auto.


Ltac clear_lift_subst :=
  repeat setoid_rewrite closed_lift;
  repeat setoid_rewrite closed_subst;
  try resolve_closed.

Lemma steps_beta e1 e2:
  steps (app (lam e1) e2) (subst0 e2 e1).
Proof.
  eapply steps_step; [apply step_beta|];cbn.
  apply steps_refl.
Qed.

(* contextual semantics lift *)
Lemma steps_lam e1 e2:
  steps e1 e2 -> steps (lam e1) (lam e2).
Proof.
  induction 1.
  - constructor.
  - eapply steps_step.
    2: now apply IHsteps.
    now apply step_lam.
Qed.

Lemma steps_app_left e1 e2 e:
  steps e1 e2 -> steps (app e1 e) (app e2 e).
Proof.
  induction 1.
  - constructor.
  - eapply steps_step.
    2: now apply IHsteps.
    now apply step_app_left.
Qed.

Lemma steps_app_right e1 e2 e:
  steps e1 e2 -> steps (app e e1) (app e e2).
Proof.
  induction 1.
  - constructor.
  - eapply steps_step.
    2: now apply IHsteps.
    now apply step_app_right.
Qed.

Lemma steps_trans e1 e2 e3:
  steps e1 e2 -> steps e2 e3 -> steps e1 e3.
Proof.
  intros H1 H2.
  induction H1.
  - easy.
  - eapply steps_step.
    2: now apply IHsteps.
    easy.
Qed.

Lemma equiv_trans e1 e2 e3:
  e1 ≡ e2 -> e2 ≡ e3 -> e1 ≡ e3.
Proof.
  intros (e12&H1_2&H2_1).
  intros (e23&H2_3&H3_2).
  (* confluence at e2 -> e12, e23 *)
Admitted.

Lemma equiv_app_left e1 e2 e3:
  e1 ≡ e2 -> e1 ⋅ e3 ≡ e2 ⋅ e3.
Proof.
  intros (e12&H1_2&H2_1).
  eexists;split.
  all: apply steps_app_left;eassumption.
Qed.

Lemma equiv_app_right e1 e2 e3:
  e1 ≡ e2 -> e3 ⋅ e1 ≡ e3 ⋅ e2.
Proof.
  (* conceptually: could delay eval until needed, confluence *)
  intros (e12&H1_2&H2_1).
  eexists;split.
  all: apply steps_app_right;eassumption.
Qed.
