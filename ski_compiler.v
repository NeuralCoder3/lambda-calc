Load properties.

Lemma equiv_refl e: 
  e ≡ e.
Proof.
  eexists;split;apply steps_refl.
Qed.

Lemma equiv_app e1a e1b e2a e2b:
  e1a ≡ e1b -> e2a ≡ e2b -> app e1a e2a ≡ app e1b e2b.
Proof.
  intros [n1 [H1 H1']] [n2 [H2 H2']].
  eexists (app n1 n2);split.
  - eapply steps_trans.
    apply steps_app_left, H1.
    apply steps_app_right, H2.
  - eapply steps_trans.
    apply steps_app_left, H1'.
    apply steps_app_right, H2'.
Qed.

Lemma equiv_lam e1 e2:
  e1 ≡ e2 -> lam e1 ≡ lam e2.
Proof.
  intros [n [H1 H1']].
  now exists (lam n);split;apply steps_lam.
Qed.

Hint Resolve equiv_refl equiv_app equiv_lam : core.

Lemma lift_by_zero e k:
  lift e k 0 = e.
Proof.
  induction e in k |- *;simpl;auto.
  - destruct Nat.ltb;auto.
  - now rewrite IHe1, IHe2.
  - now f_equal.
Qed.


Lemma subst_none e1 e2 k n m:
  k <= m -> m <= k+n ->
  (lift e1 k (Datatypes.S n)) [m <- e2] = lift e1 k n.
Proof.
  intros Hlow Hhigh.
  induction e1 in k, n, m, Hlow, Hhigh |- *;simpl;auto.
  - destruct Nat.ltb eqn: H.
    + apply PeanoNat.Nat.ltb_lt in H. cbn.
      assert (Nat.eqb n0 m = false) as -> by
        (apply PeanoNat.Nat.eqb_neq;lia).
      destruct m;try lia.
      assert (Nat.leb n0 m = true) as -> by
        (apply PeanoNat.Nat.leb_le;lia).
      reflexivity.
    + cbn.
      apply PeanoNat.Nat.ltb_ge in H.
      assert (Nat.eqb (n0 + Datatypes.S n) m = false) as -> by
        (apply PeanoNat.Nat.eqb_neq; lia).
      destruct m;[f_equal;lia|].
      assert(Nat.leb (n0 + Datatypes.S n) m = false) as -> by
        (apply PeanoNat.Nat.leb_gt;lia).
      f_equal;lia.
  - rewrite IHe1_1;try lia.
    rewrite IHe1_2;try lia.
    reflexivity.
  - now rewrite IHe1;try lia.
Qed.

Lemma subst0_0 e k:
  (lift e (Datatypes.S k) 1) [k <- var 0] = e.
Proof.
  induction e in k |- *;simpl.
  - destruct Nat.ltb eqn: H;cbn.
    + apply PeanoNat.Nat.ltb_lt in H.
      assert (Nat.eqb n k = false) as -> by
        (apply PeanoNat.Nat.eqb_neq;lia).
  - admit.
  - now rewrite IHe.

(* Lemma subst0_0 e:
  (lift0 1 e) [0 <- var 0] = e.
Proof.
  induction e;simpl.
  - admit.
  - admit.
  - 
  (* - now f_equal.
  - now do 2 rewrite lift_by_zero.
  - now rewrite lift_by_zero. *)
Qed. *)

Lemma equiv_S f g:
  lam_S ⋅ (λ, f) ⋅ (λ, g) ≡ λ, f ⋅ g.
Proof.
  eexists;split;[|apply steps_refl].
  eapply steps_trans.
  {
    apply steps_app_left.
    apply steps_beta.
  } cbn.
  eapply steps_trans.
  {
    apply steps_beta.
  } cbn.
  (* reduction inside *)
  apply steps_lam.
  eapply steps_trans.
  {
    apply steps_app_left.
    apply steps_beta.
  } cbn.
  eapply steps_trans.
  {
    apply steps_app_right.
    apply steps_beta.
  } cbn.
  rewrite subst_none;try lia.
  rewrite subst_none;try lia.

  pose proof (subst_none f (λ, g) 1 1 2).
  rewrite H.


  setoid_rewrite subst_none with (k:=1 n := 1, m := 2).
Admitted.

Lemma equiv_K a:
  lam_K ⋅ a ≡ λ, lift0 1 a.
Proof.
  eexists;split;[|apply steps_refl].
  unfold lam_K.
  eapply steps_trans.
  {
    apply steps_beta.
  }
  cbn.
  apply steps_refl.
Qed.

Hint Resolve equiv_K equiv_S.

Lemma I_spec:
  lam_S ⋅ lam_K ⋅ lam_K ≡ λ, var 0.
Proof.
  eexists;split;[|apply steps_refl].
  eapply steps_trans.
  {
    apply steps_app_left.
    apply steps_beta.
  } cbn.
  eapply steps_trans.
  {
    apply steps_beta.
  } cbn.
  apply steps_lam.
  eapply steps_trans.
  {
    apply steps_app_left.
    apply steps_beta.
  } cbn.
  eapply steps_trans.
  {
    apply steps_beta.
  } cbn.
  apply steps_refl.
Qed.

Hint Resolve I_spec.

Lemma eta_equiv e:
  e ≡ λ, (lift0 1 e) ⋅ (var 0).
Proof.
  eexists;split;[apply steps_refl|].
  eapply steps_step;[|apply steps_refl].
  apply step_eta.
Qed.

(* 1/2
reify_combined (unlift0 e9) ≡ lam (app (reify_combined e9) (var 0))
2/2
app lam_K (reify_combined (unlift0 b)) ≡ lam (reify_combined b) *)

Fixpoint unlift_lam (k:nat) e :=
  match e with
  | lam e => lam (unlift_lam (Datatypes.S k) e)
  | app e1 e2 => app (unlift_lam k e1) (unlift_lam k e2)
  | var n => 
    if Nat.leb k n then
      var (pred n)
    else var n
  end.
Definition unlift0_lam := unlift_lam 0. 

(* Lemma unlift_reification k e:
  reify_combined (unlift k e) = unlift_lam k (reify_combined e). *)




(* 
Fixpoint unlift_lam (k:nat) e :=
  match e with
  | lam e => lam (unlift_lam (Datatypes.S k) e)
  | app e1 e2 => app (unlift_lam k e1) (unlift_lam k e2)
  | var n => 
    if Nat.leb k n then
      var (pred n)
    else var n
  end.
Definition unlift0_lam := unlift_lam 0. 
*)

(* if not binds var 0, lift0 1 (unlift0 a) = a *)
(* Lemma equiv_K_unlift a:
  lam_K ⋅ (unlift0_lam a) ≡ λ, a.
Proof.
  eexists;split;[|apply steps_refl].
  unfold lam_K.
  eapply steps_trans.
  {
    apply steps_beta.
  }
  cbn.
  apply steps_refl.
Qed. *)









Inductive combined :=
  | CLam : combined -> combined
  | CApp : combined -> combined -> combined
  | CVar : nat -> combined
  | CS : combined
  | CK : combined
  .

Definition CI := CApp (CApp CS CK) CK.

From Equations Require Import Equations.

Fixpoint embed_lam (e:lambda) : combined :=
  match e with
  | lam e => CLam (embed_lam e)
  | app e1 e2 => CApp (embed_lam e1) (embed_lam e2)
  | var n => CVar n
  end.

(* Equations? to_ski (e:lambda) : combined :=
  to_ski (lam e) := CLam (to_ski e);
  to_ski (app e1 e2) := CApp (to_ski e1) (to_ski e2);
  to_ski (var n) := CVar n. *)

Fixpoint binds (k:nat) (e:combined) :=
  match e with
  | CLam e => binds (Datatypes.S k) e
  | CApp e1 e2 => orb (binds k e1) (binds k e2)
  | CVar n => Nat.eqb n k
  | _ => false
  end.

Fixpoint size (e:combined) :=
  match e with
  | CLam e => Datatypes.S (size e)
  | CApp e1 e2 => Datatypes.S (size e1 + size e2)
  | _ => 1
  end.

  (*
  by wf e relation
  *)

  Ltac obligation_tactic :=
    simpl in *; 
    Tactics.program_simplify;
    CoreTactics.equations_simpl;
    try Tactics.program_solve_wf.

  (* Show Obligation Tactic. *)
(* Obligation Tactic := idtac. *)


(*
need that the result of ski is smaller
(and thus need lambda much larger)


or stepwise esolang
https://esolangs.org/wiki/S_and_K_Turing-completeness_proof
*)

(*
decrease >=k by 1
*)
Fixpoint unlift (k:nat) e :=
  match e with
  | CLam e => CLam (unlift (Datatypes.S k) e)
  | CApp e1 e2 => CApp (unlift k e1) (unlift k e2)
  | CVar n => 
    if Nat.leb k n then
      CVar (pred n)
    else CVar n
  | e => e
  end.
Definition unlift0 := unlift 0.

Compute (unlift0 (CVar 1)).

Fixpoint ski_step e :=
  (* match e with
  | CLam (CApp x (CVar 0)) => x
  | CLam (CVar 0) => CI
  (* or general b without var 0 *)
  | CLam (CVar y) => CApp CK (CVar y)
  | CLam (CApp e1 e2) => CApp (CApp CS (CLam e1)) (CLam e2)
  (* congruence *)
  | CLam e => CLam (ski_step e)
  | CApp e1 e2 => CApp (ski_step e1) (ski_step e2)
  | _ => e
  end. *)
  match e with
  | CLam b =>
    if binds 0 b then
      match b with
      (* λ x. f x = f *)
      | CApp x (CVar 0) => unlift0 x
      (* λ x. x = I *)
      | CVar 0 => CI
      (* λ x. a b => S (λ x. a) (λ x. b) *)
      | CApp e1 e2 => CApp (CApp CS (CLam e1)) (CLam e2)
      | _ => CLam (ski_step b)
      end
    else 
      (* λ x. b => K b *)
      CApp CK (unlift0 b)
  | CApp e1 e2 => CApp (ski_step e1) (ski_step e2)
  | _ => e
  end.


(* λ m n. n m *)
Definition e0 := CLam (CLam (CApp (CVar 0) (CVar 1))).
Definition e1 := ski_step e0.
Definition e2 := ski_step e1.
Definition e3 := ski_step e2.
Definition e4 := ski_step e3.
Definition e5 := ski_step e4.
Definition e6 := ski_step e5.

Notation "λ, e" := (CLam e) (at level 60, e at level 99).
Notation "e1 ⋅ e2" := (CApp e1 e2) (at level 50).
Notation "'⬡' n" := (CVar n) (at level 50).

Compute e0.
Compute e1.
Compute e2.
Compute e3.
Compute e4.

(*
results in SK
embed (to_ski (embed e)) ≡ e
*)

Fixpoint is_sk_bool c :=
  match c with
  | CLam _ => false
  | CApp e1 e2 => (is_sk_bool e1 && is_sk_bool e2)%bool
  | CVar _ => false
  | CK | CS => true
  end.

Inductive is_sk : combined -> Prop :=
  | is_sk_K : is_sk CK
  | is_sk_S : is_sk CS
  | is_sk_app e1 e2 : is_sk e1 -> is_sk e2 -> is_sk (CApp e1 e2)
  .

Fixpoint reify_combined c :=
  match c with
  | CLam e => lam (reify_combined e)
  | CApp e1 e2 => app (reify_combined e1) (reify_combined e2)
  | CVar n => var n
  | CS => lam_S
  | CK => lam_K
  end.

Require Import FunInd.
Functional Scheme ski_step_ind := Induction for ski_step Sort Prop.


(* 
Lemma equiv_lam.
Lemma equiv_S.
Lemma equiv_K. *)


Lemma ski_step_equiv e e' :
  ski_step e = e' -> reify_combined e' ≡ reify_combined e.
Proof.
  intros <-.
  functional induction (ski_step e) using ski_step_ind;cbn [reify_combined CI] in *.
  all: auto.
  - admit. (* reify unlift f = lam x, f x (eta) *)
  - (* K *)
    admit.
Admitted.




(*
removes a lam (and var)
or else
moves an app out of lam
*)
Fixpoint lambdaness c :=
  match c with
  | CLam e => 4+20 * lambdaness e
  | CApp e1 e2 => 1+lambdaness e1 + lambdaness e2
  (* var theoretically but not necessary *)
  | _ => 1
  end.

Lemma sk_fixpoint c:
  is_sk c -> ski_step c = c.
Proof.
  induction 1;cbn;auto.
  now rewrite IHis_sk1,IHis_sk2.
Qed.

(*
unlift only changes var, lambdaness does not care about var
*)
Lemma unlift_lambdaness k c:
  lambdaness (unlift k c) = lambdaness c.
Proof.
  induction c in k |- *;cbn [unlift lambdaness].
  - now rewrite IHc.
  - now rewrite IHc1,IHc2.
  - now destruct Nat.leb.
  - reflexivity.
  - reflexivity.
Qed.

Lemma binds_not_sk n c:
  binds n c = true -> ~ is_sk c.
Proof.
  induction c in n |- *;cbn.
  - intros _. inversion 1.
  - intros [H1%IHc1 | H2%IHc2]%Bool.orb_prop;
    inversion 1;firstorder.
  - intros _. inversion 1.
  - inversion 1.
  - inversion 1.
Qed.

Lemma ski_step_lambdaness c:
  lambdaness (ski_step c) < lambdaness c \/ is_sk c.
Proof.
  induction c.
  - cbn [ski_step] in *.
    destruct (binds 0 c) eqn:H0.
    2: {
      cbn [lambdaness].
      unfold unlift0; rewrite unlift_lambdaness.
      lia.
    }
    apply binds_not_sk in H0 as H1.
    destruct IHc;firstorder.
    destruct c eqn:Hc.
    1,4,5: rewrite <- Hc in *;cbn [lambdaness];lia.
    {
      destruct c0_2 eqn:Hc0_2.
      all: cbn [lambdaness];left.
      all: try lia.
      destruct n.
      - unfold unlift0; rewrite unlift_lambdaness. lia.
      - cbn [lambdaness]. lia.
    }
    {
      destruct n.
      2: now cbn in H0.
      left;cbn;lia.
    }
  - destruct IHc1 as [H1 | H1], IHc2 as [H2 | H2];
    try apply sk_fixpoint in H1 as H1';
    try apply sk_fixpoint in H2 as H2';simpl;
    try rewrite H1';
    try rewrite H2';
    try lia.
    right. now constructor.
  - admit. (* open expression *)
  - right;constructor.
  - right;constructor.
Admitted.


Lemma sk_bool_eq c :
  is_sk_bool c = true <-> is_sk c.
Proof.
  induction c;cbn;firstorder.
  - discriminate H1.
  - inversion H1.
  - apply andb_prop in H3 as [].
    constructor; firstorder.
  - apply andb_true_intro.
    inversion H3.
    firstorder.
  - inversion H.
  - inversion H.
  - constructor.
  - constructor.
Qed.


Definition reify (c:combined) (Cert: is_sk_bool c = true) : SK.
Proof.
  assert(c = c) as H by reflexivity.
  induction c;cbn in *.
  - inversion Cert.
  - destruct (is_sk_bool c1) eqn:H1, (is_sk_bool c2) eqn:H2;cbn in Cert;try congruence.
    (* apply andb_prop in Cert as [He1 He2]. *)
    (* apply IHc1 in He1.
    apply IHc2 in He2. *)
    exact (SK_app (IHc1 eq_refl eq_refl) (IHc2 eq_refl eq_refl)).
  - inversion Cert.
  - exact S.
  - exact K.
Defined.

Equations? to_sk (c:combined) : SK by wf (lambdaness c) lt :=
  (* to_sk c with is_sk_bool c := {
    | true := reify c _;
    | false := to_sk (ski_step c)
  }. *)
  to_sk c := 
    (* let H : is_sk_bool c = is_sk_bool c := eq_refl in *)
    (* let finished := is_sk_bool c in
    match finished as b in  with
    | true => reify c _
    | false => to_sk (ski_step c)
    end. *)
    (* match is_sk_bool c as finished with
    | true => _
    | false => to_sk (ski_step c)
    end. *)
    match is_sk_bool c as finished return (is_sk_bool c = finished -> SK) with
    | true => fun H => reify c H
    | false => fun H => to_sk (ski_step c)
    end eq_refl.
    (* _. *)
Proof.
(* refine (
  match is_sk_bool c as finished in is_sk_bool c return (is_sk_bool c = finished -> SK) with
  | true => fun H => reify c _
  | false => fun H => to_sk (ski_step c)
  end eq_refl).
) *)
pose proof (ski_step_lambdaness c) as [].
- apply H0.
- apply sk_bool_eq in H0.
  congruence.
Defined.

Definition sk_test := to_sk e0.
Eval native_compute in (sk_test).
(* Recursive Extraction sk_test. *)


Notation "λ, e" := (lam e) (at level 60, e at level 99).
Notation "e1 ⋅ e2" := (app e1 e2) (at level 50).

Definition nil := λ, λ, var 0.
Definition B0 := λ, λ, var 1.
Definition B1 := λ, λ, var 0.
Definition F0 C :=
  λ, var 0 ⋅ (λ, (lift0 2 C) ⋅ (var 0 ⋅ lam_K ⋅ lam_S)).
Definition F1 F C :=
  F ⋅ (λ, (lift0 1 F) ⋅ (λ, (lift0 2 C) ⋅ (var 1 ⋅ var 0))).
Definition F' := 
  (λ, λ, λ, var 0 ⋅ 
    (λ, var 0 ⋅ (F0 (var 2)) ⋅ (F1 (var 3) (var 2)))).
Definition F := lam_Y ⋅ F'.

Definition F_combined := embed_lam F.
Definition F_sk := to_sk F_combined.

Eval native_compute in (F).

Extraction Language OCaml.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt. 
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Constant Nat.eqb => "(=)".


Recursive Extraction F_sk lambdaness.
(* Eval native_compute in (F_sk). *)








(* 
(*
eventually is_sk
*)

Inductive transformed : combined -> combined -> Prop :=
  | TransRefl e: transformed e e
  | TransStep e e' e'': transformed e e' -> ski_step e' = e'' -> transformed e e''.

(* Lemma eventual_ski e:
  {e' | transformed e e' /\ is_sk e'}.
Proof.
  induction e.
  - admit.
  - destruct IHe1 as [e1' [H1 H1']].
    destruct IHe2 as [e2' [H2 H2']].
    exists (CApp e1' e2').
    split.
    + econstructor;eauto.
    + cbn;auto. *)



Equations? to_ski (e:combined) : combined by wf (size e) lt :=
  to_ski CS := CS;
  to_ski CK := CK;
  to_ski (CVar n) := CVar n;
  (* λ x. f x ≡ f  (eta reduction) *)
  to_ski (CLam (CApp x (CVar 0))) := to_ski x;
  (* λ x. x ≡ I *)
  to_ski (CLam (CVar 0)) := CI;
  (* λ x. b ≡ K b' (if x not in b) *)
  (* λ x. b ≡ S (λ x. e1)' (λ x. e2)'  if b' = e1 e2 *)
  (* other cases are impossible *)
  to_ski (CLam b) := 
    let b' := to_ski b in
    if binds 0 b' then
      match b' with
      | CApp e1 e2 => CApp (CApp CS (to_ski (CLam e1))) (to_ski (CLam e2))
      | _ => CK (* dummy *)
      end
    else CApp CK b';

  (* lifting *)
  to_ski (CApp x y) := CApp (to_ski x) (to_ski y).
Proof.
  all: try (now obligation_tactic).
  (* all: try lia. *)
  (* 23: {
  } *)
  14: {
  }
Next Obligation.
 *)
