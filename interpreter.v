Load properties.

(*
Syntax
*)

(*
nil := λ x y. y
cons v vs = λ x y. x v vs
  (x = λ a. a F0 F1)

B0 := λ x y. x
B1 := λ x y. y
*)

Definition nil := λ, λ, var 0.
(* Definition cons v vs := λ, λ, var 1 ⋅ v ⋅ vs. *)
Definition B0 := λ, λ, var 1.
Definition B1 := λ, λ, var 0.

(*

F = Y (λ e c s. s (λ a. a F0 F1))
F0 = λ t. t (λ b. c (b K S))
F1 = e (λ x. e (λ y. c (x y)))

F C (encode M :: N) 
  ~> C M N

F0 C (b::xs) 
  ~> C (b K S) xs
F1 C F (enc A ++ enc B ++ ys)
  ~> F (λ x. F (λ y. C (x y))) (enc A ++ enc B ++ ys)
  ~> ...
  ~> F (λ y. C (A y)) (enc B ++ ys)
  ~> (λ y. C (A y)) B ys
  ~> C (A B) ys

*)

Definition F0 C :=
  λ, var 0 ⋅ (λ, (lift0 2 C) ⋅ (var 0 ⋅ lam_K ⋅ lam_S)).
Definition F1 F C :=
  F ⋅ (λ, (lift0 1 F) ⋅ (λ, (lift0 2 C) ⋅ (var 1 ⋅ var 0))).

Definition F' := 
  (* λ f c s. s *)
  (λ, λ, λ, var 0 ⋅ 
    (* λ a. a F0 F1 *)
    (* F0 C, F1 F C *)
    (λ, var 0 ⋅ (F0 (var 2)) ⋅ (F1 (var 3) (var 2)))).
Definition F := lam_Y ⋅ F'.







(*
Helper functions
*)

Fixpoint encode (s : SK) : list bool :=
  match s with
  | K => [false;false]
  | S => [false;true]
  | SK_app s1 s2 => true::encode s1 ++ encode s2
  end.

Fixpoint encode_list (l : list SK) : list bool :=
  match l with
  | [] => []
  | x::xs => encode x ++ encode_list xs
  end.

Fixpoint to_lam (s : SK) : lambda :=
  match s with
  | K => lam_K
  | S => lam_S
  | SK_app s1 s2 => app (to_lam s1) (to_lam s2)
  end.

(*
  nested pair approach
  [] => λ x y. y
  [x,y, ..., z] => <x, <y, ..., <z, nil>>>
  <a,b> => λ z. z a b
*)
Definition tuple a b := λ, var 0 ⋅ a ⋅ b.
Fixpoint embed_lam_list (xs : list lambda) : lambda :=
  match xs with
  | [] => λ, λ, var 0
  | x::xs => tuple x (embed_lam_list xs)
  end.

Definition embed_list (l : list bool) : lambda :=
  embed_lam_list (map (fun (x:bool) => if x then B1 else B0) l).





(*
Specification:
*)

Definition F0_spec C b xs :=
  (F0 C) ⋅ (tuple b xs) ≡ C ⋅ (b ⋅ lam_K ⋅ lam_S) ⋅ xs.

Definition F1_spec C A B xs :=
  (F1 F C) ⋅ 
  embed_list (encode A ++ encode B ++ encode_list xs) ≡ 
  C ⋅ (to_lam A ⋅ to_lam B) ⋅ (embed_list (encode_list xs)).

Definition F_spec C (x:SK) (xs:list SK) :=
  F ⋅ C ⋅ (embed_list (encode x ++ encode_list xs)) ≡ C ⋅ (to_lam x) ⋅ (embed_list(encode_list xs)).








(*
Aux lemmas
*)

Lemma closed_SK x: closed0 (to_lam x).
Proof.
  induction x;cbn;try easy;lia.
Qed. 

Lemma closed_embed_lam_list xs:
  (* (forall x, In x xs -> closed0 x) -> *)
  Forall (closed 0) xs ->
  closed0 (embed_lam_list xs).
Proof.
  induction 1;cbn;resolve_closed.
Qed.

Corollary closed_embed_list xs:
  closed0 (embed_list xs).
Proof.
  unfold embed_list.
  eapply closed_embed_lam_list.
  induction xs;constructor;auto.
  destruct a;cbn;resolve_closed.
Qed.

Hint Resolve closed_SK.
Hint Resolve closed_embed_lam_list.
Hint Resolve closed_embed_list.


Lemma B0_select a b:
  closed0 a -> closed0 b ->
  B0 ⋅ a ⋅ b ≡ a.
Proof.
  (* could be strengthened => a should only be forbidden from binding b *)
  intros.
  eexists;split;[|apply steps_refl].
  eapply steps_trans.
  apply steps_app_left,steps_beta. cbn;clear_lift_subst.
  eapply steps_trans.
  apply steps_beta. cbn;clear_lift_subst.
  apply steps_refl.
Qed.

Lemma B1_select a b:
  closed0 a -> closed0 b ->
  B1 ⋅ a ⋅ b ≡ b.
Proof.
  (* could be strengthened => a should only be forbidden from binding b *)
  intros.
  eexists;split;[|apply steps_refl].
  eapply steps_trans.
  apply steps_app_left,steps_beta. cbn;clear_lift_subst.
  eapply steps_trans.
  apply steps_beta. cbn;clear_lift_subst.
  apply steps_refl.
Qed.



(*
Main lemma chain
*)


Lemma F0_spec_proof C a xs:
  closed0 C -> closed0 a -> closed0 xs ->
  F0_spec C a xs.
Proof.
  unfold F0_spec.
  intros HC_C HC_a HC_xs.
  unfold F0.
  (* remember lam_K as K.
  remember lam_S as S. *)
  eexists;split. 
  2: apply steps_refl.
  - eapply steps_trans.
    apply steps_beta.
    cbn;clear_lift_subst.

    eapply steps_trans.
    apply steps_beta.
    cbn;clear_lift_subst.

    eapply steps_trans.
    apply steps_app_left, steps_beta.
    cbn;clear_lift_subst.

    fold lam_K lam_S.
    apply steps_refl.
Qed.

Lemma F1_spec_proof C A B xs:
  (* (forall C x xs, closed0 C -> F_spec C x xs) -> *)
  (forall C, closed0 C -> F_spec C A (B::xs) ) ->
  (forall C, closed0 C -> F_spec C B (xs) ) ->
  closed0 C -> 
  F1_spec C A B xs.
Proof.
  intros F_spec_proof_A F_spec_proof_B HC_C.
  unfold F1_spec, F1.
  remember (to_lam A) as Al.
  remember (to_lam B) as Bl.
  eapply equiv_trans.
  {
    remember (λ, (lift0 1 F) ⋅ (λ, (lift0 2 C) ⋅ (var 1 ⋅ var 0))) as Cont.
    pose proof (F_spec_proof_A Cont).
    unfold F_spec in H; cbn -[lift0] in H.
    subst.
    apply H.
    clear_lift_subst.
  }
  eapply equiv_trans.
  {
    eexists;split;[|apply steps_refl].
    apply steps_app_left.
    apply steps_beta.
  }
  cbn -[F].  clear_lift_subst.
  eapply equiv_trans.
  {
    apply F_spec_proof_B.
    clear_lift_subst.
  }
  eexists;split;[|apply steps_refl].
  apply steps_app_left.
  eapply steps_step.
  1: apply step_beta.
  cbn;clear_lift_subst.
  now subst; apply steps_refl.
  (* or leave open using Defined for transparency check of recursion *)
Qed.

Lemma F_fix C:
  closed0 C -> 
  F ⋅ C ≡ F' ⋅ F ⋅ C.
Proof.
  intros HC_C.
  unfold F.
  eapply equiv_trans.
  {
    apply equiv_app_left.
    apply fixpoint.
    resolve_closed.
  }
  eexists;split;[|apply steps_refl].
  apply steps_refl.
Qed.

Lemma F_unfold C xs:
  closed0 C -> 
  closed0 xs -> 
  F ⋅ C ⋅ xs ≡ 
  xs ⋅ (λ, (var 0) ⋅ (F0 C) ⋅ (F1 F C)).
Proof.
  intros HC_C HC_xs. 
  eapply equiv_trans.
  {
    apply equiv_app_left.
    now apply F_fix.
  }
  eexists;split;[|apply steps_refl].

  (* inline F and C *)
  eapply steps_trans.
  {
    do 2 apply steps_app_left.
    apply steps_beta.
  }
  cbn -[lam_Y F']; clear_lift_subst.
  (* cbn -[lam_Y F0 F']; clear_lift_subst. *)
  eapply steps_trans.
  {
    apply steps_app_left.
    apply steps_beta.
  }
  cbn -[lam_Y F']; clear_lift_subst.

  (* fold F0 C *)
  pose (X := F0 C).
  assert (X=F0 C) by reflexivity.
  unfold F0 in H.
  rewrite closed0_lift in H;[|assumption].
  setoid_rewrite <- H;subst X;clear H.

  pose (X := F1 F C).
  assert (X=F1 F C) by reflexivity.
  unfold F1, F in H.
  do 2  rewrite closed0_lift in H;try resolve_closed.
  setoid_rewrite <- H;subst X.

  (* reduce app tuple *)
  eapply steps_trans.
  {
    apply steps_beta.
  }
  cbn -[lam_Y F0 F1 F' tuple]; clear_lift_subst.
  2-3: cbn;clear_lift_subst.

  apply steps_refl.
Qed.

Lemma F_app_head C b xs:
  closed0 C -> 
  closed0 b -> closed0 xs -> 
  F ⋅ C ⋅ (tuple b xs) ≡ b ⋅ (F0 C) ⋅ (F1 F C) ⋅ xs.
Proof.
  intros HC_C HC_b HC_xs. 
  eapply equiv_trans.
  apply F_unfold;cbn;try resolve_closed.
  eexists;split;[|apply steps_refl].

  (* apply tuple *)
  eapply steps_trans.
  {
    apply steps_beta.
  }
  cbn -[lam_Y F0 F1 F']; clear_lift_subst.
  2-3: cbn;clear_lift_subst.
  (* apply head *)
  eapply steps_trans.
  {
    apply steps_app_left.
    apply steps_beta.
  }
  cbn -[lam_Y F0 F1 F']; clear_lift_subst.
  2-3: cbn;clear_lift_subst.

  apply steps_refl.
Qed.

Corollary F_app_0 C xs:
  closed0 C -> 
  closed0 xs -> 
  F ⋅ C ⋅ (tuple B0 xs) ≡ F0 C ⋅ xs.
Proof.
  intros.
  eapply equiv_trans.
  apply F_app_head;try assumption;clear_lift_subst.
  apply equiv_app_left, B0_select.
  all: cbn;clear_lift_subst.
Qed.

Corollary F_app_1 C xs:
  closed0 C -> 
  closed0 xs -> 
  F ⋅ C ⋅ (tuple B1 xs) ≡ F1 F C ⋅ xs.
Proof.
  intros.
  eapply equiv_trans.
  apply F_app_head;try assumption;clear_lift_subst.
  apply equiv_app_left, B1_select.
  all: cbn;clear_lift_subst.
Qed.

(*
F0 0, F0 1
=> F⋅K, F⋅S
*)
Corollary F0_app_0 C xs:
  closed0 C -> closed0 xs ->
  F0 C ⋅ (tuple B0 xs) ≡ C ⋅ lam_K ⋅ xs.
Proof.
  intros.
  eapply equiv_trans.
  apply F0_spec_proof;resolve_closed.
  apply equiv_app_left, equiv_app_right, B0_select;resolve_closed.
Qed.

Corollary F0_app_1 C xs:
  closed0 C -> closed0 xs ->
  F0 C ⋅ (tuple B1 xs) ≡ C ⋅ lam_S ⋅ xs.
Proof.
  intros.
  eapply equiv_trans.
  apply F0_spec_proof;resolve_closed.
  apply equiv_app_left, equiv_app_right, B1_select;resolve_closed.
Qed.

Corollary F_app_K C xs:
  closed0 C -> 
  F ⋅ C ⋅ (embed_list (encode K ++ encode_list xs)) ≡ C ⋅ lam_K ⋅ (embed_list (encode_list xs)).
Proof.
  intros.
  cbn.
  eapply equiv_trans.
  apply F_app_0.
  3: apply F0_app_0.
  all: cbn;firstorder.
  apply closed_inc, closed_embed_list.
Qed.

Corollary F_app_S C xs:
  closed0 C -> 
  F ⋅ C ⋅ (embed_list (encode S ++ encode_list xs)) ≡ C ⋅ lam_S ⋅ (embed_list (encode_list xs)).
Proof.
  intros.
  cbn.
  eapply equiv_trans.
  apply F_app_0.
  3: apply F0_app_1.
  all: cbn;firstorder.
  apply closed_inc, closed_embed_list.
Qed.

(*
Now app
*)

Lemma F_app_app C A B xs:
  (forall C : lambda, closed0 C -> F_spec C A (B :: xs)) ->
  (forall C : lambda, closed0 C -> F_spec C B xs) ->
  closed0 C ->
  (F ⋅ C) ⋅ embed_list (encode (SK_app A B) ++ encode_list xs)
  ≡ (C ⋅ to_lam (SK_app A B)) ⋅ embed_list (encode_list xs).
Proof.
  intros.
  cbn.
  rewrite <- app_assoc.
  eapply equiv_trans.
  apply F_app_1;cbn;clear_lift_subst.
  1: apply closed_embed_list.
  now apply F1_spec_proof;cbn;clear_lift_subst.
Qed.

Lemma F_nil C:
  closed0 C ->
  F ⋅ C ⋅ nil ≡ λ, var 0.
Proof.
  intros HC_C.
  eapply equiv_trans.
  apply F_unfold;try resolve_closed.
  eexists;split;[|apply steps_refl].
  apply steps_beta.
Qed.


Lemma F_spec_proof C x xs:
  closed0 C -> 
  F_spec C x xs.
Proof.
  intros HC_C.
  induction x in C,HC_C,xs |-*.
  + now apply F_app_S.
  + now apply F_app_K.
  + apply F_app_app;eauto.
Qed.
