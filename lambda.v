Require Import List.
Import ListNotations.
From Equations Require Import Equations.
Require Import Relations.

(* deBruijn encoding *)

(*
conceptually inspired by things I saw in MetaCoq

another implementation:
https://github.com/pi8027/lambda-calculus/blob/master/coq/deBruijn/Untyped.v
*)

Inductive lambda : Type :=
| var : nat -> lambda
| app : lambda -> lambda -> lambda
| lam : lambda -> lambda.

(* substitution *)

(* lift +n if >=k *)
Fixpoint lift (e : lambda) (k : nat) (n : nat) : lambda :=
  match e with
  | var n' => if Nat.ltb n' k then var n' else var (n'+n)
  | app e1 e2 => app (lift e1 k n) (lift e2 k n)
  | lam e => lam (lift e (S k) n)
  end.
Notation lift0 e n := (lift e 0 n).


(*
subst k with e

k -> e
k+(S i) -> k+i
n (<k) -> n

start with k=0
*)
Fixpoint subst (x : lambda) (k : nat) (e:lambda) : lambda :=
  match e with
  | var n => 
    if Nat.eqb n k then lift0 x k (* lift e over all inner binders *)
    else if Nat.ltb n k then var n (* keep inner vars the same *)
    else var (n-1) (* remove binder k => cope with open terms (redex under binder) *)
  | app e1 e2 => app (subst x k e1) (subst x k e2)
  | lam e => lam (subst x (S k) e)
  end.
Notation subst0 x := (subst x 0).


Inductive step : lambda -> lambda -> Prop :=
| step_var n : step (var n) (var n)
| step_beta e1 e2 : step (app (lam e1) e2) (subst0 e2 e1)
| step_lam e1 e2: step e1 e2 -> step (lam e1) (lam e2)
| step_app_left e1 e2 e1' : step e1 e1' -> step (app e1 e2) (app e1' e2)
| step_app_right e1 e2 e2' : step e2 e2' -> step (app e1 e2) (app e1 e2').
(*
we could restrict the redex a lot more
*)

Inductive steps : lambda -> lambda -> Prop :=
| steps_refl e : steps e e
| steps_step e1 e2 e3 : step e1 e2 -> steps e2 e3 -> steps e1 e3.

(*
ω := λx.x x
Ω := ω ω -> ... -> ω ω = Ω
*)
Definition omega := lam (app (var 0) (var 0)).
Definition Omega := app omega omega.

Lemma step_eq e1 e2 e3: step e1 e3 -> e2 = e3 -> step e1 e2.
Proof.
  now intros ? ->.
Qed.

Notation "λ, e" := (lam e) (at level 60, e at level 99).
Notation "e1 ⋅ e2" := (app e1 e2) (at level 50).
Notation "e [ k <- e' ]" := (subst e' k e) (at level 0, e' at level 99).

Example sanity:
  (λ, var 0 ⋅ var 0) = 
  λ, (var 0 ⋅ var 0).
Proof.
  reflexivity.
Qed.

Example sanity2:
  (var 0 ⋅ var 1 ⋅ var 2) =
  ((var 0 ⋅ var 1) ⋅ var 2).
Proof.
  reflexivity.
Qed.

Example omega_step:
  step Omega Omega.
Proof.
  eapply step_eq.
  (* unfold Omega, omega. *)
  apply step_beta.
  now cbn.
Qed.

Definition equivalent e1 e2 := 
  exists e3, steps e1 e3 /\ steps e2 e3.

Notation "e1 ≡ e2" := (equivalent e1 e2) (at level 70).




(*
K = λx.λy.x
S = λx.λy.λz.(x z) (y z)

Y = λf.(λx.f (x x)) (λx.f (x x))
*)
Definition lam_K := λ, λ, var 1.
Definition lam_S := λ, λ, λ, (var 2 ⋅ var 0) ⋅ (var 1 ⋅ var 0).
Definition lam_Y := λ, 
  let r := λ, var 1 ⋅ (var 0 ⋅ var 0) in
  r ⋅ r.

(* could be boolean but prop is easier *)
Fixpoint closed k e :=
  match e with
  | var n => n < k
  | app e1 e2 => (closed k e1) /\ (closed k e2)
  | lam e => closed (S k) e
  end.
Notation closed0 e := (closed 0 e).

Lemma closed_lift e k n:
  closed k e -> lift e k n = e.
Proof.
  induction e in k,n |- *;intros H.
  - cbn [lift]. cbn in H. now apply PeanoNat.Nat.ltb_lt in H as ->.
  - cbn. destruct H. now rewrite IHe1,IHe2. 
  - cbn. rewrite IHe;easy.
Qed.

Definition closed0_lift e n := closed_lift e 0 n.

Require Import Lia.

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
  closed k e -> closed (S k) e.
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


(* lift steps over app *)
(* lift equiv over app *)


(*
nil := λ x y. y
cons v vs = λ x y. x v vs
  (x = λ a. a F0 F1)

B0 := λ x y. x
B1 := λ x y. y
*)

Definition nil := λ, λ, var 1.
Definition cons v vs := λ, λ, var 1 ⋅ v ⋅ vs.
Definition B0 := λ, λ, var 0.
Definition B1 := λ, λ, var 1.

(*

F = Y (λ e c s. s (λ a. a F0 F1))
F0 = λ t. t (λ b. c (b K S))
F1 = e (λ x. e (λ y. c (x y)))

F C (encode M :: N) 
  ~> C M N

F0 C (a::xs) 
  ~> C (a K S) xs
F1 C F (enc A ++ enc B ++ ys)
  ~> F (λ x. F (λ y. C (x y))) (enc A ++ enc B ++ ys)
  ~> ...
  ~> F (λ y. C (A y)) (enc B ++ ys)
  ~> (λ y. C (A y)) B ys
  ~> C (A B) ys

*)

Definition F0 C :=
  λ, var 0 ⋅ (λ, C ⋅ (var 0 ⋅ lam_K ⋅ lam_S)).
Definition F1 C F :=
  F ⋅ (λ, F ⋅ (λ, C ⋅ (var 1 ⋅ var 0))).

Definition F' := 
  (* λ f c s. s *)
  (λ, λ, λ, var 0 ⋅ 
    (* λ a. a F0 F1 *)
    (* F0 C, F1 C F *)
    (λ, var 0 ⋅ (F0 (var 2) ⋅ F1 (var 2) (var 3)))).
Definition F := lam_Y ⋅ F'.


(* Ltac clear_lift_subst :=
  let rec f :=
    repeat (setoid_rewrite closed_lift;[|resolve_closed]);
    repeat (setoid_rewrite closed_subst;[|resolve_closed])
  with resolve_closed :=
    clear_lift_subst;
    cbn;firstorder;try lia;now eauto
  in f. *)

Hint Resolve closed_inc : core.

Ltac resolve_closed :=
  cbn;firstorder;lia;now auto.

(* Ltac resolve_closed :=
  clear_lift_subst;
  cbn;firstorder;try lia;now eauto
  with
Ltac clear_lift_subst :=
  repeat (setoid_rewrite closed_lift;[|resolve_closed]);
  repeat (setoid_rewrite closed_subst;[|resolve_closed]). *)
  (* repeat (
    setoid_rewrite closed_lift;[|
    firstorder;try lia;now eauto]);
  repeat setoid_rewrite closed_subst;
  (repeat apply closed_inc;try easy). *)

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

Definition F0_spec C a xs :=
  (F0 C) ⋅ (cons a xs) ≡ λ, C ⋅ (a ⋅ lam_K ⋅ lam_S) ⋅ xs.

Lemma F0_spec_proof C a xs:
  closed0 C -> closed0 a -> closed0 xs ->
  F0_spec C a xs.
Proof.
  unfold F0_spec.
  intros HC_C HC_a HC_xs.
  unfold cons, F0.
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
    apply steps_lam, steps_app_left, steps_beta.
    cbn;clear_lift_subst.

    fold lam_K lam_S.
    apply steps_refl.
Qed.

Inductive SK : Type :=
  | S : SK
  | K : SK
  | SK_app : SK -> SK -> SK.

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

Fixpoint embed_list (l : list bool) : lambda :=
  match l with
  | [] => nil
  | x::xs => cons (if x then B1 else B0) (embed_list xs)
  end.

Definition F_spec C (x:SK) (xs:list SK) :=
  (* F ⋅ C ⋅ (embed_list (encode_list (x::xs))) ≡ C ⋅ (to_lam x) ⋅ (embed_list(encode_list xs)). *)
  F ⋅ C ⋅ (embed_list (encode x ++ encode_list xs)) ≡ C ⋅ (to_lam x) ⋅ (embed_list(encode_list xs)).

Lemma equiv_trans e1 e2 e3:
  e1 ≡ e2 -> e2 ≡ e3 -> e1 ≡ e3.
Proof.
  intros (e12&H1_2&H2_1).
  intros (e23&H2_3&H3_2).
  (* confluence at e2 -> e12, e23 *)
Admitted.

Definition F1_spec C A B xs :=
  (F1 C F) ⋅ 
  embed_list (encode A ++ encode B ++ encode_list xs) ≡ 
  C ⋅ (to_lam A ⋅ to_lam B) ⋅ (embed_list (encode_list xs)).

(* Lemma closed_F : closed0 F.
Proof.
  unfold F; firstorder;cbn;lia.
Qed.

Lemma closed_F' : closed0 F'.
Proof.
  firstorder;cbn;lia.
Qed.

Lemma closed_Y : closed0 lam_Y.
Proof.
  firstorder;cbn;lia.
Qed.*)

Lemma closed_SK x: closed0 (to_lam x).
Proof.
  induction x;cbn;try easy;lia.
Qed. 

Hint Resolve closed_SK.

Lemma F1_spec_proof C A B xs:
  (forall C x xs, closed0 C -> F_spec C x xs) ->
  closed0 C -> 
  F1_spec C A B xs.
Proof.
  intros F_spec_proof HC_C.
  unfold F1_spec, F1.
  remember (to_lam A) as Al.
  remember (to_lam B) as Bl.
  eapply equiv_trans.
  {
    remember (λ, F ⋅ (λ, C ⋅ (var 1 ⋅ var 0))) as Cont.
    pose proof (F_spec_proof Cont A (B::xs)).
    unfold F_spec in H; cbn in H.
    subst.
    apply H.
    resolve_closed.
  }
  eapply equiv_trans.
  {
    eexists;split;[|apply steps_refl].
    apply steps_app_left.
    apply steps_beta.
  }
  cbn -[F].  clear_lift_subst.
  (* cbn -[F].  clear_lift_subst;try now first [apply closed_F|apply closed_SK]. *)
  eapply equiv_trans.
  {
    apply F_spec_proof.
    clear_lift_subst.
    (* firstorder;cbn;try lia. *)
    (* all: apply closed_inc; 
        now first [assumption|apply closed_SK]. *)
  }
  eexists;split;[|apply steps_refl].
  apply steps_app_left.
  eapply steps_step.
  1: apply step_beta.
  cbn;clear_lift_subst.
  (* all: try apply closed_SK. *)
  now subst; apply steps_refl.
Defined.

Lemma equiv_app_left e1 e2 e3:
  e1 ≡ e2 -> e1 ⋅ e3 ≡ e2 ⋅ e3.
Proof.
  intros (e12&H1_2&H2_1).
  eexists;split.
  all: apply steps_app_left;eassumption.
Qed.

(* Hint Resolve closed_inc : core. *)
(* Hint Resolve closed_F : core.
Hint Resolve closed_Y : core.
Hint Resolve closed_F' : core. *)

Lemma F_spec_proof C ys:
  closed0 C -> 
  match ys with
  | [] => F ⋅ C ⋅ nil ≡ λ, var 0
  | x::xs => F_spec C x xs
  end.
Proof.
  induction ys as [|x xs IH].
  - intros HC_C.
    unfold F.
    eapply equiv_trans.
    {
      do 2 apply equiv_app_left.
      apply fixpoint.
      resolve_closed.
    }
    eexists;split;[|apply steps_refl].

    eapply steps_trans.
    do 2 apply steps_app_left.
    apply steps_beta.
    cbn -[lam_Y F0 F']; clear_lift_subst.

    eapply steps_trans.
    apply steps_app_left.
    apply steps_beta.
    cbn -[lam_Y F0 F']; clear_lift_subst.

    eapply steps_trans.
    apply steps_beta.
    cbn -[lam_Y F0 F']; clear_lift_subst.

    eapply steps_trans.
    apply steps_beta.
    cbn -[lam_Y F0 F']; clear_lift_subst.

    admit.
  - destruct xs.

(λ, λ, var 0
         ⋅ (F0 (var 2)
            ⋅ ((lam_Y ⋅ F') ⋅ (λ, C ⋅ (λ, var 2 ⋅ (var 1 ⋅ var 0))))))


    eapply steps_trans.
    apply steps_beta.
    cbn -[lam_Y F0 F']; clear_lift_subst.

    eapply steps_trans.
    apply steps_beta.
    cbn -[lam_Y F0 F']; clear_lift_subst.


    cbn.
    eexists;split;[|apply steps_refl].
    apply steps_app_left.
    apply steps_beta.
  unfold F_spec.
Admitted.


(* Lemma F_spec_proof C x xs:
  closed0 C -> 
  F_spec C x xs.
Proof.
  unfold F_spec.
Admitted. *)
