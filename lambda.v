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

Notation "e1 ≡ e2" := (equivalent e1 e2) (at level 0).




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
  λ, var 0 ⋅ (λ, C ⋅ (var 1 ⋅ lam_K ⋅ lam_S)).
Definition F1 C F :=
  F ⋅ (λ, F ⋅ (λ, C ⋅ (var 1 ⋅ var 0))).
