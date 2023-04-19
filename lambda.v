(*

1. Lambda:
2. Semantics:
3. Properties:
4. Interpreter:

*)

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

Inductive SK : Type :=
  | S : SK
  | K : SK
  | SK_app : SK -> SK -> SK.

Notation "λ, e" := (lam e) (at level 60, e at level 99).
Notation "e1 ⋅ e2" := (app e1 e2) (at level 50).

(* substitution *)

(* lift +n if >=k *)
Fixpoint lift (e : lambda) (k : nat) (n : nat) : lambda :=
  match e with
  | var n' => if Nat.ltb n' k then var n' else var (n'+n)
  | app e1 e2 => app (lift e1 k n) (lift e2 k n)
  | lam e => lam (lift e (1+k) n)
  end.
Notation lift0 n e := (lift e 0 n).


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
    if Nat.eqb n k then lift0 k x (* lift e over all inner binders *)
    else if Nat.ltb n k then var n (* keep inner vars the same *)
    else var (n-1) (* remove binder k => cope with open terms (redex under binder) *)
  | app e1 e2 => app (subst x k e1) (subst x k e2)
  | lam e => lam (subst x (1+k) e)
  end.
Notation subst0 x := (subst x 0).
Notation "e [ k <- e' ]" := (subst e' k e) (at level 0, e' at level 99).

(* could be boolean but prop is easier *)
Fixpoint closed k e :=
  match e with
  | var n => n < k
  | app e1 e2 => (closed k e1) /\ (closed k e2)
  | lam e => closed (1+k) e
  end.
Notation closed0 e := (closed 0 e).

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
