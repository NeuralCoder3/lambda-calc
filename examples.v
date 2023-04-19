
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


Example omega_step:
  step Omega Omega.
Proof.
  eapply step_eq.
  (* unfold Omega, omega. *)
  apply step_beta.
  now cbn.
Qed.
