Load lambda.

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


Definition equivalent e1 e2 := 
  exists e3, steps e1 e3 /\ steps e2 e3.

Notation "e1 ≡ e2" := (equivalent e1 e2) (at level 70).
