Inductive even : nat -> Prop :=
  base : (even 0)
| step : forall (n : nat), (even n) -> (even (S (S n))) .

(* See Chlipala, CPDT Predicates chapter (definition of even) for example
 * similar to below.  Possibly identical.
 *)
Lemma pred_even : forall (n:nat), (even n) -> (even (pred (pred n))) .
(* instead of doing induction over n, do induction over the structure of the
 * proof.  ie, do induction over even.
 *   in coq, we can use number to indicate anonymous terms.  In the below
 * case, induction 1 means to induct over the first even predicate.
 *)
induction 1 .
  simpl . constructor .
  simpl . exact H . (* or assumption . *)
Qed .
(* First failed attempt
intros. unfold pred.
Abort .
*)
(* 2nd failed attempt.  inducting over n leads nowhere good
induction n. simpl . intro ; exact H .
Abort .
*)
(*  Want to substitute n (nat) for S n ... is that allowed ? *)
