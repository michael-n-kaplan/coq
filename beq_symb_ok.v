Module M .
Inductive symb : Type :=
  minus : symb
| zero : symb
| succ : symb
| quot : symb
.
End M.

Definition beq_symb (f g : M.symb) : bool :=
 match f, g with
  M.minus, M.minus => true
| M.zero, M.zero => true
| M.succ, M.succ => true
| M.quot, M.quot => true
| _, _ => false
 end .

(* Tactic to decide beq_symb_ok from CoLoR VSignature 
Ltac beq_symb_ok := intros f g; split;
  [destruct f; destruct g; simpl; intro; (discr || refl)
    | intro; subst g; destruct f; refl].
 *)

Lemma beq_symb_ok : forall f g : M.symb, beq_symb f g = true <-> f = g .
Proof .
  intros f g . split . (* break into 
                            beq_symb f g = true -> f = g  and
                            f = g -> beq_symb f g = true *)
  (* for first case, we can simply, though tediously, do a case analysis over
     all possible cominbations of f and g.  Since there are 4 symbols, this will
     generate 16 total subcases. *)
  destruct f .
    destruct g .
      simpl . intro . reflexivity .
      simpl . intro . discriminate .
      simpl . intro . discriminate .
      simpl . intro . discriminate .
    destruct g .
      simpl . intro . discriminate .
      simpl . intro . reflexivity .
      simpl . intro . discriminate .
      simpl . intro . discriminate .
Restart .
  intros f g ; split .
  (* All of the above cases are identical, except for refl / discr, so we'll 
     make use of the fact that the semi-colon operator applies what comes after
     it to EACH generated subcase to collapse the above (incomplete) case 
     analysis into one line *)
  destruct f ; destruct g ; simpl ; intro ; (discriminate || reflexivity ) .
  (* We now start the other half of the original proof,
     f = g -> beq_symb f g = true *)
  intro .
    (* given the hypothesis 'f = g', we can replace g with f in the rest of the
       proof using the substitute tactic *)
  subst g .
  (* Now we again do a case analysis over f, but this time only four cases
     are generated since we have "f f" instead of "f g" as arguments.
     We'll still use ; to apply reflexivity to all generated subgoals
   *)
  destruct f ; reflexivity .
Qed .
