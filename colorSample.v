(* Sample of a termination proof certified in CoLoR extracted from
 * 2001-color-coq-library.pdf
 *
 * Note: paper only contains snippets from the proof, so some things will
 *   be manually added by me
 *)

Require Export CoLoR.Term.WithArity.ASignature . 
Require Import CoLoR.Term.WithArity.ATerm .
Require Import CoLoR.Term.WithArity.ATrs .
(* Note: Having below caused @Fun later in file to not type check.
         The identical names used caused various problems, and the below is
         unnecessary for this file.
 *)
(* Require Import CoLoR.Term.Varyadic.VTerm . *)
Require Import CoLoR.Util.List.ListUtil .  (* for list_ok at least *)
Require Import CoLoR.Util.Nat.NatUtil .  (* for check_gt at least *)
Require Import CoLoR.Util.Vector.VecUtil .  (* for Vnil at least *)

(* Representation of the TRS:  compute the quotient of two nats in unary
  minus(x, zero) -> x
  minus(succ(x), succ(y)) -> minus(x,y)
  quot(zero, succ(y)) -> zero
  quot(succ(x), succ(y)) -> succ(quot(minus(x,y), succ(y))

 Above system is not "simply terminating" (if y=succ(x), the RHS of 4th rule
can in embedded in the corresponding LHS.

 Can use "argument filtering" (which I don't understand yet) to create below TRS
and then prove termination with a "simplification ordering"
  minus(zero) -> zero
  minus(succ(x)) -> succ(minus(x))
  quot(zero, succ(y)) -> zero
  quot(succ(x), succ(y)) -> succ(quot(minus(x), succ(y))

Note: The two TRSs do NOT compute the same results, so i'm not sure why the
argument filtering technique is valid.
*)

Open Scope nat_scope .

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

Lemma beq_symb_ok : forall f g : M.symb, beq_symb f g = true <-> f = g .
  Proof. beq_symb_ok. Qed. 
Definition ar (s : M.symb) : nat :=
 match s with
   M.minus => 1
 | M.quot => 2
 | M.succ => 1
 | M.zero => 0
 end .
Check mkSignature .
Check ASignature.mkSignature .
(* signature 1 *)
Module S1.
  Definition Sig := ASignature.mkSignature ar beq_symb_ok .
 (* Definition Sig := mkSignature ar beq_symb_ok . *)
  Definition Fs : list Sig := M.zero::M.succ::M.quot::M.minus::nil .
  Lemma Fs_ok : forall f : Sig, In f Fs. Proof.  list_ok. Qed.
  Definition some_symbol : Sig := M.minus .
  (* Not sure if / why arify_some_symbol is necessary *)
  Lemma arity_some_symbol : arity some_symbol > 0 . Proof . check_gt. Qed.
End S1.

(* rewrite rules *)
Definition E : ATrs.rules S1.Sig := nil .  (* no equations *)

Check ATrs.mkRule .
Check @ATrs.mkRule .
Check @ATerm.term .

Check Fun .

(* Definition Signature := ASignature.Signature . *)


(*  
 Check Fun S1.Sig . -- Error: The term "S1.Sig" has type "ASignature.Signature"
                        while it is expected to have type "symbol ?171". 
 Check @Fun S1.Sig . -- Error: The term "S1.Sig" has type "ASignature.Signature"
                        while it is expected to have type "Signature". *)
Definition R : ATrs.rules S1.Sig := @ATrs.mkRule S1.Sig
  (@Fun S1.Sig M.minus (Vcons (@Fun S1.Sig M.zero Vnil) Vnil))
    (@Fun S1.Sig M.zero Vnil)
(* TODO: encode other 3 rules *)
  :: nil .

Definition rel := ATrs.red_mod E R .


