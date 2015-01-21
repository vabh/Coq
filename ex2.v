Require Import Bool Arith List.

Variables P Q R : Prop.

(* 5. Write the script that proves the following formula
   (P -> (P /\ Q) -> R) -> P /\ (Q /\ P) -> R. *)

Lemma ex5 :
   (P -> (P /\ Q) -> R) -> P /\ (Q /\ P) -> R.
Proof.
intros r_if_pq_if_p.
intros pqp.
  destruct pqp as [p qp].
  apply r_if_pq_if_p.
  exact p.
  split.
  exact p.
apply qp.

Qed.
  
(* 7. Write the script that proves the following formula
     (P /\ Q) \/ R -> P \/ R *)

Lemma ex6 :
  (P /\ Q) \/ R -> P \/ R.
Proof.
intros p_a_q_o_r.
destruct p_a_q_o_r as [ pq | r].

destruct pq as [ p q].

left.
exact p.
right.
exact r.

Qed.

(* 7. Write the script that proves the following formula
   ((P -> Q \/ P) -> R) -> R \/ Q  *)

Lemma ex7 :
  ((P -> Q \/ P) -> R) -> R \/ Q.
Proof.

intros qp_if_p.
left.
apply qp_if_p.
intros qop_if_p.
right.
exact qop_if_p.
Qed.

(*
8. P \/ R -> (P -> Q) -> ~ Q -> R
*)
Lemma ex8 :
  P \/ R -> (P -> Q) -> ~ Q -> R.
Proof.
  intros pr.
  intros q_if_p.
  intros nq.
  destruct pr as [p | r].
  case nq.
  apply q_if_p.
  exact p.
  exact r.
Qed.

(*
9. P \/ ~Q -> ~P -> (Q -> R) \/ P
*)

Lemma ex9 :
  P \/ ~Q -> ~P -> (Q -> R) \/ P.
Proof.
intros p_o_nq.
intros np.
destruct p_o_nq as [p | nq].
right.
exact p.
left.
intros q.
case nq.
exact q.
Qed.