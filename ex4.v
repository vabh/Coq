Require Import Bool Arith List.

Fixpoint lo (n : nat) :=
match n with
 | 0 => nil
 | S p => 2 * p + 1:: lo p
 end.

Compute lo 5.
Compute length (lo 5).

Lemma len_proof:
  forall n, length (lo n) = n.
Proof.
induction n as [ | n' IHn'].
reflexivity.
simpl.
rewrite IHn'.
reflexivity.
Qed.

(* Define a function sl that takes a list of natural numbers as input and
returns the sum of all the elements in the list. *)

Fixpoint sl (l : list nat) :=
match l with
  | nil => 0
  | x::xs => x + (sl xs)
  end.

Compute sl (lo 6).

Lemma sl_lo_proof:
  forall n, sl (lo n) = n * n.
Proof.
induction n as [ | n IHn'].
reflexivity.
simpl.
rewrite IHn'.
rewrite plus_0_r.

SearchAbout ( _ * S _).
rewrite mult_succ_r.
rewrite (plus_comm (n * n)).

SearchAbout (_ + 1).
rewrite NPeano.Nat.add_1_r.
SearchAbout ( S _ + _).
rewrite plus_Sn_m.
rewrite plus_assoc.
reflexivity.
(*ring.*)
Qed.

Fixpoint lo' (n m : nat) : list nat :=
match n with
| 0 => nil
| S p => m :: lo' p (m + 2)
end.

Definition lo2 n := lo' n 1.

Lemma sl_lo :
  forall n m, sl (lo' n (m+1)) = n *m + n* n.
Proof.
induction n as  [ | n IHn].
intros m.
simpl.
reflexivity.
intros m.
simpl.
replace (m + 1 + 2) with ((m + 2) + 1).
  rewrite IHn.
  ring.
ring.
Qed.


Fixpoint add x y := 
  match x with 
    |0 => y 
    | S p => add p (S y) 
  end.

Lemma add1:
  forall x y, add x (S y) = S (add x y).
Proof.
induction x as [ | y Ihy].
reflexivity.
simpl.
intros y0.
rewrite Ihy.
reflexivity.
Qed.

Lemma add2:
  forall x, add x 0 = x.
Proof.
induction x as [ | x IHx].
reflexivity.
simpl.

rewrite add1.
rewrite IHx.
reflexivity.

Qed.

Lemma ad3:
  forall x y, add (S x) y = S (add x y).
Proof.

induction x as [ | x Ihx].

reflexivity.
simpl.
intros y.
rewrite add1.
reflexivity.
Qed.

Lemma ad4:
forall x y z, add x (add y z) = add (add x y) z.
Proof.

induction x as [ | IHyz].
intros y z.
reflexivity.
simpl.
intros y z.

rewrite add1.
rewrite add1.
rewrite ad3.
rewrite IHIHyz.
reflexivity.

Qed.

Lemma ad5:
  forall x y, add x y = x + y.
Proof.

induction x as [ | x IHx].
simpl.
reflexivity.
intros y.
simpl.
rewrite add1.
rewrite IHx.
reflexivity.
Qed.








