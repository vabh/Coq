Require Import ZArith Bool List Arith Psatz.
Open Scope Z_scope.

Lemma proof_ring x y z:
  x * (x + y) + (z + 2) ^ 2 = 
  x ^ 2 + z ^ 2 + 4 * z + x * y + 4.
Proof.
ring.
Qed.
Close Scope Z_scope.

Fixpoint mod2 (n : nat) :=
  match n with S (S n) => mod2 n |  _ => n end.

Lemma mod2_lt :
 forall n, mod2 n < 2. 
Proof.
assert (main: forall n, mod2 n < 2 /\ mod2 (S n) < 2).
induction n.
simpl.
omega.
split.
destruct IHn as [_ it].
exact it.
simpl.
destruct IHn as [it _];
exact it.
intros n.
destruct (main n) as [it _].
exact it.
Qed.

Lemma le_ind :
  forall P : nat -> Prop,
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n: nat, P n.

intros P ind_lt n.
assert ( main : forall m, m <= n -> P m).
induction n.
  intros m mle0.
  apply ind_lt.
  intros p pltm.
  omega.
intros m mleSn.
assert (disj : m <= n \/ m = S n).
apply NPeano.Nat.le_succ_r.
  exact mleSn.
  destruct disj as [mlen | misSn].
    apply IHn.
    exact mlen.
  rewrite misSn.
  apply ind_lt.
  intros p pltSn.
  apply IHn.
  omega.
apply main.
reflexivity.
Qed.

Lemma mod2_lt_2:
  forall n, mod2 n < 2.
Proof.
induction n as  [p IHp] using le_ind.
destruct p as [ |q].
  simpl.
  omega.
destruct q as [|q'].
 simpl.
  omega.
simpl.
apply IHp.
omega.
Qed.

Fixpoint mod2 (n : nat) :=
  match n with S (S n) => mod2 n |  _ => n end.

Fixpoint div2 (n : nat) :=
      match n with S (S p) => S (div2 p) | _ => 0 end.

Lemma mod2_div2_eq n : n = mod2 n + 2 * div2 n.
Proof.

assert ( H : n = mod2 n + 2 * div2 n /\ S n = mod2 (S n) + 2 * div2 (S n)).
induction n.
simpl.
omega.

destruct IHn as [L R].
split.
apply R.
simpl mod2.
simpl div2.

replace (mod2 n + 2 * S (div2 n)) with (S (S ( mod2 n + 2 * div2 n ))).
rewrite <- L.
reflexivity.
ring.

tauto.

Qed.

