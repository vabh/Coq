Require Import Bool Arith List.
  
(* 6. Write the script that proves the following formula
   forall (P Q : nat -> Prop),
   forall (x y : nat), (forall z, P z -> Q z) -> x = y -> P x ->
     P x /\ Q y. *)

Lemma ex6 :
  forall (P Q : nat -> Prop),
   forall (x y : nat), (forall z, P z -> Q z) -> x = y -> P x -> P x /\ Q y.
Proof.
intros P Q.
intros x y.
intros z.

intros x_eq_y.
intros px.

split.

exact px.

rewrite  <- x_eq_y.

apply z.
exact px.

Qed.


(* 8. Write the script that proves the following formula
   forall P : nat -> Prop, (forall x, P x) ->
     exists y:nat, P y /\ y = 0 *)

Lemma ex8 :
  forall P : nat -> Prop, (forall x, P x) -> exists y:nat, P y /\ y = 0.
Proof.
intros P.
intros Px.

exists 0.

split.

apply Px.
reflexivity.
Qed.

(* 1. Write a predicate multiple_of type nat -> nat -> Prop, 
   so that multiple a b expresses that a is a multiple of b
  (in other words, there exists a number k such that a = k * b). *)

Definition multiple_of (a b : nat) : Prop := 
 exists k,  a = k * b.

(* 2. Write a formula using natural numbers that expresses that when
   n is even (a multiple of 2) then n * n is even. *)

Definition even (n : nat) :=
  multiple_of n 2.

Check forall n, even n -> even (n * n).

(* 3. Write a formula using natural numbers that expresses that when
   a number n is a multiple of some k, then n * n is a multiple of k
   (you don't have to prove it yet). *)

Definition mul_sq (n k : nat) :=
 forall (n k : nat), (multiple_of n k) -> ( multiple_of (n * n) k).

Check forall n k, mul_sq n k.

(* 4. Write a predicate odd of type nat -> Prop that characterize
   odd numbers like 3, 5, 37.  Avoid ~ (even ..). *)

Definition odd (n : nat) : Prop :=
  even (n + 1).
  
(* 9. Search the lemma proving associativity of multiplication *)

SearchAbout ( _ * _ * _ = _ *(_ * _) ).

(* 10. Write the script that proves that when n is a multiple of k,
   then n * n is also a multiple of k. *)

Lemma ex10 :
  forall (n k : nat), (multiple_of n k) -> ( multiple_of (n * n) k).
Proof.
unfold multiple_of.
intros n k.
intros k0.


(* 11. Search the lemmas proving the following properties:
   - distributivity of plus and mult
   - associativity of plus
   - 1 is a neutral elelemt for multiplication *)

SearchAbout ( 1 * _ = _ ).

(* 12. Show that the sum of two even numbers is even *)

Lemma ex12 : ...

(* 13. Write the script that proves that when n is odd,
   then n * n is also odd. *)

Lemma ex13 : ...
