Require Import Bool Arith List.

(* 1. Define a recursive function that takes as input a list of numbers
   and returns the product of these numbers, *)

Fixpoint prodlist (l : list nat) :=
  match l with
  | nil => 1
  | x :: xs => x * prodlist xs
  end.

Compute prodlist nil.
Compute prodlist (0 :: 3 :: 7 :: nil).
Compute prodlist (3 :: 4 :: 2 :: nil).

(* 2. Define a recursive function that takes a list of numbers and
   returns true if and only if this list contains the number 0.
   Hint: pattern match on both the list and the elements of the list. *)

Fixpoint has_a_0 (l : list nat) :=
  match l with
  | nil => false
  | x :: xs => 
    match x with
    | 0 => true
    | S _ => has_a_0 xs
    end
  end.

Compute has_a_0 (2 :: 3 :: 0 :: 7 :: nil).
Compute has_a_0 nil.
Compute has_a_0 (3 :: 5 :: nil).

(* 3. Define a recursive function that takes as input two numbers and
   returns true if and only if these two numbers are the same natural
   number (such a function already exists in the Coq libraries
   (function beq_nat, but how would you define such a function), using
   only pattern-matching and recursion. *)

Fixpoint beq (a b : nat) :=
  match a, b with
  | 0, 0 => true
  | 0, S _ => false
  | S _, 0 => false
  | S a1, S b1 => beq a1 b1
end.

Compute beq 4 5.
Compute beq 7 7.

(* 4. Define a recursive function that takes a number n and a number
   a as input and returns a list of numbers containing n elements
   that are all a. *)

Fixpoint mklist (n a : nat) (l: list nat) :=
  match n with
  | 0 => l
  | S n1 => mklist n1 a (a::l)
  end.

Compute mklist 5 2 nil.
(*
Fixpoint mklist (n a : nat) :=
  match n with
  | 0 => nil
  | S n1 => 
              cons a (mklist n1 a)
*)

(* 5. Define a function that takes a number n and a number a and returns
   the list of n elements a ::a + 1:: Â· Â· Â· ::a + n:: nil. *)

Fixpoint mklist1 (n a : nat) :=
  match n with
  | 0 => nil
  | S n1 => cons (a) (mklist1 n1 (a + 1))
  end.

Compute mklist1 5 2.

(* 6. Define a function that takes as input a natural number and returns
   an element of option nat containing the predecessor if it exists or
   None if the input is 0. *)
Fixpoint pred (n : nat) :=
  match n with
  | 0 => None
  | S x => Some x
end.

Compute pred 0.
Compute pred 6.

(* 7. Define a recursive function that takes as input a list of numbers
   and returns the length of this list. *)

Fixpoint length (l : list nat) (n : nat) :=
  match l with
  | nil => n
  | x :: xs => length xs (n + 1)
  end.

Compute length nil 0.
Compute length (2 :: 3 :: nil) 0.
Compute length (2 :: 3 :: 4 :: 4 :: nil) 0.

(* 8. Can you write a recursive function values that takes as input a
   function f of type nat -> nat, an initial value a of type nat
   and a count n of type nat and produces the list
   a :: f a :: f (f a) :: ... *)

Fixpoint fold (f : nat -> nat) (a : nat) (n : nat) :=
  match n with
  | 0 => nil
  | S n1 => cons (a) (fold f (f a) n1)
  end.

Compute fold (fun x : nat => x) 0 5.
Compute fold (fun x : nat => x + 1) 3 4.
Compute fold S 3 4.

(* 9. To every natural number, we can associate the list of its digits
   from right to left. For instance, 239 should be associated to the list
   9::3::2::nil. We also consider that 0 can be mapped to nil. If l is
   such a list, we can consider the successor of a list of digits.
   For instance, the successor of 9::3::2::nil is 0::4::2.
   Define the algorithm on lists of natural numbers that computes the
   successor of that list. *)

Fixpoint lsucc (l: list nat) :=
  match l with
  | nil => 1::nil
  | x :: xs  =>
      match x with
      | 9 => 0 :: lsucc xs
      | _ => (x + 1) :: xs
      end
  end.

Compute lsucc (3 :: 9 :: 1 :: nil).
Compute lsucc (9 :: 3 :: 1 :: nil).
Compute lsucc (9 :: 9 :: 1 :: nil).
Compute lsucc nil.
Compute lsucc (9 :: nil).

Check lsucc.
(* 10. Assuming that lsuc is the function defined at the previous
   exercise, define the function nat_digits that maps every natural
   number to the corresponding list of digits (naive solutions are
   welcome, as long as they run). *)

Fixpoint nat_digits_aux (n i: nat) (li : list nat) :=
  match i with
  | 0 => li
  | S i1 => nat_digits_aux n i1 (lsucc li)
  end.

Definition nat_digits (n : nat) :=
  nat_digits_aux n n nil.

Compute nat_digits 4532.

(* 11. In the same context as the previous two exercises, define a function
   value that maps every list of digits to the natural number it
   represents. Thus, value (9::3::2::nil) should compute to 239. *)

Fixpoint value (l : list nat) :=
  match l with 
  | nil => 0
  | x::xs => x + 10 * value(xs)
end.
Compute value (0 :: 2 :: 3 :: 4 :: nil).

(* 12. In the same context as the previous exercises, define a function
   licit that tells whether a list of integers corresponds to the digits
   of natural number: no digit should be larger than 9. For instance,
   licit (9::3::2::0::nil) should compute to true and licit (239::nil)
   should compute to false. *)

Fixpoint licit (l : list nat) (b : bool):=
  match l, b with
  | nil, true => true
  | _, false => false
  | x::xs, true => licit xs (leb x 10)
end.

Compute licit (9 :: 3 :: 2 :: 0 :: 34 :: nil) true.
Compute licit (2 :: 3 :: 9 :: nil) true.

(* 13. In the same context as the previous exercises, define functions
   to add two lists of digits so that the result represents the sum of
   the numbers represented by the lists of digits. In other words
   addl (7::2::nil) (5::3::nil) should return 2::6::nil
   (Hint: you should implement the algorithm you learned in elementary
   school for adding numbers). *)

Fixpoint addl (l1 l2 l: list nat) (c : nat) :=
  match l1, l2 with
  | nil, nil => l
  | nil, x::xs => (x +)
  | _, nil => l1::l
  | x1::xs1, x2::xs2 => 
    match leb (x1 + x2) 10 with
    | true => addl xs1 xs2 0
    | false => addl xs1 xs2 1
  end
end.

Compute addl (7 :: 2 :: nil) (5 :: 3 :: nil) nil 0.

(* 14. In the same context as the previous exercises, define a function
   for multiplying a list by a small natural number (by successive
   additions) and then a function mull for multiplying two lists of
   digits. *)

... mulln ...

Compute mulln 3 (2 :: 1 :: nil).

... mull ...

Compute 14 * 13.
Compute mull (4 :: 1 :: nil) (3 :: 1 :: nil).
Compute 437 * 25.
Compute mull (7 :: 3 :: 4 :: nil) (5 :: 2 :: nil).
Compute 97 * 75.
Compute mull (7 :: 9 :: nil) (5 :: 7 :: nil).
