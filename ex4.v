Fixpoint lo (n : nat)
match n with
 | 0 => nil
 | S p => 2 * p + 1::lo p
 end.