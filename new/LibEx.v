(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)


Lemma eq_sym : forall {A: Type} (n m : A), n = m -> m = n.
Proof.
Admitted.
Implicit Arguments eq_sym [A n m].

(* deprecated, use "neq_sym" instead *)
Lemma neq_refl : forall n m : nat, n <> m -> m <> n.
Proof.
Admitted.
Implicit Arguments neq_refl [n m].

Lemma neq_sym : forall {A: Type} (n m : A), n <> m -> m <> n.
Proof.
Admitted.
Implicit Arguments neq_sym [n m].

