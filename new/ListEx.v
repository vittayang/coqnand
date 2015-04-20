(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import Lists.List.
Require Export Bnat.

(* written by zhanghui *)
Fixpoint list_append {A: Set} (l: list A) (a: A) : list A :=
  match l with
    | nil => cons a nil
    | cons x l' => cons x (list_append l' a)
  end.

Fixpoint list_none {A: Set} (n: nat) : list (option A) :=
  match n with 
    | O => nil
    | S n => cons None (list_none n)
  end.

(* written by zhanghui *)
Fixpoint list_repeat {A: Set} (n : nat) (elem : A) : list A :=
  match n with
    | O => nil
    | S n' => cons elem (list_repeat n' elem)
  end.

Fixpoint list_get {A: Set} (l: list A) (i: nat) : option A :=
  match i, l with 
    | O, cons a l' => Some a
    | S i', cons a l' => list_get l' i'
    | _, _ => None
  end.

Fixpoint list_set {A: Set} (l: list A) (i: nat) (a: A): option (list A) :=
  match i, l with
    | O, cons a' l' => Some (cons a l')
    | S i', cons a' l' => 
      match list_set l' i' a with
        | None => None 
        | Some l'' => Some (cons a' l'')
      end
    | _, _ => None
  end.

Fixpoint list_find_aux {A:Set} (beq_a: A->A->bool) (l:list A) (a: A) (i: nat) : option nat :=
  match l with 
    | nil => None
    | cons a' l' => match beq_a a a' with
                      | true => Some i
                      | false => list_find_aux beq_a l' a (S i) 
                    end
  end.

Definition list_find {A:Set} (beq_a: A->A->bool) (l:list A) (a: A) : option nat :=
  list_find_aux beq_a l a O.

Fixpoint list_find_rev_aux {A:Set} (beq_a: A->A->bool) (l:list A) (a: A) (i: nat) : option nat :=
  match l with 
    | nil => None
    | cons a' l' => match list_find_rev_aux beq_a l' a (S i) with 
                      | Some i' => Some i'
                      | None => match beq_a a a' with
                                  | true => Some i
                                  | false => None 
                                end
                    end
  end.

Definition list_find_rev {A:Set} (beq_a: A->A->bool) (l:list A) (a: A): option nat :=
  list_find_rev_aux beq_a l a O.

(* Eval compute in (list_find beq_nat (0::1::99::3::4::5::99::7::nil) 99). *)
(* Eval compute in (list_find_rev beq_nat (0::1::99::3::4::5::99::7::nil) 99). *)

Fixpoint list_find_min {A: Set} (l: list A) (pred: A -> A -> option bool) : option A :=
  match l with
    | nil => None
    | cons x nil => Some x
    | cons x l' =>
      match list_find_min l' pred with
        | None => None
        | Some m =>
          match pred x m with
            | None => None
            | Some b =>
              match b with
                | true => Some x
                | false => Some m
              end
          end
      end
  end. 

Definition blt_nat_opt (n1 n2 : nat) : option bool :=
  Some (ble_nat n1 n2).

Definition test_list_1 := (11::22::33::44::55::88::66::77::88::9::nil).
Example list_find_min_test1 : list_find_min test_list_1 blt_nat_opt = Some 9.
Proof. reflexivity. Qed.

Definition list_find_min_index {A: Set} (l: list A) (pred_min: A -> A -> option bool)
           (pred_eq: A -> A -> bool): option nat :=
  match list_find_min l pred_min with
    | None => None
    | Some a =>
      list_find pred_eq l a
  end.

Example list_find_min_index_test1 : list_find_min_index test_list_1 blt_nat_opt beq_nat = Some 9.
Proof. reflexivity. Qed.

Fixpoint list_in {A: Set} (beq_a: A->A->bool) (l: list A) (a : A) : bool :=
  match l with 
    | nil => false
    | cons a' l' => match beq_a a a' with
                      | true => true
                      | false => list_in beq_a l' a 
                    end
  end.

Lemma list_set_length_preserv: 
  forall {A: Set} (l:list A) i l' (a: A),
    blt_nat i (length l) = true
    -> list_set l i a = Some l'
    -> length l' = length l.
Proof.
  intro A.
  induction l; destruct i; simpl; intros.
    discriminate.
    discriminate.
  destruct l' as [ | a' l'].
  discriminate.
  inversion H0.
  subst a0 l'.
  simpl; trivial.
  destruct l' as [ | a' l'].
  destruct (list_set l i a0).
    inversion H0.
    discriminate.
  simpl.
  remember (list_set l i a0) as x.
  destruct x.
  inversion H0; subst.
  assert (length l' = length l).
    eapply IHl; eauto.
  auto with arith.
  discriminate.
Qed.                                    
