(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import String.
Require Import List.
Require Import ListEx.

(* A temporary definition of chars. *)
(* TODO: we will use the Intergers.v from Compcert Project *)
Inductive char : Type :=
| c_null : char
| c_a : char
| c_b : char 
| c_c : char
| c_d : char
| c_e : char
| c_f : char
| c_g : char
| c_h : char
| c_0 : char
| c_1 : char
| c_2 : char
| c_3 : char
| c_4 : char
| c_5 : char
| c_info : string -> char
.

Notation "'0xA'" := (c_a).
Notation "'0xFF'" := (c_null).
Notation "<< s >>" := (c_info s).

Definition byte := char.

Definition data := list byte.

Definition zero_data (sz: nat) : data :=
  list_repeat sz c_null.

(* TODO: next version
Record chunk (sz: nat) : Set :=
  mkchunk {
    chunk_data: list byte;
    chunk_size: length chunk_data = sz
  }.

Notation "{{ s }}" := (mkchunk _ s _) (at level 200).

*)
