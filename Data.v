(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import String.
Require Import ListEx.

(* A temporary definition of chars. *)
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
| c_6 : char
| c_7 : char
| c_info : string -> char
| c_ff : char
.

Notation "'0xA'" := (c_a).
Notation "'0xNN'" := (c_null).
Notation "'0xFF'" := (c_ff).
Notation "<< s >>" := (c_info s).

Definition byte := char.

Definition data := list byte.

Definition zero_data (sz: nat) : data :=
  list_repeat_list sz c_null.

Definition ff_data (sz: nat) : data :=
  list_repeat_list sz c_ff.
