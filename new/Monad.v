(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

(* Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B := *)
(*   match a with *)
(*     | Some x => f x *)
(*     | None => None *)
(*   end. *)

Inductive result (A: Set) : Set :=
  | Unknown : result A
  | Ok (a: A) : result A.
Implicit Arguments Unknown [A]. 
Implicit Arguments Ok [A]. 

(* Arguments Unknown {A}. *)
(* Arguments Ok {A} _.  *)

Notation "'do' x <- A ; B" :=
  (match A with
     | Some y => (fun x => B) y
     | None => None end)
  (at level 200, x ident).

Notation "'do' x <-- A ; B" := 
  (match A with 
     | Some y => (fun x => B) y 
     | None => Unknown 
   end)
  (at level 200, x ident).

Notation "'do' x <== A ; B" := 
  (match A with 
     | Unknown => Unknown
     | Ok y => (fun x => B) y 
   end)
  (at level 200, x ident).

Notation "'do' '[' x1 ',' x2 ']' <- o ; f" :=
  (match o with Some (y1, y2) => (fun x1 x2 => f) y1 y2 | None => None end)
  (at level 200).

Notation "'do' '[' x1 ',' x2 ']' <-- A ; B" := 
  (match A with 
     | Some (y1, y2) => (fun x1 x2 => B) y1 y2
     | None => Unknown end)
  (at level 200, x ident).

Notation "'do' '[' x1 ',' x2 ']' <== A ; B" := 
  (match A with 
     | Unknown => Unknown
     | Ok (y1, y2) => (fun x1 x2 => B) y1 y2 
   end)
  (at level 200, x ident).

Notation "'ret' x" := (Ok x) (at level 200, only parsing).

Notation "'check' b ; f" :=
  (match b with false => None | true => f end)
  (at level 200).

Notation "'test' b ; f" :=
  (match b with false => Unknown | true => f end)
  (at level 200).
