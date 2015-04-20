(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import List.
Require Import ListEx.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import Bast0.
Require Import FTLProp.

Section INV.

  Variable bit : block_info_table.
  Variable bmt : block_mapping_table.
  Variable fbq : list block_no.

(* ## I1: every valid pbn has an item in the BIT table, and vice versa.  *)
Definition I_pbn_bit_valid := forall (pbn : block_no), 
                   valid_block_no pbn
                   <-> exists bi, bit_get bit pbn = Some bi.

(* ## I2: every pbn in BMT is valid 
 *)
Definition I_pbn_bmt_valid := forall (lbn : block_no), 
                   forall (pbn: block_no),
                     pbn_in_bmt_lbn bmt lbn pbn
                     -> valid_block_no pbn.

(* ## I3: every pbn in freebq is valid.
 *)

Definition I_pbn_fbq_valid := forall (pbn: block_no),
                    fbq_in fbq pbn = true
                    -> valid_block_no pbn. 

(* ## I4: every pbn in freebq is of "INVALID" or "ERASED" state.
*)

Definition I_pbn_fbq_state := forall (pbn: block_no) bi,
                                fbq_in fbq pbn = true
                                -> bit_get bit pbn = Some bi 
                                -> bi_state bi = bs_invalid \/ bi_state bi = bs_erased.

(* ## I5: every pbn in the block_mapping_table is of "bs_log" state or "bs_data". 
 *)

(*TODO: The following definition is easier to understand 

Definition I_pbn_bmt_used :=
  forall (pbn : block_no) bi,
    bit_get bit pbn = Some bi
    -> (forall lbn, pbn_in_bmt_data bmt lbn pbn -> bi_state bi = bs_data lbn)
       /\ (forall lbn, pbn_in_bmt_log bmt lbn pbn -> exists pmt, bi_state bi = bs_log lbn pmt).
*)
Definition I_pbn_bmt_used :=
  forall lbn (pbn : block_no) bi,
    bit_get bit pbn = Some bi
    -> (pbn_in_bmt_data bmt lbn pbn -> bi_state bi = bs_data lbn)
       /\ (pbn_in_bmt_log bmt lbn pbn -> exists pmt, bi_state bi = bs_log lbn pmt).

(* ## I6: for every valid pbn, it is either in freebq, or in BMT *)

Definition I_pbn_habitation := (* pbn_bmt_freebq_dec *)
  forall pbn,
    valid_block_no pbn
    -> ((exists lbn, pbn_in_bmt_lbn bmt lbn pbn) /\ fbq_in fbq pbn = false ) 
       \/ ((forall lbn, ~ pbn_in_bmt_lbn bmt lbn pbn) /\ fbq_in fbq pbn = true).

 
(* ## I7: every two pbns in BMT are different *)
  
Definition I_pbn_bmt_distinguishable := 
  forall lbn lbn' pbn pbn',
    lbn <> lbn'
    -> pbn_in_bmt_lbn bmt lbn pbn 
    -> pbn_in_bmt_lbn bmt lbn' pbn'
    -> pbn <> pbn'.

Definition I_pbn_bmt_distinguishable_2 := forall lbn pbn pbn',
                   bmt_get bmt lbn = Some (Some pbn, Some pbn')
                   -> pbn <> pbn'.
                   
(* ## I8: every two pbns in FREEBQ are different *)

Definition I_pbn_fbq_distinguishable:= forall i i' pbn pbn',
                     i <> i'
                     -> fbq_get fbq i = Some pbn
                     -> fbq_get fbq i' = Some pbn'
                     -> pbn <> pbn'.

(* Derivable !!! *)
(* ## I9: the number of blocks in freebq should be greater than GC_THRESHOLD, so as to 
          ensure the process of GC could be done.
 *)

(* Definition I_blocks_abundant := *)
(*   blt_nat MIN_FREE_BLOCKS (length fbq) = true. *)

(* Definition I_blocks_minimum := *)
(*     length fbq > GC_THRESHOLD. *)

(* Definition I_blocks_minimum_after_allocation := *)
(*     length fbq >= GC_THRESHOLD. *)

(* ## I9: every valid lbn is in the domain of BMT *)

Definition I_valid_lbn_has_entry_in_bmt : Prop :=
  forall lbn,
    valid_logical_block_no lbn
    <-> exists bme, bmt_get bmt lbn = Some bme.

(* TODO: I11 is admissible. It is removed *)
(* ## I11: the total number of blocks is a constant. *)
(*       This invariant doesn't have to hold, unless we prove block-leak-free. *)

(* TODO: If we add GC, this invariant should be removed. *)
  
(* Definition I_used_blocks_less_than_2_max_lbn : Prop := *)
(*   count_used_blocks bit <= 2 * MAX_LOGICAL_BLOCKS. *)

Variable c: chip.

(* $1: if a block is "INVALID" or "ERASED" in BIT, its hardware 
       part is in the state of "FREE".
 *)

Definition chip_bi_coherent (c: chip) (pbn: block_no) (bi: block_info) : Prop :=
  exists b, chip_get_block c pbn = Some b 
            /\ match (bi_state bi) with
                 | bs_erased => block_coherent_erased bi b
                 | bs_invalid => block_state b = bs_programmed
                 | bs_data _ => block_coherent_data bi b
                 | bs_log _ _ => block_coherent_log bi b
               end.

Definition J_bi_block_coherent (c: chip) (bit: block_info_table) := 
  forall pbn bi, 
    bit_get bit pbn = Some bi
    -> chip_bi_coherent c pbn bi.

(*
  Admissible invariant 
 *)

Definition I_pbn_data_in_bmt :=
  forall pbn bi lbn, 
    bit_get bit pbn = Some bi
    -> bi_state bi = bs_data lbn
    -> pbn_in_bmt_data bmt lbn pbn.

Definition I_pbn_log_in_bmt :=
  forall pbn bi lbn pmt, 
    bit_get bit pbn = Some bi
    -> bi_state bi = bs_log lbn pmt
    -> pbn_in_bmt_log bmt lbn pbn.

(* ## IA1: the total number of blocks is a constant. *)
(*       This invariant doesn't have to hold, unless we prove block-leak-free. *)

Definition I_bmt_fbq_distinguiable := 
  forall pbn pbn' lbn, 
    valid_block_no pbn
    -> valid_block_no pbn'
    -> pbn_in_bmt_data bmt lbn pbn \/ pbn_in_bmt_log bmt lbn pbn
    -> fbq_in fbq pbn' = true
    -> pbn <> pbn'.

End INV.
                   
(*

Lemma $1: 
   invariant is satisfied 
   -> merge_block _____ = res_okay _.

 *)

Definition F_Inv (f: FTL) : Prop :=
  let bit := ftl_bi_table f in
  let bmt := ftl_bm_table f in
  let fbq := ftl_free_blocks f in
    I_pbn_bit_valid bit         (* I1 *)
    /\ I_pbn_bmt_valid bmt      (* I2 *)
    /\ I_pbn_fbq_valid fbq   (* I3 *)
    /\ I_pbn_fbq_state bit fbq   (* I4 *)
    /\ I_pbn_bmt_used bit bmt       (* I5 *)
    /\ I_pbn_habitation bmt fbq     (* I6 *)
    /\ I_pbn_bmt_distinguishable bmt   (* I7_1 *)
    /\ I_pbn_bmt_distinguishable_2 bmt (* I7_2 *)
    /\ I_pbn_fbq_distinguishable fbq   (* I8 *)
    (* /\ I_blocks_abundant fbq            (* I9 *) *)
    /\ I_valid_lbn_has_entry_in_bmt bmt  (* I10 *).
    (* /\ I_used_blocks_less_than_2_max_lbn bit  (* I11 *). *)

Definition R_Inv (c: chip) (f: FTL) : Prop :=
  let bit := ftl_bi_table f in
  let bmt := ftl_bm_table f in
  let fbq := ftl_free_blocks f in
  J_bi_block_coherent c bit.

Definition Inv (c: chip) (f: FTL) := 
  F_Inv f /\ R_Inv c f.

