(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

(* ************* ************************************* *****)

Require Import ListEx.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import Bast0.


(*  -------------------------------------------------------------

  Predicates for block no.

*)

Definition valid_logical_block_no (lbn: block_no) := bvalid_logical_block_no lbn = true.

Definition valid_block_no (pbn: block_no) := bvalid_block_no pbn = true.

Definition valid_page_off (off: page_off) := bvalid_page_off off = true.

Lemma valid_page_off_dec : 
  forall off,
    valid_page_off off \/ ~ valid_page_off off.
Proof.
  intros.
  unfold valid_page_off.
  destruct (bvalid_page_off off).
  left; trivial.
  right.
  auto.
Qed.

(*  -------------------------------------------------------------

  Predicates for block mapping table

*)

Definition pbn_in_bmt_data (bmt: block_mapping_table) 
           (lbn: block_no) (pbn: block_no) : Prop :=
  exists x, bmt_get bmt lbn = Some (Some pbn, x).

Definition pbn_in_bmt_log (bmt: block_mapping_table) 
           (lbn: block_no) (pbn: block_no) : Prop :=
  exists x, bmt_get bmt lbn = Some (x, Some pbn).

Definition pbn_in_bmt_lbn (bmt: block_mapping_table) 
           (lbn: block_no) (pbn: block_no) : Prop :=
  pbn_in_bmt_data bmt lbn pbn \/ pbn_in_bmt_log bmt lbn pbn .

Definition pbn_in_bmt (bmt: block_mapping_table) (pbn: block_no) : Prop:=
  exists lbn, pbn_in_bmt_lbn bmt lbn pbn.

Definition pbn_in_bmr (pbn: block_no) (bmr: prod (option block_no) (option block_no)) : Prop :=
  match bmr with
    | (Some pbn', None) => pbn = pbn'
    | (None, Some pbn') => pbn = pbn'
    | (Some pbn', Some pbn'') => pbn = pbn' \/ pbn = pbn''
    | (None, None) => False
  end.

Definition pbn_not_in_bmr (pbn: block_no) (bmr: bmt_record) : Prop :=
  match bmr with
    | (Some pbn', Some pbn'') => pbn <> pbn' /\ pbn <> pbn''
    | (Some pbn', None) => pbn <> pbn'
    | (None, Some pbn') => pbn <> pbn'
    | (None, None) => True
  end.

Definition pbn_not_in_bmt (bmt: block_mapping_table) (pbn: block_no) : Prop:=
  ~ pbn_in_bmt bmt pbn.

(*  -------------------------------------------------------------

  Predicates for page mapping table

*)

Definition pmt_domain_is_complete (pmt: page_mapping_table) : Prop :=
  pmt_len pmt = PAGES_PER_BLOCK.

Definition pmt_page_state (pmt: page_mapping_table) (b: block) : Prop :=
  forall loc,
     valid_page_off loc
     -> (pmt_get pmt loc = Some (pmte_empty)
         -> exists p, block_get_page b loc = Some p 
                  /\ page_state p = ps_free)
        /\ (forall off, 
              pmt_get pmt loc = Some (pmte_log off)
              -> exists p, block_get_page b loc = Some p
                           /\ page_state p = ps_programmed).

Definition pmt_shape (pmt: page_mapping_table) (np: page_off) : Prop :=
  forall loc,
    valid_page_off loc
    -> (blt_nat loc np = true 
        -> exists off, pmt_get pmt loc = Some (pmte_log off))
       /\ (blt_nat loc np = false 
           -> pmt_get pmt loc = Some pmte_empty).

(*  -------------------------------------------------------------

  Predicates for "block info"

*)

Definition block_coherent_log (bi: block_info) (b: block): Prop :=
  exists pmt lbn, 
    bi_state bi = bs_log lbn pmt 
    /\ bi_used_pages bi = next_page b
    /\ block_state b = bs_programmed
    /\ pmt_domain_is_complete pmt
    /\ pmt_page_state pmt b
    /\ pmt_shape pmt (next_page b).

Definition block_coherent_data (bi: block_info) (b: block) : Prop :=
  exists lbn, 
    bi_state bi = bs_data lbn 
    /\ bi_used_pages bi = next_page b
    /\ block_state b = bs_programmed
    /\ next_page b = PAGES_PER_BLOCK
    /\ (forall loc,
          valid_page_off loc
          -> exists p, block_get_page b loc = Some p
                       /\ page_state p = ps_programmed).

Definition block_coherent_erased (bi: block_info) (b: block) : Prop :=
  bi_state bi = bs_erased
  /\ bi_used_pages bi = next_page b
  /\ block_state b = bs_free
  /\ next_page b = 0
  /\ (forall loc,
        valid_page_off loc
        -> exists p, block_get_page b loc = Some p
                     /\ page_state p = ps_free).
  
Definition block_coherent_data_partial (loc: page_off) (b: block): Prop :=
  next_page b = loc
  /\ block_state b = bs_programmed
  /\ (forall off,
        valid_page_off off
        -> (blt_nat off loc = true
            -> exists p, block_get_page b off = Some p
                         /\ page_state p = ps_programmed)
           /\ (blt_nat off loc = false
               -> exists p, block_get_page b off = Some p
                            /\ page_state p = ps_free)).
