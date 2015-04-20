(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import LibEx.
Require Import ListEx.
Require Import Config.
Require Import Data.
Require Import Monad.

Require Import Nandv2.

Definition ecc_chunk := chunk ECC_IN_OOB_SIZE.

Definition MDATA_IN_OOB_SIZE := 4.

Definition oob_mdata_chunk := chunk MDATA_IN_OOB_SIZE.

Program Definition make_oob_chunk (md: oob_mdata_chunk) (ecc: ecc_chunk) : oob_chunk.
Admitted.

Program Definition read_data_with_ecc (d: data_chunk) (ecc: ecc_chunk) : data_chunk.
Admitted.

Program Definition get_ecc_from_oob_chunk (oob: oob_chunk) : ecc_chunk.
Admitted.

Program Definition get_mdata_from_oob_chunk (oob: oob_chunk) : oob_mdata_chunk.
Admitted.

(* *********** OOB operations for BFTL ************* *)

Inductive page_state_in_oob : Set := 
  | ps_oob_unprogrammed : page_state_in_oob
  | ps_oob_mlog : page_state_in_oob
  | ps_oob_mdata : page_state_in_oob
  | ps_oob_data (off: page_off) : page_state_in_oob.

Program Definition read_page_state_from_oob (md: oob_mdata_chunk) : page_state_in_oob.
Admitted.

Program Definition write_page_state_to_oob (pso: page_state_in_oob) : oob_mdata_chunk.
Admitted.

Program Definition ubi_read_page (c: chip) (pbn: block_no) (loc: page_off) 
   : result (prod data_chunk page_state_in_oob).
Admitted.

Program Definition ubi_write_page (c: chip) (pbn: block_no) (loc: page_off) (d: data_chunk) (ps: page_state_in_oob)
   : result chip.
Admitted.

Program Definition ubi_erase_block (c: chip) (pbn: block_no) : result chip.
Admitted.

