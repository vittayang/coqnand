(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import String.
Require Import List.
Require Import ListEx.

(************** Chip Definitions *****************************)
(*

Definition PAGE_DATA_SIZE := 512.

Definition PAGE_SPARE_AREA_SIZE := 16.

Definition BLOCKS := 2048.

Definition PAGES_PER_BLOCK := 32.


Definition SECTOR_DATA_SIZE := 512.

Definition NUM_OF_SECTORS := BLOCKS * PAGES_PER_BLOCK.

*)

(***** Minimalized Configuration for Testing ******)

Definition PAGE_DATA_SIZE := 32.

Definition PAGE_OOB_SIZE := 8.

Definition ECC_IN_OOB_SIZE := 4.

Definition PAGE_SPARE_AREA_SIZE := 2.

Definition BLOCKS := 16.

Definition NUM_OF_BLOCKS := 16.

Definition PAGES_PER_BLOCK := 16.

Definition NUM_OF_SECTORS := BLOCKS * PAGES_PER_BLOCK.

Definition SECTOR_DATA_SIZE := PAGE_DATA_SIZE.

Definition MAX_LOGICAL_BLOCKS := 4.

Definition MIN_FREE_BLOCKS := 3.

Definition GC_THRESHOLD := 4.

Definition PLANES := 2.
