(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Definition PAGE_DATA_SIZE := 32.

Definition PAGE_OOB_SIZE := 8.

Definition ECC_IN_OOB_SIZE := 4.

Definition PAGE_SPARE_AREA_SIZE := 2.

Definition BLOCKS := 16.

Definition NUM_OF_BLOCKS := BLOCKS.

Definition PAGES_PER_BLOCK := 16.

Definition SECTOR_DATA_SIZE := PAGE_DATA_SIZE.

Definition MAX_PHYSICAL_BLOCKS := BLOCKS.

Definition MAX_LOGICAL_BLOCKS := 4.

Definition MIN_FREE_BLOCKS := 3.

Definition GC_THRESHOLD := 4.

Definition NUM_OF_SECTORS := MAX_LOGICAL_BLOCKS * PAGES_PER_BLOCK.
