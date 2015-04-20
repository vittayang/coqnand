Require Export bast0.

(******* Common Testing Facilities *******)

(* Generate data for a page, filled with some char. *)
Definition gen_page_data (c: byte) : data := list_repeat PAGE_DATA_SIZE c.

Definition wrec : Set := (nat * nat * byte) %type.

Fixpoint write_batch (c: chip)(f: FTL) (wl : list wrec) : option (chip * FTL) :=
  match wl with 
    | nil => Some (c, f)
    | cons wr wl' => 
      let (pn, char) := wr in
      let (b, off) := pn in
      do [c', f'] <-- FTL_write c f b off (gen_page_data char);
      write_batch c' f' wl'
  end.

Open Scope list_scope.

(* for nand page *)
Notation "'data'" := ps_programmed.
Notation "'free'" := ps_free.

(* for nand block *)
Notation "'data'" := bs_programmed.
Notation "'free'" := bs_free.

(* for ftl block info *)
Notation "'invalid'" := bs_invalid.
Notation "'erased'" := bs_erased.
Notation "'used in:' x ''" := (bs_used x).

Notation "'[' d ',' o ',' s  ]" := (mkpage d o s).
Notation "'{' pages , next_page: next_page , state ' }'" := (mkblock pages next_page state).
Notation "< x ; .. ; y >" := (cons x .. (cons y nil) ..).

Let test_chip_state_1 := 
  let wl := (0,0,c_a)::(0,1,c_b)::(0,0,c_c)::(0,0,c_d)::
            (*(1,0,c_c)::(1,1,c_d)::(1,0,c_a)::(1,0,c_b)::
            (2,0,c_e)::(2,1,c_f)::(2,0,c_g)::(2,0,c_h)::
            (2,0,c_g)::(2,1,c_h)::(2,0,c_e)::(2,0,c_f)::
*)nil in
  do [c, f] <-- write_batch nand_init ftl_init wl;
  do i <-- bmt_get (bm_table f) 0;
  do i1 <-- alloc_block c f;
  ret (i, i1, c, f).

Eval compute in test_chip_state_1.

(*
Definition system_status := option (prod chip FTL).

Definition index := block_no.

Definition ftl_write (sys_status : system_status) (logical_block_index : index)
           (page_offset : index) (page_data : data) : system_status :=
  do [chip_status, ftl_status] <-- sys_status;
  do r <-- FTL_write chip_status ftl_status logical_block_index page_offset page_data;
  ret r.

Definition ftl_read : data.
Admitted.

Inductive ftl_write_read_tuple : Set :=
  | WriteTuple : index -> index -> data -> ftl_write_read_tuple
  | ReadTuple : index -> index -> ftl_write_read_tuple.


Inductive joiner : Set

Definition ftl_write_read_sequence (sys_status : system_status) (rw_tulple : ftl_write_read_tuple)
  := ftl
Definition init_system := (nand_init, init_FTL).
*)
(******* Testing the Function 'merge_block'. ********)

(* Test 1: merge a data block and a log block. *)
Module MERGE_BLOCK_TEST_1.

Let set_chip := (* fill log block *)
                do [chip_state_1, FTL_1] <-- FTL_write nand_init ftl_init 1 0 (gen_page_data c_a);
                do [chip_state_2, FTL_2] <-- FTL_write chip_state_1 FTL_1 1 1 (gen_page_data c_b);
                (* log block has been filled, so the next write will cause the ftl to create a new
                 data block, copy the log block, and allocate a new log block, then write into it. *)
                do [chip_state_3, FTL_3] <-- FTL_write chip_state_2 FTL_2 1 0 (gen_page_data c_c);
                (* next write will fill the newly allocated log block, then it will be full. *)
                do [chip_state_4, FTL_4] <-- FTL_write chip_state_3 FTL_3 1 1 (gen_page_data c_d);
                (* log block is full again, but this time the data block is presented, so we gonna take
                a merge between the data block and the log block.*)
                (* so there is already a merge taking place here, which belongs to the 3rd case in
                merge_block_fix. *)
                do r <-- FTL_write chip_state_4 FTL_4 1 1 (gen_page_data c_e);
                ret r.
(* check the result*)
Eval compute in  set_chip.

(* try to manualy merge block 3(data) and block 4(log) into block 0. *)
Eval compute in 
  do [c, ftl] <-- set_chip;
  do bmt_entry <-- bmt_get (bm_table ftl) 1;
 (* ret alloc_block_with_gc c ftl. *)
  match bmt_entry with
      | (Some bln_d, Some bln_l) =>
        (
          do [fbn, s] <-- get_free_block (mk_sys_state c ftl);
          ret merge s 1 fbn
        )
      | (_, _) => None
  end.
(* Seems to be correct, in block 0, page 0 is 'c_c' and page 1 is 'c_e'.*)
End MERGE_BLOCK_TEST_1.

Module MERGE_BLOCK_TEST_2.
(* Merging a log block with the data block being None. *)
Let set_chip := do [chip_state_1, FTL_1] <-- (FTL_write nand_init ftl_init 1 0 (gen_page_data c_a));
                do r <-- FTL_write chip_state_1 FTL_1 1 1 (gen_page_data c_b);
                ret r.
Eval compute in  set_chip.

Eval compute in 
  do [c, ftl] <-- set_chip;
  do bmt_entry <-- bmt_get (bm_table ftl) 1;
 (* ret alloc_block_with_gc c ftl. *)
  match bmt_entry with
      | (None, Some bln_l) =>
        (
(*          ret read_log_block c bi_l 0 0 *)
          do [fb, s] <-- get_free_block (mk_sys_state c ftl); 
          ret merge s 1 fb 
        )
      | (_, _) => None
  end.
(* The result seems to be good. *)
End MERGE_BLOCK_TEST_2.

(********* Testing 'gc_blocks' *********************)

Module FTL_WRITE_TEST.

Let set_chip := 
  let wl := (0,0,c_a)::(0,1,c_b)::(0,0,c_c)::(0,0,c_d)::
            (1,0,c_c)::(1,1,c_d)::(1,0,c_a)::(1,0,c_b)::
            (2,0,c_e)::(2,1,c_f)::(2,0,c_g)::(2,0,c_h)::
            (*(2,0,c_g)::(2,1,c_h)::(2,0,c_e)::(2,0,c_f)::
*)nil in
  do [c, f] <-- write_batch nand_init ftl_init wl;  
  let bmt := bm_table f in
  let bit := bi_table f in
  let freebq := free_blocks f in
  ret  (c, f).
Eval compute in set_chip.

(*
Let chip' := do [c, f] <-- set_chip;
            do i <-- find_victim (bm_table f) (bi_table f);
            do [fb, s] <-- alloc_block c f;
            do [c', f'] <-- merge (Some s) i fb;
            ret (i,(alloc_block c' f'), c, f).
(*            let (c', ftl') := (pack : prod chip FTL) in*)
(*            ret (i, pbn_free, pack).*)
(*            merge (mk_sys_state c' ftl') i pbn_free.*)

(*            do [c',f'] <-- gc_block c f;
             ret (i, (free_blocks f), (free_blocks f'), (bm_table f), (bm_table f')).
*)
Eval compute in chip'. *)

(************ Testing 'get_free_block'  *******************************)
Module GET_FREE_BLOCK_TEST.

Let set_chip := 
  let wl := (0,0,c_a)::(0,1,c_b)::(0,0,c_c)::(0,0,c_d)::
            (1,0,c_c)::(1,1,c_d)::(1,0,c_a)::(1,0,c_b)::
            (2,0,c_e)::(2,1,c_f)::(*(2,0,c_g)::(2,0,c_h)::
            (2,0,c_g)::(2,1,c_h)::(2,0,c_e)::(2,0,c_f)::
*)nil in
  do [c, f] <-- write_batch nand_init ftl_init wl; 
  ret (c, f).

Eval compute in set_chip.

Let chip' := do [c, f] <-- set_chip;
             do [b, s] <-- get_free_block (mk_sys_state c f);
             do [b', s'] <-- get_free_block s;
             ret get_free_block s'.
Eval compute in chip'.

End GET_FREE_BLOCK_TEST.

(************* Testing 'FTL_read' ***************************)
Module FTL_READ_TEST.

Let set_chip := 
  let wl := (0,0,c_a)::(0,1,c_b)::(0,0,c_c)::(0,0,c_d)::
            (1,0,c_c)::(1,1,c_d)::(1,0,c_a)::(1,1,c_b)::
            (2,0,c_e)::(2,1,c_f)::(2,0,c_g)::(2,1,c_h)::
            (*(2,0,c_g)::(2,1,c_h)::(2,0,c_e)::(2,0,c_f)::
*)nil in
  do [c, f] <-- write_batch nand_init ftl_init wl;  
  ret (c, f).
Eval compute in set_chip.

Let set_chip_random := 
  let wl := (3,0,c_a)::(0,1,c_b)::(1,1,c_c)::(0,0,c_d)::
            (2,1,c_c)::(1,0,c_d)::(2,0,c_a)::(1,1,c_b)::
            (2,0,c_e)::(1,1,c_f)::(*(3,1,c_g)::(2,1,c_h)::
*)nil in
  do [c, f] <-- write_batch nand_init ftl_init wl;  
  ret (c, f).
Eval compute in set_chip_random.


Eval compute in 
    do [c, f] <-- set_chip_random;
    ret ((FTL_read c f 0 0), (FTL_read c f 0 1), (FTL_read c f 1 0),
         (FTL_read c f 1 1), (FTL_read c f 2 0), (FTL_read c f 2 1),
         (FTL_read c f 3 0),
         set_chip_random).

End FTL_READ_TEST.

(************************************)


Let chip_1 := do [c, f] <-- set_chip;
            do [block_n, c_f] <-- alloc_block c f;
match c_f with (c', f') =>
            ret (block_n, (free_blocks f), (free_blocks f'), (bm_table f), (bm_table f'))
end.
Eval compute in chip_1.

End FTL_WRITE_TEST.


Goal forall x, merge_block nand_init. 

Let s1 :=  FTL_write nand_init init_FTL 1 1 (list_repeat PAGE_DATA_SIZE c_a).

Let s2 := do [chip1, ftl1] <-- s1;
             FTL_write  chip1 ftl1 1 1 (gen_pg_data c_b).
Eval compute in s1.

Eval compute in s2.

Goal forall x,FTL_write nand_init init_FTL 1 1 (list_repeat PAGE_DATA_SIZE c_a) = x.
  intros x.
  compute.
  unfold init_FTL.
  simpl.
  unfold nand_init.
  simpl.
  unfold FTL_write.
  compute.
  Eval compute in  bm_table_get
          (bm_table
             {|
             bi_table := init_bi_table;
             bm_table := init_bm_table;
             free_blocks := init_free_blocks |}) 1.

Abort.
Eval compute in FTL_write nand_init init_FTL 1 1 (list_repeat PAGE_DATA_SIZE c_a).
Definition ftl_test_func1 : option data := do [chip', FTL'] <-- FTL_write nand_init init_FTL 1 1 (list_repeat PAGE_DATA_SIZE c_a) ;
                                    do r <-- FTL_read chip' FTL' 1 1 ;
                                    ret r.

Eval compute in init_FTL.
Eval compute in ftl_test_func1.
Eval compute in Some (list_repeat PAGE_DATA_SIZE c_a).


Example ftl_test1 : ftl_test_func1 = Some (list_repeat PAGE_DATA_SIZE c_a).
Proof. reflexivity.
