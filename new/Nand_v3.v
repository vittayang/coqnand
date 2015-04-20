(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import Lists.List.
Require Import ListEx.
Require Import Config.
Require Import Data.
Require Import Monad.

(* 

       NAND hardware interface (Version 3) 

  NAND Flash is easily to be formalized, due to the sophisicated geography of NAND
flash chips. We follow a common accepted standard, Open NAND FLash Interface (ONFi)
, that published by a few flash manufacturers, Intel, Micron, etc. Please note 
we simplify the hardware specification presented in the document, for a reason 
that we aim to provide a simple ilustration of NAND flash to developers. 

  In the model, we use raw bytes for spare area. 

  No NAND chip can be pristine. There are a unknown number of bad blocks in a
new NAND. So manufacturers are responsible to mark them out by setting specifical
cells to 0x00 in a bad block. FTL is supposed to scan all blocks and remember
which are bad and should not be used again. In our model, however, we don't 
simulate bad blocks so far. Nevertheless, we shall support bad blocks in next 
versions if we model more NAND commands with failure return according to the 
standard. 
  
 *)

(* Record chunk (sz: nat) : Set :=  *)
(*   mkchunk {  *)
(*     chunk_data: list byte; *)
(*     chunk_size: length chunk_data = sz *)
(*   }. *)

(* Notation "{{ s }}" := (mkchunk _ s _) (at level 200) : nand_scope. *)
Print blt_nat.

Definition page_off := nat.

Definition block_no := nat.

Definition plane_no := nat.

Definition page_no := prod block_no page_off.

Definition bvalid_block_no (pbn: block_no) : bool := 
  (blt_nat pbn BLOCKS).

Definition bvalid_page_off (off: page_off) : bool := 
  (blt_nat off PAGES_PER_BLOCK).

Definition bvalid_plane_no (pn: plane_no) : bool :=
  (blt_nat pn PLANES).

Inductive page_hw_state : Set :=
  | ps_free
  | ps_programmed
  | ps_invalid.

Record page : Set := 
  mkpage {
      page_data : data;
      page_state : page_hw_state
    }.

Inductive block_hw_status : Set :=
  | bs_normal
  | bs_invalid
  | bs_bad.

Record block : Set := 
  mkblock {
      block_pages : list page;
      block_next_page : page_off;
      block_erase_count: nat;
      block_state : block_hw_status
      (* block_pages_num: length block_pages = PAGES_PER_BLOCK *)
    }.

Definition BLOCKS_PER_PLANE := 1024.

Record plane : Set := 
  mkplane {
      plane_blocks: list block;
      plane_page_register: data
      (* plane_blocks_num : length plane_blocks = BLOCKS_PER_PLANE *)
    }. 

Inductive lun_addr : Set :=
  | mklun_addr (pn: plane_no) (b: block_no) (po: page_off) .

Inductive plane_addr : Set :=
  | mkplane_addr (b: block_no) (po: page_off).

Inductive command : Set :=
  | read_start  (* 00h *)
  | read_confirm (* 30h *)
  | read_ID (* 90h *)
  | reset (* FFh *)
  | erase_start (* 60h *)
  | erase_confirm (* D0h *)
  | program_start (* D0h *)
  | program_confirm (* 10h *)
  | read_status (* 70h *).

Definition col_addr := nat.

Definition row_addr := lun_addr.

Definition bvalid_row_addr (ra : row_addr) : bool :=
  match ra with
    | mklun_addr pn b po =>
      match bvalid_plane_no pn with 
        | true => 
           match bvalid_block_no b with
             | true  => bvalid_page_off po
             | false => false
           end
        | false => false
      end
end.

Definition bvalid_col_addr (ca : col_addr) : bool :=
  blt_nat ca (PAGE_DATA_SIZE+PAGE_OOB_SIZE).

Definition bvalid_addr (addr : prod row_addr col_addr) : bool :=
  match addr with 
    | (ra, ca) => 
       match bvalid_row_addr ra with
         | true => bvalid_col_addr ca
         | false => false
       end
end.

Inductive lun_hw_internal_state : Set := 
  | lun_idle 

  | lun_read_wait_addr 
  | lun_read_wait_confirm 
  | lun_read_busy
  | lun_read_wait_recv

  | lun_prog_wait_addr
  | lun_prog_wait_data
  | lun_prog_wait_confirm
  | lun_prog_busy

  | lun_erase_wait_addr 
  | lun_erase_wait_confirm
  | lun_erase_busy

  | lun_read_ID
  | lun_readID_wait_addr
  | lun_read_status.

Record lun: Set :=
  mklun{
      lun_plane0 : plane;
      lun_plane1 : plane;
      lun_cmd_reg: option command;
      lun_addr_reg: option (prod row_addr col_addr) (* row addr. and col addr. *);
      lun_status_RB: bool; (* ready = true, busy = false *)
      lun_status_SF: bool; (* succ = true, fail = false *)
      lun_intern_state: lun_hw_internal_state
    }.

Record target : Set := 
  mktarget {
      target_lun: lun
    }. 

Record device : Set :=
  mkdevice {
      device_target: target
    }.

(* ******** Initialization *************** *)

Definition init_page_data : data :=
  list_repeat (PAGE_DATA_SIZE+PAGE_OOB_SIZE) c_null.

Definition init_page : page :=
  mkpage init_page_data ps_free.

Definition init_block : block :=
  mkblock (list_repeat PAGES_PER_BLOCK init_page) 0 0 bs_normal.

Definition init_plane : plane :=
  mkplane (list_repeat BLOCKS_PER_PLANE init_block) nil.

Definition init_lun : lun :=
  mklun init_plane init_plane None None true true lun_idle.

Definition init_target : target :=
  mktarget init_lun.

Definition init_device : device :=
  mkdevice init_target.

(* ********* Nand Internal Operations (over hardware) ************** *)


Definition device_get_plane (d: device) (pn: plane_no) : option plane:=
  check bvalid_plane_no pn;
  do lun <- Some (target_lun (device_target d));
  match pn with
        | 0 => Some (lun_plane0 lun)
        | 1 => Some (lun_plane1 lun)
        | _ => None
  end.

Definition device_set_plane (d: device) (pn: plane_no) (pl:plane) : option device:=
 check bvalid_plane_no pn;
  do lun <- Some (target_lun (device_target d));
  match pn with
        | 0 => Some (mkdevice(mktarget(mklun
                                       pl
                                       (lun_plane1 lun)
                                       (lun_cmd_reg lun)
                                       (lun_addr_reg lun)
                                       (lun_status_RB lun)
                                       (lun_status_SF lun)
                                       (lun_intern_state lun))))
        | 1 => Some (mkdevice(mktarget(mklun
                                       (lun_plane0 lun)
                                       pl
                                       (lun_cmd_reg lun)
                                       (lun_addr_reg lun)
                                       (lun_status_RB lun)
                                       (lun_status_SF lun)
                                       (lun_intern_state lun))))
        | _ => None
  end.

Definition plane_get_block (pl : plane) (ba: block_no) : option block :=
  do b <- list_get (plane_blocks pl) ba;
  Some b.

Definition plane_set_block (pl : plane) (bn: block_no) (b: block): option plane :=
  do bl <- list_set (plane_blocks pl) bn b;
  Some (mkplane bl (plane_page_register pl)).

Definition block_set_invalid (b: block) : option block :=
  Some (mkblock (block_pages b) (block_next_page b) (block_erase_count b) bs_invalid). 

Definition page_set_invalid (p: page) : option page :=
  Some (mkpage (page_data p) ps_invalid). 

Definition plane_set_block_invalid (pl : plane) (ba: block_no) : option plane :=
  do b  <- plane_get_block pl ba;
  do b' <- block_set_invalid b;
  do bl' <- list_set (plane_blocks pl) ba b';
  Some (mkplane bl' nil).

Definition block_get_page (b: block) (po: page_off) : option page :=
  do p <- list_get (block_pages b) po;
  Some p.

Definition block_set_page (b: block) (po: page_off) (p: page) : option block :=
  check bvalid_page_off po;
  do plst' <- list_set (block_pages b) po p;
  Some (mkblock plst' (S po) (block_erase_count b) bs_normal).

Definition page_get_data (p: page) : option data:=
  Some (page_data p).

Definition plane_get_page (pl: plane) (bn: block_no) (po: page_off) : option page :=
  check bvalid_block_no bn;
  check bvalid_page_off po;
  do b <- plane_get_block pl bn;
  do pgl <- Some (block_pages b);
  do p <- list_get pgl po;
  Some p.

Definition plane_set_page (pl: plane) (bn: block_no) (po: page_off) (p: page) : option plane :=
  check bvalid_block_no bn;
  check bvalid_page_off po;
  do b <- plane_get_block pl bn;
  do pgl <- Some (block_pages b);
  do pgl' <- list_set pgl po p;
  do b' <- Some (mkblock pgl' (S po) (block_erase_count b) bs_normal);
  do pl' <- plane_set_block pl bn b';
  Some pl'.

Definition plane_set_page_invalid (pl: plane) (ba: block_no) (po: page_off) : option plane :=
  do b <- plane_get_block pl ba;
  do p <- block_get_page b po; 
  do p' <- page_set_invalid p;
  do pgl' <- list_set (block_pages b) po p';
  do b' <- Some (mkblock pgl' (S (block_next_page b)) (block_erase_count b) bs_normal);
  do bl' <- list_set (plane_blocks pl) ba b';
  Some (mkplane bl' nil).
  
Definition block_set_erased (ec: nat): block :=
  mkblock (list_repeat PAGES_PER_BLOCK init_page) 0 (S ec) bs_normal.

Definition device_get_block (d: device) (addr: prod row_addr col_addr) : option block :=
  do [raddr, caddr] <- Some addr; 
  match raddr with
    | mklun_addr pn bn off =>
      do lun <- Some (target_lun (device_target d));
      do pl <- match pn with
                  | 0 => Some (lun_plane0 lun)
                  | 1 => Some (lun_plane1 lun)
                  | _ => None
                end;
      do b <- plane_get_block pl bn;
      Some b
  end.

(* ******************** Nand chip Operational Semantics ********************** *)

(* Parameter lun_set_intern_state : lun -> lun_hw_internal_state -> lun. *)

(* Parameter block_no_is_odd : nat -> bool. *)

(* Parameter read_plane_data : plane -> plane_addr -> option plane. *)

Definition lun_set_page_invalid (lu: lun) (la: lun_addr) : result lun :=
  match la with 
    | mklun_addr pn b po => 
      do pl <-- match pn with 
                  | 0 => Some (lun_plane0 lu)
                  | 1 => Some (lun_plane1 lu)
                  | _ => None
                end;
      do pl' <-- plane_set_page_invalid pl b po;
      do lu' <-- match pn with 
                    | 0 => Some (mklun pl' (lun_plane1 lu) None None true true lun_idle)
                    | 1 => Some (mklun (lun_plane0 lu) pl' None None true true lun_idle)
                    | _ => None
                  end;
      ret lu'
  end.

Definition lun_set_block_invalid (lu : lun) (la: lun_addr) : result lun :=
  match la with 
    | mklun_addr pn b po => 
      do pl <-- match pn with 
                  | 0 => Some (lun_plane0 lu)
                  | 1 => Some (lun_plane1 lu)
                  | _ => None
                end;
      do pl' <-- plane_set_block_invalid pl b;
      do lu' <-- match pn with 
                    | 0 => Some (mklun pl' (lun_plane1 lu) None None true true lun_idle)
                    | 1 => Some (mklun (lun_plane0 lu) pl' None None true true lun_idle)
                    | _ => None
                  end;
      ret lu'
  end.

Definition send_cmd (d: device) (cmd: command) : result device :=
  match cmd with 
    | read_start => match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_idle => 
                        let lun := (target_lun (device_target d)) in
                        let lun' := (mklun (lun_plane0 lun)
                                          (lun_plane1 lun) 
                                          (Some read_start)
                                          None
                                          true
                                          true
                                          lun_read_wait_addr) in
                        Ok (mkdevice(mktarget lun'))
                      | _ => Unknown
                    end
    | read_confirm => 
         match (lun_intern_state (target_lun (device_target d))) with
           | lun_read_wait_confirm => 
             let lun := (target_lun (device_target d)) in 
             let lun' := (mklun (lun_plane0 lun)
                                (lun_plane1 lun)
                                (Some read_confirm)
                                (lun_addr_reg lun)
                                false
                                true
                                lun_read_busy) in
             Ok (mkdevice(mktarget lun'))
           | _ => Unknown
         end

  | read_ID (* 90h *) => 
                    match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_idle => 
                        let lun := (target_lun (device_target d)) in
                        let lun' := (mklun (lun_plane0 lun)
                                          (lun_plane1 lun) 
                                          (Some read_ID)
                                          None
                                          true
                                          true
                                          lun_read_ID) in
                        Ok (mkdevice(mktarget lun'))
                      | _ => Unknown
                    end

  | reset (* FFh *) => 
                    match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_prog_busy => 
                          let lu := (target_lun (device_target d)) in
                          do [la, col] <-- (lun_addr_reg lu);
                          do lu' <== lun_set_page_invalid lu la;
                          ret (mkdevice(mktarget lu'))

                      | lun_erase_busy => 
                          let lu := (target_lun (device_target d)) in
                          do [la, col] <-- (lun_addr_reg lu);
                          do lu' <== lun_set_block_invalid lu la;
                          ret (mkdevice(mktarget lu'))
                      | _ =>                         
                          let lu := (target_lun (device_target d)) in
                          let lu' := (mklun (lun_plane0 lu)
                                           (lun_plane1 lu) 
                                           None
                                           None
                                           true 
                                           true
                                           lun_idle) in
                          ret (mkdevice(mktarget lu'))

                    end

  | erase_start (* 60h *) => 
                    match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_idle => 
                        let lu := (target_lun (device_target d)) in
                        let lu' := (mklun (lun_plane0 lu)
                                          (lun_plane1 lu) 
                                          (Some erase_start)
                                          None
                                          true
                                          true
                                          lun_erase_wait_addr) in
                        Ok (mkdevice(mktarget lu'))
                      | _ => Unknown
                    end

  | erase_confirm (* D0h *) =>                     
                    match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_erase_wait_confirm => 
                        let lu := (target_lun (device_target d)) in
                        let lu' := (mklun (lun_plane0 lu)
                                          (lun_plane1 lu) 
                                          (Some erase_confirm)
                                          (lun_addr_reg lu)
                                          false
                                          true
                                          lun_erase_busy) in
                        ret (mkdevice(mktarget lu'))
                      | _ => Unknown
                    end

  | program_start (* D0h *) => 
                    match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_idle => 
                        let lu := (target_lun (device_target d)) in
                        let lu' := (mklun (lun_plane0 lu)
                                          (lun_plane1 lu) 
                                          (Some program_start)
                                          None
                                          true
                                          true
                                          lun_prog_wait_addr) in
                        Ok (mkdevice(mktarget lu'))
                      | _ => Unknown
                    end

  | program_confirm (* 10h *) => 
                    match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_prog_wait_confirm => 
                        let lu := (target_lun (device_target d)) in
                        let lu' := (mklun (lun_plane0 lu)
                                          (lun_plane1 lu) 
                                          (Some program_confirm)
                                          (lun_addr_reg lu)
                                          false
                                          true
                                          lun_prog_busy) in
                        ret (mkdevice(mktarget lu'))
                      | _ => Unknown
                    end

  | read_status (* 70h *) => 
                    match (lun_intern_state (target_lun (device_target d))) with 
                      | lun_idle => 
                        let lu := (target_lun (device_target d)) in
                        let lu' := (mklun (lun_plane0 lu)
                                          (lun_plane1 lu) 
                                          (Some read_status)
                                          None
                                          (lun_status_RB lu)
                                          (lun_status_SF lu)
                                          lun_read_status) in
                        Ok (mkdevice(mktarget lu'))
                      | _ => Unknown
                    end
  end.

Definition device_status := prod bool bool.

Definition recv_status (d: device) : result (prod device_status device) :=
  match (lun_intern_state (target_lun (device_target d))) with 
    | lun_read_status => 
      let lu := (target_lun (device_target d)) in
      let sRB := lun_status_RB lu in
      let sSF := lun_status_SF lu in
      let lu' := (mklun (lun_plane0 lu)
                        (lun_plane1 lu) 
                        None
                        None
                        (lun_status_RB lu)
                        (lun_status_SF lu)
                        lun_idle) in
      Ok ((lun_status_RB lu, lun_status_SF lu), (mkdevice(mktarget lu')))
    | _ => Unknown
  end.

Definition send_full_addr (d: device) (addr: prod row_addr col_addr) : result device :=
  match (lun_intern_state (target_lun (device_target d))) with
    | lun_read_wait_addr => 
      let lu := (target_lun (device_target d)) in
      let lu' := (mklun (lun_plane0 lu)
                        (lun_plane1 lu) 
                        (lun_cmd_reg lu)
                        (Some addr)
                        (lun_status_RB lu)
                        (lun_status_SF lu)
                        lun_read_wait_confirm) in
      Ok (mkdevice(mktarget lu'))

    | lun_prog_wait_addr => 
      let lu := (target_lun (device_target d)) in
      let lu' := (mklun (lun_plane0 lu)
                        (lun_plane1 lu) 
                        (lun_cmd_reg lu)
                        (Some addr)
                        (lun_status_RB lu)
                        (lun_status_SF lu)
                        lun_prog_wait_data) in
      Ok (mkdevice(mktarget lu'))

    | _ => Unknown
  end.

Definition send_2cycle_addr (d: device) (addr: (prod plane_no block_no)) : result device :=
  match (lun_intern_state (target_lun (device_target d))) with
    | lun_erase_wait_addr => 
      let lu := (target_lun (device_target d)) in
      let lu' := (mklun (lun_plane0 lu)
                        (lun_plane1 lu) 
                        (lun_cmd_reg lu)
                        (Some (mklun_addr (fst addr) (snd addr) 0, 0))
                        (lun_status_RB lu)
                        (lun_status_SF lu)
                        lun_erase_wait_confirm) in
      Ok (mkdevice(mktarget lu'))
    | _ => Unknown
  end.

Definition send_1cycle_addr (d: device) (addr: block_no) : result device :=
  match (lun_intern_state (target_lun (device_target d))) with
    | lun_readID_wait_addr => 
      let lu := (target_lun (device_target d)) in
      let lu' := (mklun (lun_plane0 lu)
                        (lun_plane1 lu) 
                        (lun_cmd_reg lu)
                        (Some (mklun_addr (0) (addr) 0, 0))
                        (lun_status_RB lu)
                        (lun_status_SF lu)
                        lun_read_wait_recv) in
      Ok (mkdevice(mktarget lu'))
    | _ => Unknown
  end.

Definition send_data (de: device) (d: data) : result device :=
  match (lun_intern_state (target_lun (device_target de))) with

    | lun_prog_wait_data => 
      do lu <-- Some (target_lun (device_target de));
      do a <-- (lun_addr_reg lu);
      do raddr <-- Some (fst a);
      do pl <-- match raddr with 
                  | mklun_addr pn bn po => 
                    match pn with
                      | 0 => Some (lun_plane0 lu)
                      | 1 => Some (lun_plane1 lu)
                      | _ =>  None
                    end
                end;
      do caddr <-- Some (snd a);
      do d' <-- Some (zero_data (caddr));
      do d'' <-- Some (d' ++ d);
      do pl' <-- Some (mkplane (plane_blocks pl) d'');
      do lu' <-- match raddr with 
                   | mklun_addr pn bn po => 
                     match pn with 
                       | 0 => Some (mklun pl'
                                          (lun_plane1 lu) 
                                          (lun_cmd_reg lu)
                                          (lun_addr_reg lu)
                                          (lun_status_RB lu)
                                          (lun_status_SF lu)
                                      lun_prog_wait_confirm)
                       | 1 => Some (mklun (lun_plane0 lu)
                                          pl'
                                          (lun_cmd_reg lu)
                                          (lun_addr_reg lu)
                                          (lun_status_RB lu)
                                          (lun_status_SF lu)
                                      lun_prog_wait_confirm)
                       | _ => None 
                     end
                 end;
      ret (mkdevice(mktarget lu'))
    | _ => Unknown
  end.

Definition list_sub {A: Set} (l: list A) (n: nat) : option (list A).
Admitted.

Parameter init_data_ID : data.

Definition recv_data (de: device) : result (prod data device) :=
  match (lun_intern_state (target_lun (device_target de))) with 

    | lun_read_wait_recv => 
      do lu <-- Some (target_lun (device_target de));
      do a <-- (lun_addr_reg lu);
      do row <-- Some (fst a);
      do col <-- Some (snd a);
      match row with 
           | mklun_addr pn bn po =>
               do pl <-- match pn with
                      | 0 => Some (lun_plane0 lu)
                      | 1 => Some (lun_plane1 lu)
                      | _ =>  None
                    end;
               do lu' <-- match pn with 
                                | 0 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   true
                                                   lun_idle)
                                | 1 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   true
                                                   lun_idle)
                                | _ =>  None
                              end;
               do d <-- list_sub (plane_page_register pl) col;
               ret (d, (mkdevice(mktarget lu')))
      end

    | lun_read_ID => 
      do lu <-- Some (target_lun (device_target de));
      do d <-- Some (init_data_ID);
      ret (d, (mkdevice(mktarget (mklun (lun_plane0 lu)
                             (lun_plane1 lu)
                             None
                             None
                             true
                             true
                             lun_idle))))

    | _ => Unknown
  end.

Definition wait_cmd (d: device) : result device :=
  match (lun_intern_state (target_lun (device_target d))) with

    | lun_read_busy => 
      do lu <-- Some (target_lun (device_target d));
      do a <-- (lun_addr_reg lu);
      do row <-- Some (fst a);
      do col <-- Some (snd a);
      do lu' <==
         match row with 
           | mklun_addr pn bn po =>
             do pl <-- match pn with
                      | 0 => Some (lun_plane0 lu)
                      | 1 => Some (lun_plane1 lu)
                      | _ =>  None
                    end;
             do b <-- plane_get_block pl bn;
             do pg <-- plane_get_page pl bn po;
             do pl' <-- Some (mkplane (plane_blocks pl) (page_data pg));
             do lu' <-- match pn with 
                          | 0 => Some (mklun pl'
                                             (lun_plane1 lu)
                                             None
                                             (lun_addr_reg lu)
                                             true
                                             true
                                             lun_read_wait_recv)
                          | 1 => Some (mklun (lun_plane0 lu)
                                             pl'
                                             None
                                             (lun_addr_reg lu)
                                             true
                                             true
                                             lun_read_wait_recv)
                          | _ => None
                        end;
             ret lu'
         end;
      ret (mkdevice(mktarget lu'))
      
    | lun_prog_busy => 
      do lu <-- Some (target_lun (device_target d));
      do a <-- (lun_addr_reg lu);
      do raddr <-- Some (fst a);
      do lu' <==
         match raddr with 
           | mklun_addr pn bn po =>
             do pl <-- match pn with
                      | 0 => Some (lun_plane0 lu)
                      | 1 => Some (lun_plane1 lu)
                      | _ =>  None
                    end;
             do b <-- plane_get_block pl bn;
             match (block_state b) with
               | bs_bad => 
                   do lu' <-- match pn with 
                                | 0 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   false
                                                   lun_idle)
                                | 1 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   false
                                                   lun_idle)
                                | _ =>  None
                              end;
                   ret lu'
               | bs_invalid => 
                   do lu' <-- match pn with 
                                | 0 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   false
                                                   lun_idle)
                                | 1 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   false
                                                   lun_idle)
                                | _ =>  None
                              end;
                   ret lu'
               | _ => 
                   do pl' <-- plane_set_page pl bn po (mkpage (plane_page_register pl) ps_programmed);
                   do lu' <-- match pn with 
                                | 0 => Some (mklun pl' 
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   true
                                                   lun_idle)
                                | 1 => Some (mklun (lun_plane0 lu)
                                                   pl'
                                                   None
                                                   None
                                                   true
                                                   true
                                                   lun_idle)
                                | _ =>  None
                              end;
                   ret lu'
             end
         end;
      ret (mkdevice(mktarget lu'))

    | lun_erase_busy => 

      do lu <-- Some (target_lun (device_target d));
      do a <-- (lun_addr_reg lu);
      do raddr <-- Some (fst a);
      do lu' <==
         match raddr with 
           | mklun_addr pn bn po =>
             do pl <-- match pn with
                      | 0 => Some (lun_plane0 lu)
                      | 1 => Some (lun_plane1 lu)
                      | _ =>  None
                    end;
             do b <-- plane_get_block pl bn;
             match (block_state b) with
               | bs_bad => 
                   do lu' <-- match pn with 
                                | 0 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   false
                                                   lun_idle)
                                | 1 => Some (mklun (lun_plane0 lu)
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   false
                                                   lun_idle)
                                | _ =>  None
                              end;
                   ret lu'
               | _ => 
                   do pl' <-- plane_set_block pl bn (block_set_erased (block_erase_count b));
                   do lu' <-- match pn with 
                                | 0 => Some (mklun pl' 
                                                   (lun_plane1 lu)
                                                   None
                                                   None
                                                   true
                                                   true
                                                   lun_idle)
                                | 1 => Some (mklun (lun_plane0 lu)
                                                   pl'
                                                   None
                                                   None
                                                   true
                                                   true
                                                   lun_idle)
                                | _ =>  None
                              end;
                   ret lu'
             end
         end;
      ret (mkdevice(mktarget lu'))

    | _ => Unknown
  end.

(* ******************** Nand chip driver ********************** *)

Definition nand_read_data (de: device) (addr: prod row_addr col_addr) : result (prod data device) :=
  do d0 <== send_cmd de read_start;
  do d1 <== send_full_addr d0 addr;
  do d2 <== send_cmd d1 read_confirm;
  do d3 <== wait_cmd d2;
  do [d, d4] <== recv_data d3;
  Ok (d, d4).

Definition nand_read_spare (de: device) (row: row_addr) : result (prod data device) :=
  do d0 <== send_cmd de read_start;
  do d1 <== send_full_addr d0 (row, PAGE_DATA_SIZE);
  do d2 <== send_cmd d1 read_confirm;
  do d3 <== wait_cmd d2;
  do [d, d4] <== recv_data d3;
  Ok (d, d4).

Definition nand_write_data (de: device) (addr: prod row_addr col_addr) (d: data) : result device :=
  do d0 <== send_cmd de program_start;
  do d1 <== send_full_addr d0 addr;
  do d2 <== send_data d1 d;
  do d3 <== send_cmd d2 program_confirm;
  do d4 <== wait_cmd d3;
  Ok d4.

Definition nand_erase (de: device) (addr: prod plane_no block_no)  : result device :=
  do d0 <== send_cmd de erase_start;
  do d1 <== send_2cycle_addr d0 (addr);
  do d2 <== send_cmd d1 erase_confirm;
  do d3 <== wait_cmd d2;
  Ok d3.

Definition nand_read_ID (de: device) : result (prod data device)  :=
  do d0 <== send_cmd de read_ID;
  do d1 <== send_1cycle_addr d0 0;
  do [d, d2] <== recv_data d1;
  Ok (d, d2).
  
Definition nand_read_status (d: device): result (prod device_status device) :=
  do d0 <== send_cmd d read_status;
  do [s, d1]  <== recv_status d0;
  Ok (s, d1).

Definition nand_reset (d: device) :result device :=
  do d0 <== send_cmd d reset;
  Ok d0.

(*  -------------------------------------------------------------

  Lemmas 

*)

(*Lemma read_spec: 
  forall c f lbn off d,
    Inv (c, f)
    -> valid_logical_block_no lbn
    -> valid_page_off off
    -> exists c' f',
         FTL_write c f lbn off d = Some (c', f')
         /\ Inv (c', f')
         /\ FTL_read c' f' lbn off = Some d
         /\ (forall off', 
               off' <> off 
               -> FTL_read c' f' lbn off' = FTL_read c f lbn off')
         /\ (forall lbn' off', 
               lbn' <> lbn
               -> FTL_read c' f' lbn' off' = FTL_read c f lbn' off').
Proof.

 test (bvalid_block_no pbn);

*)



Definition valid_block_no (pbn: block_no) := bvalid_block_no pbn = true.

Definition valid_page_off (off: page_off) := bvalid_page_off off = true.

Definition valid_addr (addr: prod row_addr col_addr) := bvalid_addr addr = true.



Lemma nand_read_data_eq_in_same_block : 
  forall c addr c',
    chip_get_block c addr = chip_get_block c' addr
    -> nand_read_data c addr = nand_read_data c' addr.
Proof.



Admitted. 
(*
  intros c addr off c'.
  unfold nand_read_data.
  destruct (bvalid_block_no pbn) eqn:Hpbn.
  rewrite <- Hc.
  trivial.
  trivial.
Qed.
*)




Lemma invalid_off_implies_nand_read_page_none : 
  forall c addr,
    bvalid_addr addr = false
    -> nand_read_data c addr = Unknown.
Proof.
Admitted.

Definition nand_write_data_sem addr c c' pn bn poff col d lu b:=
  (forall pn', 
     pn' <> pn
     -> chip_get_plane c pn' = chip_get_plane c pn)
  /\ (exists pl', 
        chip_get_plane c pn = Some pl'
        /\ exists lu', 
             lu' = chip_lun c'
             /\ (lun_status_SF lu' = false
                /\ (exists b', 
                      plane_get_block pl' bn = Some b'
                      /\ (block_state b' = bs_bad \/ block_state b' = bs_invalid))
                /\ lun_plane0 lu'= lun_plane0 lu
                /\ lun_plane1 lu'= lun_plane1 lu
                /\ lun_cmd_reg lu' = lun_cmd_reg lu
                /\ lun_addr_reg lu' = lun_addr_reg lu
                /\ lun_status_RB lu' = true
                /\ lun_intern_state lu' = lun_idle)
               \/
               (lun_status_SF lu' = true
                /\ (forall addr',
                      addr' <> addr
                      -> chip_get_block c addr' = chip_get_block c' addr'))
             /\ (lun_status_RB lu' = true
                 /\ lun_cmd_reg lu'= None
                 /\ lun_addr_reg lu' = None 
                 /\ lun_intern_state lu' = lun_idle
                 /\ (exists b', 
                       plane_get_block pl' bn = Some b'
                       /\ block_next_page b' = S poff
                       /\ block_erase_count b' = block_erase_count b
                       /\ block_state b' = bs_normal
                       /\ (exists p', block_get_page b' poff = Some p'
                                      /\ p' = mkpage (zero_data(col) ++ d) ps_programmed))
                )
     ).


Lemma nand_write_data_spec:
  forall c addr pn bn poff col pl b p d lu,
    addr = ((mklun_addr pn bn poff),col:col_addr)
    -> lu = chip_lun c
    -> chip_get_plane c pn = Some pl
    -> plane_get_block pl bn = Some b
    -> block_get_page b poff = Some p
    -> bvalid_page_off poff = true
    -> ble_nat (block_next_page b) poff = true
    -> page_state p = ps_free
    -> exists c' , nand_write_data c addr d = Ok c'
                 /\ nand_write_data_sem addr c c' pn bn poff col d lu b.
                    .

               
    
   

Lemma nand_write_data_spec: 
  forall c addr,
    bvalid_addr = true
    -> bvalid_page_off off = true
    -> chip_get_block c pbn = Some b
    -> block_get_page b off = Some p
    -> ble_nat (next_page b) off = true
    -> page_state p = ps_free
    -> exists c', nand_write_page c pbn off d o = Some c'
               /\ (exists b', chip_get_block c' pbn = Some b'
                              /\ next_page b' = S off
                              /\ block_erase_count b' = block_erase_count b
                              /\ block_state b' = bs_programmed
                              /\ (exists p', block_get_page b' off = Some p'
                                            /\ p' = mkpage d o ps_programmed)
                              /\ forall off',
                                   off' <> off 
                                   -> bvalid_page_off off' = true
                                   -> block_get_page b' off' = block_get_page b off')
               /\ (forall pbn', 
                     pbn' <> pbn
                     -> chip_get_block c pbn' = chip_get_block c' pbn').
Proof.
