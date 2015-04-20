(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)


Require Import List.
Require Import ListEx.
Require Import LibEx.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import NandLems.

Require Import Bast0.
Require Import FTLProp.
Require Import FTLLems.

Require Import Inv.

Section INV.
  
  (* Derivable Invariants *)

  Variable bit : block_info_table.
  Variable bmt : block_mapping_table.
  Variable fbq : list block_no.

(* ##BF: if a block is "INVALID" or "ERASED" in BIT, it must be in 
       the free block queue.
 *)

Definition I_pbn_bit_in_fbq : Prop :=
  forall pbn bi,
    bit_get bit pbn = Some bi
    -> bi_state bi = bs_invalid \/ bi_state bi = bs_erased
    -> fbq_in fbq pbn = true.

(* ##BB: if a block is "DATA" or "LOG" in BIT, it must be in 
       the block mapping table.
 *)

Definition I_pbn_bit_in_bmt : Prop :=
  forall pbn bi,
    bit_get bit pbn = Some bi
    -> (forall lbn, bi_state bi = bs_data lbn -> pbn_in_bmt_data bmt lbn pbn)
       /\ (forall lbn pmt, bi_state bi = bs_log lbn pmt -> pbn_in_bmt_log bmt lbn pbn).

(* ##SC: blocks in bmt + blocks in fbq = all blocks 

 *)

Fixpoint count_pbn_in_bmt (bmt: block_mapping_table) : nat :=
  match bmt with
    | nil => 0
    | cons bme bmt' => match bme with
                        | (Some _, Some _) => 2 + count_pbn_in_bmt bmt'
                        | (Some _, None) => 1 + count_pbn_in_bmt bmt'
                        | (None, Some _) => 1 + count_pbn_in_bmt bmt'
                        | _ => count_pbn_in_bmt bmt'
                      end
  end.

Definition I_bmt_count_fbq_len_constant :=
  count_pbn_in_bmt bmt + length fbq = NUM_OF_BLOCKS.

(* ##FC: there are always enough blocks in free block queue.
 *)

Definition I_fbq_len_greater_than_constant : Prop :=
  length fbq >= MIN_FREE_BLOCKS .


End INV.

(* ---------------------------------------------------------------- *)

Lemma I_fbq_len_greater_than_constant_implies_check_freebq_count_abundant : 
  forall fbq,
    I_fbq_len_greater_than_constant fbq
    -> check_freebq_count fbq = fbqs_abundant.
Proof.
  unfold I_fbq_len_greater_than_constant.
  intros.
  unfold check_freebq_count.
  unfold ge in H.
  assert (blt_nat (length fbq) MIN_FREE_BLOCKS = false).
    solvebnat.
  unfold ble_nat.
  rewrite H0.
  trivial.
Qed.

(* ---------------------------------------------------------------- *)

Lemma I_pbn_bit_in_fbq_admissible :
  forall bit bmt fbq,
      I_pbn_bit_valid bit
      -> I_pbn_fbq_valid fbq
      -> I_pbn_fbq_state bit fbq
      -> I_pbn_bmt_used bit bmt
      -> I_pbn_habitation bmt fbq
      -> I_pbn_bit_in_fbq bit fbq.
Proof.
  intros bit bmt fbq HI1 HI3 HI4 HI5 HI6.
  intros pbn bi Hgbi Hbis.
  destruct (HI1 pbn) as [HI11 HI12].
  assert (Hvpbn : valid_block_no pbn).
    apply HI12.
    exists bi; trivial.
  destruct (HI6 pbn Hvpbn) as [HI61 | HI62].
    destruct HI61 as [[lbn Hinbmt] Hnotin].
    destruct Hinbmt as [Hinbmt | Hinbmt].
      destruct (HI5 lbn pbn bi Hgbi) as [HI51 HI52].
      rewrite (HI51 Hinbmt) in Hbis.
      destruct Hbis; discriminate.
    destruct (HI5 lbn pbn bi Hgbi) as [HI51 HI52].
    destruct (HI52 Hinbmt) as [pmt Hpmt]. 
    rewrite Hpmt in Hbis.
    destruct Hbis; discriminate.
  destruct HI62 as [_ H].
  apply H.
Qed.


Lemma I_pbn_bit_in_bmt_admissible :
  forall bit bmt fbq,
      I_pbn_bit_valid bit
      -> I_pbn_fbq_valid fbq
      -> I_pbn_fbq_state bit fbq
      -> I_pbn_bmt_used bit bmt
      -> I_pbn_habitation bmt fbq
      -> I_pbn_bit_in_bmt bit bmt.
Proof.
  intros bit bmt fbq HI1 HI3 HI4 HI5 HI6.
  assert (HIBF : I_pbn_bit_in_fbq bit fbq).
    apply I_pbn_bit_in_fbq_admissible with bmt; trivial.
  unfold I_pbn_bit_in_bmt.
  intros pbn bi Hgbi.
  assert (Hvpbn: valid_block_no pbn).
    destruct (HI1 pbn).
    apply H0.
    exists bi; trivial.
  destruct (HI6 pbn Hvpbn) as [H | H].
    destruct H as [H1 H2].
    destruct  H1 as [lbn' H1].
    destruct (HI5 lbn' pbn bi Hgbi) as [HI51 HI52].
    destruct H1 as [H1 | H1].
      assert (Hbis1 := HI51 H1).
      split.
        intros lbn Hbis2.
        rewrite Hbis1 in Hbis2.
        injection Hbis2; intro; subst lbn'.
        trivial.
      intros lbn pmt Hbis2.
      rewrite Hbis1 in Hbis2.
      discriminate.
    destruct (HI52 H1) as [pmt Hbis1].
    split.
      intros lbn Hbis2.
      rewrite Hbis1 in Hbis2.
      discriminate.
    intros lbn pmt' Hbis2.
    rewrite Hbis1 in Hbis2.
    injection Hbis2; intros; subst lbn' pmt'.
    trivial.
  destruct H as [H1 H2].
  assert (Hbis1 := HI4 pbn bi H2 Hgbi).
  split.
    intros lbn Hbis2.
    destruct Hbis1 as [Hbis1 | Hbis1]; rewrite Hbis1 in Hbis2; discriminate.
  intros lbn pmt Hbis2.
  destruct Hbis1 as [Hbis1 | Hbis1]; rewrite Hbis1 in Hbis2; discriminate.
Qed.

(* ************************************************************************** *)

Lemma count_pbn_in_bmt_is_less_equal_than_2_bmt_len : 
  forall bmt,
    count_pbn_in_bmt bmt <= 2 * bmt_len bmt.
Proof.
  induction bmt.
    simpl.
    omega.
  destruct a as [bmrd bmrl].
  simpl.
  destruct bmrd as [pd | ]; destruct bmrl as [pl | ].
    omega.
    omega.
    omega.
    omega.
Qed.

Fixpoint count_used_blocks (bit: block_info_table) : nat :=
  match bit with
    | nil => 0
    | cons bi bit' => match bi_state bi with
                        | bs_data _ => 1 + count_used_blocks bit'
                        | bs_log _ _ => 1 + count_used_blocks bit'
                        | _ => count_used_blocks bit'
                      end
  end.

Fixpoint count_unused_blocks (bit: block_info_table) : nat :=
  match bit with
    | nil => 0
    | cons bi bit' => match bi_state bi with
                        | bs_invalid => 1 + count_unused_blocks bit'
                        | bs_erased => 1 + count_unused_blocks bit'
                        | _ => count_unused_blocks bit'
                      end
  end.

Lemma  count_bit_is_equal_to_constant: 
  forall bit, 
    count_unused_blocks bit + count_used_blocks bit = length bit.
Proof.
  induction bit.
    simpl; trivial.
  simpl.
  destruct (bi_state a); simpl.
  rewrite IHbit; trivial.
  rewrite IHbit; trivial.
  rewrite <- IHbit.
  omega.
  rewrite <- IHbit.
  omega.
Qed. 
                                           
Lemma bmt_len_is_equal_to_max_lbn : 
  forall bmt,
    I_valid_lbn_has_entry_in_bmt bmt (* I10 *)
    -> bmt_len bmt = MAX_LOGICAL_BLOCKS.
Proof.
  unfold bmt_len.
  unfold I_valid_lbn_has_entry_in_bmt.
  unfold bmt_get.
  intros bmt HI10.
  apply length_intro.
  intros i.
  destruct (HI10 i) as [H1 H2].
  split.
    intros.
    apply (H1 H).
  intro Hblt.
  destruct (list_get bmt i) eqn:Hget; trivial.
  unfold valid_logical_block_no in H2.
  unfold bvalid_logical_block_no in H2.
  rewrite Hblt in H2.
  discriminate H2. 
  exists b; trivial.
Qed.

Definition get_unused_blocks_list (bit: block_info_table) : list block_no :=
  list_filter_domain bit (fun bi => match bi_state bi with 
                                      | bs_invalid => true 
                                      | bs_erased => true 
                                      | _ => false 
                                    end) 0.

Lemma get_unused_blocks_bit_length : 
  forall bit base,
    length (list_filter_domain bit (fun bi => match bi_state bi with 
                                      | bs_invalid => true 
                                      | bs_erased => true 
                                      | _ => false 
                                    end) base ) = count_unused_blocks bit.
Proof. 
  unfold get_unused_blocks_list.
  induction bit.
    simpl; trivial.
  simpl.
  intros base.
  destruct (bi_state a); simpl.
  rewrite IHbit.
  trivial.
  rewrite IHbit.
  trivial.
  rewrite IHbit.
  trivial.
  rewrite IHbit.
  trivial.
Qed.

Lemma get_unused_blocks_list_elim :
  forall bit pbn ,
    list_inb beq_nat (get_unused_blocks_list bit) pbn = true 
    -> exists bi, bit_get bit pbn = Some bi
                  /\ (bi_state bi = bs_invalid \/ bi_state bi = bs_erased).
Proof.
  unfold get_unused_blocks_list.
  intros bit pbn Hget.
  destruct (@list_filter_domain_elim _ bit pbn 0 _ beq_nat Hget) as [bi [H1 H2]].
    apply neq_beq_false.
    apply beq_true_eq.
  exists bi.
  split; trivial.
  destruct (bi_state bi); try discriminate.
  left; trivial.
  right; trivial.
Qed.

Lemma get_unused_blocks_list_subset_fbq :
  forall bit fbq l,
    I_pbn_bit_in_fbq bit fbq  (* $IBF *)
    -> l = get_unused_blocks_list bit
    -> forall pbn,
         list_inb beq_nat l pbn = true 
         -> fbq_in fbq pbn = true.
Proof.
  intros bit fbq l HIBF Hl pbn Hinb.
  unfold I_pbn_bit_in_fbq in HIBF.
  rewrite Hl in Hinb.
  destruct (get_unused_blocks_list_elim _ _ Hinb) as [bi [Hgetbi Hbis]].
  apply HIBF with bi; trivial.
Qed.

Definition get_used_blocks_list (bit: block_info_table) : list block_no :=
  list_filter_domain bit (fun bi => match bi_state bi with 
                                      | bs_data _ => true 
                                      | bs_log _ _ => true 
                                      | _ => false 
                                    end) 0.

Lemma get_used_blocks_bit_length :
  forall bit base,
    length (list_filter_domain bit (fun bi => match bi_state bi with 
                                      | bs_data _  => true 
                                      | bs_log _ _ => true 
                                      | _ => false 
                                    end) base) = count_used_blocks bit.
Proof.
  induction bit.
    simpl; trivial.
  simpl.
  intros base.
  destruct (bi_state a); simpl.
  rewrite IHbit.
  trivial.
  rewrite IHbit.
  trivial.
  rewrite IHbit.
  trivial.
  rewrite IHbit.
  trivial.
Qed.

Lemma length_get_used_block_in_bit_is_equal_to_count_used_blocks :
  forall bit,
    length (get_used_blocks_list bit) = count_used_blocks bit.
Proof.
  unfold get_used_blocks_list.
  intro bit.
  rewrite <- (get_used_blocks_bit_length bit 0).
  trivial.
Qed.

Lemma list_unique_get_unused_blocks :
  forall bit,
    list_unique beq_nat (get_unused_blocks_list bit) = true.
Proof.
  unfold get_unused_blocks_list.
  intros.
  apply list_unique_list_filter_domain.
Qed.

Lemma length_unused_blocks_is_equal_to_length_fbq :
  forall bit fbq,
    I_pbn_bit_in_fbq bit fbq  (* $IBF *)
    -> I_pbn_bit_valid bit (* I1 *)
    -> I_pbn_fbq_valid fbq (* I3 *)
    -> I_pbn_fbq_state bit fbq (* I4 *)
    -> I_pbn_fbq_distinguishable fbq (* I8 *)
    -> length (get_unused_blocks_list bit) = length fbq.
Proof.
  intros bit fbq HIBF HI1 HI3 HI4 HI8.
  apply (@list_length_after_permutation _ (get_unused_blocks_list bit) fbq beq_nat).
  
  apply list_unique_get_unused_blocks; trivial.

  apply list_unique_intro.
    apply beq_false_neq.
    apply beq_true_eq.
  intros i1 i2 a1 a2 Hneq Hgi1 Hgi2.
  unfold I_pbn_fbq_distinguishable in HI8.
  apply HI8 with i1 i2; trivial.

  intros i a Hg.
  apply get_unused_blocks_list_subset_fbq with bit ((get_unused_blocks_list bit)); trivial.
  apply list_inb_true_intro with i; trivial.
  apply beq_false_neq.

  intros i pbn Hg.
  assert (Hfbqin : fbq_in fbq pbn = true).
    apply list_inb_true_intro with i; trivial.
    apply beq_false_neq.
  destruct (proj1 (HI1 pbn) (HI3 pbn Hfbqin)) as [bi Hgbi].
  unfold get_unused_blocks_list.
  assert (pbn = 0 + pbn).
    simpl; trivial.
  rewrite H.
  apply (@list_filter_domain_intro _ bit pbn 0 _ beq_nat bi); trivial.
  destruct (HI4 pbn bi Hfbqin Hgbi) as [H1 | H1]; rewrite H1; trivial.
  apply neq_beq_false.
  
  apply eq_beq_true.
  
  apply beq_false_neq.

  apply beq_true_eq.
Qed.

Definition get_pbn_from_bmt (bmt: block_mapping_table) : list block_no :=
  list_opt_dual_filter bmt (fun (pbn : block_no) => true).

Lemma length_get_pbn_from_bmt_is_equal_to_count_pbn_in_bmt :
  forall bmt,
    length (get_pbn_from_bmt bmt) = count_pbn_in_bmt bmt.
Proof.
  induction bmt.
    simpl.
    trivial.
  unfold get_pbn_from_bmt in * .
  simpl.
  destruct a as [bmrd bmrl].
  destruct bmrd; destruct bmrl; simpl.
  rewrite IHbmt; trivial.
  rewrite IHbmt; trivial.
  rewrite IHbmt; trivial.
  rewrite IHbmt; trivial.
Qed.

Lemma list_unique_get_used_blocks :
  forall bit,
    list_unique beq_nat (get_used_blocks_list bit) = true.
Proof.
  unfold get_used_blocks_list.
  intros.
  apply list_unique_list_filter_domain.
Qed.

Lemma get_pbn_from_bmt_subset_bmt : 
  forall bmt pbn,
    list_inb beq_nat (get_pbn_from_bmt bmt) pbn = true
    -> exists lbn, pbn_in_bmt_lbn bmt lbn pbn.
Proof.
  induction bmt as [ | bmr bmt].
    simpl.
    intros; discriminate.
  intros pbn Hinb.
  unfold get_pbn_from_bmt in * .
  destruct bmr as [bmrd bmrl].
  assert (Hx: forall bmrd bmt lbn pbn, 
            pbn_in_bmt_lbn bmt lbn pbn 
            -> pbn_in_bmt_lbn (bmrd :: bmt) (S lbn) pbn).
    clear.
    intros.
    destruct H as [H | H]; destruct H; unfold bmt_get in H.
      left; exists x; unfold bmt_get; simpl; trivial.
    right; exists x; unfold bmt_get; simpl; trivial.
  destruct bmrd as [bd | ]; destruct bmrl as [bl | ]; simpl in * .
  
  destruct (beq_nat pbn bd) eqn:Hbd.
    rewrite (beq_true_eq _ _ Hbd).
    exists 0; simpl.
    left; exists (Some bl); trivial.
  destruct (beq_nat pbn bl) eqn:Hbl.
    rewrite (beq_true_eq _ _ Hbl).
    exists 0; simpl.
    right; exists (Some bd). 
    unfold bmt_get; simpl; trivial.
  destruct (IHbmt pbn Hinb) as [lbn IH].
  exists (S lbn).
  apply Hx; trivial.

  destruct (beq_nat pbn bd) eqn:Hbd.
    rewrite (beq_true_eq _ _ Hbd).
    exists 0; simpl.
    left; exists None; trivial.
  destruct (IHbmt pbn Hinb) as [lbn IH].
  exists (S lbn).
  apply Hx; trivial.

  destruct (beq_nat pbn bl) eqn:Hbl.
    rewrite (beq_true_eq _ _ Hbl).
    exists 0; simpl.
    right; exists None. 
    unfold bmt_get; simpl; trivial.
  destruct (IHbmt pbn Hinb) as [lbn IH].
  exists (S lbn).
  apply Hx; trivial.

  destruct (IHbmt pbn Hinb) as [lbn IH].
  exists (S lbn).
  apply Hx; trivial.
Qed.

Lemma bmt_subset_get_pbn_from_bmt : 
  forall bmt pbn lbn,
    pbn_in_bmt_lbn bmt lbn pbn
    -> list_inb beq_nat (get_pbn_from_bmt bmt) pbn = true.
Proof.
  induction bmt as [ | bmr bmt].
    simpl.
    intros.
    destruct H.
      destruct H.
        unfold bmt_get in H.
        simpl in H.
        destruct lbn; discriminate.
      destruct H.
      unfold bmt_get in H.
      simpl in H.
      destruct lbn; discriminate.
  intros.
  unfold get_pbn_from_bmt.
  simpl.
  destruct bmr as [bmrd bmrl].
  destruct bmrd as [bd |]; destruct bmrl as [bl |].
  
  simpl.
  destruct (beq_nat pbn bd) eqn:Hbd; trivial.
  destruct (beq_nat pbn bl) eqn:Hbl; trivial.
  destruct H.
    destruct H.
      unfold bmt_get in H.
      simpl in H.
      destruct lbn.
        injection H; intros; subst x pbn.
        apply False_ind.
        apply beq_false_neq with bd bd; trivial.
      unfold get_pbn_from_bmt in IHbmt.  
      rewrite (IHbmt pbn lbn); trivial.
      left.
      exists x; trivial.
    destruct H.
    unfold bmt_get in H.
    destruct lbn.
      injection H; intros; subst x pbn.
      apply False_ind.
      apply beq_false_neq with bl bl; trivial.
      unfold get_pbn_from_bmt in IHbmt.  
      rewrite (IHbmt pbn lbn); trivial.
      right.
      exists x; trivial.
  
  simpl.
  destruct (beq_nat pbn bd) eqn:Hbd; trivial.
  destruct H.
    destruct H.
    unfold bmt_get in H.
    simpl in H.
    destruct lbn.
      injection H; intros; subst x pbn.
      apply False_ind.
      apply beq_false_neq with bd bd; trivial.
    unfold get_pbn_from_bmt in IHbmt.  
    rewrite (IHbmt pbn lbn); trivial.
    left.
    exists x; trivial.
  destruct H.
  unfold bmt_get in H.
  destruct lbn.
    simpl in H.
    discriminate.
  simpl in H.
  unfold get_pbn_from_bmt in IHbmt.  
  rewrite (IHbmt pbn lbn); trivial.
  right.
  exists x; trivial.

  simpl.
  destruct (beq_nat pbn bl) eqn:Hbl; trivial.
  destruct H.
    destruct H.
    unfold bmt_get in H.
    simpl in H.
    destruct lbn.
      discriminate.
    unfold get_pbn_from_bmt in IHbmt.  
    rewrite (IHbmt pbn lbn); trivial.
    left.
    exists x; trivial.
  destruct H.
  unfold bmt_get in H.
  destruct lbn.
    simpl in H.
    injection H; intros; subst x pbn.
    apply False_ind.
    apply beq_false_neq with bl bl; trivial.
  unfold get_pbn_from_bmt in IHbmt.  
  rewrite (IHbmt pbn lbn); trivial.
  right.
  exists x; trivial.

  destruct H.
    destruct H.
    destruct lbn.
      unfold bmt_get in H.
      simpl in H.
      discriminate.
    unfold get_pbn_from_bmt in IHbmt.
    rewrite (IHbmt pbn lbn); trivial.
    unfold bmt_get in H.
    simpl in H.
    left; exists x; trivial.
  destruct H.
  destruct lbn.
    unfold bmt_get in H.
    simpl in H.
    discriminate.
  unfold get_pbn_from_bmt in IHbmt.
  rewrite (IHbmt pbn lbn); trivial.
  unfold bmt_get in H.
  simpl in H.
  right; exists x; trivial.
Qed.

Lemma list_unique_get_pbn_from_bmt : 
  forall bmt,
    I_pbn_bmt_distinguishable bmt (* I7_1 *)
    -> I_pbn_bmt_distinguishable_2 bmt (* I7_2 *)
    -> list_unique beq_nat (get_pbn_from_bmt bmt) = true.
Proof.
  induction bmt as [ | bmr bmt].
    simpl.
    intros; trivial.
  unfold get_pbn_from_bmt.
  simpl.
  intros HI71 HI72.
  destruct bmr as [bmrd bmrl].
  destruct bmrd as [ bd| ]; destruct bmrl as [bl | ].
 
  simpl.
  assert (Hneq: beq_nat bd bl = false).
    assert (Hx := HI72 0 bd bl).
    unfold bmt_get in Hx.
    simpl in Hx.
    apply neq_beq_false.
    apply Hx; trivial.
  rewrite Hneq.
  destruct (list_inb beq_nat (list_opt_dual_filter bmt (fun _ : block_no => true)) bd) eqn:Hinb.
    destruct (get_pbn_from_bmt_subset_bmt _ _ Hinb) as [lbn Hlbn].
    assert (Hx := HI71 0 (S lbn) bd bd).
    apply False_ind.
    apply Hx; trivial.
    unfold pbn_in_bmt_lbn.
    left.
    exists (Some bl).
    unfold bmt_get.
    simpl.
    trivial.
  destruct (list_inb beq_nat (list_opt_dual_filter bmt (fun _ : block_no => true)) bl) eqn:Hinbl.
    destruct (get_pbn_from_bmt_subset_bmt _ _ Hinbl) as [lbn Hlbn].
    assert (Hx := HI71 0 (S lbn) bl bl).
    apply False_ind.
    apply Hx; trivial.
    unfold pbn_in_bmt_lbn.
    right.
    exists (Some bd).
    unfold bmt_get.
    simpl.
    trivial.
  apply IHbmt; simpl.
    intros lbn1 lbn2 pbn1 pbn2 Hln Hpbn1 Hpbn2.
    apply (HI71 (S lbn1) (S lbn2) pbn1 pbn2); trivial.
    intro HF; injection HF; apply Hln; trivial.
    intros lbn pbn1 pbn2 Hg.
    apply (HI72 (S lbn) pbn1 pbn2).
    unfold bmt_get.
    simpl.
    trivial.
  
  simpl.
  destruct (list_inb beq_nat (list_opt_dual_filter bmt (fun _ : block_no => true)) bd) eqn:Hinb.
    destruct (get_pbn_from_bmt_subset_bmt _ _ Hinb) as [lbn Hlbn].
    assert (Hx := HI71 0 (S lbn) bd bd).
    apply False_ind.
    apply Hx; trivial.
    unfold pbn_in_bmt_lbn.
    left.
    exists None.
    unfold bmt_get.
    simpl.
    trivial.
  apply IHbmt; simpl.
    intros lbn1 lbn2 pbn1 pbn2 Hln Hpbn1 Hpbn2.
    apply (HI71 (S lbn1) (S lbn2) pbn1 pbn2); trivial.
    intro HF; injection HF; apply Hln; trivial.
    intros lbn pbn1 pbn2 Hg.
    apply (HI72 (S lbn) pbn1 pbn2).
    unfold bmt_get.
    simpl.
    trivial.
  
  simpl.
  destruct (list_inb beq_nat (list_opt_dual_filter bmt (fun _ : block_no => true)) bl) eqn:Hinbl.
    destruct (get_pbn_from_bmt_subset_bmt _ _ Hinbl) as [lbn Hlbn].
    assert (Hx := HI71 0 (S lbn) bl bl).
    apply False_ind.
    apply Hx; trivial.
    unfold pbn_in_bmt_lbn.
    right.
    exists None.
    unfold bmt_get.
    simpl.
    trivial.
  apply IHbmt; simpl.
    intros lbn1 lbn2 pbn1 pbn2 Hln Hpbn1 Hpbn2.
    apply (HI71 (S lbn1) (S lbn2) pbn1 pbn2); trivial.
    intro HF; injection HF; apply Hln; trivial.
    intros lbn pbn1 pbn2 Hg.
    apply (HI72 (S lbn) pbn1 pbn2).
    unfold bmt_get.
    simpl.
    trivial.

  apply IHbmt; simpl.
    intros lbn1 lbn2 pbn1 pbn2 Hln Hpbn1 Hpbn2.
    apply (HI71 (S lbn1) (S lbn2) pbn1 pbn2); trivial.
    intro HF; injection HF; apply Hln; trivial.
    intros lbn pbn1 pbn2 Hg.
    apply (HI72 (S lbn) pbn1 pbn2).
    unfold bmt_get.
    simpl.
    trivial.
Qed.


Lemma get_used_blocks_list_elim :
  forall bit pbn ,
    list_inb beq_nat (get_used_blocks_list bit) pbn = true 
    -> exists bi, bit_get bit pbn = Some bi
                  /\ ((exists lbn, bi_state bi = bs_data lbn) \/ (exists lbn pmt, bi_state bi = bs_log lbn pmt)).
Proof.
  unfold get_used_blocks_list.
  intros bit pbn Hget.
  destruct (@list_filter_domain_elim _ bit pbn 0 _ beq_nat Hget) as [bi [H1 H2]].
    apply neq_beq_false.
    apply beq_true_eq.
  exists bi.
  split; trivial.
  destruct (bi_state bi); try discriminate.
  left.
  exists lbn; trivial.
  right.
  exists lbn, pmt; trivial.
Qed.


Lemma get_used_blocks_list_subset_get_pbn_from_bmt :
  forall bit bmt l,
    I_pbn_bit_in_bmt bit bmt  (* $IBB *)
    -> l = get_used_blocks_list bit
    -> forall pbn,
         list_inb beq_nat l pbn = true 
         -> list_inb beq_nat (get_pbn_from_bmt bmt) pbn = true.
Proof.
  intros bit bmt l HIBB Hl pbn Hinb.
  unfold I_pbn_bit_in_bmt in HIBB.
  rewrite Hl in Hinb.
  destruct (get_used_blocks_list_elim _ _ Hinb) as [bi [Hgetbi Hbis]].
  destruct Hbis as [H1 | H2].
    destruct H1 as [lbn H1].
    apply bmt_subset_get_pbn_from_bmt with lbn; trivial.
    destruct (HIBB pbn bi Hgetbi) as [Hx Hy].
    left.    
    apply (Hx lbn); trivial.
  destruct H2 as [lbn [pmt H2]].
  apply bmt_subset_get_pbn_from_bmt with lbn; trivial.
  destruct (HIBB pbn bi Hgetbi) as [Hx Hy].
  right.    
  apply (Hy lbn pmt); trivial.
Qed.

Lemma length_get_used_blocks_in_bit_is_equal_to_get_pbn_from_bmt :
  forall bit bmt,
    I_pbn_bit_in_bmt bit bmt  (* $IBB *)
    -> I_pbn_bit_valid bit (* I1 *)
    -> I_pbn_bmt_valid bmt (* I2 *)
    -> I_pbn_bmt_used bit bmt (* I5 *)
    -> I_pbn_bmt_distinguishable bmt (* I7_1 *)
    -> I_pbn_bmt_distinguishable_2 bmt (* I7_2 *)
    -> length (get_used_blocks_list bit) = length (get_pbn_from_bmt bmt).
Proof.
  intros bit bmt HIBB HI1 HI2 HI5 HI7_1 HI7_2.
  apply (@list_length_after_permutation _ (get_used_blocks_list bit) (get_pbn_from_bmt bmt) beq_nat).

  apply list_unique_get_used_blocks; trivial.

  apply list_unique_get_pbn_from_bmt; trivial.

  intros i a Hg.
  apply get_used_blocks_list_subset_get_pbn_from_bmt with bit (get_used_blocks_list bit); trivial .
  apply list_inb_true_intro with i; trivial.
  apply beq_false_neq.

  intros i pbn Hg.
  assert (Hx : list_inb beq_nat (get_pbn_from_bmt bmt) pbn = true).
    apply list_inb_true_intro with i; trivial.
    apply beq_false_neq.
  destruct (get_pbn_from_bmt_subset_bmt bmt pbn Hx) as [lbn Hin].
  assert (Hvpbn := HI2 _ _ Hin).
  destruct (proj1 (HI1 pbn)  Hvpbn) as [bi Hgbi].
  unfold get_used_blocks_list.
  assert (Ha : pbn = 0 + pbn).
    simpl; trivial.
  rewrite Ha.
  apply (@list_filter_domain_intro _ bit pbn 0 _ beq_nat bi); trivial.
    destruct (HI5 lbn pbn bi Hgbi) as [HI51 HI52].
    destruct Hin as [Hin | Hin].
      rewrite (HI51 Hin); trivial.
    destruct (HI52 Hin) as [pmt Hbis].
    rewrite Hbis; trivial.
    apply neq_beq_false.
    apply eq_beq_true.
  
  apply beq_false_neq.
  apply beq_true_eq.
Qed.


Lemma length_bit_is_equal_to_max_blocks : 
  forall bit, 
    I_pbn_bit_valid bit
    -> length bit = BLOCKS.
Proof.
  unfold I_pbn_bit_valid.
  unfold bit_get.
  intros bit HI1.
  apply length_intro.
  intros i.
  destruct (HI1 i) as [H1 H2].
  split.
    intros.
    apply (H1 H).
  intro Hblt.
  destruct (list_get bit i) eqn:Hget; trivial.
  unfold valid_block_no in H2.
  unfold bvalid_block_no in H2.
  rewrite Hblt in H2.
  discriminate H2. 
  exists b; trivial.
Qed.                                            

Lemma I_bmt_count_fbq_len_constant_derivable :
  forall bit bmt fbq,
    I_pbn_bit_valid bit (* I1 *)
    -> I_pbn_bmt_valid bmt (* I2 *)
    -> I_pbn_fbq_valid fbq (* I3 *)
    -> I_pbn_fbq_state bit fbq (* I4 *)
    -> I_pbn_bmt_used bit bmt (* I5 *)
    -> I_pbn_habitation bmt fbq (* I6 *)
    -> I_pbn_bmt_distinguishable bmt (* I7_1 *)
    -> I_pbn_bmt_distinguishable_2 bmt (* I7_2 *)
    -> I_pbn_fbq_distinguishable fbq (* I8 *)
    -> I_valid_lbn_has_entry_in_bmt bmt (* I10 *)
    -> I_bmt_count_fbq_len_constant bmt fbq .
Proof.
  intros bit bmt fbq HI1 HI2 HI3 HI4 HI5 HI6 HI71 HI72 HI8 HI10.
  unfold I_bmt_count_fbq_len_constant.
  assert (Hc := count_bit_is_equal_to_constant bit).
  assert (HBF : I_pbn_bit_in_fbq bit fbq). 
    apply I_pbn_bit_in_fbq_admissible with bmt; trivial.
  assert (HBB : I_pbn_bit_in_bmt bit bmt). 
    apply I_pbn_bit_in_bmt_admissible with fbq; trivial.
  assert (Hfbq : length (get_unused_blocks_list bit) = length fbq). 
    apply (length_unused_blocks_is_equal_to_length_fbq bit fbq); trivial.
  assert (H1 : length (get_unused_blocks_list bit) = count_unused_blocks bit). 
    unfold get_unused_blocks_list.
    rewrite get_unused_blocks_bit_length; trivial.
  rewrite H1 in Hfbq.
  assert (Hbmtlen : bmt_len bmt = MAX_LOGICAL_BLOCKS).
    apply bmt_len_is_equal_to_max_lbn; trivial.
  assert (Hbitlen : length bit = NUM_OF_BLOCKS).
    rewrite length_bit_is_equal_to_max_blocks; trivial.
  rewrite Hbitlen in Hc.
  rewrite Hfbq in Hc.
  rewrite <- (length_get_used_block_in_bit_is_equal_to_count_used_blocks bit) in Hc.
  rewrite (length_get_used_blocks_in_bit_is_equal_to_get_pbn_from_bmt bit bmt) in Hc; trivial.
  rewrite length_get_pbn_from_bmt_is_equal_to_count_pbn_in_bmt in Hc.
  omega.
Qed.

Lemma I_fbq_len_greater_than_constant_derivable :
  forall bit bmt fbq,
    I_pbn_bit_valid bit (* I1 *)
    -> I_pbn_bmt_valid bmt (* I2 *)
    -> I_pbn_fbq_valid fbq (* I3 *)
    -> I_pbn_fbq_state bit fbq (* I4 *)
    -> I_pbn_bmt_used bit bmt (* I5 *)
    -> I_pbn_habitation bmt fbq (* I6 *)
    -> I_pbn_bmt_distinguishable bmt (* I7_1 *)
    -> I_pbn_bmt_distinguishable_2 bmt (* I7_2 *)
    -> I_pbn_fbq_distinguishable fbq (* I8 *)
    -> I_valid_lbn_has_entry_in_bmt bmt (* I10 *)
    -> I_fbq_len_greater_than_constant fbq.
Proof.
  intros bit bmt fbq HI1 HI2 HI3 HI4 HI5 HI6 HI71 HI72 HI8 HI10.
  unfold I_fbq_len_greater_than_constant.
  assert (HSC: I_bmt_count_fbq_len_constant bmt fbq).
    apply I_bmt_count_fbq_len_constant_derivable with bit; trivial.
  unfold I_bmt_count_fbq_len_constant in HSC.
  assert (Hbmtlen : bmt_len bmt = MAX_LOGICAL_BLOCKS).
    apply bmt_len_is_equal_to_max_lbn; trivial.
  assert (Hbit : length bit >= MIN_FREE_BLOCKS + 2 * (bmt_len bmt)).
    rewrite length_bit_is_equal_to_max_blocks; trivial.
    rewrite Hbmtlen.
    apply PBN_is_greater_than_2_LBN.
  assert (Hbitlen : length bit = NUM_OF_BLOCKS).
    rewrite length_bit_is_equal_to_max_blocks; trivial.
  rewrite Hbitlen in Hbit.
  assert (Hbmtcnt:= count_pbn_in_bmt_is_less_equal_than_2_bmt_len bmt).
  omega.
Qed.
