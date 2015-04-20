(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import LibEx.
Require Import List.
Require Import ListEx.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import Bast0.
Require Import FTLProp.
Require Import FTLLems.
Require Import FTLLems2.

Require Import Inv.
Require Import InvLems.
Require Import Inv2.

(* Require Import Framework. *)

Lemma ftl_write_spec: 
  forall c f lbn off d,
    Inv c f
    -> valid_logical_block_no lbn
    -> valid_page_off off
    -> exists c' f',
         FTL_write c f lbn off d = Some (c', f')
         /\ Inv c' f'
         /\ FTL_read c' f' lbn off = Some d
         /\ (forall off', 
               off' <> off 
               -> FTL_read c' f' lbn off' = FTL_read c f lbn off')
         /\ (forall lbn' off', 
               lbn' <> lbn
               -> FTL_read c' f' lbn' off' = FTL_read c f lbn' off').
Proof.
  intros c f lbn off d HI Hlbn Hoff.
  destruct HI as [HFI HRI].
  destruct HFI as [HI1 [HI2 [HI3 [HI4 [HI5 [HI6 [HI7_1 [HI7_2 [HI8 HI10]]]]]]]]].
  unfold R_Inv in HRI.
  rename HRI into HJ.
  unfold FTL_write.
  destruct f as [bit bmt fbq].
  simpl in * .
  destruct ((proj1 (HI10 lbn)) Hlbn) as [bme Hbme].
  destruct bme as [bmd bmr].
  destruct bmd as [pbn_data | ]; destruct bmr as [pbn_log | ].

  (* case 1: bmt_get lbn = ( pbn_data, pbn_log )  *)
  assert (Hbdinbmt : pbn_in_bmt_lbn bmt lbn pbn_data).
    left. exists (Some pbn_log). trivial.
  assert (Hblinbmt : pbn_in_bmt_lbn bmt lbn pbn_log).
    right. exists (Some pbn_data). trivial.
  assert (Hbd: valid_block_no pbn_data).
    apply (HI2 lbn pbn_data); trivial.
  assert (Hbl: valid_block_no pbn_log).
    apply (HI2 lbn pbn_log); trivial.
  rewrite Hbme.
  destruct (HI1 pbn_log) as [Hx _].
  destruct (Hx Hbl) as [bi_log Hbil].
  clear Hx.
  rewrite Hbil.
  destruct (check_block_is_full bi_log) eqn:Hcklog.

    (* case 1 - 1, log block is full *)
    assert (HInv: Inv c (mk_FTL bit bmt fbq)).
      unfold Inv, F_Inv, R_Inv.
      simpl.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
    destruct (merge_block_case1_spec c (mk_FTL bit bmt fbq) lbn pbn_data pbn_log HInv Hlbn Hbme)
        as [c' [f' [Hm [HI' [[bfx [Hbmt'1 Hbmt'2]] [Hlen Hread]]]]]].
    rewrite Hm.
    clear HI1 HI2 HI3 HI4 HI5 HI6 HI7_1 HI7_2 HI8 HI10 HJ HInv.
    destruct HI' as [HFI' HRI'].
    destruct HFI' as [HI1' [HI2' [HI3' [HI4' [HI5' [HI6' [HI7_1' [HI7_2' [HI8' HI10']]]]]]]]].
    unfold R_Inv in HRI'.
    rename HRI' into HJ'.
    destruct f' as [bit' bmt' fbq'].
    simpl in * .
    assert (HSC': I_fbq_len_greater_than_constant fbq').
      apply (I_fbq_len_greater_than_constant_derivable bit' bmt'); trivial.
    destruct (alloc_block_spec c' bit' bmt' fbq' HI1' HI3' HI4' HI8' HSC' HJ')
      as [pf [c2 [f2 [bif2 [Ha [Hpf [Hbif2 [Hc'c2_1 [Hc'c2_2 [Hc'c2_3 [Hbmt2 [Hbit2 [Hfbq2 HJc2]]]]]]]]]]]]].
    rewrite Ha.
    destruct f2 as [bit2 bmt2 fbq2].
    simpl in * .
    assert (Hbif2get: bit_get bit2 pf = Some bif2).
      apply (bit_update_bit_get_eq bit'); trivial.
    rewrite Hbif2get.
    set (bi2 := bi_set_state bif2 (bs_log lbn blank_pmt)).
    assert (exists b2, chip_get_block c2 pf = Some b2
                       /\ (bi_state bi2 = bs_log lbn blank_pmt
                           /\ bi_used_pages bi2 = next_page b2
                           /\ block_state b2 = bs_free
                           /\ next_page b2 = 0
                           /\ (forall loc,
                                 valid_page_off loc
                                 -> exists p, block_get_page b2 loc = Some p
                                              /\ page_state p = ps_free))).
      unfold J_bi_block_coherent in HJc2.
      unfold chip_bi_coherent in HJc2.
      destruct (HJc2 pf bif2 Hbif2get) as [b2 [Hb2 Hco2]].
      destruct Hbif2 as [Hbif2_1 Hbif2_2].
      rewrite Hbif2_1 in Hco2.
      exists b2.
      split; trivial.
      subst bi2.
      unfold bi_state, bi_set_state.
      simpl.
      split; trivial.
      unfold block_coherent_erased in Hco2.
      destruct Hco2 as [Hx1 [Hx2 [Hx3 [Hx4 Hx5]]]].
      rewrite Hx2.
      split; trivial.
      split; trivial.
      split; trivial.
    destruct H as [b2 [Hgetb2 Hb2_2]].
    destruct (write_log_block_spec_write_emp c2 pf b2 bi2 off lbn d Hgetb2 Hpf Hoff Hb2_2)
      as [c3 [bi3 [Hw [Hbi3_1 [Hbi3_2 [Hbi3_3 [Hco3 [Hrc3 [Hr Hc2c3]]]]]]]]].
    rewrite Hw.
    
    assert (Hbmt2get: bmt_get bmt2 lbn = Some (Some bfx, None)).
      rewrite Hbmt2.
      trivial.
    destruct (bmt_update_log_spec bmt2 lbn pf (Some bfx, None) Hbmt2get)
        as [bmt3 [Hbmtup [Hbmt3_1 Hbmt3_2]]].
    rewrite Hbmtup.
    rewrite Hoff.
    destruct (bit_update_spec bit2 pf bif2 bi3 Hbif2get) as [bit3 [Hbit3 [Hbi3get Hbit3_2]]].
    rewrite Hbit3.
    exists c3, (mk_FTL bit3 bmt3 fbq2).
    split; trivial.
    split.

      (* case <1> (Some bd, Some bl) ==> <1> (log block is full) ==> <1> Inv (c', f') *)
      split.
        (* F_Inv preservation *)
        unfold F_Inv.
        simpl.
        split. (* I1 *)
          apply (I_pbn_bit_valid_preserv_bit_update pf bit2 bi3 bit3); auto.
          apply (I_pbn_bit_valid_preserv_bit_update pf bit' bif2 bit2); auto.
        split. (* I2 *)
          subst bmt2.
          apply (I_pbn_bmt_valid_preserv_bmt_update_log bmt' lbn pf bmt3); auto.
        split. (* I3 *)
          apply (I_pbn_fbq_valid_preserv_fbq_deq fbq' pf fbq2 HI3'); auto.
          destruct Hfbq2 as [_ [_ Hdeq]].
          trivial.
        split. (* I4 *)
          destruct Hfbq2 as [H1 [H2 Hdeq]].
          apply (I_pbn_fbq_state_preserv_bit_update bit2 fbq2 pf bi3 bit3); auto.
          apply (I_pbn_fbq_state_preserv_bit_update bit' fbq2 pf bif2 bit2); auto.
          apply (I_pbn_fbq_state_preserv_fbq_deq bit' fbq' pf fbq2); trivial.
        split. (* I5 *)
          assert (Hst: exists pmt, bi_state bi3 = bs_log lbn pmt).
            destruct Hco3 as [b' [Hb' Hco']].
            unfold block_coherent_log in Hco'.
            destruct Hco' as [pmt [lbnx [Hbss _]]].
            unfold bi_lbn in Hbi3_2.
            rewrite Hbss in Hbi3_2.
            injection Hbi3_2.
            intro Hlbnx; subst lbnx.
            exists pmt. 
            trivial.
          destruct Hst as [pmt Hst].
          apply (I_pbn_bmt_used_preserv_bmt_update_log bit2 bmt2 pf lbn bi3 pmt bit3 bmt3); trivial.
          subst bmt2.
          apply (I_pbn_bmt_used_preserv_bit_update_irre bit' bmt' pf bif2 bit2 HI5' Hbit2); trivial.
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
          destruct Hfbq2 as [Hfbq' _].
          trivial.
          subst bmt2.
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
          destruct Hfbq2 as [Hfbq' _].
          trivial.
        split. (* I6 *)
          destruct Hfbq2 as [_ [_ Hfbq2]].
          simpl in Hbmt3_1.
          subst bmt'.
          apply (I_pbn_habitation_preserv_bmt_update_log bmt2 fbq' lbn bfx pf bmt3 fbq2); trivial.
          apply (HI2' lbn bfx).
          left; exists None; trivial.
        split. (* I7_1 *)
          subst bmt2.
          apply (I_pbn_bmt_distinguishable_preserv_bmt_update_log bmt' lbn pf bmt3 HI7_1'); trivial.
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
          destruct Hfbq2 as [Hfbq' _].
          trivial.
        split. (* I7_2 *)
          subst bmt2.
          apply (I_pbn_bmt_distinguishable_2_preserv_bmt_update_log bmt' lbn pf bmt3 HI7_2' Hbmtup); trivial.
          destruct Hfbq2 as [Hfbq' _].
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
        split. (* I8 *)
          destruct Hfbq2 as [_ [_ Hfbq2]].
          apply (I_pbn_fbq_distinguishable_preserv_fbq_deq fbq' pf fbq2 HI8' Hfbq2); trivial.
        (* I10 *)
        subst bmt2.
        apply (I_valid_lbn_has_entry_in_bmt_preserv_bmt_update_log bmt' lbn pf bmt3 HI10' Hbmtup); trivial.
      (* R_Inv *)
      unfold R_Inv.
      simpl.

      destruct Hco3 as [b' [Hgetb' Hco3]].
      apply (J_bi_block_coherent_preserv_write_block_log c2 bit2 pf bi3 b' c3 bit3 HJc2 Hbit3 Hgetb' Hc2c3); trivial.

    (* case <1> (Some bd, Some bl) ==> <1> (log block is full) ==> <2> Write_Read_on_Spot *) 
    split.
      unfold FTL_read.
      rewrite Hoff.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.
      rewrite Hrc3.
      trivial.
    (* case <1> (Some bd, Some bl) ==> <1> (log block is full) ==> <3> Write Read out of Spot, in the same block *) 
    split.
      intros off' Hoff'neq.
      unfold FTL_read at 1.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.

      rewrite (Hr off' (neq_refl Hoff'neq)).
      rewrite <- (Hread lbn off').
      unfold FTL_read.
      simpl.
      rewrite Hbmt'1.
      assert (Hneq : pf <> bfx).
        intro Heq.
        subst bfx.
        destruct Hfbq2 as [Hfbq2 _].
        assert (Hx: pbn_in_bmt bmt' pf).
          unfold pbn_in_bmt.
          exists lbn.
          unfold pbn_in_bmt_lbn.
          left.
          exists None.
          trivial.
        rewrite (I_pbn_habitation_in_bmt_implies_not_in_fbq pf bmt' fbq' Hpf HI6' Hx)
            in Hfbq2.
        discriminate.
      assert (Hc2c':= Hc'c2_3 bfx (neq_refl Hneq)).
      assert (Hc3c2:= Hc2c3 bfx (neq_refl Hneq)).
      rewrite (read_data_block_unchanged c' bfx off' c2 (eq_sym Hc2c')).
      rewrite (read_data_block_unchanged c2 bfx off' c3 (eq_sym Hc3c2)).
      trivial.

    (* case <1> (Some bd, Some bl) ==> <1> (log block is full) ==> <4> Write Read out of Spot, in different blocks *) 
    intros lbn' off' Hlbn'.
    rewrite <- (Hread lbn' off').
    unfold FTL_read.
    simpl.
    assert (HB: bmt_get bmt3 lbn' = bmt_get bmt' lbn').
      rewrite (bmt_update_log_bmt_get_neq bmt2 lbn pf bmt3 lbn' Hbmtup (neq_refl Hlbn')).
      subst bmt2.
      trivial.
    rewrite HB.
    destruct (bmt_get bmt' lbn') as [bmr' | ] eqn:Hbmt'get'; trivial.
    destruct bmr' as [bmr_data' bmr_log'].
    destruct bmr_data' as [pbn_data' | ]; destruct bmr_log' as [pbn_log' | ].
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists (Some pbn_data').
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (Some pbn_log').
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit' pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit' pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit' pbn_log') as [bilog' | ] eqn:Hbilog'.
      assert (Hc2c':= Hc'c2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c' pbn_log' off' bilog' c2 (eq_sym Hc2c')).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
      assert (Hc2c'x:= Hc'c2_3 pbn_data' Hpd').
      assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
      rewrite (read_data_block_unchanged c' pbn_data' off' c2 (eq_sym Hc2c'x)).
      rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
      trivial.
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (None).
      trivial.
    assert (Hc2c'x:= Hc'c2_3 pbn_data' Hpd').
    assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
    rewrite (read_data_block_unchanged c' pbn_data' off' c2 (eq_sym Hc2c'x)).
    rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
    trivial.
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists None.
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit' pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit' pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit' pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hc2c':= Hc'c2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c' pbn_log' off' bilog' c2 (eq_sym Hc2c')).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
    trivial.

    (* case <1> (Some bd, Some bl) ==> <2> (log block is not full) *) 
    assert (Hb : exists b, 
                   chip_get_block c pbn_log = Some b 
                   /\ block_coherent_log bi_log b
                   /\ bi_lbn bi_log = Some lbn).
      unfold J_bi_block_coherent in HJ.
      assert (Hco:= HJ pbn_log bi_log Hbil).
      unfold chip_bi_coherent in Hco.
      destruct (HI5 lbn pbn_log bi_log Hbil) as [HI5_1 HI5_2].
      assert (Hin: pbn_in_bmt_log bmt lbn pbn_log).
        exists (Some pbn_data); trivial.
      destruct (HI5_2 Hin) as [pmt Hbils].
      rewrite Hbils in Hco.
      destruct Hco as [b [Hb Hco]].
      exists b.
      split; trivial.
      split; trivial.
      unfold bi_lbn.
      rewrite Hbils.
      trivial.
    destruct Hb as [b [Hgetb [Hcob Hbilbn]]].
    assert (Hnextb : bvalid_page_off (next_page b) = true).
      unfold block_coherent_log in Hcob.
      unfold check_block_is_full in Hcklog.
      destruct Hcob as [pmt [lbnx [_ [Hbup _]]]].
      rewrite <- Hbup.
      unfold bvalid_page_off.
      destruct (blt_nat (bi_used_pages bi_log) PAGES_PER_BLOCK); try discriminate.
      trivial.
    destruct (write_log_block_spec_write_nonemp c pbn_log b bi_log off lbn d Hgetb Hbl Hoff Hbilbn Hnextb Hcob) 
      as [c' [bi' [Hw [Hbi'1 [Hbi'2 [Hbi'3 [Hcc'1 [Hrc' [Hrc'2 Hrc'3]]]]]]]]].
    rewrite Hw.
    destruct (bit_update_spec bit pbn_log bi_log bi' Hbil) 
      as [bit' [Hbit' [Hbit'get1 Hbit'get2]]].
    rewrite Hbit'.
    exists c', (mk_FTL bit' bmt fbq).
    rewrite Hoff.
    split; trivial.
    simpl in * .
    split.

      (* case <1> (Some bd, Some bl) ==> <2> (log block is not full) ==> <1> Inv (c', f') *)
      split.
        (* F_Inv *)
        unfold F_Inv.
        simpl.
        split. (* I1 *)
          apply (I_pbn_bit_valid_preserv_bit_update pbn_log bit bi' bit'); auto.
        split. (* I2 *)
          trivial.
        split. (* I3 *)
          trivial.
        split. (* I4 *)
          apply (I_pbn_fbq_state_preserv_bit_update bit fbq pbn_log bi' bit'); auto.
          apply (I_pbn_habitation_in_bmt_implies_not_in_fbq pbn_log bmt fbq Hbl HI6); trivial.
          exists lbn.
          right.
          exists (Some pbn_data).
          trivial.
        split. (* I5 *)
          assert (Hst: exists pmt, bi_state bi' = bs_log lbn pmt).
            destruct Hcc'1 as [b' [Hgetb' Hcob']].
            destruct Hcob' as [pmt [lbn' [Hbis [Hbiu [Hbs [Hpps Hpnp]]]]]].
            exists pmt.
            unfold bi_lbn in Hbi'3.
            rewrite Hbis in Hbi'3.
            injection Hbi'3.
            intro.
            subst lbn'.
            trivial.
          destruct Hst as [pmt Hst].

          apply (I_pbn_bmt_used_preserv_write_log_block bit bmt pbn_log lbn bi' bit'); trivial.
            exists (Some pbn_data); trivial.
          exists pmt; trivial.
        split. (* I6 *)
          trivial.
        split. (* I7_1 *)
          trivial.
        split. (* I7_2 *)
          trivial.
        split. (* I8 *)
          trivial.
        (* I10 *)
        trivial.
      (* R_Inv *)
      unfold R_Inv.
      simpl.
      destruct Hcc'1 as [b' [Hgetb' Hco']].
      apply (J_bi_block_coherent_preserv_write_block_log c bit pbn_log bi' b' c' bit' HJ Hbit' Hgetb' Hrc'3); trivial.

    (* case <1> (Some bd, Some bl) ==> <2> (log block is not full) ==> <2> Write_Read_on_Spot *) 
    split.
      unfold FTL_read.
      simpl.
      rewrite Hbme.
      rewrite Hoff.
      rewrite Hbit'get1.
      rewrite Hrc'.
      trivial.

    (* case <1> (Some bd, Some bl) ==> <2> (log block is full) ==> <3> Write Read out of Spot, in the same block *) 
    split.
      intros off' Hoff'neq.
      unfold FTL_read at 1.
      simpl.
      rewrite Hbme.
      simpl.
      rewrite Hbit'get1.
      rewrite (Hrc'2 off' (neq_refl Hoff'neq)).
      unfold FTL_read.
      simpl.
      rewrite Hbme.
      rewrite Hbil.
      
      assert (Hneq : pbn_data <> pbn_log).
        apply (HI7_2 lbn pbn_data pbn_log); trivial.
      assert (Hcc':= Hrc'3 pbn_data Hneq).
      rewrite (read_data_block_unchanged c pbn_data off' c' (eq_sym Hcc')).
      trivial.

    (* case <1> (Some bd, Some bl) ==> <2> (log block is not full) ==> <4> Write Read out of Spot, in different blocks *) 
    intros lbn' off' Hlbn'.
    unfold FTL_read.
    simpl.
    destruct (bmt_get bmt lbn') as [bmr | ] eqn:Hbmtget'; trivial.
    destruct bmr as [bmr_data bmr_log].
    destruct bmr_data as [pbn_data' | ]; destruct bmr_log as [pbn_log' | ].
    assert (Hpl': pbn_log' <> pbn_log).
      intro HF.
      subst pbn_log'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      right.
      exists (Some pbn_data').
      trivial.
    assert (Hpd': pbn_data' <> pbn_log).
      intro HF.
      subst pbn_data'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      left.
      exists (Some pbn_log').
      trivial.
    assert (Hbit'get' : bit_get bit' pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit' bi' pbn_log); trivial. 
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hcc':= (eq_sym (Hrc'3 pbn_log' Hpl'))).
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c' Hcc').
      destruct (read_log_block c' bilog' pbn_log' off') as [ d' | ]; trivial.
      assert (Hcc'2:= (eq_sym (Hrc'3 pbn_data' Hpd'))).
      rewrite (read_data_block_unchanged c pbn_data' off' c' Hcc'2).
      trivial.

    assert (Hpd': pbn_data' <> pbn_log).
      intro HF.
      subst pbn_data'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      left.
      exists None.
      trivial.
    assert (Hcc'2:= (eq_sym (Hrc'3 pbn_data' Hpd'))).
    rewrite (read_data_block_unchanged c pbn_data' off' c' Hcc'2).
    trivial.

    assert (Hpl': pbn_log' <> pbn_log).
      intro HF.
      subst pbn_log'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      right.
      exists None.
      trivial.
    assert (Hbit'get' : bit_get bit' pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit' bi' pbn_log); trivial. 
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hcc':= (eq_sym (Hrc'3 pbn_log' Hpl'))).
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c' Hcc').
      trivial.
    trivial.

  (* case <2> (Some bd, None) *)
  assert (Hbdinbmt : pbn_in_bmt_lbn bmt lbn pbn_data).
    left. exists None. trivial.
  assert (Hbd: valid_block_no pbn_data).
    apply (HI2 lbn pbn_data); trivial.
  rewrite Hbme.
  rewrite Hoff.
  (* destruct (HI1 pbn_log) as [Hx _]. *)
  (* destruct (Hx Hbl) as [bi_log Hbil]. *)
  (* clear Hx. *)
  (* rewrite Hbil. *)
  (* destruct (check_block_is_full bi_log) eqn:Hcklog. *)

  (*   (* case 1 - 1, log block is full *) *)
  (*   assert (HInv: Inv (c, (mk_FTL bit bmt fbq))). *)
  (*     unfold Inv, F_Inv, R_Inv. *)
  (*     simpl. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*     split; trivial. *)
  (*   destruct (merge_block_case1_spec c (mk_FTL bit bmt fbq) lbn pbn_data pbn_log HInv Hlbn Hbme) *)
  (*       as [c' [f' [Hm [HI' [[bfx [Hbmt'1 Hbmt'2]] [Hlen Hread]]]]]]. *)
  (*   rewrite Hm. *)
  (*   clear HI1 HI2 HI3 HI4 HI5 HI6 HI7_1 H7_2 HI8 HI10 HJ HInv. *)
  (*   destruct HI' as [HFI' HRI']. *)
  (*   destruct HFI' as [HI1' [HI2' [HI3' [HI4' [HI5' [HI6' [HI7_1' [HI7_2' [HI8' HI10']]]]]]]]]. *)
  (*   unfold R_Inv in HRI'. *)
  (*   rename HRI' into HJ'. *)
  (*   destruct f' as [bit' bmt' fbq']. *)
  (*   simpl in * . *)
  assert (HSC: I_fbq_len_greater_than_constant fbq).
    apply (I_fbq_len_greater_than_constant_derivable bit bmt); trivial.
  destruct (alloc_block_spec c bit bmt fbq HI1 HI3 HI4 HI8 HSC HJ)
      as [pf [c2 [f2 [bif2 [Ha [Hpf [Hbif2 [Hcc2_1 [Hcc2_2 [Hcc2_3 [Hbmt2 [Hbit2 [Hfbq2 HJc2]]]]]]]]]]]]].
  rewrite Ha.
  destruct f2 as [bit2 bmt2 fbq2].
  simpl in * .
  assert (Hbif2get: bit_get bit2 pf = Some bif2).
    apply (bit_update_bit_get_eq bit); trivial.
  rewrite Hbif2get.
  set (bi2 := bi_set_state bif2 (bs_log lbn blank_pmt)).
  assert (exists b2, chip_get_block c2 pf = Some b2
                       /\ (bi_state bi2 = bs_log lbn blank_pmt
                           /\ bi_used_pages bi2 = next_page b2
                           /\ block_state b2 = bs_free
                           /\ next_page b2 = 0
                           /\ (forall loc,
                                 valid_page_off loc
                                 -> exists p, block_get_page b2 loc = Some p
                                              /\ page_state p = ps_free))).
    unfold J_bi_block_coherent in HJc2.
    unfold chip_bi_coherent in HJc2.
    destruct (HJc2 pf bif2 Hbif2get) as [b2 [Hb2 Hco2]].
    destruct Hbif2 as [Hbif2_1 Hbif2_2].
    rewrite Hbif2_1 in Hco2.
    exists b2.
    split; trivial.
    subst bi2.
    unfold bi_state, bi_set_state.
    simpl.
    split; trivial.
    unfold block_coherent_erased in Hco2.
    destruct Hco2 as [Hx1 [Hx2 [Hx3 [Hx4 Hx5]]]].
    rewrite Hx2.
    split; trivial.
    split; trivial.
    split; trivial.
  destruct H as [b2 [Hgetb2 Hb2_2]].
  destruct (write_log_block_spec_write_emp c2 pf b2 bi2 off lbn d Hgetb2 Hpf Hoff Hb2_2)
      as [c3 [bi3 [Hw [Hbi3_1 [Hbi3_2 [Hbi3_3 [Hco3 [Hrc3 [Hr Hc2c3]]]]]]]]].
  rewrite Hw.
  assert (Hbmt2get: bmt_get bmt2 lbn = Some (Some pbn_data, None)).
      rewrite Hbmt2.
      trivial.
  destruct (bmt_update_log_spec bmt2 lbn pf (Some pbn_data, None) Hbmt2get)
        as [bmt3 [Hbmtup [Hbmt3_1 Hbmt3_2]]].
  rewrite Hbmt2 in Hbmtup.
  rewrite Hbmtup.
  destruct (bit_update_spec bit2 pf bif2 bi3 Hbif2get) as [bit3 [Hbit3 [Hbi3get Hbit3_2]]].
  rewrite Hbit3.
  exists c3, (mk_FTL bit3 bmt3 fbq2).
  split; trivial.
  split.
    (* case <2> (Some bd, None) ==> <1> (log block is full) ==> <1> Inv (c', f') *)
    split.
      (* F_Inv preservation *)
      unfold F_Inv.
      simpl.
      split. (* I1 *)
        apply (I_pbn_bit_valid_preserv_bit_update pf bit2 bi3 bit3); auto.
        apply (I_pbn_bit_valid_preserv_bit_update pf bit bif2 bit2); auto.
      split. (* I2 *)
        subst bmt2.
        apply (I_pbn_bmt_valid_preserv_bmt_update_log bmt lbn pf bmt3); auto.
      split. (* I3 *)
        apply (I_pbn_fbq_valid_preserv_fbq_deq fbq pf fbq2 HI3); auto.
        destruct Hfbq2 as [_ [_ Hdeq]].
        trivial.
      split. (* I4 *)
        destruct Hfbq2 as [H1 [H2 Hdeq]].
        apply (I_pbn_fbq_state_preserv_bit_update bit2 fbq2 pf bi3 bit3); auto.
        apply (I_pbn_fbq_state_preserv_bit_update bit fbq2 pf bif2 bit2); auto.
        apply (I_pbn_fbq_state_preserv_fbq_deq bit fbq pf fbq2); trivial.
      split. (* I5 *)
        assert (Hst: exists pmt, bi_state bi3 = bs_log lbn pmt).
          destruct Hco3 as [b' [Hb' Hco']].
          unfold block_coherent_log in Hco'.
          destruct Hco' as [pmt [lbnx [Hbss _]]].
          unfold bi_lbn in Hbi3_2.
          rewrite Hbss in Hbi3_2.
          injection Hbi3_2.
          intro Hlbnx; subst lbnx.
          exists pmt. 
          trivial.
        subst bmt2.
        destruct Hst as [pmt Hst].
        apply (I_pbn_bmt_used_preserv_bmt_update_log bit2 bmt pf lbn bi3 pmt bit3 bmt3); trivial.
        apply (I_pbn_bmt_used_preserv_bit_update_irre bit bmt pf bif2 bit2 HI5 Hbit2); trivial.
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
        destruct Hfbq2 as [Hfbq' _].
        trivial.
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
        destruct Hfbq2 as [Hfbq' _].
        trivial.
      split. (* I6 *)
        destruct Hfbq2 as [_ [_ Hfbq2]].
        simpl in Hbmt3_1.
        subst bmt2.
        apply (I_pbn_habitation_preserv_bmt_update_log bmt fbq lbn pbn_data pf bmt3 fbq2); trivial.
      split. (* I7_1 *)
        subst bmt2.
        apply (I_pbn_bmt_distinguishable_preserv_bmt_update_log bmt lbn pf bmt3 HI7_1); trivial.
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
        destruct Hfbq2 as [Hfbq' _].
        trivial.
      split. (* I7_2 *)
        subst bmt2.
        apply (I_pbn_bmt_distinguishable_2_preserv_bmt_update_log bmt lbn pf bmt3 HI7_2 Hbmtup); trivial.
        destruct Hfbq2 as [Hfbq' _].
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
      split. (* I8 *)
        destruct Hfbq2 as [_ [_ Hfbq2]].
        apply (I_pbn_fbq_distinguishable_preserv_fbq_deq fbq pf fbq2 HI8 Hfbq2); trivial.
      (* I10 *)
      subst bmt2.
      apply (I_valid_lbn_has_entry_in_bmt_preserv_bmt_update_log bmt lbn pf bmt3 HI10 Hbmtup); trivial.
    (* R_Inv *)
    unfold R_Inv.
    simpl.

    destruct Hco3 as [b' [Hgetb' Hco3]].
    apply (J_bi_block_coherent_preserv_write_block_log c2 bit2 pf bi3 b' c3 bit3 HJc2 Hbit3 Hgetb' Hc2c3); trivial.

    (* case <2> (Some bd, None) ==> <1> (log block is full) ==> <2> Write_Read_on_Spot *)
    split.
      unfold FTL_read.
      rewrite Hoff.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.
      rewrite Hrc3.
      trivial.
    (* case <2> (Some bd, None) ==> <1> (log block is full) ==> <3> Write Read out of Spot, in the same block *)
    split.
      intros off' Hoff'neq.
      unfold FTL_read at 1.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.

      rewrite (Hr off' (neq_refl Hoff'neq)).
      (* rewrite <- (Hread lbn off'). *)
      unfold FTL_read.
      simpl.
      rewrite Hbme.
      assert (Hneq : pf <> pbn_data).
        intro Heq.
        subst pbn_data.
        destruct Hfbq2 as [Hfbq2 _].
        assert (Hx: pbn_in_bmt bmt pf).
          unfold pbn_in_bmt.
          exists lbn.
          unfold pbn_in_bmt_lbn.
          left.
          exists None.
          trivial.
        rewrite (I_pbn_habitation_in_bmt_implies_not_in_fbq pf bmt fbq Hpf HI6 Hx)
            in Hfbq2.
        discriminate.
      assert (Hc2c':= Hcc2_3 pbn_data (neq_refl Hneq)).
      assert (Hc3c2:= Hc2c3 pbn_data (neq_refl Hneq)).
      rewrite (read_data_block_unchanged c pbn_data off' c2 (eq_sym Hc2c')).
      rewrite (read_data_block_unchanged c2 pbn_data off' c3 (eq_sym Hc3c2)).
      trivial.

    (* case <2> (Some bd, None) ==> <1> (log block is full) ==> <4> Write Read out of Spot, in different blocks *)
    intros lbn' off' Hlbn'.
    unfold FTL_read.
    simpl.
    assert (HB: bmt_get bmt3 lbn' = bmt_get bmt lbn').
      subst bmt2.
      rewrite (bmt_update_log_bmt_get_neq bmt lbn pf bmt3 lbn' Hbmtup (neq_refl Hlbn')).
      trivial.
    rewrite HB.
    destruct (bmt_get bmt lbn') as [bmr' | ] eqn:Hbmtget'; trivial.
    destruct bmr' as [bmr_data' bmr_log'].
    destruct bmr_data' as [pbn_data' | ]; destruct bmr_log' as [pbn_log' | ].
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists (Some pbn_data').
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (Some pbn_log').
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'.
      assert (Hc2c:= Hcc2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c2 (eq_sym Hc2c)).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
      assert (Hc2cx:= Hcc2_3 pbn_data' Hpd').
      assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
      rewrite (read_data_block_unchanged c pbn_data' off' c2 (eq_sym Hc2cx)).
      rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
      trivial.
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (None).
      trivial.
    assert (Hc2cx:= Hcc2_3 pbn_data' Hpd').
    assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
    rewrite (read_data_block_unchanged c pbn_data' off' c2 (eq_sym Hc2cx)).
    rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
    trivial.
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists None.
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hc2c:= Hcc2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c2 (eq_sym Hc2c)).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
    trivial.

  (* case <3> (None, Some bl) *)
  assert (Hblinbmt : pbn_in_bmt_lbn bmt lbn pbn_log).
    right. exists None. trivial.
  assert (Hbl: valid_block_no pbn_log).
    apply (HI2 lbn pbn_log); trivial.
  rewrite Hbme.
  destruct (HI1 pbn_log) as [Hx _].
  destruct (Hx Hbl) as [bi_log Hbil].
  clear Hx.
  rewrite Hbil.
  destruct (check_block_is_full bi_log) eqn:Hcklog.

    (* case <3> (None, Some bl) => <1> log block is full *)
    assert (HInv: Inv c (mk_FTL bit bmt fbq)).
      unfold Inv, F_Inv, R_Inv.
      simpl.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
      split; trivial.
    destruct (merge_block_case2_spec c (mk_FTL bit bmt fbq) lbn pbn_log HInv Hlbn Hbme)
        as [c' [f' [Hm [HI' [[bfx [Hbmt'1 Hbmt'2]] [Hlen Hread]]]]]].
    rewrite Hm.
    clear HI1 HI2 HI3 HI4 HI5 HI6 HI7_1 HI7_2 HI8 HI10 HJ HInv.
    destruct HI' as [HFI' HRI'].
    destruct HFI' as [HI1' [HI2' [HI3' [HI4' [HI5' [HI6' [HI7_1' [HI7_2' [HI8' HI10']]]]]]]]].
    unfold R_Inv in HRI'.
    rename HRI' into HJ'.
    destruct f' as [bit' bmt' fbq'].
    simpl in * .
    assert (HSC': I_fbq_len_greater_than_constant fbq').
      apply (I_fbq_len_greater_than_constant_derivable bit' bmt'); trivial.
    destruct (alloc_block_spec c' bit' bmt' fbq' HI1' HI3' HI4' HI8' HSC' HJ')
      as [pf [c2 [f2 [bif2 [Ha [Hpf [Hbif2 [Hc'c2_1 [Hc'c2_2 [Hc'c2_3 [Hbmt2 [Hbit2 [Hfbq2 HJc2]]]]]]]]]]]]].
    rewrite Ha.
    destruct f2 as [bit2 bmt2 fbq2].
    simpl in * .
    assert (Hbif2get: bit_get bit2 pf = Some bif2).
      apply (bit_update_bit_get_eq bit'); trivial.
    rewrite Hbif2get.
    set (bi2 := bi_set_state bif2 (bs_log lbn blank_pmt)).
    assert (exists b2, chip_get_block c2 pf = Some b2
                       /\ (bi_state bi2 = bs_log lbn blank_pmt
                           /\ bi_used_pages bi2 = next_page b2
                           /\ block_state b2 = bs_free
                           /\ next_page b2 = 0
                           /\ (forall loc,
                                 valid_page_off loc
                                 -> exists p, block_get_page b2 loc = Some p
                                              /\ page_state p = ps_free))).
      unfold J_bi_block_coherent in HJc2.
      unfold chip_bi_coherent in HJc2.
      destruct (HJc2 pf bif2 Hbif2get) as [b2 [Hb2 Hco2]].
      destruct Hbif2 as [Hbif2_1 Hbif2_2].
      rewrite Hbif2_1 in Hco2.
      exists b2.
      split; trivial.
      subst bi2.
      unfold bi_state, bi_set_state.
      simpl.
      split; trivial.
      unfold block_coherent_erased in Hco2.
      destruct Hco2 as [Hx1 [Hx2 [Hx3 [Hx4 Hx5]]]].
      rewrite Hx2.
      split; trivial.
      split; trivial.
      split; trivial.
    destruct H as [b2 [Hgetb2 Hb2_2]].
    destruct (write_log_block_spec_write_emp c2 pf b2 bi2 off lbn d Hgetb2 Hpf Hoff Hb2_2)
      as [c3 [bi3 [Hw [Hbi3_1 [Hbi3_2 [Hbi3_3 [Hco3 [Hrc3 [Hr Hc2c3]]]]]]]]].
    rewrite Hw.
    
    assert (Hbmt2get: bmt_get bmt2 lbn = Some (Some bfx, None)).
      rewrite Hbmt2.
      trivial.
    destruct (bmt_update_log_spec bmt2 lbn pf (Some bfx, None) Hbmt2get)
        as [bmt3 [Hbmtup [Hbmt3_1 Hbmt3_2]]].
    rewrite Hbmtup.
    rewrite Hoff.
    destruct (bit_update_spec bit2 pf bif2 bi3 Hbif2get) as [bit3 [Hbit3 [Hbi3get Hbit3_2]]].
    rewrite Hbit3.
    exists c3, (mk_FTL bit3 bmt3 fbq2).
    split; trivial.
    split.

      (* case <3> (None, Some bl) ==> <1> (log block is full) ==> <1> Inv (c', f') *)
      split.
        (* F_Inv preservation *)
        unfold F_Inv.
        simpl.
        split. (* I1 *)
          apply (I_pbn_bit_valid_preserv_bit_update pf bit2 bi3 bit3); auto.
          apply (I_pbn_bit_valid_preserv_bit_update pf bit' bif2 bit2); auto.
        split. (* I2 *)
          subst bmt2.
          apply (I_pbn_bmt_valid_preserv_bmt_update_log bmt' lbn pf bmt3); auto.
        split. (* I3 *)
          apply (I_pbn_fbq_valid_preserv_fbq_deq fbq' pf fbq2 HI3'); auto.
          destruct Hfbq2 as [_ [_ Hdeq]].
          trivial.
        split. (* I4 *)
          destruct Hfbq2 as [H1 [H2 Hdeq]].
          apply (I_pbn_fbq_state_preserv_bit_update bit2 fbq2 pf bi3 bit3); auto.
          apply (I_pbn_fbq_state_preserv_bit_update bit' fbq2 pf bif2 bit2); auto.
          apply (I_pbn_fbq_state_preserv_fbq_deq bit' fbq' pf fbq2); trivial.
        split. (* I5 *)
          assert (Hst: exists pmt, bi_state bi3 = bs_log lbn pmt).
            destruct Hco3 as [b' [Hb' Hco']].
            unfold block_coherent_log in Hco'.
            destruct Hco' as [pmt [lbnx [Hbss _]]].
            unfold bi_lbn in Hbi3_2.
            rewrite Hbss in Hbi3_2.
            injection Hbi3_2.
            intro Hlbnx; subst lbnx.
            exists pmt. 
            trivial.
          destruct Hst as [pmt Hst].
          apply (I_pbn_bmt_used_preserv_bmt_update_log bit2 bmt2 pf lbn bi3 pmt bit3 bmt3); trivial.
          subst bmt2.
          apply (I_pbn_bmt_used_preserv_bit_update_irre bit' bmt' pf bif2 bit2 HI5' Hbit2); trivial.
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
          destruct Hfbq2 as [Hfbq' _].
          trivial.
          subst bmt2.
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
          destruct Hfbq2 as [Hfbq' _].
          trivial.
        split. (* I6 *)
          destruct Hfbq2 as [_ [_ Hfbq2]].
          simpl in Hbmt3_1.
          subst bmt'.
          apply (I_pbn_habitation_preserv_bmt_update_log bmt2 fbq' lbn bfx pf bmt3 fbq2); trivial.
          apply (HI2' lbn bfx).
          left; exists None; trivial.
        split. (* I7_1 *)
          subst bmt2.
          apply (I_pbn_bmt_distinguishable_preserv_bmt_update_log bmt' lbn pf bmt3 HI7_1'); trivial.
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
          destruct Hfbq2 as [Hfbq' _].
          trivial.
        split. (* I7_2 *)
          subst bmt2.
          apply (I_pbn_bmt_distinguishable_2_preserv_bmt_update_log bmt' lbn pf bmt3 HI7_2' Hbmtup); trivial.
          destruct Hfbq2 as [Hfbq' _].
          apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6'); trivial.
        split. (* I8 *)
          destruct Hfbq2 as [_ [_ Hfbq2]].
          apply (I_pbn_fbq_distinguishable_preserv_fbq_deq fbq' pf fbq2 HI8' Hfbq2); trivial.
        (* I10 *)
        subst bmt2.
        apply (I_valid_lbn_has_entry_in_bmt_preserv_bmt_update_log bmt' lbn pf bmt3 HI10' Hbmtup); trivial.
      (* R_Inv *)
      unfold R_Inv.
      simpl.

      destruct Hco3 as [b' [Hgetb' Hco3]].
      apply (J_bi_block_coherent_preserv_write_block_log c2 bit2 pf bi3 b' c3 bit3 HJc2 Hbit3 Hgetb' Hc2c3); trivial.

    (* case <3> (None, Some bl) ==> <1> (log block is full) ==> <2> Write_Read_on_Spot *) 
    split.
      unfold FTL_read.
      rewrite Hoff.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.
      rewrite Hrc3.
      trivial.
    (* case <3> (None, Some bl) ==> <1> (log block is full) ==> <3> Write Read out of Spot, in the same block *) 
    split.
      intros off' Hoff'neq.
      unfold FTL_read at 1.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.

      rewrite (Hr off' (neq_refl Hoff'neq)).
      rewrite <- (Hread lbn off').
      unfold FTL_read.
      simpl.
      rewrite Hbmt'1.
      assert (Hneq : pf <> bfx).
        intro Heq.
        subst bfx.
        destruct Hfbq2 as [Hfbq2 _].
        assert (Hx: pbn_in_bmt bmt' pf).
          unfold pbn_in_bmt.
          exists lbn.
          unfold pbn_in_bmt_lbn.
          left.
          exists None.
          trivial.
        rewrite (I_pbn_habitation_in_bmt_implies_not_in_fbq pf bmt' fbq' Hpf HI6' Hx)
            in Hfbq2.
        discriminate.
      assert (Hc2c':= Hc'c2_3 bfx (neq_refl Hneq)).
      assert (Hc3c2:= Hc2c3 bfx (neq_refl Hneq)).
      rewrite (read_data_block_unchanged c' bfx off' c2 (eq_sym Hc2c')).
      rewrite (read_data_block_unchanged c2 bfx off' c3 (eq_sym Hc3c2)).
      trivial.

    (* case <3> (None, Some bl) ==> <1> (log block is full) ==> <4> Write Read out of Spot, in different blocks *) 
    intros lbn' off' Hlbn'.
    rewrite <- (Hread lbn' off').
    unfold FTL_read.
    simpl.
    assert (HB: bmt_get bmt3 lbn' = bmt_get bmt' lbn').
      rewrite (bmt_update_log_bmt_get_neq bmt2 lbn pf bmt3 lbn' Hbmtup (neq_refl Hlbn')).
      subst bmt2.
      trivial.
    rewrite HB.
    destruct (bmt_get bmt' lbn') as [bmr' | ] eqn:Hbmt'get'; trivial.
    destruct bmr' as [bmr_data' bmr_log'].
    destruct bmr_data' as [pbn_data' | ]; destruct bmr_log' as [pbn_log' | ].
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists (Some pbn_data').
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (Some pbn_log').
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit' pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit' pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit' pbn_log') as [bilog' | ] eqn:Hbilog'.
      assert (Hc2c':= Hc'c2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c' pbn_log' off' bilog' c2 (eq_sym Hc2c')).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
      assert (Hc2c'x:= Hc'c2_3 pbn_data' Hpd').
      assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
      rewrite (read_data_block_unchanged c' pbn_data' off' c2 (eq_sym Hc2c'x)).
      rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
      trivial.
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (None).
      trivial.
    assert (Hc2c'x:= Hc'c2_3 pbn_data' Hpd').
    assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
    rewrite (read_data_block_unchanged c' pbn_data' off' c2 (eq_sym Hc2c'x)).
    rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
    trivial.
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt' fbq' Hpf HI6').
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists None.
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit' pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit' pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit' pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hc2c':= Hc'c2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c' pbn_log' off' bilog' c2 (eq_sym Hc2c')).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
    trivial.

    (* case <3> (None, Some bl) ==> <2> (log block is not full) *) 
    assert (Hb : exists b, 
                   chip_get_block c pbn_log = Some b 
                   /\ block_coherent_log bi_log b
                   /\ bi_lbn bi_log = Some lbn).
      unfold J_bi_block_coherent in HJ.
      assert (Hco:= HJ pbn_log bi_log Hbil).
      unfold chip_bi_coherent in Hco.
      destruct (HI5 lbn pbn_log bi_log Hbil) as [HI5_1 HI5_2].
      assert (Hin: pbn_in_bmt_log bmt lbn pbn_log).
        exists None; trivial.
      destruct (HI5_2 Hin) as [pmt Hbils].
      rewrite Hbils in Hco.
      destruct Hco as [b [Hb Hco]].
      exists b.
      split; trivial.
      split; trivial.
      unfold bi_lbn.
      rewrite Hbils.
      trivial.
    destruct Hb as [b [Hgetb [Hcob Hbilbn]]].
    assert (Hnextb : bvalid_page_off (next_page b) = true).
      unfold block_coherent_log in Hcob.
      unfold check_block_is_full in Hcklog.
      destruct Hcob as [pmt [lbnx [_ [Hbup _]]]].
      rewrite <- Hbup.
      unfold bvalid_page_off.
      destruct (blt_nat (bi_used_pages bi_log) PAGES_PER_BLOCK); try discriminate.
      trivial.
    destruct (write_log_block_spec_write_nonemp c pbn_log b bi_log off lbn d Hgetb Hbl Hoff Hbilbn Hnextb Hcob) 
      as [c' [bi' [Hw [Hbi'1 [Hbi'2 [Hbi'3 [Hcc'1 [Hrc' [Hrc'2 Hrc'3]]]]]]]]].
    rewrite Hw.
    destruct (bit_update_spec bit pbn_log bi_log bi' Hbil) 
      as [bit' [Hbit' [Hbit'get1 Hbit'get2]]].
    rewrite Hbit'.
    exists c', (mk_FTL bit' bmt fbq).
    rewrite Hoff.
    split; trivial.
    simpl in * .
    split.

      (* case <3> (None, Some bl) ==> <2> (log block is not full) ==> <1> Inv (c', f') *)
      split.
        (* F_Inv *)
        unfold F_Inv.
        simpl.
        split. (* I1 *)
          apply (I_pbn_bit_valid_preserv_bit_update pbn_log bit bi' bit'); auto.
        split. (* I2 *)
          trivial.
        split. (* I3 *)
          trivial.
        split. (* I4 *)
          apply (I_pbn_fbq_state_preserv_bit_update bit fbq pbn_log bi' bit'); auto.
          apply (I_pbn_habitation_in_bmt_implies_not_in_fbq pbn_log bmt fbq Hbl HI6); trivial.
          exists lbn.
          right.
          exists None.
          trivial.
        split. (* I5 *)
          assert (Hst: exists pmt, bi_state bi' = bs_log lbn pmt).
            destruct Hcc'1 as [b' [Hgetb' Hcob']].
            destruct Hcob' as [pmt [lbn' [Hbis [Hbiu [Hbs [Hpps Hpnp]]]]]].
            exists pmt.
            unfold bi_lbn in Hbi'3.
            rewrite Hbis in Hbi'3.
            injection Hbi'3.
            intro.
            subst lbn'.
            trivial.
          destruct Hst as [pmt Hst].

          apply (I_pbn_bmt_used_preserv_write_log_block bit bmt pbn_log lbn bi' bit'); trivial.
            exists None; trivial.
          exists pmt; trivial.
        split. (* I6 *)
          trivial.
        split. (* I7_1 *)
          trivial.
        split. (* I7_2 *)
          trivial.
        split. (* I8 *)
          trivial.
        (* I10 *)
        trivial.
      (* R_Inv *)
      unfold R_Inv.
      simpl.
      destruct Hcc'1 as [b' [Hgetb' Hco']].
      apply (J_bi_block_coherent_preserv_write_block_log c bit pbn_log bi' b' c' bit' HJ Hbit' Hgetb' Hrc'3); trivial.

    (* case <3> (None, Some bl) ==> <2> (log block is not full) ==> <2> Write_Read_on_Spot *) 
    split.
      unfold FTL_read.
      simpl.
      rewrite Hbme.
      rewrite Hoff.
      rewrite Hbit'get1.
      rewrite Hrc'.
      trivial.

    (* case <3> (None, Some bl) ==> <2> (log block is full) ==> <3> Write Read out of Spot, in the same block *) 
     split.
      intros off' Hoff'neq.
      unfold FTL_read at 1.
      simpl.
      rewrite Hbme.
      simpl.
      rewrite Hbit'get1.
      rewrite (Hrc'2 off' (neq_refl Hoff'neq)).
      unfold FTL_read.
      simpl.
      rewrite Hbme.
      rewrite Hbil.
      trivial.

    (* case <3> (None, Some bl) ==> <2> (log block is not full) ==> <4> Write Read out of Spot, in different blocks *) 
    intros lbn' off' Hlbn'.
    unfold FTL_read.
    simpl.
    destruct (bmt_get bmt lbn') as [bmr | ] eqn:Hbmtget'; trivial.
    destruct bmr as [bmr_data bmr_log].
    destruct bmr_data as [pbn_data' | ]; destruct bmr_log as [pbn_log' | ].
    assert (Hpl': pbn_log' <> pbn_log).
      intro HF.
      subst pbn_log'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      right.
      exists (Some pbn_data').
      trivial.
    assert (Hpd': pbn_data' <> pbn_log).
      intro HF.
      subst pbn_data'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      left.
      exists (Some pbn_log').
      trivial.
    assert (Hbit'get' : bit_get bit' pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit' bi' pbn_log); trivial. 
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hcc':= (eq_sym (Hrc'3 pbn_log' Hpl'))).
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c' Hcc').
      destruct (read_log_block c' bilog' pbn_log' off') as [ d' | ]; trivial.
      assert (Hcc'2:= (eq_sym (Hrc'3 pbn_data' Hpd'))).
      rewrite (read_data_block_unchanged c pbn_data' off' c' Hcc'2).
      trivial.

    assert (Hpd': pbn_data' <> pbn_log).
      intro HF.
      subst pbn_data'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      left.
      exists None.
      trivial.
    assert (Hcc'2:= (eq_sym (Hrc'3 pbn_data' Hpd'))).
    rewrite (read_data_block_unchanged c pbn_data' off' c' Hcc'2).
    trivial.

    assert (Hpl': pbn_log' <> pbn_log).
      intro HF.
      subst pbn_log'.
      assert (Hx := HI7_1 lbn lbn' pbn_log pbn_log (neq_refl Hlbn')).
      apply Hx; trivial.
      right.
      exists None.
      trivial.
    assert (Hbit'get' : bit_get bit' pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit' bi' pbn_log); trivial. 
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hcc':= (eq_sym (Hrc'3 pbn_log' Hpl'))).
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c' Hcc').
      trivial.
    trivial.

  (* case <4> (None, None) *)
  rewrite Hbme.
  rewrite Hoff.
  assert (HSC: I_fbq_len_greater_than_constant fbq).
    apply (I_fbq_len_greater_than_constant_derivable bit bmt); trivial.
  destruct (alloc_block_spec c bit bmt fbq HI1 HI3 HI4 HI8 HSC HJ)
      as [pf [c2 [f2 [bif2 [Ha [Hpf [Hbif2 [Hcc2_1 [Hcc2_2 [Hcc2_3 [Hbmt2 [Hbit2 [Hfbq2 HJc2]]]]]]]]]]]]].
  rewrite Ha.
  destruct f2 as [bit2 bmt2 fbq2].
  simpl in * .
  assert (Hbif2get: bit_get bit2 pf = Some bif2).
    apply (bit_update_bit_get_eq bit); trivial.
  rewrite Hbif2get.
  set (bi2 := bi_set_state bif2 (bs_log lbn blank_pmt)).
  assert (exists b2, chip_get_block c2 pf = Some b2
                       /\ (bi_state bi2 = bs_log lbn blank_pmt
                           /\ bi_used_pages bi2 = next_page b2
                           /\ block_state b2 = bs_free
                           /\ next_page b2 = 0
                           /\ (forall loc,
                                 valid_page_off loc
                                 -> exists p, block_get_page b2 loc = Some p
                                              /\ page_state p = ps_free))).
    unfold J_bi_block_coherent in HJc2.
    unfold chip_bi_coherent in HJc2.
    destruct (HJc2 pf bif2 Hbif2get) as [b2 [Hb2 Hco2]].
    destruct Hbif2 as [Hbif2_1 Hbif2_2].
    rewrite Hbif2_1 in Hco2.
    exists b2.
    split; trivial.
    subst bi2.
    unfold bi_state, bi_set_state.
    simpl.
    split; trivial.
    unfold block_coherent_erased in Hco2.
    destruct Hco2 as [Hx1 [Hx2 [Hx3 [Hx4 Hx5]]]].
    rewrite Hx2.
    split; trivial.
    split; trivial.
    split; trivial.
  destruct H as [b2 [Hgetb2 Hb2_2]].
  destruct (write_log_block_spec_write_emp c2 pf b2 bi2 off lbn d Hgetb2 Hpf Hoff Hb2_2)
      as [c3 [bi3 [Hw [Hbi3_1 [Hbi3_2 [Hbi3_3 [Hco3 [Hrc3 [Hr Hc2c3]]]]]]]]].
  rewrite Hw.
  assert (Hbmt2get: bmt_get bmt2 lbn = Some (None, None)).
      rewrite Hbmt2.
      trivial.
  destruct (bmt_update_log_spec bmt2 lbn pf (None, None) Hbmt2get)
        as [bmt3 [Hbmtup [Hbmt3_1 Hbmt3_2]]].
  rewrite Hbmt2 in Hbmtup.
  rewrite Hbmtup.
  destruct (bit_update_spec bit2 pf bif2 bi3 Hbif2get) as [bit3 [Hbit3 [Hbi3get Hbit3_2]]].
  rewrite Hbit3.
  exists c3, (mk_FTL bit3 bmt3 fbq2).
  split; trivial.
  split.
    (* case <4> (None, None) ==> <1> (log block is full) ==> <1> Inv (c', f') *)
    split.
      (* F_Inv preservation *)
      unfold F_Inv.
      simpl.
      split. (* I1 *)
        apply (I_pbn_bit_valid_preserv_bit_update pf bit2 bi3 bit3); auto.
        apply (I_pbn_bit_valid_preserv_bit_update pf bit bif2 bit2); auto.
      split. (* I2 *)
        subst bmt2.
        apply (I_pbn_bmt_valid_preserv_bmt_update_log bmt lbn pf bmt3); auto.
      split. (* I3 *)
        apply (I_pbn_fbq_valid_preserv_fbq_deq fbq pf fbq2 HI3); auto.
        destruct Hfbq2 as [_ [_ Hdeq]].
        trivial.
      split. (* I4 *)
        destruct Hfbq2 as [H1 [H2 Hdeq]].
        apply (I_pbn_fbq_state_preserv_bit_update bit2 fbq2 pf bi3 bit3); auto.
        apply (I_pbn_fbq_state_preserv_bit_update bit fbq2 pf bif2 bit2); auto.
        apply (I_pbn_fbq_state_preserv_fbq_deq bit fbq pf fbq2); trivial.
      split. (* I5 *)
        assert (Hst: exists pmt, bi_state bi3 = bs_log lbn pmt).
          destruct Hco3 as [b' [Hb' Hco']].
          unfold block_coherent_log in Hco'.
          destruct Hco' as [pmt [lbnx [Hbss _]]].
          unfold bi_lbn in Hbi3_2.
          rewrite Hbss in Hbi3_2.
          injection Hbi3_2.
          intro Hlbnx; subst lbnx.
          exists pmt. 
          trivial.
        subst bmt2.
        destruct Hst as [pmt Hst].
        apply (I_pbn_bmt_used_preserv_bmt_update_log bit2 bmt pf lbn bi3 pmt bit3 bmt3); trivial.
        apply (I_pbn_bmt_used_preserv_bit_update_irre bit bmt pf bif2 bit2 HI5 Hbit2); trivial.
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
        destruct Hfbq2 as [Hfbq' _].
        trivial.
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
        destruct Hfbq2 as [Hfbq' _].
        trivial.
      split. (* I6 *)
        destruct Hfbq2 as [_ [_ Hfbq2]].
        simpl in Hbmt3_1.
        subst bmt2.
        apply (I_pbn_habitation_preserv_bmt_update_log_case2 bmt fbq lbn pf bmt3 fbq2); trivial.
      split. (* I7_1 *)
        subst bmt2.
        apply (I_pbn_bmt_distinguishable_preserv_bmt_update_log bmt lbn pf bmt3 HI7_1); trivial.
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
        destruct Hfbq2 as [Hfbq' _].
        trivial.
      split. (* I7_2 *)
        subst bmt2.
        apply (I_pbn_bmt_distinguishable_2_preserv_bmt_update_log bmt lbn pf bmt3 HI7_2 Hbmtup); trivial.
        destruct Hfbq2 as [Hfbq' _].
        apply (I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6); trivial.
      split. (* I8 *)
        destruct Hfbq2 as [_ [_ Hfbq2]].
        apply (I_pbn_fbq_distinguishable_preserv_fbq_deq fbq pf fbq2 HI8 Hfbq2); trivial.
      (* I10 *)
      subst bmt2.
      apply (I_valid_lbn_has_entry_in_bmt_preserv_bmt_update_log bmt lbn pf bmt3 HI10 Hbmtup); trivial.
    (* R_Inv *)
    unfold R_Inv.
    simpl.

    destruct Hco3 as [b' [Hgetb' Hco3]].
    apply (J_bi_block_coherent_preserv_write_block_log c2 bit2 pf bi3 b' c3 bit3 HJc2 Hbit3 Hgetb' Hc2c3); trivial.

    (* case <4> (None, None) ==> <1> (log block is full) ==> <2> Write_Read_on_Spot *)
    split.
      unfold FTL_read.
      rewrite Hoff.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.
      rewrite Hrc3.
      trivial.
    (* case <4> (None, None) ==> <1> (log block is full) ==> <3> Write Read out of Spot, in the same block *)
    split.
      intros off' Hoff'neq.
      unfold FTL_read at 1.
      simpl.
      rewrite Hbmt3_1.
      simpl.
      rewrite Hbi3get.

      rewrite (Hr off' (neq_refl Hoff'neq)).
      (* rewrite <- (Hread lbn off'). *)
      unfold FTL_read.
      simpl.
      rewrite Hbme.
      trivial.

    (* case <4> (None, None) ==> <1> (log block is full) ==> <4> Write Read out of Spot, in different blocks *)
    intros lbn' off' Hlbn'.
    unfold FTL_read.
    simpl.
    assert (HB: bmt_get bmt3 lbn' = bmt_get bmt lbn').
      subst bmt2.
      rewrite (bmt_update_log_bmt_get_neq bmt lbn pf bmt3 lbn' Hbmtup (neq_refl Hlbn')).
      trivial.
    rewrite HB.
    destruct (bmt_get bmt lbn') as [bmr' | ] eqn:Hbmtget'; trivial.
    destruct bmr' as [bmr_data' bmr_log'].
    destruct bmr_data' as [pbn_data' | ]; destruct bmr_log' as [pbn_log' | ].
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists (Some pbn_data').
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (Some pbn_log').
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'.
      assert (Hc2c:= Hcc2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c2 (eq_sym Hc2c)).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
      assert (Hc2cx:= Hcc2_3 pbn_data' Hpd').
      assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
      rewrite (read_data_block_unchanged c pbn_data' off' c2 (eq_sym Hc2cx)).
      rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
      trivial.
      trivial.
    assert (Hpd': pbn_data' <> pf).
      intro HF.
      subst pbn_data'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      left.
      exists (None).
      trivial.
    assert (Hc2cx:= Hcc2_3 pbn_data' Hpd').
    assert (Hc3c2x:= Hc2c3 pbn_data' Hpd').
    rewrite (read_data_block_unchanged c pbn_data' off' c2 (eq_sym Hc2cx)).
    rewrite (read_data_block_unchanged c2 pbn_data' off' c3 (eq_sym Hc3c2x)).
    trivial.
    assert (Hpl': pbn_log' <> pf).
      intro HF.
      subst pbn_log'.
      assert (Hx:= I_pbn_habitation_in_fbq_implies_not_in_bmt pf bmt fbq Hpf HI6).
      destruct Hfbq2 as [Hpf1 _].
      apply Hx; trivial.
      exists lbn'.
      right.
      exists None.
      trivial.
    assert (Hbit'get' : bit_get bit3 pbn_log' = bit_get bit pbn_log').
      rewrite (bit_update_bit_get_neq bit2 pbn_log' bit3 _ pf Hbit3 Hpl').
      rewrite (bit_update_bit_get_neq bit pbn_log' bit2 _ pf Hbit2 Hpl').
      trivial.
    rewrite Hbit'get'.
    destruct (bit_get bit pbn_log') as [bilog' | ] eqn:Hbilog'; trivial.
      assert (Hc2c:= Hcc2_3 pbn_log' Hpl').
      assert (Hc3c2:= Hc2c3 pbn_log' Hpl').
      rewrite (read_log_block_unchanged c pbn_log' off' bilog' c2 (eq_sym Hc2c)).
      rewrite (read_log_block_unchanged c2 pbn_log' off' bilog' c3 (eq_sym Hc3c2)).
      destruct (read_log_block c3 bilog' pbn_log' off') as [ d' | ]; trivial.
    trivial.
 
Qed.

Lemma ftl_write_some_implies_valid_addr: 
  forall c f lbn off d c' f',
    Inv c f
    -> FTL_write c f lbn off d = Some (c', f')
    -> valid_logical_block_no lbn
       /\ valid_page_off off.
Proof.
  intros c f lbn off d c' f' HI Hw.
  unfold FTL_write in Hw.
  destruct (bvalid_page_off off) eqn:Hvo.
  destruct HI as [HFI HRI].
  destruct HFI as [HI1 [HI2 [HI3 [HI4 [HI5 [HI6 [HI7_1 [H7_2 [HI8 HI10]]]]]]]]].
  destruct (HI10 lbn) as [Hx Hy].
  destruct (bmt_get (ftl_bm_table f) lbn) as [bmr | ] eqn:Hget.
  split; trivial.
  apply Hy.
  exists bmr; trivial.
  discriminate.
  discriminate.
Qed.
