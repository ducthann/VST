(* Instead of deriving a juicy-machine execution from the CSL proof, we derive a dry-machine execution
   directly, along the lines of the sequential adequacy proof (veric/SequentialClight). *)
Require Import Coq.Strings.String.

From Coq Require Import FunctionalExtensionality.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.

Require Import VST.msl.eq_dec.
Require Import VST.veric.external_state.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SequentialClight.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.canon.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
(*Require Import VST.concurrency.juicy.juicy_machine.*)
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
(*Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_initial.
Require Import VST.concurrency.juicy.semax_progress.
Require Import VST.concurrency.juicy.semax_preservation_jspec.
Require Import VST.concurrency.juicy.semax_safety_makelock.
Require Import VST.concurrency.juicy.semax_safety_spawn.
Require Import VST.concurrency.juicy.semax_safety_release.
Require Import VST.concurrency.juicy.semax_safety_freelock.
Require Import VST.concurrency.juicy.semax_preservation.
Require Import VST.concurrency.juicy.semax_simlemmas.*)
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Require Import VST.veric.Clight_initial_world.
Require Import VST.concurrency.juicy.initial_world_with_rmap.
Require Import VST.veric.initialize.
Require Import iris_ora.algebra.gmap.


Import ThreadPool.
Set Bullet Behavior "Strict Subproofs".

Definition funspec_auth `{!funspecGS Σ} m :=
  own (inG0 := funspec_inG) funspec_name (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) m).

Section semax_prog_with_rmap.
  Context `{!VSTGS OK_ty Σ} (OK_spec : Jext_spec Σ).

  Definition state_interp_with_rmap (m : mem) (z : OK_ty) (σ : rmap) : iProp Σ :=
    frag_mem_auth 1 m σ ∗ ext_auth z.

  Lemma inflate_initial_mem_with_rmap_rev :
    forall m bounds (gev : Genv.t Clight.fundef type) G
       (vl : list (ident * globdef Clight.fundef type)) (Hnr : list_norepet (map fst (rev vl)))
           (SAME_IDS : match_fdecs (prog_funct' vl) (rev G)),
      inflate_initial_mem_with_rmap m bounds gev G ⊣⊢
        inflate_initial_mem_with_rmap m bounds gev (rev G).
  Proof.
    intros.
    rewrite /inflate_initial_mem_with_rmap.
    apply big_sepL_proper; intros.
    destruct (bounds _).
    apply big_sepL_proper; intros.
    rewrite /inflate_loc_with_rmap.
    destruct (access_at _ _ _); last done.
    destruct p; try done.
    rewrite /funspec_of_loc.
    if_tac; try done.
    destruct (Genv.invert_symbol _ _) eqn:Hb; last done.
    rewrite find_id_rev //.
    rewrite -list_norepet_rev -map_rev -match_fdecs_norepet //.
    apply list_norepet_prog_funct'.
    rewrite -list_norepet_rev -map_rev //.
  Qed.

  Lemma init_data_list_lem_with_rmap :
  forall (ge : genv) m0 (v : globvar type) m1 b m2 m3 m4,
    Mem.alloc m0 0 (init_data_list_size (gvar_init v)) = (m1, b) ->
    store_zeros m1 b 0 (init_data_list_size (gvar_init v)) = Some m2 ->
    Genv.store_init_data_list ge m2 b 0 (gvar_init v) = Some m3 ->
    Mem.drop_perm m3 b 0 (init_data_list_size (gvar_init v))
              (Genv.perm_globvar v) = Some m4 ->
    forall {F} (gl : list (ident * globdef F type)) i G
      (SANITY : (common.AST.init_data_list_size (gvar_init v) < Ptrofs.modulus)%Z)
      (AL : initializers_aligned 0 (gvar_init v) = true)
      (Hgl : Mem.nextblock m0 = Z.to_pos (Z.succ (Zlength gl))),
      inflate_initial_mem_with_rmap
        m4 (globals_bounds 1 (gl ++ [(i, Gvar v)])) ge G
      ⊢
      inflate_initial_mem_with_rmap
        m0 (globals_bounds 1 gl) ge G ∗
      if gvar_volatile v then True
      else init_data_list2pred
             (genviron2globals (filter_genv ge))
             (gvar_init v)
             (readonly2share (gvar_readonly v))
             (Vptr b Ptrofs.zero).
  Proof.
    intros.
    rewrite /inflate_initial_mem_with_rmap.
    erewrite Mem.nextblock_drop,
      Genv.store_init_data_list_nextblock,
      Genv.store_zeros_nextblock,
      Mem.nextblock_alloc by done.
    rewrite Pos2Nat.inj_succ /= Nat.sub_0_r.
    destruct (Pos2Nat.is_succ (Mem.nextblock m0)) as (n & Hnext).
    rewrite Hnext seq_S big_sepL_app /=.
    pose proof (Mem.alloc_result _ _ _ _ _ H) as ->.
    iIntros "(Hrest & Hb & _)".
    iSplitL "Hrest".
    - rewrite Nat.sub_0_r.
      iApply (big_sepL_mono with "Hrest").
      intros ?? (-> & ?)%lookup_seq.
      rewrite globals_bounds_app1;
        last by rewrite Zlength_correct in Hgl; lia.
      destruct (globals_bounds _ _ _).
      iIntros "Hrest".
      iApply (big_sepL_mono with "Hrest").
      intros.
      rewrite /Mem.drop_perm in H2.
      destruct Mem.range_perm_dec; inv H2.
      rewrite /inflate_loc_with_rmap /access_at /contents_at /=.
      assert (Pos.of_nat (S k) <> Mem.nextblock m0) by lia.
      erewrite store_init_data_list_other_block; [|eassumption..].
      erewrite store_zeros_other_block; [|eassumption..].
      erewrite mem_lemmas.AllocContentsOther; [|eassumption..].
      rewrite Maps.PMap.gso //.
      apply (alloc_dry_unchanged_on
               _ _ (Pos.of_nat (S k), (z + y)%Z))
        in H as (Haccess & Hcontents);
        last by intros [??].
      rewrite {1}/access_at /= in Haccess.
      apply equal_f with Cur in Haccess.
      rewrite Haccess.
      erewrite <- store_zeros_access by eassumption.
      by apply store_init_data_list_outside'
        in H1 as (Hcontents3 & -> & _).
    - destruct (gvar_volatile v) eqn:VOL; first done.
      rewrite -Hnext Pos2Nat.id.
      pose proof (nth_error_app gl [(i, Gvar v)] O) as Hv.
      replace (length gl)
        with (Pos.to_nat (Mem.nextblock m0) - 1)%nat in Hv
          by (rewrite Zlength_correct in Hgl; lia).
      rewrite Nat.add_0_r /= in Hv.
      erewrite globals_bounds_nth; [|lia|done].
      simpl.
      pose proof (load_store_init_data_lem1 H0 H1).
      assert
        (forall (chunk : memory_chunk) (ofs : Z),
            Mem.load chunk m4 (Mem.nextblock m0) ofs =
              Mem.load chunk m3 (Mem.nextblock m0) ofs).
      {
        intros.
        eapply Mem.load_drop; eauto.
        right; right; right.
        rewrite /Genv.perm_globvar VOL.
        simple_if_tac; constructor.
      }
      rewrite seq_app big_sepL_app.
      iDestruct "Hb" as "(Hb & Hend)".
      iAssert emp with "[Hend]" as "_".
      {
        rewrite /inflate_loc_with_rmap /=.
        pose proof (init_data_list_size_pos (gvar_init v)).
        rewrite Z.add_0_l Z2Nat.id; last lia.
        erewrite <- access_drop_3; [|eauto|lia].
        edestruct store_init_data_list_outside'
          as (_ & <- & _); first done.
        erewrite store_zeros_access by done.
        erewrite <- alloc_access_other; [|eauto|lia].
        rewrite nextblock_access_empty //; last lia.
      }
      
    (* In this range [drop_perm] installs [Readable] or [Writable],
       so the old and new inflate-location predicates coincide. *)
      iAssert ([∗ list] o ∈ seq 0 (Z.to_nat (init_data_list_size (gvar_init v))),
         inflate_loc m4 ge G (Mem.nextblock m0, (0 + Z.of_nat o)%Z)) with "[Hb]" as "Hb_old".
      {
        iApply (big_sepL_mono with "Hb").
        intros k o (-> & Hk)%lookup_seq.
        rewrite /inflate_loc_with_rmap /inflate_loc.
        erewrite drop_perm_access by done.
        rewrite Z.sub_0_r.
        rewrite if_true.
        2: {
          split; first done.
          split; first lia.
          pose proof (init_data_list_size_pos (gvar_init v)) as Hpos.
          apply Nat2Z.inj_lt in Hk. lia.
        }
        rewrite /Genv.perm_globvar VOL.
        erewrite drop_perm_access by exact H2.
        rewrite Z.sub_0_r.
        rewrite if_true.
        2: {
          split; first reflexivity.
          split; lia. }
        rewrite /Genv.perm_globvar VOL.
        destruct (gvar_readonly v) eqn:Hreadonly; done.
      }
      iApply (init_data_list_lem' _ _ _ _ _ _ [] with "Hb_old");
        try done.
      + eapply Genv.load_store_init_data_invariant,
          Genv.store_init_data_list_charact; try done.
        eapply Genv.store_zeros_read_as_zero; eauto.
      + intros.
        erewrite drop_perm_access by done.
        rewrite Z.sub_0_r if_true //.
      + intros.
        eapply load_store_init_data1_invariant; eauto.
  Qed.

  Lemma global_initializers_with_rmap :
    forall (prog : Clight.program) G m
      (Hnorepet : list_norepet (prog_defs_names prog))
      (AL: initialize.all_initializers_aligned prog)
      (SAME_IDS: match_fdecs (prog_funct prog) G)
      (Hinit : Genv.init_mem prog = Some m),
      inflate_initial_mem_with_rmap m (block_bounds prog) (globalenv prog) G ⊢
        initialize.globvars2pred (initialize.globals_of_genv (filter_genv (globalenv prog)))
        (prog_vars prog).
  Proof.
    intros prog G m Hnorepet AL SAME_IDS Hinit.
    change
      (inflate_initial_mem_with_rmap m (block_bounds prog) (globalenv prog) G ⊢
         globvars2pred (genviron2globals (filter_genv (globalenv prog))) (prog_vars prog)).
    set (gp := globalenv prog).
    unfold all_initializers_aligned in AL.
    unfold Genv.init_mem in Hinit.
    unfold globalenv, Genv.globalenv in *.
    unfold prog_vars, prog_funct in *.
    destruct prog as [fl prog_pub main prog_types cenv Hcenv].
    simpl in * |-.
    simpl prog_vars'.
    simpl initial_core.
    remember (Genv.add_globals _ fl) as gev.
    rewrite <- (rev_involutive fl) in *.
    rewrite alloc_globals_rev_eq in Hinit.
    forget (rev fl) as vl.
    unfold prog_defs_names in Hnorepet.
    simpl in Hnorepet.
    rewrite <- rev_prog_vars' in AL |- *.
    rewrite <- rev_prog_funct' in SAME_IDS.
    rewrite globvars2pred_rev.
    rewrite forallb_rev in AL.
    rewrite <- (rev_involutive G) in SAME_IDS.
    rewrite match_fdecs_rev in SAME_IDS.
    2: {
      apply list_norepet_prog_funct'.
      rewrite <- list_norepet_rev, <- map_rev; auto.
    }
    rewrite -> inflate_initial_mem_with_rmap_rev with (vl := vl) by auto.
    rewrite map_rev in Hnorepet.
    rewrite list_norepet_rev in Hnorepet.
    forget (rev G) as G'.
    clear G.
    rename G' into G.
    assert (Hsymb := add_globals_hack _ _ prog_pub Hnorepet Heqgev).
    assert (H1 : forall j, In j (map (@fst _ _) G) -> ~ In j (map (@fst _ _) (prog_vars' vl))).
    { intros j Hj.
      pose proof (proj2 (match_ids (prog_funct' vl) G j SAME_IDS) Hj) as Hin'.
      clear -Hnorepet Hin'.
      intro Hjvar.
      induction vl.
      { inv Hjvar. }
      inv Hnorepet.
      specialize (IHvl H2).
      destruct a as [i [fd | gv]]; simpl in *.
      - destruct Hin' as [Hin' | Hin'].
        + subst j.
          clear -Hjvar H1.
          apply H1; clear H1.
          induction vl; simpl in *; auto.
          destruct a as [i' [fd' | gv']]; auto.
          destruct Hjvar; auto.
        + apply IHvl; auto.
      - destruct Hjvar as [Hjvar | Hjvar].
        + subst j.
          apply H1; clear -Hin'.
          induction vl; simpl in *; auto.
          destruct a as [i' [fd' | gv']]; auto.
          destruct Hin'; auto.
        + apply IHvl; auto.
    }
    assert (H1' : forall j, In j (map fst (prog_funct' vl)) -> In j (map fst G)).
    { clear -SAME_IDS.
      forget (prog_funct' vl) as fs.
      intro j.
      induction SAME_IDS; simpl; auto; tauto.
    }
    assert (NRG : list_norepet (map fst G)).
    {
      clear -SAME_IDS Hnorepet.
      eapply match_fdecs_norepet; eauto.
      apply list_norepet_prog_funct'; auto.
    }
    clear SAME_IDS Heqgev.
    change (map fst vl)
      with (map fst (@nil (ident * funspec)) ++ map fst vl)
      in Hnorepet.
    change G with (nil ++ G).
    set (G0 := @nil (ident * funspec)) in *.
    change G with (G0 ++ G) in NRG.
    clearbody G0.
    revert Hsymb m G0 G NRG Hnorepet Hinit H1 H1'.
    induction vl; intros; simpl.
    - inv Hinit.
      rewrite /globvars2pred /=.
      by iIntros "_".
    - simpl in Hinit.
      revert Hinit.
      case_eq (alloc_globals_rev gev Mem.empty vl); intros; try congruence.
      spec IHvl.
      { clear -AL.
        simpl in AL.
        destruct a as [i g].
        destruct g; auto.
        simpl in AL.
        apply andb_true_iff in AL.
        destruct AL; auto.
      }
      spec IHvl.
      { intros.
        assert (H4' : (Pos.to_nat b <= length vl)%nat).
        { clear -H0. rewrite Zlength_correct in H0. lia. }
        assert (POS := Pos2Z.is_pos b).
        rewrite Hsymb.
        rewrite Pos_to_nat_eq_S /=.
        replace
          (length vl - (Z.to_nat (Z.pos b) - 1))%nat
          with
          (S (length vl - S (Z.to_nat (Z.pos b) - 1)))%nat
          by (simpl; pose proof (Pos2Nat.is_pos b); lia).
        simpl.
        apply iff_refl.
        rewrite Zlength_cons.
        lia.
      }
      destruct a as [i g].
      assert (FS : Genv.find_symbol gev i = Some (Mem.nextblock m0)).
      { assert (Genv.find_symbol gev i = Some (Mem.nextblock m0)); auto.
        apply Hsymb.
        apply alloc_globals_rev_nextblock in H.
        rewrite H.
        rewrite Zlength_cons.
        rewrite Z2Pos.id.
        + rewrite Zlength_correct; lia.
        + rewrite Zlength_correct; lia.
        + simpl.
          apply alloc_globals_rev_nextblock in H.
          rewrite H.
          replace
            (Pos.to_nat (Z.to_pos (Z.succ (Zlength vl))))
            with (S (length vl))
            by (rewrite Pos_to_nat_eq_S Zlength_correct; lia).
          rewrite Nat.sub_diag.
          reflexivity.
      }
      specialize (IHvl m0 G0 G NRG).
      spec IHvl.
      { clear -Hnorepet.
        apply list_norepet_app in Hnorepet as [? [? ?]].
        inv H0.
        apply list_norepet_app; split3; auto.
        apply list_disjoint_cons_right in H1; auto.
      }
      specialize (IHvl H).
      spec IHvl.
      { intros ? Hin%H1 ?.
        contradiction Hin.
        destruct g; simpl; auto.
      }
      spec IHvl.
      { intros.
        apply H1'.
        destruct g; simpl; auto.
      }
      destruct g as [fd | v].
      + (* Gfun case *)
        simpl.
        simpl in Hinit.
        destruct (Mem.alloc m0 0 1) eqn:Halloc.
        assert (Hfun : exists fs, funspec_of_loc gev (G0 ++ G) (Mem.nextblock m0, 0%Z) = Some fs).
        { assert (Hin_i : In i (map fst G)).
          { apply H1'. simpl; auto. }
          apply in_map_iff in Hin_i.
          destruct Hin_i as [[j fs] [Hij Hinfs]].
          simpl in Hij; subst j.
          exists fs.
          rewrite /funspec_of_loc /=.
          erewrite Genv.find_invert_symbol by exact FS.
          erewrite find_id_i; eauto.
          Search In "++".
          apply in_or_app; auto.
        }
        destruct Hfun as [fs Hfun].
        iIntros "Hmem".
        iApply IHvl.
        rewrite /inflate_initial_mem_with_rmap.
        erewrite Mem.nextblock_drop, Mem.nextblock_alloc by eassumption.
        replace (Pos.to_nat (Pos.succ _) - 1)%nat with (S (Pos.to_nat (Mem.nextblock m0) - 1))%nat
          by lia.
        rewrite seq_S big_sepL_app /= -Nat.sub_succ_l /=; last lia.
        iDestruct "Hmem" as "(Hmem & Hnew & _)".
        pose proof (Mem.alloc_result _ _ _ _ _ Halloc) as Hb.
        assert (Hfun1 : exists fs : funspec,
                   funspec_of_loc gev G (Mem.nextblock m0, 0%Z) = Some fs).
        {
          assert (Hin_i : In i (map fst G)).
          { apply H1'; simpl; auto. }
          rewrite in_map_iff in Hin_i.
          destruct Hin_i as [[i' fs1] [Hi Hinfs]].
          simpl in Hi.
          subst i'.
          exists fs1.
          rewrite /funspec_of_loc /=.
          erewrite Genv.find_invert_symbol by exact FS.
          erewrite find_id_i; eauto.
          rewrite map_app in NRG.
          apply list_norepet_app in NRG as [_ [NRG_G _]]; auto.
        }
        destruct Hfun as [fs1 Hfun].
        iPoseProof (affine with "Hnew") as "_".
        { destruct (block_bounds _) as [lo hi].
          apply big_sepL_affine.
          intros k o Ho.
          rewrite /inflate_loc_with_rmap.
          rewrite Nat.sub_0_r Pos2Nat.id.
          erewrite drop_perm_access by eassumption.
          if_tac.
          - replace (lo + Z.of_nat o)%Z with 0%Z.
            2: { destruct H0 as [_ [? ?]]; lia. }
            destruct Hfun1 as (? & Hfun1).
            rewrite Hfun1.
            apply _.
          - eapply alloc_dry_unchanged_on
              in H0 as [Ha _]; last done.
            rewrite -Ha nextblock_access_empty //; last lia.
            apply _.
        }
        iApply (big_sepL_mono with "Hmem").
        intros ?? (-> & ?)%lookup_seq.
        rewrite /block_bounds /=.
        apply alloc_globals_rev_nextblock in H.
        rewrite globals_bounds_app1;
          last by rewrite Zlength_correct in H; rewrite rev_length; lia.
        destruct (globals_bounds _ _ _).
        iIntros "Hmem".
        iApply (big_sepL_mono with "Hmem").
        intros.
        rewrite /inflate_loc_with_rmap.
        pose proof (Mem.alloc_result _ _ _ _ _ Halloc) as ->.
        assert (Pos.of_nat (S k) <> Mem.nextblock m0) by lia.
        erewrite <- access_drop_3; [|eassumption|auto].
        erewrite <- alloc_access_other; [|eassumption|auto].
        erewrite <- drop_perm_contents by eassumption.
        rewrite /contents_at.
        erewrite mem_lemmas.AllocContentsOther1; done.
      + (* Gvar case *)
        rewrite /globvars2pred /globvar2pred /=.
        simpl in Hinit.
        destruct (Mem.alloc m0 0) eqn:Halloc.
        destruct (store_zeros m1 b 0 _) eqn:Hstore; last done.
        destruct (Genv.store_init_data_list _ _ _ _ _)
          eqn:Hinit_data; last done.
        rewrite /= !andb_true_iff in AL.
        destruct AL as ((? & ?%Z.ltb_lt) & ?).
        rewrite (init_data_list_lem_with_rmap gp) //.
        rewrite IHvl.
        iIntros "($ & ?)".
        rewrite /genviron2globals /Map.get /filter_genv FS.
        apply Mem.alloc_result in Halloc as ->; done.
        Locate Zlength_rev.
        rewrite sublist.Zlength_rev.
        eapply alloc_globals_rev_nextblock; eauto.
   Qed.
  
  Lemma semax_prog_rule_with_rmap {CS : compspecs} :
    forall V G prog m h z,
      postcondition_allows_exit OK_spec Ctypesdefs.tint ->
      semax_prog OK_spec (C := CS) prog z V G  ->
      Genv.init_mem prog = Some m ->
      { b : Values.block & { q : CC_core &
                            (Genv.find_symbol
                               (globalenv prog) (prog_main prog) = Some b) *
      (exists m',
         semantics.initial_core (cl_core_sem (globalenv prog)) h m q m' (Vptr b Ptrofs.zero) nil) *

      (state_interp Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z
       ⊢ |==> ∃ σ : rmap,
           state_interp_with_rmap m z σ ∗
           ⌜access_map_pointwise_eq (perm_of_rmap σ) (getCurPerm m)⌝ ∗
           (jsafeN OK_spec (globalenv prog) ⊤ z q ∧
            matchfunspecs (globalenv prog) G))
    } }%type.
  Proof.
    intros until z.
    intro EXIT.
    intros ? H1.
    generalize H; intros [? [AL [HGG [[? [GC ?]] [GV ?]]]]].
    destruct (find_id (prog_main prog) G) as [fspec |] eqn:Hfind; last first.
    rewrite Hfind in H4; try contradiction.
    assert (H4' : exists post, In (prog_main prog, main_spec_ext' prog z post) G /\
                            fspec = main_spec_ext' prog z post).
    { rewrite Hfind in H4.
      destruct H4 as [post ?].
      pose proof Hfind as Hin.
      apply find_id_e in Hin.
      exists post.
      subst fspec.
      split; auto.
    }
    clear H4.
    rename H4' into H4.
    assert (H5 : { f | In (prog_main prog, f) (prog_funct prog) }).
    forget (prog_main prog) as id.
    assert (H4' : In id (map fst G)).
    { destruct H4 as [? [H4 _]].
      apply in_map_fst in H4; auto. }
    pose proof (initialize.match_fdecs_in _ _ _ H4' H2).
    apply in_map_sig in H5.
    2: decide equality.
    destruct H5 as [[? ?] [? ?]]; subst.
    eauto.
    destruct H5 as [f H5].
    apply compute_list_norepet_e in H0.
    assert (indefs : In (prog_main prog, Gfun f) (AST.prog_defs prog)).
    { apply in_prog_funct_in_prog_defs; auto. }
    pose proof (find_funct_ptr_exists prog (prog_main prog) f) as EXx.
    apply find_symbol_funct_ptr_ex_sig in EXx; auto.
    destruct EXx as [b [Hsymbol Hfunct]]; auto.
    destruct fspec as [[params retty] cc A E P Q].
    assert (cc = cc_default /\ params = nil) as (-> & ->).
    { clear -H4; destruct H4 as [? [? ?]]; inv H0; auto. }
    assert (Hretty : retty = Ctypesdefs.tint).
    { destruct H4 as [post [? ?]]; by inv H6. }
    subst retty.
    assert (SPEP := semax_prog_entry_point OK_spec V G prog b (prog_main prog)
                      nil nil A E P Q h z EXIT H Hsymbol Hfind).
    spec SPEP.
    constructor.
    set (gargs := (filter_genv (globalenv prog), @nil val)) in *.
    cbv beta iota zeta in SPEP.
    destruct SPEP as [q [Hinit Hsafe]].
    exists b, q.
    split; [split |]; auto.
    clear Hinit.
    iIntros "((Hm & Hext) & Hf & Hz)".
    iMod (initialize_mem_with_rmap' with "[$Hm $Hf]")
      as "((%σ & Hσ & %Hperm) & Hm & Hcore & Hmatch)"; [done.. |].
    iModIntro.
    iExists σ.
    iSplitL "Hσ Hext".
    { rewrite /state_interp_with_rmap; iFrame. }
    iSplit.
    { iPureIntro; done. }
    iSplit; last done.
    destruct H4 as [post [H4 H4']].
    unfold main_spec_ext' in H4'.
    injection H4' as -> HP HQ.
    apply inj_pair2 in HP as ->.
    apply inj_pair2 in HQ as ->.
    iApply (Hsafe (initialize.globals_of_genv (filter_genv (globalenv prog)))).
    iCombine "Hcore Hmatch" as "Hcore".
    rewrite (initial_core_funassert _ V _ _ (Map.empty _) (Map.empty _)) //; iFrame.
    iIntros "!>".
    iSplit; first done.
    iApply global_initializers_with_rmap; eauto.
Qed.
 
End semax_prog_with_rmap.

(* up *)
Existing Instance shared.shared_equiv.
Lemma coherent_equiv m σ1 σ2 : ✓ (σ1 : resource_map.rmapUR _ _ _) → σ1 ≡ σ2 → coherent m σ1 ↔ coherent m σ2.
Proof.
  intros Hv H; rewrite /coherent.
  apply Morphisms_Prop.all_iff_morphism; intros l.
  specialize (H l).
  f_equiv.
  - split; intros Hnone H1; apply Hnone in H1; rewrite H1 in H; inv H; auto.
  - rewrite /resource_at; erewrite resR_to_resource_eq; done.
Qed.

(*Definition add_fresh_block (b : Values.block) (cur : access_map) : access_map :=
  PMap.set b (fun _ => None) cur.

(* Definition remove_region (b: Values.block) (lo hi: Z) (pm: access_map) : access_map :=
  setPermBlock None b lo pm (Z.to_nat (hi - lo)). *)

(* Half-open range [lo, hi) implemented via length = Z.to_nat (hi - lo) *)
Definition setPerm_range (p : option permission)
  (b : Values.block) (lo hi : Z) (cur : access_map)
  : access_map :=
  if Z.leb hi lo then cur
  else setPermBlock p b lo cur (Z.to_nat (hi - lo)).

Definition remove_region (b : Values.block) (lo hi : Z) (cur : access_map)
  : access_map := setPerm_range None b lo hi cur.

Definition add_region (b : Values.block) (lo hi : Z) (perm : permission) (cur : access_map)
  : access_map := setPerm_range (Some perm) b lo hi cur.
*)

Definition can_store_at (p : access_map) (l : positive * Z) : Prop :=
  match (p # (fst l)) (snd l) with
  | Some q => perm_order q Writable   (* or just: perm_order Writable q *)
  | None   => False
  end.

Lemma writable_at_equiv (p : access_map) (l : positive * Z) :
  (match (p # (fst l)) (snd l) with
   | Some q => perm_order q Writable
   | None   => False
   end) <->
    Mem.perm_order'' ((p # (fst l)) (snd l)) (Some Writable).
Proof.
  unfold Mem.perm_order''.
  destruct ((p # (fst l)) (snd l)) as [q|]; cbn; split; auto.
Qed.

Definition contents_at (m : mem) (l : positive * Z) : memval :=
  ZMap.get (snd l) ((Mem.mem_contents m) # (fst l)).

Lemma writable_at_perm_order_cases (p : access_map) (loc : positive * Z) (x : option permission) :
  can_store_at p loc -> p # (loc.1) loc.2 = x -> x = Some Freeable \/ x = Some Writable.
Proof.
  rewrite /can_store_at.
  destruct (p # (loc.1) loc.2) as [q|] eqn: Hp; [|contradiction].
  intros; destruct x as [r|]; try tauto; try discriminate.
  inv H0. inv H. by right. by left.
Qed.

Lemma access_at_restrPermMap_Cur p m loc (Hlt : permMapLt p (getMaxPerm m)):
  access_at (restrPermMap Hlt) loc Cur = p # (loc.1) loc.2 .
Proof.
  destruct loc as [b ofs].
  assert (Hacc: forall m b ofs, access_at m (b,ofs) Cur = (getCurPerm m) # b ofs).
  { rewrite /getCurPerm /access_at /=. intros; by rewrite Maps.PMap.gmap. }
  rewrite Hacc.
  pose proof (mem_equiv.getCur_restr p m Hlt) as Heq.
  specialize (Heq b).
  by rewrite Heq.
Qed.

Lemma restrPermMap_Cur_eq m p (Hlt : permMapLt p (getMaxPerm m)) :
  forall b ofs, (Mem.mem_access (restrPermMap Hlt)) # b ofs Cur = p # b ofs.
Proof.
  intros b ofs.
  pose proof (mem_equiv.getCur_restr p m Hlt) as Heq.
  assert (Heq1: forall b ofs m, Maps.PMap.get b (getCurPerm m) ofs =
                          Maps.PMap.get b (Mem.mem_access m) ofs Cur).
  { rewrite /getCurPerm. intros. by rewrite Maps.PMap.gmap. }
  specialize (Heq1 b ofs (restrPermMap Hlt)).
  rewrite -Heq1.
  specialize (Heq b).
  by rewrite Heq.
Qed.

Lemma readable_dfrac_perm_order m p dq
  (v : memval) (v0 : agree (leibnizO resource)) loc (Hlt : permMapLt p (getMaxPerm m))
  (rsh : readable_dfrac dq):
  (option_map (λ v : agree resource,
         proj1_sig (resource_map.elem_of_agree v)) (Some v0)) = Some (VAL v) ->
  Mem.perm_order'' (access_at (restrPermMap Hlt) loc Cur)
    (perm_of_res (resR_to_resource (Some (shared.YES dq rsh v0)))) ->
  Mem.perm_order'' (p # (loc.1) loc.2) (Some Readable).
Proof.
  pose proof (access_at_restrPermMap_Cur p m loc Hlt) as Haccess.
  intros ? Horder.
  rewrite Haccess in Horder.
  set dq1 := (shared.dfrac_of (shared.YES dq rsh v0)).
  set r1 := (option_map (λ v : agree resource, proj1_sig (resource_map.elem_of_agree v))
                (shared.val_of (shared.YES dq rsh v0))).
  pose proof (perm_of_res_cases dq1 r1) as Hperm_res.
  destruct Hperm_res as [Hperm_res1 | Hperm_res2].
  - destruct Hperm_res1 as (? & ? & Hres_dfrac).
    rewrite /dq1 /r1 in Hres_dfrac.
    simpl in Horder.
    destruct dq.
    destruct s.
    simpl in *.
    destruct (`(resource_map.elem_of_agree v0)).
    simpl in *.
    destruct x0.
    subst.
    rewrite /perm_of_sh in Horder.
    repeat if_tac in Horder; subst; simpl in *; try done;
      eapply mem_lemmas.po_trans; eauto; [try apply perm_F_any | try apply perm_W_R].
    + repeat if_tac in Hres_dfrac; subst.
      * by pose proof (bot_unreadable).
      * rewrite /perm_of_sh in Hres_dfrac.
        repeat if_tac in Hres_dfrac; subst; easy.
    + rewrite /perm_of_sh in Hres_dfrac.
      repeat if_tac in Hres_dfrac; subst; easy.
    + rewrite /perm_of_sh in Hres_dfrac.
      repeat if_tac in Hres_dfrac; subst; easy.
    + simpl in *; destruct (`(resource_map.elem_of_agree v0)); destruct x0;
      repeat if_tac in Hres_dfrac; subst; auto; try easy.
      rewrite mem_lemmas.po_oo in H1.
      eapply mem_lemmas.po_trans; eauto.
  - rewrite /dq1 /r1 /= in Hperm_res2; destruct Hperm_res2 as (? & Hperm_res2);
      simpl in *;  destruct dq; destruct s; destruct (`(resource_map.elem_of_agree v0));
      specialize (H0 v); easy.
Qed.

Lemma permMapLt_trans (p q r : access_map): permMapLt p q -> permMapLt q r -> permMapLt p r.
Proof.
  intros Hpq Hqr b ofs.
  eapply mem_lemmas.po_trans; eauto.
Qed.

Lemma can_store_at_getCurPerm_of_perm_order' (m : Mem.mem) (b : Values.block) (ofs : Z):
  Mem.perm_order' ((Mem.mem_access m) # b ofs Cur) Writable ->
  can_store_at (getCurPerm m) (b,ofs).
Proof.
  rewrite /Mem.perm_order' /can_store_at /getCurPerm /=.
  intros H.
  rewrite PMap.gmap.
  destruct ((Mem.mem_access m) # b ofs Cur); done.
Qed.
  
Lemma storebytes_contents_or_canstore_cur p m (Hlt : permMapLt p (getMaxPerm m))
  (m' : Mem.mem) b ofs bytes
  (Hst1 : Mem.storebytes (restrPermMap Hlt) b ofs bytes = Some m')
  (Hf : forall ofs0 : Z, (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z ->
      Mem.perm_order' ((Mem.mem_access (restrPermMap Hlt)) # b ofs0 Cur) Writable):
  forall loc, contents_at m' loc = contents_at (restrPermMap Hlt) loc
         \/ can_store_at (getCurPerm (restrPermMap Hlt)) loc.
Proof.
  intros [b0 ofs0].
  Transparent Mem.storebytes.
  rewrite /Mem.storebytes in Hst1.
  destruct (Mem.range_perm_dec (restrPermMap Hlt) b ofs
              (ofs + Z.of_nat (length bytes)) Cur Writable) as [Hrp | Hnrp]; try discriminate.
  inversion Hst1; subst m'; clear Hst1.
  Require Import Classical_Prop.
  destruct (peq b0 b) as [-> | Hbneq].
  - destruct (classic (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z) as [Hin | Hout].
    + right; apply can_store_at_getCurPerm_of_perm_order'; by apply Hf.
    + left; rewrite /contents_at /= PMap.gss Mem.setN_outside; auto. lia.
   - left; rewrite /contents_at PMap.gso //=.
Qed.

Lemma storebytes_contents_or_canstore_cur1 m (m' : Mem.mem) b ofs bytes
  (Hst1 : Mem.storebytes m b ofs bytes = Some m')
  (Hf : forall ofs0 : Z, (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z ->
      Mem.perm_order' ((Mem.mem_access m) # b ofs0 Cur) Writable):
  forall loc, contents_at m' loc = contents_at m loc \/ can_store_at (getCurPerm m) loc.
Proof.
  intros [b0 ofs0].
  Transparent Mem.storebytes.
  unfold Mem.storebytes in Hst1.
  destruct (Mem.range_perm_dec m b ofs (ofs + length bytes) Cur Writable)
    as [Hrp | Hnrp].
  2: discriminate.
  inversion Hst1; subst m'; clear Hst1.
  destruct (peq b0 b) as [-> | Hbneq].
  - destruct (classic (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z) as [Hin | Hout].
    + right.
      apply can_store_at_getCurPerm_of_perm_order'.
      by apply Hf.
    + left.
      rewrite /contents_at /=.
      rewrite PMap.gss.
      rewrite Mem.setN_outside; auto.
      lia.
   - left.
     rewrite /contents_at /=.
     rewrite PMap.gso //=.
Qed.

Lemma free_contents : forall m b lo hi m', Mem.free m b lo hi = Some m' ->
    Mem.mem_contents m' = Mem.mem_contents m.
Proof.
  intros m b lo hi m' H.
  Transparent Mem.free.
  unfold Mem.free in H.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable);
    inversion H; subst; simpl; reflexivity.
Qed.

Lemma free_list_contents :
  forall m l m',
    Mem.free_list m l = Some m' ->
    Mem.mem_contents m' = Mem.mem_contents m.
Proof.
  intros m l.
  revert m.
  induction l as [| [[b lo] hi] tl IH]; intros.
  - simpl in H. inversion H; subst. reflexivity.
  - simpl in H.
    destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; try discriminate.
    specialize (IH m1 m').
    apply IH in H.
    apply free_contents in Hfree.
    by rewrite <- Hfree.
Qed.

Lemma mem_contents_restrPermMap {p m}
  (Hlt : permMapLt p (getMaxPerm m)) :
  Mem.mem_contents (restrPermMap Hlt) = Mem.mem_contents m.
Proof. reflexivity. Qed.

Lemma free_preserve_disjoint_and_lt :
  forall (m m1 : mem) (b : positive) (lo hi : Z) (a : access_map),
    permMapLt a (getMaxPerm m) ->
    permMapsDisjoint (getCurPerm m) a ->
    Mem.free m b lo hi = Some m1 ->
    permMapsDisjoint (getCurPerm m1) a /\ permMapLt a (getMaxPerm m1).
Proof.
  intros m m1 b lo hi a Hlt Hdis Hfree.
  Transparent Mem.free.
  unfold Mem.free in Hfree.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); try discriminate.
  inv Hfree.
  split.
  - unfold permMapsDisjoint in *.
    intros.
    destruct (Pos.eq_dec b0 b) as [->|Hbneq].
    + rewrite /getCurPerm PMap.gmap PMap.gss /=.
      destruct (zle lo ofs) as [Hle|Hnle];
        destruct (zlt ofs hi) as [Hltz|Hnlt]; simpl.
      * by eexists.
      * specialize (Hdis b ofs) as [pu Hpu].
        rewrite /getCurPerm PMap.gmap in Hpu.
        by eexists.
      * specialize (Hdis b ofs) as [pu Hpu].
        rewrite /getCurPerm PMap.gmap in Hpu.
        by eexists.
      * specialize (Hdis b ofs) as [pu Hpu].
        rewrite /getCurPerm PMap.gmap in Hpu.
        by eexists.
    + specialize (Hdis b0 ofs) as [pu Hpu].
      rewrite /getCurPerm PMap.gmap in Hpu.
      exists pu.
      rewrite /getCurPerm !PMap.gmap PMap.gso //.
  - unfold permMapLt in *.
    intros.
    destruct (Pos.eq_dec b0 b) as [->|Hbneq].
    + specialize (Hlt b ofs).
      rewrite /getMaxPerm PMap.gmap PMap.gss.
      destruct (zle lo ofs) as [Hle|Hnle];
        destruct (zlt ofs hi) as [Hltz|Hnlt]; simpl.
      * destruct (a # b ofs) eqn:Ha; try done.
        rewrite /permMapsDisjoint in Hdis.
        destruct (Hdis b ofs) as [pu Hpu].
        have Hperm : Mem.perm m b ofs Cur Freeable.
        { apply r. lia. }
        rewrite /Mem.perm in Hperm.
        rewrite /getCurPerm PMap.gmap in Hpu.
        destruct ((Mem.mem_access m) # b ofs Cur) as [p1|] eqn:Hacc; try done.
        rewrite Ha in Hpu.
        rewrite /perm_union /= in Hpu;
          destruct p1; try discriminate; inv Hperm.
      * by rewrite /getCurPerm PMap.gmap in Hlt.
      * by rewrite /getCurPerm PMap.gmap in Hlt.
      * by rewrite /getCurPerm PMap.gmap in Hlt.
   + rewrite /getMaxPerm !PMap.gmap PMap.gso //.
     specialize (Hlt b0 ofs).
     by rewrite /getCurPerm PMap.gmap in Hlt.
Qed.

Lemma free_list_preserve_disjoint_and_lt :
  forall m l m' a,
    permMapLt a (getMaxPerm m) ->
    permMapsDisjoint (getCurPerm m) a ->
    Mem.free_list m l = Some m' ->
    permMapsDisjoint (getCurPerm m') a /\
      permMapLt a (getMaxPerm m').
Proof.
  intros m l m' a Hlt Hdis Hfl.
  generalize dependent m'.
  generalize dependent m.
  induction l as [| x tl IH]; intros m Hlt Hdis m' Hfl.
  - by inv Hfl.
  - destruct x as [[b lo] hi].
    simpl in Hfl.
    destruct (Mem.free m b lo hi) eqn: Hfree; try discriminate.
    destruct (free_preserve_disjoint_and_lt m m0 b lo hi a Hlt Hdis Hfree)
      as [Hdis1 Hlt1].
    eapply IH; eauto.
Qed.


Lemma mem_step_preserve_disjoint_and_lt :
  forall (mi mi' : mem) (a : access_map),
    permMapLt a (getMaxPerm mi) ->
    permMapsDisjoint (getCurPerm mi) a ->
    mem_step mi mi' ->
    permMapsDisjoint (getCurPerm mi') a /\
      permMapLt a (getMaxPerm mi').
Proof.
  intros mi mi' a Hlt Hdis Hs.
  revert a Hlt Hdis.
  induction Hs; intros a Hlt Hdis.
  4 : {
    destruct (IHHs1 _ Hlt Hdis) as [Hdis1 Hlt1].
    destruct (IHHs2 _ Hlt1 Hdis1) as [Hdis2 Hlt2].
    split; auto.
  }
  - apply Mem.storebytes_access in H.
    split.
    + assert (Hcur: getCurPerm m' = getCurPerm m).
      { by rewrite /getCurPerm H. }
      by rewrite Hcur.
    + assert (Hmax: getMaxPerm m' = getMaxPerm m).
      { by rewrite /getMaxPerm H. }
      by rewrite Hmax.
  - unfold permMapsDisjoint in *.
    have Hfresh : ~ Mem.valid_block m b'.
    { eapply Mem.fresh_block_alloc; eauto. }
    split.
    + intros.
      destruct (Pos.eq_dec b b') as [->|Hneq].
      * have HaNone : a # b' ofs = None.
        { eapply invalid_block_empty; eauto. }
        exists ((getCurPerm m') # b' ofs).
        rewrite HaNone.
        rewrite /perm_union /=.
        destruct ((getCurPerm m') # b' ofs) as [p|] eqn:Hc; simpl; reflexivity.
      * specialize (Hdis b ofs) as [pu Hpu].
        exists pu.
        simpl.
        assert (Hcur: (getCurPerm m') # b ofs = (getCurPerm m) # b ofs).
        {
          rewrite /getCurPerm !PMap.gmap.
          inv H; simpl.
          rewrite PMap.gso //.
        }
        by rewrite Hcur.
    + unfold permMapLt in *.
      intros.
      destruct (Pos.eq_dec b b') as [->|Hneq].
      * have HaNone : a # b' ofs = None.
        { eapply invalid_block_empty; eauto. }
        rewrite HaNone.
        apply perm_order''_None.
      * specialize (Hlt b ofs).
        inv H; simpl.
        unfold getMaxPerm in *.
        rewrite !PMap.gmap //= in Hlt |- *.
        rewrite PMap.gso //.
  - eapply free_list_preserve_disjoint_and_lt; eauto.
Qed.

(*
Definition perm_row_of_rmap (σ : rmap) (b : positive) : Z -> option permission :=
    fun ofs => perm_of_res (σ @ (b, ofs)).

  (* step: Given the current permission map p, update block b to use the row computed from σ.
     σ has many entries, but perm_of_rmap σ must return one final access_map
     start with empty map, update with entry 1, 2, .... and return final map

   *)
Definition perm_of_rmap (σ : rmap) : access_map :=
    fold_right (fun '(loc, _) p => PMap.set loc.1 (perm_row_of_rmap σ loc.1) p)
      (PMap.init (fun _ => None)) (map_to_list σ).
  
Lemma perm_row_of_rmap_lookup : forall σ b ofs,
    perm_row_of_rmap σ b ofs = perm_of_res (σ @ (b, ofs)).
  Proof. reflexivity. Qed.

Lemma perm_of_rmap_fold_lookup : forall σ l b ofs,
    (forall ofs0 r, σ !! (b, ofs0) = Some r -> ((b, ofs0), r) ∈ l) ->
    (fold_right (fun '(loc, _) (p : PMap.t (Z -> option permission)) =>
          PMap.set loc.1 (perm_row_of_rmap σ loc.1) p) (PMap.init (fun _ => None)) l) # b ofs =
    perm_of_res (σ @ (b, ofs)).
Proof.
  intros σ l.
  induction l as [| [[b0 ofs0] r0] l IH]; intros b ofs Hin; simpl.
  - rewrite PMap.gi.
    assert (σ !! (b, ofs) = None) as Hnone.
    { destruct (σ !! (b, ofs)) as [r|] eqn:Hlook; auto.
      specialize (Hin ofs r Hlook); inversion Hin.
    }
    by rewrite /resource_at Hnone /= eq_dec_refl.
  - destruct (Pos.eq_dec b0 b) as [-> | Hb].
    + by rewrite PMap.gss /perm_row_of_rmap.
    + rewrite PMap.gso //.
      apply IH.
      intros ofs1 r1 Hlook.
      specialize (Hin ofs1 r1 Hlook).
      rewrite elem_of_cons in Hin.
      destruct Hin as [Hin | Hin]; try done.
      by inversion Hin; subst.
Qed.

  Lemma perm_of_rmap_lookup : forall σ b ofs,
      (perm_of_rmap σ) # b ofs = perm_of_res (σ @ (b, ofs)).
  Proof.
    intros σ b ofs.
    rewrite /perm_of_rmap.
    apply perm_of_rmap_fold_lookup.
    intros; rewrite elem_of_map_to_list //.
  Qed.
*)



  Lemma free_preserves_other_cur (q : access_map) (m m' : mem) (b : Values.block) (lo hi : Z) :
    permMapLt q (getCurPerm m) ->
    permMapsDisjoint (getCurPerm m) q ->
    Mem.free m b lo hi = Some m' ->
    permMapLt q (getCurPerm m') /\ permMapsDisjoint (getCurPerm m') q.
  Proof.
    intros Hq Hdisj Hfree.
    split.
    - (* q remains below the current permissions *)
      intros b' ofs.
      destruct (q # b' ofs) as [pq |] eqn:Hq_at.
      2: { apply perm_order''_None. }
      assert (Hperm : Mem.perm m b' ofs Cur pq).
      { unfold Mem.perm.
        specialize (Hq b' ofs).
        unfold getCurPerm in Hq.
        rewrite Hq_at in Hq.
        rewrite mem_lemmas.po_oo.
        by rewrite PMap.gmap in Hq. }
      pose proof (Mem.perm_free_inv m b lo hi m' Hfree b' ofs Cur pq Hperm) as Hinv.
      destruct Hinv as [[Hb Hin] | Hperm'].
      + subst b'.
        (* A successful free requires Freeable here. *)
        exfalso.
        unfold permMapLt in Hq.
        specialize (Hq b ofs).
        rewrite Hq_at in Hq.
        pose proof (Mem.free_range_perm _ _ _ _ _ Hfree) as Hfreeable.
        specialize (Hfreeable ofs Hin).
        unfold permMapsDisjoint in Hdisj.
        specialize (Hdisj b ofs).
        destruct Hdisj as (pu & Hdisj).
        rewrite Hq_at in Hdisj.
        unfold getCurPerm in Hdisj.
        rewrite PMap.gmap in Hdisj.
        destruct ((Mem.mem_access m) # b ofs Cur) as [pm |] eqn:Hm.
        * unfold Mem.perm, Mem.perm_order' in Hfreeable.
          rewrite Hm in Hfreeable.
          assert (pm = Freeable) as ->.
          { destruct pm; inversion Hfreeable; reflexivity. }
          simpl in Hdisj. done.
        * unfold Mem.perm, Mem.perm_order' in Hfreeable.
          by rewrite Hm in Hfreeable.
      + unfold getCurPerm.
        rewrite PMap.gmap.
        by rewrite perm_access /access_at /= in Hperm'.
    - (* Removing permissions preserves disjointness. *)
      unfold permMapsDisjoint in *.
      intros b' ofs.
      specialize (Hdisj b' ofs).
      pose proof (Mem.free_result _ _ _ _ _ Hfree) as Hres.
      rewrite Hres.
      unfold getCurPerm.
      rewrite PMap.gmap.
      unfold Mem.unchecked_free; simpl.
      unfold getCurPerm in Hdisj.
      rewrite PMap.gmap in Hdisj.
      rewrite PMap.gsspec.
      destruct (peq b' b) as [-> | Hneq].
      + destruct (zle lo ofs && zlt ofs hi).
        * exists (q # b ofs); simpl; done.
        * done.
      + done.
  Qed.

  Lemma free_list_preserves_other_cur
    (q : access_map) :
    forall (l : list (Values.block * Z * Z)) (m m' : mem),
      permMapLt q (getCurPerm m) ->
      permMapsDisjoint (getCurPerm m) q ->
      Mem.free_list m l = Some m' ->
      permMapLt q (getCurPerm m') /\
        permMapsDisjoint (getCurPerm m') q.
  Proof.
    induction l as [| [[b lo] hi] l IH];
      intros m m' Hq Hdisj Hfree.
    - simpl in Hfree.
      inversion Hfree; subst.
      split; assumption.
    - simpl in Hfree.
      destruct (Mem.free m b lo hi) as [m1 |] eqn:Hfree1;
        try discriminate.

      pose proof
        (free_preserves_other_cur
           q m m1 b lo hi Hq Hdisj Hfree1)
        as [Hq1 Hdisj1].

      eapply IH; eauto.
  Qed.

  Lemma permMapLt_free_list_other
    (p q : access_map)
    (m m' : mem)
    (Hlt : permMapLt p (getMaxPerm m))
    (l : list (Values.block * Z * Z)) :
    permMapLt q p ->
    permMapsDisjoint p q ->
    Mem.free_list (restrPermMap Hlt) l = Some m' ->
    permMapLt q (getCurPerm m').
  Proof.
    intros Hqp Hdisj Hfree.
    pose proof (free_list_preserves_other_cur q l (restrPermMap Hlt) m') as Hpres.
    apply Hpres; auto.
    - pose proof (mem_equiv.getCur_restr _ _ Hlt) as Heq.
      rewrite /mem_equiv.access_map_equiv in Heq.
      unfold permMapLt in Hqp |- *.
      intros.
      specialize (Heq b).
      specialize (Hqp b ofs).
      by rewrite Heq.
    - unfold permMapsDisjoint in Hdisj |- *.
      intros.
      specialize (Hdisj b ofs).
      destruct Hdisj as (pu & Hdisj).
      pose proof (mem_equiv.getCur_restr _ _ Hlt) as Heq.
      rewrite /mem_equiv.access_map_equiv in Heq.
      specialize (Heq b).
      rewrite Heq.
      exists pu. done.
  Qed.

  Definition other_lt_and_disjoint (p : access_map) (σj : rmap) (m m' : mem) : Prop :=
  permMapLt (perm_of_rmap σj) (getMaxPerm m') /\
    permMapLt (perm_of_rmap σj) (getMaxPerm m) /\
    permMapsDisjoint p (perm_of_rmap σj).

  (*
    Lemma coherent_mem_step_other
    (m m' : mem) (p r r' : access_map) (σ : rmap)
    (Hp  : permMapLt p  (getMaxPerm m))
    (Hr  : permMapLt r  (getMaxPerm m))
    (Hr' : permMapLt r' (getMaxPerm m'))
    (Hsub  : permMapLt (perm_of_rmap σ) r)
    (Hsub' : permMapLt (perm_of_rmap σ) r') :
  coherent (restrPermMap Hr) σ ->
  mem_step (restrPermMap Hp) m' ->
  permMapsDisjoint p (perm_of_rmap σ) ->
  coherent (restrPermMap Hr') σ.

   *)

  Lemma coherent_mem_step_other_aux (m m' : mem) (p : access_map) (σ : rmap)
    (Hp : permMapLt p (getMaxPerm m))
    (Hσ : permMapLt (perm_of_rmap σ) (getMaxPerm m))
    (Hσ' : permMapLt (perm_of_rmap σ) (getMaxPerm m')) :
    coherent (restrPermMap Hσ) σ ->
    mem_step (restrPermMap Hp) m' ->
    permMapsDisjoint p (perm_of_rmap σ) ->
    coherent (restrPermMap Hσ') σ.
  Proof.
    intros Hchr Hstep Hother.
    remember (restrPermMap Hp) as ms eqn:Hsrc in Hstep.
    revert Hσ'.
    generalize dependent m.
    generalize dependent p.
    induction Hstep; intros; subst; last first.
    have Hcur : mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hp)) p.
    { apply mem_equiv.getCur_restr. }
    have Hmid : permMapsDisjoint (getCurPerm m'') (perm_of_rmap σ) /\
          permMapLt (perm_of_rmap σ) (getMaxPerm m'').
    { eapply (mem_step_preserve_disjoint_and_lt (restrPermMap Hp) m'' (perm_of_rmap σ)); eauto.
      - by rewrite restr_Max_eq.
      - rewrite /mem_equiv.access_map_equiv in Hcur.
        rewrite /permMapsDisjoint in Hother |- *.
        intros b ofs.
        specialize (Hcur b).
        rewrite Hcur.
        apply (Hother b ofs). }
    destruct Hmid as (Hother'' & Hσ'').
    have Hchr'' : coherent (restrPermMap Hσ'') σ.
    { eapply (IHHstep1 p Hother m0 Hp Hσ Hchr eq_refl Hσ''); eauto. }
    eapply (IHHstep2 (getCurPerm m'') Hother'' m'' (cur_lt_max m'') Hσ'' Hchr'').
    symmetry.
    apply restrPermMap_eq.
    - unfold coherent in *.
      intros.
      specialize (Hchr loc).
      split.
      + intro Hge.
        apply Hchr.
        assert (Hnxt: Mem.nextblock m' = Mem.nextblock m0).
        { apply (mem_lemmas.nextblock_freelist l (restrPermMap Hp) m'); auto. }
        rewrite restrPermMap_nextblock in Hge.
        rewrite restrPermMap_nextblock.
        by rewrite Hnxt in Hge.
      + unfold coherent_loc in *.
        split.
        * rewrite /contents_cohere /juicy_mem.contents_at /=.
          intros.
          rewrite /coherent in Hchr.
          destruct Hchr as (? & Hchr).
          rewrite /coherent_loc /contents_cohere in Hchr.
          destruct Hchr as (Hchr & ?).
          destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
          { rewrite /resource_at in H0.
            destruct (σ !! loc) eqn: E; last first.
            { rewrite E in H0. inv H0. }
            rewrite restrPermMap_nextblock in H1.
            rewrite Heq1 in H1.
            assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
            apply H1 in Hge. inv Hge.
          }
          apply Hchr in H0.
          rewrite /juicy_mem.contents_at in H0.
          apply free_list_contents in H.
          rewrite mem_contents_restrPermMap in H0.
          by rewrite H mem_contents_restrPermMap.
        * rewrite /access_cohere.
          Unshelve.
          rewrite /coherent in Hchr.
          destruct Hchr as (? & ? & ?).
          rewrite /access_cohere in H2.
          rewrite access_at_restrPermMap_Cur in H2.
          rewrite access_at_restrPermMap_Cur.
          done.
       - (* Alloc *)
         Transparent Mem.alloc.
         rewrite /Mem.alloc /= in H.
         injection H as Hxy.
         pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
         simpl in Hacc.
         assert (mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hp)) p).
         { apply mem_equiv.getCur_restr. }
         pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
         simpl in Hcnt.
         pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
         simpl in Hnxt.
         clear Hxy.
         unfold coherent in *.
         intros.
         specialize (Hchr loc).
         split.
         + intro Hge.
           apply Hchr.
           rewrite restrPermMap_nextblock in Hge.
           rewrite /coherent in Hchr.
           rewrite restrPermMap_nextblock.
           subst; lia.
         + rewrite /coherent_loc.
           split.
           ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
              intros.
              rewrite /coherent in Hchr.
              destruct Hchr as (? & Hchr).
              rewrite /coherent_loc /contents_cohere in Hchr.
              destruct Hchr as (Hchr & ?).
              destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
              { destruct (σ !! loc) eqn: E; last first.
                { rewrite /resource_at in H1.
                  rewrite E in H1. inv H1.
                }
                rewrite restrPermMap_nextblock in H2.
                rewrite Heq1 in H2.
                assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
                by apply H2 in Hge.
              }
              apply Hchr in H1.
              rewrite /juicy_mem.contents_at mem_contents_restrPermMap in H1.
              rewrite Hcnt.
              rewrite PMap.gso //.
           ** rewrite /access_cohere.
              rewrite access_at_restrPermMap_Cur.
              rewrite /coherent in Hchr.
              destruct Hchr as (? & ?).
              rewrite /coherent_loc in H2.
              destruct H2 as (? & ?).
              rewrite /access_cohere in H3.
              by rewrite access_at_restrPermMap_Cur in H3.
       - (* Mem.storebytes  *)
         pose proof H as Hst.
         pose proof H as Hst1.
         Transparent Mem.storebytes.
         rewrite /Mem.storebytes in H.
         destruct (Mem.range_perm_dec _ _ _ _ Cur Writable) as [Hf | Hf]; last first; try done.  
         injection H as Hxy.
         pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
         simpl in Hacc.
         assert (Hcur : getCurPerm m' = getCurPerm (restrPermMap Hp)).
         { rewrite /getCurPerm.
           rewrite Hacc. done. }
         assert (Hmax : getMaxPerm m' = getMaxPerm (restrPermMap Hp)).
         { by rewrite /getMaxPerm Hacc. }
         pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
         simpl in Hcnt.
         pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
         simpl in Hnxt.
         clear Hxy.
         unfold coherent in *.
         intros.
         split; auto.
         + intros. apply Hchr; auto; simpl in *; rewrite Hnxt // in H.
         + unfold Mem.range_perm, Mem.perm in Hf.
           assert (Hloc: forall loc, contents_at m' loc = contents_at (restrPermMap Hp) loc
                                     \/ can_store_at (getCurPerm (restrPermMap Hp)) loc).
           { eapply storebytes_contents_or_canstore_cur; eauto. }
           destruct (Hchr loc) as (_ & Hcoh).
           destruct (Hloc loc) as [Hmem_eq | Hwrite].
           * rewrite /contents_at in Hmem_eq.
             rewrite /coherent_loc /contents_cohere /resource_at /juicy_mem.contents_at
               in Hcoh |- *.
             split; simpl.
             intros.
             rewrite Hmem_eq mem_contents_restrPermMap.
             rewrite mem_contents_restrPermMap in Hcoh.
             apply Hcoh; auto.
             rewrite /access_cohere !access_at_restrPermMap_Cur in Hcoh |- *.
             apply Hcoh.
           * rewrite / coherent_loc in Hcoh |- *.
             rewrite /contents_cohere /access_cohere /= in Hcoh |- *.
             rewrite ! access_at_restrPermMap_Cur in Hcoh |- *.
             split; try apply Hcoh.
             intros ? Hres.
             destruct Hcoh as (Hv & _); specialize (Hv _ Hres).
             rewrite !restrPermMap_contents in Hv |- *.
             rewrite /resource_at /resR_to_resource in Hres.
             rewrite /permMapsDisjoint in Hother.
             specialize (Hother loc.1 loc.2).
             destruct (σ !! loc) eqn: E; last first.
             { rewrite E in Hres. inv Hres. } 
             rewrite E /= in Hres.
             destruct s; last first. inv Hres.
             rewrite /resource_at in Hchr.
             specialize (Hchr loc).
             destruct Hchr as (_ & _ & HpermHlt1).
             rewrite E in HpermHlt1.
             apply writable_at_perm_order_cases
               with (x := access_at (restrPermMap Hp) loc Cur) in Hwrite; auto.
             2 : { by rewrite /getCurPerm /access_at PMap.gmap. }
             rewrite /access_at in Hwrite.
             rewrite restrPermMap_Cur_eq in Hwrite.
             pose proof (access_at_restrPermMap_Cur (perm_of_rmap σ) m0 loc Hσ) as Haccess1.
             rewrite /access_cohere Haccess1 in HpermHlt1.
             assert (Hread: Mem.perm_order' ((perm_of_rmap σ) # (loc.1) loc.2) Readable).
             { rewrite mem_lemmas.po_oo.
               eapply readable_dfrac_perm_order with (Hlt:= Hσ) (rsh := rsh) ; try eauto.
               by rewrite Haccess1.
             }
             assert (Hwrite1: Mem.perm_order' (p # (loc.1) loc.2) Writable).
             { destruct Hwrite as [Hwrite | Hwrite];
                 rewrite mem_lemmas.po_oo; rewrite Hwrite;
                 [try apply perm_F_any | apply perm_refl].
             }
             assert (¬ ∃ pu : option permission,
                    perm_union ((perm_of_rmap σ) # (loc.1) loc.2) (p # (loc.1) loc.2) = Some pu).
             { apply (perm_order_clash
                        ((perm_of_rmap σ) # (loc.1) loc.2) (p # (loc.1) loc.2)); auto. }
             rewrite perm_union_comm in H.
             done.
  Qed.

Lemma permMapLt_decay_disjoint
    (pmap : access_map) (m m' : mem)
    (Hdecay : decay m m')
    (Hltp : permMapLt pmap (getMaxPerm m))
    (Hdisj : permMapsDisjoint (getCurPerm m) pmap) :
  permMapLt pmap (getMaxPerm m').
Proof.
  intros b ofs.
  destruct (mem_lemmas.valid_block_dec m b) as [Hvalid | Hinvalid].
  - destruct (Hdecay b ofs) as [_ Hold].
    specialize (Hold Hvalid).
    destruct Hold as [Hfree | Hsame].
    + (* The step freed this location. *)
      assert (Hpnone : pmap # b ofs = None).
      {
        specialize (Hdisj b ofs) as [pu Hunion].
        rewrite getCurPerm_correct in Hunion.
        unfold permission_at in Hunion.

        destruct (Hfree Cur) as [Hfree_cur _].
        rewrite Hfree_cur in Hunion.

        destruct (pmap # b ofs) as [p |] eqn:Hp;
          last reflexivity.
        destruct p; simpl in Hunion; discriminate.
      }
      rewrite Hpnone.
      apply perm_order''_None.
    + (* Maximum permission is unchanged. *)
      specialize (Hsame Max).
      specialize (Hltp b ofs).
      rewrite getMaxPerm_correct in Hltp |- *.
      unfold permission_at in Hltp |- *.
      rewrite Hsame in Hltp.
      rewrite getMaxPerm_correct. done.
  - (* σ0 has no permission on an initially invalid block. *)
    assert (Hpnone : pmap # b ofs = None).
    { eapply permMapLt_invalid_block; eauto. }
    rewrite Hpnone.
    apply perm_order''_None.
Qed.
(*
    
Lemma conc_mem_auth_lookup1 `{!conc_VSTGS OK_ty Σ} i g p m perms :
  perms !! i = Some (g, p) →
  conc_mem_auth m perms ⊢ ∃ Hp : permMapLt p (getMaxPerm m),
        thread_mem_auth g (restrPermMap Hp) ∗
          (∀ m', ⌜mem_step (restrPermMap Hp) m' /\ sc_others_lt_and_disjoint perms i m m'⌝ ∧
             thread_mem_auth g m' -∗
        conc_mem_auth m' (<[i:=(g, getCurPerm m')]>perms)).
Proof.
  rewrite /conc_mem_auth; intros.
  iIntros "(% & H)".
  iDestruct (big_sepM2_delete_l _ _ _ i (g, p) with "H") as "H"; auto.
  iDestruct "H" as (?) "(% & (% & H) & Hbig)".
  destruct H1 as (Hlt & H2). 
  rename x2 into σ.
  iExists Hlt. iFrame.
  iSplit.
  iPureIntro.
  { split; auto. }
  iIntros (m') "(%HSc & H)".
  destruct HSc as (HSc & (sc_others_still_lt & sc_others_still_lt1 & sc_perm_disjoint)).
  rewrite /thread_mem_auth /mem_auth.
  remember (restrPermMap Hlt).
  clear H2.
  iStopProof.
  generalize dependent m; generalize dependent p; generalize dependent perms.
  induction HSc; intros; subst; iIntros "(Hbig & H)".
  4 : {
    assert (Hcur: mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hlt)) p).
    { apply mem_equiv.getCur_restr. }
    assert (Hdisj: ∀ (j : nat) (g : gname) (a : access_map),
               j <> i → perms !! j = Some (g, a) -> permMapsDisjoint (getCurPerm m'') a /\
                 permMapLt a (getMaxPerm m'')).
    {
      intros.
      eapply (mem_step_preserve_disjoint_and_lt (restrPermMap Hlt) m'' a); eauto.
      rewrite restr_Max_eq.
      eapply (sc_others_still_lt2 j g0 a); auto.
      rewrite /mem_equiv.access_map_equiv in Hcur.
      rewrite /permMapsDisjoint.
      intros.
      specialize (Hcur b).
      rewrite Hcur.
      rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
      specialize ((sc_perm_disjoint0 j) H1).
      by rewrite H H2 /= /permMapsDisjoint in sc_perm_disjoint0.
    }
    iDestruct (IHHSc2 (<[i:=(g, getCurPerm m'')]>perms) with "[-]") as (?) "Hbig".
    - intros ????; rewrite lookup_insert_ne //; by apply sc_others_still_lt.
    - intros.
      rewrite /permMapsDisjoint_at.
      rewrite lookup_insert.
      rewrite lookup_insert_ne //.
      destruct (perms !! j) eqn: E; last first; try done.
      destruct p0.
      eapply Hdisj; eauto.
    - apply lookup_insert.
    - symmetry; apply restrPermMap_eq.
    - intros.
      rewrite lookup_insert_ne // in H2.
      eapply Hdisj; eauto.
    - rewrite delete_insert_delete; iFrame.
      iApply (big_sepM2_mono with "Hbig"); intros.
      destruct y1.
      do 2 f_equiv.
      rewrite /impl /coherent.
      intros (Hlt1 & ?).
      apply lookup_delete_Some in H1, H2.
      destruct H1 as (Hneq & Hperm).
      destruct H2 as (_ & Hσ).
      assert (Hc: permMapsDisjoint (getCurPerm m'') a /\ permMapLt a (getMaxPerm m'')).
      { eapply Hdisj; eauto. }
      destruct Hc as (Hp & Hlta).
      exists Hlta.
      intros.
      split.
      + intros.
        apply H3.
        apply semantics_lemmas.mem_step_nextblock' in HSc1.
        rewrite restrPermMap_nextblock in H1.
        rewrite restrPermMap_nextblock in HSc1.
        rewrite restrPermMap_nextblock. lia.
      + rewrite /coherent_loc /contents_cohere.
        rewrite / coherent_loc in H3 |- *.
        rewrite /contents_cohere /access_cohere /= in H3 |- *.
        rewrite ! access_at_restrPermMap_Cur in H3 |- *.
        split; last first.
        * specialize (H3 loc).
          destruct H3 as (_ & _ & Hperm_order).
          by rewrite access_at_restrPermMap_Cur in Hperm_order.
        * rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
          intros.
          pose proof H1 as Hy.
          rewrite /resource_at /resR_to_resource /= in H1.
          rewrite /coherent_loc /contents_cohere in H3.
          pose proof H3 as Hx.
          rewrite /shared.val_of /resource_at in H3.
          specialize (Hx loc).
          destruct Hx as (Hx & Hx1).
          apply Hx1 in Hy.
          destruct (y2 !! loc) eqn: E; last first.
          { rewrite /resource_at in H1.
            rewrite E in H1; inv H1.
          }
          rewrite E /= in H1.
          destruct s; last first. inv H1.
          specialize (H3 loc).
          destruct H3 as (_ & _ & HpermHlt1).
          rewrite E in HpermHlt1.
          pose proof (access_at_restrPermMap_Cur a m0 loc Hlt1) as Haccess1.
          rewrite Haccess1 in HpermHlt1.
          assert (Hread: Mem.perm_order' (a # (loc.1) loc.2) Readable).
          { rewrite mem_lemmas.po_oo.
            eapply readable_dfrac_perm_order with (Hlt:= Hlt1) (rsh := rsh); try eauto.
            rewrite Haccess1; auto.
          }
          have Hvb : Mem.valid_block (restrPermMap Hlt) loc.1.
          { unfold Mem.valid_block.
            rewrite restrPermMap_nextblock /Plt.
            destruct (Pos.lt_total loc.1 (Mem.nextblock m0)) as [Hl | [Heq | Hl]]; auto; exfalso.
            - rewrite Heq in Hx.
              assert ((Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
              by apply Hx in H2.
            - have Hge : (loc.1 >= Mem.nextblock m0)%positive.
              { assert ((Mem.nextblock m0 ≤ loc.1)%positive)
                  by apply (Pos.lt_le_incl _ _ Hl); lia.
              }
              by apply Hx in Hge.
          }
          assert (¬ Mem.perm (restrPermMap Hlt) loc.1 loc.2 Cur Writable).
          { rewrite /Mem.perm.
            intros Hcontra.
            rewrite restrPermMap_Cur_eq in Hcontra.
            assert (permMapsDisjoint p a).
            { rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
              have Hki : k <> i := fun Hki_eq => Hneq (eq_sym Hki_eq).
              specialize ((sc_perm_disjoint0 k) Hki).
              by rewrite H Hperm in sc_perm_disjoint0.
            }
            rewrite /permMapsDisjoint in H2.
            assert (¬ ∃ pu : option permission,
                        perm_union (a # (loc.1) loc.2) (p # (loc.1) loc.2) = Some pu).
            { apply (perm_order_clash (a # (loc.1) loc.2) (p # (loc.1) loc.2) Hread Hcontra). }
            specialize (H2 (loc.1) (loc.2)).
            by rewrite perm_union_comm in H2. 
          }
          assert (ZMap.get loc.2 (Mem.mem_contents (restrPermMap Hlt)) # (loc.1) =
                     ZMap.get loc.2 (Mem.mem_contents m'') # (loc.1)).
          { by apply (semantics_lemmas.mem_step_obeys_cur_write
                     (restrPermMap Hlt) (loc.1) (loc.2) m'' Hvb H2).
          }
          rewrite /juicy_mem.contents_at mem_contents_restrPermMap in Hy.
          rewrite mem_contents_restrPermMap in H3.
          by rewrite Hy in H3.
     - rewrite insert_insert; iFrame.
  }
  - pose proof H as Hst.
    pose proof H as Hst1.
    Transparent Mem.storebytes.
    rewrite /Mem.storebytes in H.
    destruct (Mem.range_perm_dec _ _ _ _ Cur Writable) as [Hf | Hf]; last first; try done.  
    injection H as Hxy.
    pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
    simpl in Hacc.
    assert (Hcur : getCurPerm m' = getCurPerm (restrPermMap Hlt)).
    { rewrite /getCurPerm.
      rewrite Hacc. done. }
    assert (Hmax : getMaxPerm m' = getMaxPerm (restrPermMap Hlt)).
    { by rewrite /getMaxPerm Hacc. }
    pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
    simpl in Hcnt.
    pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
    simpl in Hnxt.
    clear Hxy.
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    2 : { rewrite lookup_insert //=. }
    iDestruct "H" as (σ') "(% & H)".
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    iExists (<[i := σ']>σs).
    iExists σ'.
    iSplit; first rewrite lookup_insert //.
    iSplitR "Hbig".
    iFrame. iPureIntro.
    split; auto.
    exists (cur_lt_max _); rewrite restrPermMap_eq //.
    rewrite ! delete_insert_delete.
    iApply (big_sepM2_mono with "Hbig"); intros.
    destruct y1.
    do 2 f_equiv.
    rewrite /impl /coherent.
    intros (Hlt1 & ?).
    apply lookup_delete_Some in H2, H3.
    destruct H2.
    destruct H3.
    unshelve eexists.
    {
      have Hperms_k : perms !! k = Some (g0, a) by done.
      eapply (sc_others_still_lt _ _ a); eauto.
    }
    simpl; split; auto.
    * intros; apply H4; auto; simpl in *. rewrite Hnxt // in H7.
    * unfold Mem.range_perm, Mem.perm in Hf.
      assert (Hloc: forall loc, contents_at m' loc = contents_at (restrPermMap Hlt) loc
                           \/ can_store_at (getCurPerm (restrPermMap Hlt)) loc).
      { eapply storebytes_contents_or_canstore_cur; eauto. }
      destruct (H4 loc) as (_ & Hcoh).
      destruct (Hloc loc) as [Hmem_eq | Hwrite].
      + rewrite /contents_at in Hmem_eq.
        rewrite /coherent_loc /contents_cohere /resource_at /juicy_mem.contents_at in Hcoh |- *.
        split; simpl.
        intros.
        rewrite Hmem_eq mem_contents_restrPermMap.
        rewrite mem_contents_restrPermMap in Hcoh.
        apply Hcoh; auto.
        rewrite /access_cohere !access_at_restrPermMap_Cur in Hcoh |- *.
        apply Hcoh.
      + rewrite / coherent_loc in Hcoh |- *.
        rewrite /contents_cohere /access_cohere /= in Hcoh |- *.
        rewrite ! access_at_restrPermMap_Cur in Hcoh |- *.
        split; try apply Hcoh.
        intros ? Hres.
        destruct Hcoh as (Hv & _); specialize (Hv _ Hres).
        rewrite !restrPermMap_contents in Hv |- *.
        rewrite /resource_at /resR_to_resource in Hres.
        rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
        specialize (sc_perm_disjoint0 k).
        rename H2 into Hneq.
        rename H5 into Hperm.
        rewrite Hperm in sc_perm_disjoint0.
        specialize (sc_perm_disjoint0 (not_eq_sym Hneq)).
        rewrite /permMapsDisjoint /= in sc_perm_disjoint0.
        destruct (y2 !! loc) eqn: E; last first.
        { rewrite E in Hres. inv Hres. } 
        rewrite E /= in Hres.
        destruct s; last first. inv Hres.
        rewrite /resource_at in H4.
        specialize (H4 loc).
        destruct H4 as (_ & _ & HpermHlt1).
        rewrite E in HpermHlt1.
        apply writable_at_perm_order_cases
          with (x := access_at (restrPermMap Hlt) loc Cur) in Hwrite; auto.
        2 : { by rewrite /getCurPerm /access_at PMap.gmap. }
        rewrite /access_at in Hwrite.
        rewrite restrPermMap_Cur_eq in Hwrite.        
        pose proof (access_at_restrPermMap_Cur a m0 loc Hlt1) as Haccess1.
        rewrite /access_cohere Haccess1 in HpermHlt1.
        assert (Hread: Mem.perm_order' (a # (loc.1) loc.2) Readable).
        { rewrite mem_lemmas.po_oo.
          eapply readable_dfrac_perm_order with (Hlt:= Hlt1) (rsh := rsh) ; try eauto.
          by rewrite Haccess1.
        }
        assert (Hwrite1: Mem.perm_order' (p # (loc.1) loc.2) Writable).
        { destruct Hwrite as [Hwrite | Hwrite];
            rewrite mem_lemmas.po_oo; rewrite Hwrite;
            [try apply perm_F_any | apply perm_refl].
        }
        assert (¬ ∃ pu : option permission,
                    perm_union (a # (loc.1) loc.2) (p # (loc.1) loc.2) = Some pu).
        { apply (perm_order_clash (a # (loc.1) loc.2) (p # (loc.1) loc.2)); done. }
        rewrite H1 in sc_perm_disjoint0.
        specialize (sc_perm_disjoint0 loc.1 loc.2).
        simpl in sc_perm_disjoint0.
        by rewrite perm_union_comm in H2.
  - Transparent Mem.alloc.
    rewrite /Mem.alloc /= in H.
    injection H as Hxy.
    pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
    simpl in Hacc.
    assert (mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hlt)) p).
    { apply mem_equiv.getCur_restr. }
    pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
    simpl in Hcnt.
    pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
    simpl in Hnxt.
    clear Hxy.
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    2 : { rewrite lookup_insert //=. }
    iDestruct "H" as (σ') "(% & H)".
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    iExists (<[i := σ']>σs).
    iExists σ'.
    iSplit; first rewrite lookup_insert //.
    iSplitR "Hbig".
    iFrame. iPureIntro.
    split; auto.
    exists (cur_lt_max _); rewrite restrPermMap_eq //.
    rewrite ! delete_insert_delete.
    iApply (big_sepM2_mono with "Hbig"); intros.
    apply lookup_delete_Some in H5.
    destruct y1.
    iIntros "(%Hlt1 & H1)".
    iFrame "H1".
    iPureIntro.
    split; auto.
    destruct Hlt1 as (Hlt1 & Hchr).
    destruct H5 as [Hik Hσk].
    have Hperms_k : perms !! k = Some (g0, a).
    { rewrite lookup_delete_ne in H4; auto. }
    assert (Hlt': permMapLt a (getMaxPerm m')).
    { eapply sc_others_still_lt; eauto. }
    exists Hlt'.
    split.
    * intro Hge.
      rewrite restrPermMap_nextblock /= in Hge.
      rewrite /coherent in Hchr.
      apply Hchr.
      rewrite restrPermMap_nextblock. lia.
    * rewrite /coherent_loc.
      split.
      ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
         intros.
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & Hchr).
         rewrite /coherent_loc /contents_cohere in Hchr.
         destruct Hchr as (Hchr & ?).
         destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
         { rewrite /resource_at in H4.
           destruct (y2 !! loc) eqn: E; last first.
           { rewrite /resource_at in H5.
             rewrite E in H5. inv H5.
           }
           rewrite restrPermMap_nextblock in H6.
           rewrite Heq1 in H6.
           assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
           by apply H6 in Hge.
         }
         apply Hchr in H5.
         rewrite /juicy_mem.contents_at mem_contents_restrPermMap in H5.
         rewrite Hcnt.
         rewrite PMap.gso //.
      ** rewrite /access_cohere.
         rewrite access_at_restrPermMap_Cur.
         Unshelve.
         2 : { apply cur_lt_max. }
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & ?).
         rewrite /coherent_loc in H6.
         destruct H6 as (? & ?).
         rewrite /access_cohere in H7.
         by rewrite access_at_restrPermMap_Cur in H7.
  - setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    iDestruct "H" as (σ') "(% & H)".
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    2 : { rewrite lookup_insert; auto. }
    iExists (<[i := σ']>σs).
    iExists σ'.
    iSplit; first rewrite lookup_insert //.
    iSplitR "Hbig".
    iFrame. iPureIntro.
    split; auto.
    exists (cur_lt_max _); rewrite restrPermMap_eq //.
    rewrite ! delete_insert_delete.
    iApply (big_sepM2_mono with "Hbig"); intros.
    apply lookup_delete_Some in H4.
    destruct y1.
    iIntros "(%Hlt1 & H1)".
    iFrame "H1".
    iPureIntro.
    split; auto.
    destruct Hlt1 as (Hlt1 & Hchr).
    destruct H4 as [Hik Hσk].
    have Hperms_k : perms !! k = Some (g0, a).
    { rewrite lookup_delete_ne in H3; auto. }
    assert (Hlt': permMapLt a (getMaxPerm m')).
    { eapply sc_others_still_lt; eauto. }
    exists Hlt'.
    split.
    * intro Hge.
      rewrite restrPermMap_nextblock /= in Hge.
      rewrite /coherent restrPermMap_nextblock in Hchr.
      apply Hchr.
      apply nextblock_free_list in H.
      rewrite restrPermMap_nextblock in H.
      by rewrite H in Hge.
    * rewrite /coherent_loc.
      split.
      ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
         intros.
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & Hchr).
         rewrite /coherent_loc /contents_cohere in Hchr.
         destruct Hchr as (Hchr & ?).
         destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
         { rewrite /resource_at in H4.
           destruct (y2 !! loc) eqn: E; last first.
           { rewrite E in H4. inv H4. }
           rewrite restrPermMap_nextblock in H5.
           rewrite Heq1 in H5.
           assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
           by apply H5 in Hge.
         }
         apply Hchr in H4.
         rewrite /juicy_mem.contents_at mem_contents_restrPermMap in H4.
         apply free_list_contents in H.
         rewrite H.
         by rewrite mem_contents_restrPermMap.
      ** rewrite /access_cohere.
         rewrite access_at_restrPermMap_Cur.
         Unshelve.
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & ?).
         rewrite /coherent_loc in H5.
         destruct H5 as (? & ?).
         rewrite /access_cohere in H6.
         by rewrite access_at_restrPermMap_Cur in H6.
Qed.

Lemma conc_state_interp_lookup `{!conc_VSTGS OK_ty Σ} i g p m perms z :
  perms !! i = Some (g, p) →
  conc_state_interp m perms z ⊢ (∃ Hp : permMapLt p (getMaxPerm m),
        thread_state_interp g (restrPermMap Hp) z) ∗
    (∀ m', ⌜OpSC i m m' p perms⌝ ∧ thread_state_interp g m' z -∗
           conc_state_interp m' (<[i:=(g, getCurPerm m')]>perms) z).
Proof.
  iIntros (?) "(H & $)".
  iDestruct (conc_mem_auth_lookup with "[$H]") as "H"; eauto.
  iDestruct "H" as "($ & H)".
  iIntros (?) "(% & (? & $))".
  iApply "H". iSplit; done.
Qed.

Lemma conc_state_interp_lookup1 `{!conc_VSTGS OK_ty Σ} i g p m perms z :
  perms !! i = Some (g, p) →
  conc_state_interp m perms z ⊢ ∃ Hp : permMapLt p (getMaxPerm m),
        thread_state_interp g (restrPermMap Hp) z ∗
    (∀ m', ⌜mem_step (restrPermMap Hp) m' /\ sc_others_lt_and_disjoint perms i m m'⌝ ∧
             thread_state_interp g m' z -∗
        conc_state_interp m' (<[i:=(g, getCurPerm m')]>perms) z).
Proof.
  iIntros (?) "(H & $)".
  iDestruct (conc_mem_auth_lookup1 with "[$H]") as (?) "($ & H)"; eauto.
  iIntros (?) "(% & (? & $))".
  iApply "H". iSplit; done.
Qed.

(* Definition lock_state `{!conc_heapGS Σ} `{lockGS Σ} γ m ls := lock_state(heapGS0 := HeapGS _ _ (thread_gen_heapGS γ) _) m ls. *)
Definition lock_state `{!conc_VSTGS Σ} (m : mem) (lG : AMap.t (option lock_info)) :=
  ∃ lcs : gmap address ((option access_map * gname * resource_map.rmapUR _ _ _) * mpred),
  ⌜forall l p, (exists g σ R, lcs !! l = Some ((p,g,σ), R)) <-> (exists ps, AMap.find l lG = Some ps /\ p = option_map snd ps)⌝ ∧
  own(inG0 := lockGS_inG) lockGS_gname (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) (invariant_unfold <$> snd <$> lcs)) ∗
  ([∗ map] l ↦ '((p,g,σ),R)∈lcs,
     resource_map.resource_map_auth(H1 := gen_heapGpreS_heap(gen_heapGpreS := conc_gen_heap_inG)) g 1 σ ∗
     <affine> ⌜match p with
     | Some p => exists Hp : permMapLt p (getMaxPerm m), coherent (restrPermMap Hp) σ /\
        Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs (Ptrofs.one) /\ (▷R) σ
     | None => σ = ε /\ Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs (Ptrofs.zero)
     end⌝).

Lemma locks_init `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} m :
  ⊢ |==> ∃ γ, ∀ (_ : conc_heapGS Σ) γh, let lG := LockGS Σ _ γ in lock_state γh m ∅.
Proof.
  unfold lock_state, semax_conc_pred.lock_state.
  iMod (own_alloc(i := inG0)) as (γ) "H".
  { apply gmap_view.gmap_view_auth_valid. }
  iModIntro; iExists γ; iIntros.
  iExists ∅; iSplit => //=.
  rewrite fmap_empty.
  iSplitL => //.
Qed.  

Lemma init_conc_VST: forall Z `{!VSTGpreS Z Σ} `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} m (z : Z),
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ HH : conc_gen_heapGS Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS Z Σ, ∃ HL : lockGS Σ, ∃ γ0 γl γm,
    let H : conc_VSTGS Z Σ := ConcVSTGS _ _ (ConcHeapGS _ _ _ _) _ _ in
    (thread_state_interp γ0 Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z) ∗
    ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta(gen_heapGpreS := conc_gen_heap_inG)) (@conc_gen_meta_name _ HH) 1 ∅ ∗
    lock_state γl m ∅ ∗ thread_mem_auth γl Mem.empty ∗
    ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta(gen_heapGpreS := conc_gen_heap_inG)) γm 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (ext_alloc z) as (?) "(? & ?)".
  iMod gen_heap_init_names_empty as (γl ?) "(? & ?)".
  iMod (locks_init) as (?) "HL".
  iIntros "!>" (?).
  iExists (ConcGenHeapGS _ _ γm), (FunspecG _ _ γf), _, _, γh, γl, γm0.
  iFrame.
  pose proof (empty_coherent Mem.empty); repeat iSplit => //.
Qed.
(* end concurrency setup *)
*)

Ltac absurd_ext_link_naming :=
  exfalso;
  match goal with
  | H : Some (_ _, _) = _ |- _ =>
    rewrite <- ?H in *
  end;
  unfold funsig2signature in *;
  match goal with
  | H : Some (?ext_link ?a, ?b) <> Some (?ext_link ?a, ?b') |- _ =>
    simpl in H; [contradiction || congruence]
  | H : Some (?ext_link ?a, ?c) = Some (?ext_link ?b, ?d) |- _ =>
    simpl in H;
    match goal with
    | ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2 |- _ =>
      assert (a = b) by (apply ext_link_inj; congruence); congruence
    end
  end.

Ltac funspec_destruct s :=
  simpl (Jext_spec_pre); simpl (Jext_spec_type); simpl (Jext_spec_post);
  unfold funspec2pre, funspec2post;
  let Heq_name := fresh "Heq_name" in
  destruct (oi_eq_dec (Some (_ s, _)) (ef_id_sig _ (EF_external _ _)))
    as [Heq_name | Heq_name]; try absurd_ext_link_naming.

(*+ Final instantiation *)

Record CSL_proof := {
  CSL_Σ : gFunctors;
  CSL_prog : Clight.program;
  CSL_CS: compspecs;
  CSL_V : varspecs;
  CSL_G : @funspecs CSL_Σ;
  CSL_ext_link : string -> ident;
  CSL_ext_link_inj : forall s1 s2, CSL_ext_link s1 = CSL_ext_link s2 -> s1 = s2;
  CSL_all_safe : forall (HH : VSTGS unit CSL_Σ) (HL : lockGS CSL_Σ), @semax_prog _ _ HH (concurrent_ext_spec CSL_CS CSL_ext_link)
    CSL_CS CSL_prog tt CSL_V CSL_G;
  CSL_init_mem_not_none : Genv.init_mem CSL_prog <> None; }.

(*
Definition Clight_init_state (prog:Ctypes.program function) main_symb f_main init_mem :=
  State Clight_safety.main_handler
        (Scall None (Etempvar BinNums.xH (type_of_fundef f_main))
               (List.map (fun x : AST.ident * Ctypes.type => Etempvar (fst x) (snd x))
                         (Clight_new.params_of_types (BinNums.xO BinNums.xH)
                                                     (Clight_new.params_of_fundef f_main))))
        (Kseq (Sloop Sskip Sskip) Kstop) empty_env
        (temp_bindings BinNums.xH (cons main_symb nil)) init_mem.
*)

Section Safety.
  Variable CPROOF: CSL_proof.
  Definition Σ := CPROOF.(CSL_Σ).
  Definition CS :=   CPROOF.(CSL_CS).
  Definition V :=   CPROOF.(CSL_V).
  Definition G :=   CPROOF.(CSL_G).
  Definition ext_link :=   CPROOF.(CSL_ext_link).
  Definition ext_link_inj :=   CPROOF.(CSL_ext_link_inj).
  Definition prog :=   CPROOF.(CSL_prog).
  Definition all_safe :=   CPROOF.(CSL_all_safe).
  Definition init_mem_not_none :=   CPROOF.(CSL_init_mem_not_none).
  Definition ge := Clight.globalenv CPROOF.(CSL_prog).

  Definition init_mem : {m : mem | Genv.init_mem (CSL_prog CPROOF) = Some m}.
  Proof.
    pose proof init_mem_not_none.
    destruct (Genv.init_mem (CSL_prog CPROOF)); last done; eauto.
  Defined.

(*   Local Instance CEspec (HH : heapGS Σ) (HE : externalGS unit Σ) (HL : lockGS Σ) : OracleKind :=
    Concurrent_Espec unit CS ext_link. *)

  Lemma CEspec_cases : forall `{!VSTGS unit Σ, lockGS Σ} e
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) e),
    e = LOCK \/ e = UNLOCK \/ e = MKLOCK \/ e = FREE_LOCK \/ e = CREATE.
  Proof.
    intros.
    simpl in x.
    repeat (if_tac in x; [destruct e; try done; inversion H0 as [H1];
                          apply ext_link_inj in H1 as <-; auto | clear H0]); last done.
  Qed.

  (* funspecs_destruct isn't working well, so prove a spec lemma for each function *)
  Ltac next_spec := subst; let Hspecs := fresh "Hspecs" in match goal with |-context[add_funspecs_rec _ _ _ ?l] =>
    destruct l eqn: Hspecs; first done;
    injection Hspecs; clear Hspecs; intros Hspecs <-; simpl;
    unfold funspec2pre, funspec2post, ef_id_sig; simpl; if_tac end.

  (*
  Ltac solve_spec x := intros; revert x;
    unfold ext_spec_post, concurrent_ext_spec;
    pose proof ext_link_inj as Hinj; fold ext_link in Hinj;
    repeat (next_spec; first absurd_ext_link_naming); next_spec; last done;
    intros; split; [|intros (? & Heq & ?)]; eauto;
    inversion Heq as [Heq0 Heq']; apply inj_pair2 in Heq'; subst; auto. *)

  Ltac solve_spec x :=
    intros;
    revert x;
    unfold ext_spec_post, concurrent_ext_spec;
    pose proof ext_link_inj as Hinj;
    fold ext_link in Hinj;
    repeat (next_spec; first absurd_ext_link_naming);
    next_spec; last done;
    let y := fresh "x" in
    intros y;
    iSplit;
    [ iIntros "H";
      iExists y;
      iSplit;
      [ iPureIntro; apply JMeq.JMeq_refl
      | iExact "H" ]
    | iIntros "H";
      iDestruct "H" as (x'') "[%Heq H]";
      let Heq0 := fresh "Heq0" in
      let Heq' := fresh "Heq'" in
      inversion Heq as [Heq0 Heq'];
      apply inj_pair2 in Heq';
      subst;
      iExact "H" ].

  (* Definition TT_ty (Σ : gFunctors) (A : TypeTree) : Type :=
    oFunctor_car
      (dependent_type_functor_rec A)
      (Ofe (iProp Σ) ouPred_ofe_mixin)
      (Ofe (iPropI Σ) (bi_ofe_mixin (iPropI Σ))). *)

(*  Lemma CEspec_acquire_pre : forall `{Hconc : conc_VSTGS unit Σ} `{Hlock : lockGS Σ} (g : gname),
    let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
     forall (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK) args,
        (Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge)
           (sig_args (ef_sig LOCK)) args) ⊣⊢
     match acquire_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ (funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args) end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_acquire_post : forall `{Hconc : conc_VSTGS unit Σ, Hlock : lockGS Σ} g,
      let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
      forall x args,
      Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args ⊣⊢
        match acquire_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  (*
  
  Search (conc_VSTGS _ _ -> VSTGS _ _).

  Lemma CEspec_acquire_pre : forall `{!conc_VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args ⊣⊢
    match acquire_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.
  
  Lemma CEspec_acquire_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
      Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args ⊣⊢
        match acquire_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_release_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
      Jext_spec_pre (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args ⊣⊢
      match release_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_release_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) args ⊣⊢
      match release_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_makelock_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
      Jext_spec_pre (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args ⊣⊢
        match makelock_spec CS with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_makelock_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) args ⊣⊢
      match makelock_spec CS with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_freelock_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_pre (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args ⊣⊢
      match freelock_spec CS with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_freelock_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) args ⊣⊢
      match freelock_spec CS with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_spawn_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_pre (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args ⊣⊢
      match spawn_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_spawn_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_res (ef_sig CREATE)) args ⊣⊢
      match spawn_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig CREATE)) args end.
  Proof.
    solve_spec x.
  Qed.
*)
*)

  (* Program Definition spr (HH : VSTGS unit Σ) (HL : lockGS Σ) :=
    semax_prog_rule (concurrent_ext_spec CS ext_link) V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros; iIntros (??); done. Qed. *)

  Program Definition spr
    (HH : VSTGS unit Σ)
    (HL : lockGS Σ) :=
    semax_prog_rule_with_rmap
      (concurrent_ext_spec CS ext_link)
      V G prog
      (proj1_sig init_mem) 0 tt
      _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros; iIntros (??); done. Qed.
 

  Instance Sem : Semantics :=
    ClightSemanticsForMachines.ClightSem (Clight.globalenv CPROOF.(CSL_prog)).


  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Existing Instance HybridMachineSig.HybridCoarseMachine.scheduler.

  (* If there are enough of these conditions, re-split out into semax_invariant. *)
  Definition dtp := t(ThreadPool := @OrdinalPool.OrdinalThreadPool dryResources Sem).

(*  (* We want to enforce additional coherence properties between the rmap and the memory, accounting
     for the effects of locks (and other things?). *)
  Definition lock_coherent_loc m loc (r : dfrac * option resource) : Prop :=
    match r.2 with
    | Some (LK _ _ b) => Mem.load Mptr m loc.1 loc.2 = Some (Vptrofs (if b then Ptrofs.zero else Ptrofs.one))
    | _ => True
    end.

  Definition lock_coherent m σ := forall loc, lock_coherent_loc m loc (σ @ loc).

  Definition mem_auth' `{!heapGS Σ} m := ∃ σ, ⌜coherent m σ ∧ lock_coherent m σ⌝ ∧ resource_map.resource_map_auth(H0 := gen_heapGpreS_heap(gen_heapGpreS := gen_heap_inG)) (gen_heap_name _) 1 σ.
  Definition state_interp' {Z} `{!heapGS Σ} `{!externalGS Z Σ} m z := mem_auth' m ∗ ext_auth z.*)

  (* Each thread needs to be safe given only its fragment (access_map) of the shared memory. We use
     the current max permissions as an upper bound on the max permissions of the state_interp. *)

  Section conc_heap.

  Context `{HH: !VSTGS unit Σ} `{!lockGS Σ}.

  Definition frag_mem_auth q (m : mem) (σ : rmap) : iProp Σ :=
    ⌜coherent m σ⌝ ∧ resource_map.resource_map_auth
                       (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
                       (gen_heap_name heapGS_gen_heapGS) q σ.

  (*
  Definition frag_mem_auth q m : iProp Σ :=
    ∃ σ : rmap,
      ⌜coherent m σ⌝ ∧
        resource_map.resource_map_auth
          (H1 := gen_heapGpreS_heap
                   (gen_heapGpreS := gen_heap_inG))
          (gen_heap_name heapGS_gen_heapGS)
          q σ. *)
  
  Definition frag_state_interp q (m : mem) (σ : rmap) z : iProp Σ :=
    frag_mem_auth q m σ ∗ ext_auth z.

 (*
  Definition frag_state_interp q m z := frag_mem_auth q m ∗ ext_auth z. *)
  
  Lemma locks_init `{InGlock : !inG Σ (gmap_view.gmap_viewR address (later (iPropO Σ)))} (m : mem) :
    ⊢ |==> ∃ HL : lockGS Σ, ∀ heapGS0 : heapGS Σ,
        @lock_state Σ heapGS0 HL m (∅ : gset address).
  Proof.
    iMod (own_alloc
            (A := gmap_view.gmap_viewR address (laterO (iPropO Σ)))
            (gmap_view.gmap_view_auth
               (dfrac.DfracOwn 1)
               (∅ : gmap address (laterO (iPropO Σ)))))
      as (γ) "Hauth".
    { apply gmap_view.gmap_view_auth_valid. }
    iModIntro.
    iExists (LockGS Σ InGlock γ).
    iIntros (heapGS0).
    unfold lock_state, semax_conc_pred.lock_state.
    iExists (∅ : gmap address mpred).
    rewrite fmap_empty.
    rewrite big_sepM_empty.
    simpl.
    iFrame "Hauth".
    iPureIntro.
    split; auto.
    unfold lock_addresses_disjoint.
    intros.
    set_solver.
  Qed.

  Definition gen_heap_meta_auth
    (HG : gen_heapGS share address resource Σ) : iProp Σ :=
    @ghost_map.ghost_map_auth
      Σ address gname _ _
      (@gen_heapGpreS_meta share address resource Σ _ _ _
         (@gen_heap_inG share address resource Σ _ _ _ HG))
      (@gen_meta_name share address resource Σ _ _ _ HG)
      1 (∅ : gmap address gname).

  Lemma init_conc_VST_frag : forall Z `{VSTGpreS0 : !VSTGpreS Z Σ} (z : Z),
      ⊢ |==> ∀ Hinv : invGS_gen HasNoLc Σ,
        ∃ (HG : gen_heapGS share address resource Σ) (FS : funspecGS Σ)
          (ES : externalGS Z Σ) (HL : lockGS Σ),
          @state_interp Σ Z HG ES Mem.empty z ∗
            @funspec_auth Σ FS (∅ : gmap address funspecO') ∗
            @has_ext Z Σ ES z ∗
            @lock_state Σ
            ({| heapGS_invGS := Hinv;
               heapGS_gen_heapGS := HG;
               heapGS_funspecGS := FS |} : heapGS Σ) HL Mem.empty (∅ : gset address) ∗
            gen_heap_meta_auth HG.
  Proof.
    intros; iIntros.
    iMod gen_heap_init_names_empty as (γh γmeta) "(Hheap & Hmeta)".
    iMod (own_alloc (A := gmap_view.gmap_viewR address (@funspecO' Σ))
            (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) ∅)) as (γf) "Hfunspec".
    { apply gmap_view.gmap_view_auth_valid. }
    iMod (ext_alloc z) as (ES) "(Hextauth & Hhasext)".
    iMod (locks_init Mem.empty) as (HL) "Hlocks".
    iModIntro.
    iIntros (Hinv).
    pose (HG :=
            {| gen_heap_inG := VSTGpreS_heap;
              gen_heap_name := γh;
              gen_meta_name := γmeta |}).
    pose (FS := FunspecG _ _ γf).
    pose (HGS :=
            ({| heapGS_invGS := Hinv;
               heapGS_gen_heapGS := HG;
               heapGS_funspecGS := FS |} : heapGS Σ)).
    iSpecialize ("Hlocks" $! HGS).
    iExists HG, FS, ES, HL.
    unfold gen_heap_meta_auth; simpl.
    iFrame.
    pose proof (empty_coherent Mem.empty).
    repeat iSplit => //.
  Qed.

  
  Lemma frag_mem_auth_corestep_other (q : Qp) (m m' : mem) (p : access_map) (σ : rmap)
    (Hp : permMapLt p (getMaxPerm m)) (Hσ : permMapLt (perm_of_rmap σ) (getMaxPerm m))
    (Hσ' : permMapLt (perm_of_rmap σ) (getMaxPerm m')):
    mem_step (restrPermMap Hp) m' -> permMapsDisjoint p (perm_of_rmap σ) ->
    frag_mem_auth q (restrPermMap Hσ) σ -∗ frag_mem_auth q (restrPermMap Hσ') σ.
  Proof.
    intros Hstep Hdisj.
    rewrite /frag_mem_auth.
    iIntros "(%Hcoh & Hfrag)".
    iFrame.
    iPureIntro.
    split; auto.
    eapply coherent_mem_step_other_aux; eauto. 
  Qed.

  (*
    Lemma frag_mem_auth_corestep_other
    (q : Qp) (m m' : mem)
    (p r r' : access_map) (σ : rmap)
    (Hp  : permMapLt p  (getMaxPerm m))
    (Hr  : permMapLt r  (getMaxPerm m))
    (Hr' : permMapLt r' (getMaxPerm m'))
    (Hsub  : permMapLt (perm_of_rmap σ) r)
    (Hsub' : permMapLt (perm_of_rmap σ) r') :
  mem_step (restrPermMap Hp) m' ->
  permMapsDisjoint p (perm_of_rmap σ) ->
  frag_mem_auth q (restrPermMap Hr) σ -∗
  frag_mem_auth q (restrPermMap Hr') σ.

   *)

  Lemma coherent_perm_of_rmap m σ :
    coherent m σ -> permMapLt (perm_of_rmap σ) (getCurPerm m).
  Proof.
    intros Hcoh b ofs.
    specialize (Hcoh (b, ofs)).
    rewrite /coherent_loc /access_cohere in Hcoh.
    destruct Hcoh as (_ & _ & ?).
    rewrite perm_of_rmap_lookup.
    rewrite /access_at /= in H.
    rewrite /getCurPerm PMap.gmap //.
  Qed.

  Definition mem_coherent_le (a b : mem) : Prop :=
    Ple (Mem.nextblock a) (Mem.nextblock b) /\
      (forall k,
          juicy_mem.contents_at b k =
            juicy_mem.contents_at a k) /\
      (forall k,
          Mem.perm_order''
            (access_at b k Cur)
            (access_at a k Cur)).

  Lemma coherent_mono (a b : mem) (s : rmap) :
    mem_coherent_le a b ->
    coherent a s ->
    coherent b s.
  Proof.
    rewrite /coherent.
    intros (Hnext & (Hcnt & Hperm)) Hcoh loc.
    specialize (Hcoh loc).
    destruct Hcoh as (Hval & Hcnt_a & Hacc_a).
    split.
    - intros Hge.
      apply Hval.
      rewrite /Ple in Hnext.
      lia.
    - split.
      + intros v Hv.
        rewrite Hcnt.
        apply (Hcnt_a v Hv).
      + eapply mem_lemmas.po_trans; eauto.
  Qed.

  Lemma frag_mem_auth_mono q (a b : mem) (s : rmap) :
    mem_coherent_le a b ->
    frag_mem_auth q a s ⊢ frag_mem_auth q b s.
  Proof.
    intros Hab.
    rewrite /frag_mem_auth.
    iIntros "(%Hcoh & Hauth)".
    iSplit; auto.
    iPureIntro.
    eapply coherent_mono; eauto.
 Qed.

  
  Lemma coherent_perm_of_rmap_max m σ :
    coherent m σ -> permMapLt (perm_of_rmap σ) (getMaxPerm m).
  Proof.
    intros Hcoh.
    assert (Hcur: permMapLt (perm_of_rmap σ) (getCurPerm m)).
    { by apply coherent_perm_of_rmap. }
    etransitivity; eauto.
    apply mem_cur_lt_max.
  Qed.
  
  Program Definition jsafe_frag_pre q (jsafe : coPset -d> unit -d> CC_core -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> iPropO Σ := λ E z c,
     |={E}=>
    ∀ (m : mem) (σ : rmap),
    frag_state_interp q m σ z -∗
      (* Hlt is derived from the current fragment state. *)
       ∃ (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
      (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ (*frag_state_interp_1 q m σ z ∗ *)
        Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
      
      (|={E}=> ∃ c' m' σ',
          ⌜corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'⌝ ∧
          frag_state_interp q m' σ' z ∗ ▷ jsafe E z c') ∨
      
      (∃ e args x σ1, ⌜at_external (cl_core_sem ge) c (restrPermMap Hlt) = Some (e, args)⌝ ∧
        frag_state_interp q m σ1 z ∗
          Jext_spec_pre (concurrent_ext_spec CS ext_link) e x
          (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
        ▷ (∀ ret m' σ' z' (*(Hlt' : permMapLt (perm_of_rmap σ') (getMaxPerm m')) *),
            ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> frag_state_interp q m' σ' z' -∗
            Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
              (sig_res (ef_sig e)) ret -∗
            ∃ c' σ2, ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧
              frag_state_interp q m' σ2 z' ∗ jsafe E z' c')).

  Local Instance jsafe_frag_pre_contractive q: Contractive (jsafe_frag_pre q).
  Proof.
    rewrite /jsafe_frag_pre => n jsafe jsafe' Hsafe E z c.
    do 19 f_equiv.
    - try f_contractive; repeat f_equiv. apply Hsafe.
    - do 2 f_equiv. f_contractive; repeat f_equiv. apply Hsafe.
  Qed.

  Local Definition jsafe_frag_def q: coPset -> unit -> CC_core -> iProp Σ :=
    fixpoint (jsafe_frag_pre q).
  Local Definition jsafe_frag_aux : seal (jsafe_frag_def). Proof. by eexists. Qed.
  Definition jsafe_frag := jsafe_frag_aux.(unseal).
  Local Lemma jsafe_frag_unseal : jsafe_frag = jsafe_frag_def.
  Proof. rewrite -jsafe_frag_aux.(seal_eq) //. Qed.

  Lemma jsafe_frag_unfold q E z c :
    jsafe_frag q E z c ⊣⊢ jsafe_frag_pre q (jsafe_frag q) E z c.
  Proof.
    rewrite jsafe_frag_unseal.
    apply (fixpoint_unfold (jsafe_frag_pre q)).
  Qed.

  Lemma frag_state_interp_1_to_state_interp m σ z:
    frag_state_interp 1 m σ z  -∗ state_interp m z.
  Proof.
    rewrite /frag_state_interp /state_interp /frag_mem_auth.
    iIntros "((% & ?) & ?)"; by iFrame.
  Qed.

  Lemma getCurPerm_access_at (m : mem) (b : positive) (ofs : Z) :
    (getCurPerm m) # b ofs = (Mem.mem_access m) # b ofs Cur.
  Proof. rewrite /getCurPerm /= PMap.gmap //=. Qed.

  Lemma access_at_Cur_of_mem_equiv (m1 m2 : mem) (loc : address) :
    mem_equiv.mem_equiv m1 m2 ->
    access_at m1 loc Cur = access_at m2 loc Cur.
  Proof.
    intros Heqv.
    destruct Heqv as [Hcur Hmax Hcnt Hnb].
    rewrite /access_at.
    rewrite <- ! getCurPerm_access_at.
    rewrite /mem_equiv.Cur_equiv /mem_equiv.access_map_equiv in Hcur.
    specialize (Hcur loc.1).
    by rewrite Hcur.
  Qed.
(*
  Lemma access_at_restrPermMap_Cur p m loc (Hlt : permMapLt p (getMaxPerm m)):
    access_at (restrPermMap Hlt) loc Cur = p # (loc.1) loc.2 .
  Proof.
    destruct loc as [b ofs].
    assert (Hacc: forall m b ofs, access_at m (b,ofs) Cur = (getCurPerm m) # b ofs).
    { rewrite /getCurPerm /access_at /=. intros; by rewrite Maps.PMap.gmap. }
    rewrite Hacc.
    pose proof (mem_equiv.getCur_restr p m Hlt) as Heq.
    specialize (Heq b).
    by rewrite Heq.
  Qed.
*)
  Lemma access_at_cur_getCurPerm m b ofs :
    access_at m (b, ofs) Cur = (getCurPerm m) # b ofs.
  Proof.
    unfold access_at, getCurPerm.
    simpl.
    rewrite PMap.gmap.
    reflexivity.
  Qed.

  Lemma access_at_restrPermMap_perm_res m s
    (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)) b ofs :
    access_at (restrPermMap Hlt) (b, ofs) Cur = perm_of_res (s @ (b, ofs)).
  Proof.
    rewrite / access_at.
    replace ((b, ofs).1) with b by auto.
    replace ((b, ofs).2) with ofs by auto.
    change ((Mem.mem_access (restrPermMap Hlt)) # b ofs Cur)
      with (permission_at (restrPermMap Hlt) b ofs Cur).
    by rewrite restrPermMap_Cur perm_of_rmap_lookup.
  Qed.

  Lemma coherent_restrPermMap m (s : rmap) (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)) :
    coherent m s -> coherent (restrPermMap Hlt) s.
  Proof.
    intros Hcoh.
    unfold coherent in *.
    intros [b ofs].
    destruct (Hcoh (b, ofs)) as [Hnb Hloc].
    split.
    - intros Hge.
      apply Hnb; auto.
    - unfold coherent_loc in *.
      destruct Hloc as [Hcontents Haccess].
      split.
      + unfold contents_cohere in *.
        intros v Hv.
        unfold contents_at in *.
        simpl.
        by apply Hcontents.
      + unfold access_cohere.
        rewrite access_at_restrPermMap_perm_res.
        apply po_refl.
  Qed.

  Lemma coherent_restrPermMap_of_coherent m s:
    coherent m s ->
    exists (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)), coherent (restrPermMap Hlt) s.
  Proof.
    intros.
    assert (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)).
    { intros b ofs.
      unfold coherent in H.
      destruct (H (b, ofs)) as [_ Hloc].
      rewrite perm_of_rmap_lookup.
      unfold coherent_loc in Hloc.
      destruct Hloc as [_ Hperm].
      unfold access_cohere in Hperm.
      eapply juicy_mem.perm_order''_trans.
      - apply getCur_Max.
      - unfold access_at in Hperm; simpl.
        unfold getCurPerm.
        rewrite PMap.gmap. done.
    }
    exists Hlt.
    by apply coherent_restrPermMap.
  Qed.

  Lemma coherent_of_restrPermMap_coherent m σ σ1
    (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)):
    coherent m σ -> coherent (restrPermMap Hlt) σ1 -> coherent m σ1.
  Proof.
    intros Hcoh_m Hcoh_restr.
    unfold coherent in *.
    intros (b & ofs).
    destruct (Hcoh_m (b, ofs)) as [Hnb [Hcontents Haccess]].
    destruct (Hcoh_restr (b, ofs)) as [Hnb1 [Hcontents1 Haccess1]].
    split.
    - intros Hb.
      apply Hnb1.
      by rewrite restrPermMap_nextblock.
    - split.
      + unfold contents_cohere in *.
        intros v Hv.
        by apply Hcontents1.
      + unfold access_cohere in *.
        eapply juicy_mem.perm_order''_trans.
        * apply Haccess.
        * by rewrite access_at_restrPermMap_perm_res in Haccess1.
  Qed.
  
  Lemma jsafe_jsafe_frag : forall E z c,
      jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge E z c ⊢
        jsafe_frag 1 E z c.
  Proof.
    intros.
    iLöb as "IH" forall (z c).
    rewrite jsafe_unfold jsafe_frag_unfold /jsafe_pre /jsafe_frag_pre.
    iIntros ">H !> % % S".
    rewrite /frag_state_interp /frag_mem_auth.
    iDestruct "S" as "((%Hcoh & Hrmap) & Hext)".
    pose proof Hcoh as Hcoh'.
    apply coherent_restrPermMap_of_coherent in Hcoh'.
    destruct Hcoh' as (Hlt & Hcoh').
    iDestruct (frag_state_interp_1_to_state_interp with "[$Hrmap $Hext]") as "S"; try done.
    iExists Hlt.
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - iLeft.
      iDestruct "H" as (?) "($ & _ & $)".
    - iRight; iLeft.
      iMod "H" as (??) "(% & (Hstate & Hsafe))".
      iIntros "!>".
      iDestruct "Hstate" as "((% & Hma) & Hext)".
      iFrame.
      iFrame "%".
      by iApply "IH".
    - iRight; iRight.
      iDestruct "H" as (????) "((Hmem & $) & $ & H)".
      iDestruct "Hmem" as (σ1) "(%Hcoh1 & Hmem)".
       assert (coherent m σ1) as Hcoh1'.
      { eapply coherent_of_restrPermMap_coherent; eauto. }
      iExists σ1.
      iSplit; first done. 
      iSplitL "Hmem"; try iSplit; try done.
      iIntros "!>" (?????).
      rewrite /state_interp.
      iSpecialize ("H" $! ret m' z' with "[%]"); try done.
      iMod "H" as "H".
      iIntros "!> S Hpost".
      iDestruct "S" as "((%Hcoh_m' & Hauth') & Hext')".
      iDestruct ("H" with "[Hauth' Hext'] Hpost")
        as (c') "(%Hafter & [Hmem Hext'] & Hsafe)".
      { iSplitL "Hauth'".
        - iExists σ'. iFrame. iPureIntro; try done.
        - done.
      }
      iPoseProof ("IH" with "Hsafe") as "Hsafe_frag".
      iDestruct "Hmem" as (σ2) "(% & Hmem)".
      iExists c', σ2.
      iFrame.
      iSplit; try done.
   Qed.


  (*
  Lemma jsafe_perm_mono : forall `{!VSTGS unit Σ} p1 p2 E z c p, permMapLt p2 p1 ->
    jsafe_perm E z c p1 ⊢ jsafe_perm E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (p H z c).
    rewrite !jsafe_perm_unfold /jsafe_perm_pre.
    iIntros ">H !>" (?? (Hmax & Hcur)) "S".
    pose proof (PreOrder_Transitive _ _ _ Hmax H).
    iDestruct ("H" with "[%] [S]")as "?"; eauto.
    Set Printing Implicit.
    try done.
    iPureIntro.
    instantiate (1 := m).
    iPureIntro.
    instantiate (1:= m). admit.
    iPureIntro.
    iDestruct ("H" with "S") as "[H | [H | H]]"; first done.
    - iLeft; done.
    - iRight; iLeft.
      iMod "H" as (???) "(? & ?)".
      iIntros "!>"; iExists _, _; iSplit; first done; iFrame.
      by iApply "IH".
    - iRight; iRight.
      iDestruct "H" as (????) "H".
      iExists _, _, _; iSplit; first done.
      iNext; iIntros (?????).
      iMod ("H" with "[%] [%]") as (??) "(? & ?)"; [done..|].
      iIntros "!>"; iExists _; iSplit; first done; iFrame.
      by iApply "IH".
  Qed.
*)
  Existing Instance mem_equiv.access_map_equiv_Equivalence.
    
(*  Axiom external_call_memLt
    : ∀ (ef : external_function) (ge : Senv.t) (vargs : list val) (m1 : mem) 
        (t : Events.trace) (vres : val) (m2 m1' : mem),
      Events.external_call ef ge vargs m1 t vres m2
      → memLt m1 m1'
      → ∃ (m2' : mem),
          (Events.external_call ef ge vargs m1' t vres m2'
           ∧ memLt m2 m2' ∧ Mem.unchanged_on (Events.loc_out_of_bounds m1) m1' m2')%type. (* for builtins only? *)

  Lemma alloc_step_step m1 m2 xs e:
    forall m1', memLt m1 m2 -> alloc_variables ge empty_env m1 xs e m1'
           -> exists m2', alloc_variables ge empty_env m2 xs e m2' /\ memLt m1' m2'.
  Proof. intros; eapply alloc_variables_memLt_gen in H0; eauto. Qed.

  Lemma cl_step_step m1 m2 (c c': CC_core):
    forall m1', memLt m1 m2 ->
           cl_step ge c m1 c' m1' -> exists m2', cl_step ge c m2 c' m2' /\ memLt m1' m2'.
  Proof.
    intros.
    inv H0.
    (* 1st case *)
    apply Clight_evsem.assign_locT_ax2 in H4.
    destruct H4 as (?& Hassign).
    eapply assign_locT_sub_memLt with (m1 := m2) in Hassign.
    destruct Hassign as (m2' & HmemLt1 & Hassign); auto.
    eexists; esplit.
    eapply step_assign; eauto.
    eapply eval_expr_eval_lvalue_memLt; eauto; econstructor; auto. auto.
    eapply eval_expr_eval_lvalue_memLt; eauto; econstructor.
    erewrite sem_cast_memLt; eauto.
    eapply Clight_evsem.assign_locT_ax1; eauto. auto. auto.
    (* 2nd case *)
    eexists; esplit.
    eapply step_set; eapply eval_expr_memLt; eauto. auto.
    (* 3rd case *)
    eexists; esplit.
    eapply step_call; eauto.
    eapply eval_expr_memLt; eauto.
    eapply eval_exprlist_memLt; eauto. auto.
    (* 4th case *)
    eexists; esplit.
    eapply step_builtin; eauto.
    eapply eval_exprlist_memLt; eauto.
    eapply external_call_memLt in H3; eauto.
    admit. admit.
    (* 5th case *)
    eexists; esplit.
    econstructor; eauto. auto.
    (* 6th case *)
    eexists; esplit. econstructor; eauto. auto.
    (* 7th case *)
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit.
    eapply step_ifthenelse; eauto.
    eapply eval_expr_memLt; eauto.
    eapply bool_val_memLt; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eapply free_list_memLt with (m2 := m2) in H1.
    destruct H1 as (? & H1 & ?). try done.
    eexists; esplit.
    eapply step_return_0.
    instantiate (1 := x). apply H1. auto. auto.
    (**)
    eapply free_list_memLt with (m2 := m2) in H3.
    destruct H3 as (? & H3 & ?). try done.
    eexists; esplit.
    econstructor.
    eapply eval_expr_memLt; eauto.
    eapply sem_cast_memLt; eauto.
    instantiate (1 := x); auto. auto. auto.
    (**)
    eapply free_list_memLt with (m2 := m2) in H2.
    destruct H2 as (? & H2 & ?).
    eexists; esplit.
    eapply step_skip_call; eauto. auto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    eapply eval_expr_eval_lvalue_memLt; eauto; econstructor; auto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    inv H1.
    eapply alloc_variables_memLt_gen with (m2 := m2) in H4.
    destruct H4 as (? &? & ?).
    eexists; esplit. eapply step_internal_function.
    eapply function_entry2_intro; eauto. auto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    admit. admit.
    eexists; esplit. econstructor; eauto. auto.
  Admitted. *)

  Lemma permMapLt_cur: forall p m (Hlt : permMapLt (getCurPerm p) (getCurPerm m)),
      permMapLt (getCurPerm p) (getMaxPerm m).
  Proof.
    intros.
    etrans; first apply Hlt.
    apply cur_lt_max.
  Qed.

  (*
  Lemma restr_permMapLt: forall (m1 m2 : mem) (M: memLt m1 m2)
      (M1: getMaxPerm m2 = getMaxPerm m1) (Hlt : permMapLt (getCurPerm m1) (getMaxPerm m2)),
      restrPermMap Hlt = m1.
  Proof.
    intros.
    destruct M as (? & ? & ? & ?).
    pose proof (Mem_canonical_useful m1) as Hcanon.
    destruct m1, m2.
    apply Mem.mkmem_ext.
    simpl in * ; auto.
    destruct mem_access, mem_access0; simpl.
    apply f_equal_prod; auto.
    - extensionality; extensionality k.
      destruct k; auto.
      simpl in *.
      rewrite /getMaxPerm /= in M1.
      inv M1.
      by specialize (f_equal (fun f => f x) H4).
    - rewrite /getMaxPerm /= in M1.
      inv M1.
      apply PTree.extensionality; intros.
      pose proof (f_equal (fun tr => PTree.get i tr) H5) as Hb.
      rewrite !PTree.gmap1 in Hb.
      rewrite PTree.gmap.
      destruct (PTree.get i t1) as [f1|] eqn:E1;
        destruct (PTree.get i t0) as [f2|] eqn:E2; simpl in *; try congruence.
      inversion Hb as [Hf]; clear Hb; subst.
      f_equal.
      clear H4.
      extensionality ofs k.
      destruct k; simpl.
      + exact (f_equal (fun g => g ofs) Hf).
      + rewrite getCurPerm_correct /permission_at /PMap.get /=.
        rewrite E2; auto.
    - auto.
   Qed.
*)
  
  Lemma permMapLt_cur_restr: forall (m : mem) (max : access_map) (Hlt : permMapLt max (getMaxPerm m))
                               (Hmax : permMapLt (getMaxPerm m) max),
      permMapLt (getCurPerm m) (getCurPerm (restrPermMap Hlt)).
  Proof.
    intros ???? b ofs.
    pose proof (@mem_equiv.getCur_restr max m Hlt) as Heq.
    eapply (perm_order''_trans _ ((getMaxPerm m) # b ofs)); last first; try apply getCur_Max.
    rewrite /mem_equiv.access_map_equiv in Heq.
    rewrite /permMapLt /Mem.perm_order'' in Hmax.
    specialize (Heq b).
    specialize (Hmax b ofs).
    by rewrite -Heq in Hmax.
  Qed.


  (*
  Definition thread_safe max (tp : dtp) i g :=
    ∃ cnti : containsThread tp i,
    match getThreadC cnti with
    | Krun c | Kblocked c => jsafe_perm g ⊤ tt c ((getThreadR cnti).1, max)
    | Kresume c v =>
      ∀ c',
        (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
        ⌜cl_after_external None c = Some c'⌝ →
        jsafe_perm g ⊤ tt c' ((getThreadR cnti).1, max)
    | Kinit v1 v2 =>
      ∃ q_new,
      ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_perm g ⊤ tt q_new ((getThreadR cnti).1, max)
    end%I.

  Definition thread_safe max (tp : dtp) i g :=threads_safe max (tp : dtp) (gs : gmap nat gname) :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), ∃ g, ⌜gs !! i = Some g⌝ ∧ thread_safe max tp i g.
  *)


  (*
    Definition thread_safe (tp : dtp) i :=
    ∃ cnti : containsThread tp i,
      match getThreadC cnti with
      | Krun c | Kblocked c => jsafe_perm ⊤ tt c ((getThreadR cnti).1)
      | Kresume c v =>
          ∀ c',
            (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
            ⌜cl_after_external None c = Some c'⌝ →
            jsafe_perm ⊤ tt c' ((getThreadR cnti).1)
      | Kinit v1 v2 =>
          ∃ q_new,
    ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_perm ⊤ tt q_new ((getThreadR cnti).1)
  end%I.

   Definition threads_safe (tp : dtp) :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), thread_safe tp i.
   *)

  (*
thread i has a safety proof, or
thread i owns a fraction of frag_state_interp.

   *)

(*
  Definition thread_safe (tp : dtp) (i : nat) : iProp Σ :=
  ∃ cnti : containsThread tp i,
    match getThreadC cnti with
    | Krun c | Kblocked c =>
        jsafe_frag 1 ⊤ () c

    | Kresume c _ =>
        ∀ c',
          ⌜cl_after_external None c = Some c'⌝ →
          jsafe_frag 1 ⊤ () c'

    | Kinit v1 v2 =>
        ∃ c',
          ⌜cl_initial_core ge v1 [v2] = Some c'⌝ ∧
          jsafe_frag 1 ⊤ () c'
    end.

Definition threads_safe (tp : dtp) : iProp Σ :=
  [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
    thread_safe tp i.

 *)

  
  Definition thread_safe (tp : dtp) i (q : Qp):=
    ∃ cnti : containsThread tp i,
      match getThreadC cnti with
      | Krun c | Kblocked c => jsafe_frag q ⊤ tt c
      | Kresume c v =>
          ∀ c',
            (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
            ⌜cl_after_external None c = Some c'⌝ →
            jsafe_frag q ⊤ tt c'
      | Kinit v1 v2 =>
          ∃ q_new,
    ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_frag q ⊤ tt q_new
  end%I.

  (*
  Definition threads_safe (tp : dtp) (qs : gmap nat Qp) (m : mem) :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ q σ (cnti : containsThread tp i),
        ⌜qs !! i = Some q ∧ permMapLt (perm_of_rmap σ) (getThreadR cnti).1⌝ ∧
          thread_safe tp i q ∗ frag_mem_auth q m σ. *)

  Definition threads_safe (tp : dtp) (qs : gmap nat Qp) (m : mem) : iProp Σ :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ q (σ : rmap) (cnti : containsThread tp i)
        (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
        ⌜qs !! i = Some q ∧ permMapLt (perm_of_rmap σ) (getThreadR cnti).1⌝ ∗
            thread_safe tp i q ∗ frag_mem_auth q (restrPermMap Hlt) σ.

  (*
    Definition threads_safe (tp : dtp) (qs : gmap nat Qp) (m : mem) : iProp Σ :=
  [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
    ∃ q (σ : rmap) (cnti : containsThread tp i)
      (Hlt : permMapLt (getThreadR cnti).1 (getMaxPerm m)),
      ⌜qs !! i = Some q ∧
        permMapLt (perm_of_rmap σ) (getThreadR cnti).1⌝ ∗
      thread_safe tp i q ∗
      frag_mem_auth q (restrPermMap Hlt) σ.

   *)
  
  Definition threads_wellformed (tp : dtp) :=
    forall i (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i),
    match getThreadC cnti with
    | Krun q => Logic.True
    | Kblocked q => cl_at_external q <> None
    | Kresume q v => cl_at_external q <> None /\ v = Vundef
    | Kinit _ _ => Logic.True
    end.

  Definition access_at_nonempty (m : mem) (loc : address) : Prop :=
    access_at m loc Cur = Some Nonempty /\
      access_at m loc Max = Some Nonempty.

  Definition access_at_1 (m : Mem.mem) (l : address) : forall k : perm_kind, option permission :=
    fun k =>
      let '(b, ofs) := l in
      (Mem.mem_access m) # b ofs k.

  Definition nonEmptyRangeCur (m : Mem.mem) (l: Values.block * Z) : Prop :=
    forall (i : Z), (0 <= i < Z.of_nat (size_chunk_nat Mptr))%Z ->
                    (Mem.mem_access m) # (l.1) (l.2 + i)%Z Cur = Some Nonempty.

  Definition locks_coherent (tp : dtp) (m : mem) (ls : gset address) :=
    forall l,
      (l ∈ ls ->
       lockRes tp l <> None /\
         ((Mem_load_unchecked Mptr m l.1 l.2 = (Vptrofs Ptrofs.zero) /\
            lockRes tp l = Some (empty_map, empty_map)) \/
            (Mem_load_unchecked Mptr m l.1 l.2 = (Vptrofs Ptrofs.one))) /\
         (forall i  (cnti : containsThread tp i)
            (Hp : permMapLt (getThreadR cnti).1 (getMaxPerm m)), nonEmptyRangeCur (restrPermMap Hp) l)).

  Lemma storebytes_contents_eq :
    forall m m' b ofs bytes b0,
      Mem.storebytes m b ofs bytes = Some m' ->
      (Mem.mem_contents m') # b0 =
        if peq b0 b
        then Mem.setN bytes ofs ((Mem.mem_contents m) # b)
        else (Mem.mem_contents m) # b0.
  Proof.
    intros m m' b ofs bytes b0 H.
    Transparent Mem.storebytes.
    unfold Mem.storebytes in H.
    destruct (Mem.range_perm_dec m b ofs (ofs + length bytes) Cur Writable) as [RP|NRP];
      try discriminate.
    inversion H; subst m'; clear H.
    destruct (peq b0 b) as [->|Hbneq].
    - rewrite PMap.gss. reflexivity.
    - rewrite PMap.gso; auto.
  Qed.

Lemma no_overlap_to_sidecond_when_bytes_nonempty (n : nat) (l2 ofs : Z) (bytes : list memval):
  (n <> 0)%nat -> bytes <> nil ->
  (forall i , (0 <= i < Z.of_nat n)%Z -> ¬ (ofs <= l2 + i < ofs + Z.of_nat (length bytes))%Z) ->
  (l2 + Z.of_nat n <= ofs)%Z \/ (ofs + Z.of_nat (length bytes) <= l2)%Z.
Proof.
  intros Hn0 Hbytes Hno.
  set (nZ := Z.of_nat n).
  set (lenZ := Z.of_nat (length bytes)).
  destruct (Z.le_gt_cases ofs l2) as [Hofs_le_l2 | Hl2_lt_ofs].
  - (* ofs <= l2 *)
    destruct (Z.le_gt_cases (ofs + lenZ) l2) as [Hend_le_l2 | Hl2_lt_end].
    + right. lia.
    + (* contradiction with i = 0 *)
      exfalso.
      specialize (Hno 0%Z).
      apply Hno; try lia.
  - (* l2 < ofs *)
    destruct (Z.le_gt_cases (l2 + nZ) ofs) as [Hend_le_ofs | Hofs_lt_end].
    + by left.
    + (* contradiction with i = ofs - l2 *)
      exfalso.
      assert (Hn_pos : (0 < nZ)%Z). lia.
      set (i := (ofs - l2)%Z).
      specialize (Hno i).
      assert (Hi_range : (0 <= i < nZ)%Z).
      { subst i; split; [lia|]. lia. }
      specialize (Hno Hi_range).
      apply Hno.
      subst i.
      split; try lia.
      pose proof (nil_or_length_pos bytes).
      destruct H; try done; try lia.
Qed.

Lemma setPermBlock_sets_range
  (b : Values.block) (ofs : Z) (pmap0 : access_map) (n : nat) :
  forall i : Z,
    (0 <= i < Z.of_nat n)%Z ->
    (setPermBlock (Some Nonempty) b ofs pmap0 n) # b (ofs + i)%Z = Some Nonempty.
Proof.
  induction n as [|n IH]; intros i Hi.
  - simpl in Hi; lia.
  - simpl setPermBlock.
    unfold setPerm.
    rewrite Maps.PMap.gss.
    destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat n) (ofs + i)) as [Heq|Hneq].
    + done.
    + simpl.
      apply IH. lia.
Qed.

Lemma free_preserves_cur_nonempty :
  forall m m1 b lo hi (l: address),
    Mem.free m b lo hi = Some m1 ->
    (Mem.mem_access m) # (l.1) l.2 Cur = Some Nonempty ->
    (Mem.mem_access m1) # (l.1) l.2 Cur = Some Nonempty.
Proof.
  intros m m1 b lo hi l Hfree Hacc.
  destruct (peq (l.1) b) as [Hb|Hb].
  - subst.
    assert (Houtside : (l.2 < lo)%Z \/ (hi <= l.2)%Z).
    { destruct (zlt l.2 lo) as [Hlt|Hge]; [left; exact Hlt|].
      destruct (zle hi l.2) as [Hle|Hlt]; [right; exact Hle|].
      exfalso.
      pose proof (Mem.free_range_perm _ _ _ _ _ Hfree) as Hrp.
      specialize (Hrp l.2).
      assert (Hlohi : (lo <= l.2 < hi)%Z) by lia.
      apply Hrp in Hlohi.
      unfold Mem.perm in Hlohi.
      rewrite Hacc in Hlohi. inv Hlohi.
    }
    rewrite (Mem.free_result _ _ _ _ _ Hfree).
    unfold Mem.unchecked_free; simpl.
    rewrite PMap.gss.
    destruct Houtside as [Hlt | Hge].
    + destruct (zle lo l.2) eqn:Hzle; simpl; auto.
      exfalso. lia.
    + destruct (zle lo l.2) eqn:Hzle; simpl; auto.
      destruct (zlt l.2 hi) eqn:Hzlt; simpl; auto.
      lia.
  - rewrite (Mem.free_result _ _ _ _ _ Hfree).
    unfold Mem.unchecked_free; simpl.
    rewrite PMap.gso; auto.
Qed.

Lemma free_list_preserves_cur_nonempty_outside :
  forall m l m' l0 i,
    Mem.free_list m l = Some m' ->
    (Mem.mem_access m) # (l0.1) (l0.2 + i)%Z Cur = Some Nonempty ->
    (Mem.mem_access m') # (l0.1) (l0.2 + i)%Z Cur = Some Nonempty.
Proof.
  intros m l.
  revert m.
  induction l as [| [(b & lo) hi] tl IH]; intros; simpl in H.
  - inv H; try done.
  - destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; try discriminate.
    eapply IH; try done.
    eapply (free_preserves_cur_nonempty m m1 b lo hi (l0.1, (l0.2 + i)%Z)); try done.
Qed.

Lemma mem_step_preserves_nonempty_range :
  forall m m',
    mem_step m m' ->
    forall l : address,
      (forall i : Z,
          (0 <= i < size_chunk_nat Mptr)%Z ->
          (Mem.mem_access m) # (l.1) (l.2 + i)%Z Cur = Some Nonempty) ->
      forall i : Z,
        (0 <= i < size_chunk_nat Mptr)%Z ->
        (Mem.mem_access m') # (l.1) (l.2 + i)%Z Cur = Some Nonempty.
Proof.
  intros m m' Hstep.
  induction Hstep; intros.
  4 : {
    eapply IHHstep2; try done.
    intros.
    eapply IHHstep1; try done.
  }
  - erewrite Mem.storebytes_access; eauto.
  - assert (Hlneq : l.1 <> b').
    { apply Mem.alloc_result in H.
      subst.
      apply H0 in H1.
      intros Hcontra.
      assert (Hperm : Mem.perm m l.1 (l.2 + i) Cur Nonempty).
      { unfold Mem.perm, Mem.perm_order'.
        rewrite H1. apply perm_refl. }
      assert (Hvb : Mem.valid_block m l.1).
      { eapply Mem.perm_valid_block; eauto. }
      unfold Mem.valid_block in Hvb.
      rewrite Hcontra in Hvb.
      unfold Plt in Hvb. lia.
    }
    inversion H; subst; simpl.
    rewrite PMap.gso; auto.
  - eapply free_list_preserves_cur_nonempty_outside; eauto.
Qed.

Lemma mem_step_preserves_lock_bytes :
    forall m m' (l : address),
      mem_step m m' ->
      nonEmptyRangeCur m l ->
      Mem.getN (size_chunk_nat Mptr) l.2 ((Mem.mem_contents m)  # (l.1))
      = Mem.getN (size_chunk_nat Mptr) l.2 ((Mem.mem_contents m') # (l.1)).
  Proof.
    intros m m' l Hstep HNone.
    revert l HNone.
    induction Hstep; intros.
    4 : {
      unfold nonEmptyRangeCur in *.
      specialize (IHHstep1 l HNone).
      assert (HNone'' : forall i : Z, (0 <= i < size_chunk_nat Mptr)%Z ->
                 (Mem.mem_access m'') # (l.1) (l.2 + i)%Z Cur = Some Nonempty).
      { by eapply mem_step_preserves_nonempty_range. }
      specialize (IHHstep2 l HNone'').
      by rewrite IHHstep1.
    }
    - set (n := size_chunk_nat Mptr).
      have Hcontents := storebytes_contents_eq _ _ _ _ _ _ H.
      destruct (peq (l.1) b) as [Heq|Hneq].
      + subst.
        rewrite Hcontents.
        if_tac; try done.
        unfold Mem.storebytes in H.
        destruct (Mem.range_perm_dec m l.1 ofs (ofs + length bytes) Cur Writable)
          as [Hrp | Hrp]; try discriminate.
        destruct (eq_dec bytes []).
        { subst; done. }
        have Hno_overlap : forall i, (0 <= i < Z.of_nat n)%Z ->
            ¬ (ofs <= l.2 + i < ofs + Z.of_nat (length bytes))%Z.
        { intros i Hi Hover.
          have HpermW : Mem.perm m l.1 (l.2 + i) Cur Writable.
          { eapply Hrp; lia. }
          have Hacc : (Mem.mem_access m) # (l.1) (l.2 + i)%Z Cur = Some Nonempty.
          { rewrite /nonEmptyRangeCur in HNone; apply HNone; lia. }
          unfold Mem.perm in HpermW.
          rewrite Hacc in HpermW.
          inv HpermW.
        }
        rewrite Mem.getN_setN_outside; try done.
        apply no_overlap_to_sidecond_when_bytes_nonempty; try done.
      + rewrite Hcontents.
        if_tac; try done.
    - set (n := size_chunk_nat Mptr).
      Transparent Mem.alloc.
      pose proof H as Hal.
      rewrite /Mem.alloc in H.
      injection H as Hxy.
      pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
      simpl in Hcnt.
      unfold nonEmptyRangeCur in HNone.
      rewrite Hcnt.
      rewrite PMap.gso; auto.
      intro Hcontra.
      assert (Hperm : Mem.perm m l.1 l.2 Cur Nonempty).
      {
        unfold Mem.perm.
        specialize (HNone 0).
        replace (l.2 + 0%nat)%Z with l.2 in HNone; try lia.
        rewrite HNone; last first. done.
        unfold Mem.perm_order'.
        apply perm_refl. }
      apply Mem.perm_valid_block in Hperm.
      unfold Mem.valid_block in Hperm.
      subst.
      rewrite <- Hcontra in Hperm.
      unfold Plt in Hperm. lia.
    - set (n := size_chunk_nat Mptr).
      Transparent Mem.free_list.
      pose proof H as Hfl.
      (* apply free_list_contents in Hfl.
      by rewrite Hfl. *)
      Admitted. 

  (* test *)
  Definition mem_access_Cur (m : Mem.mem) : access_map :=
    Maps.PMap.map (fun f => fun ofs => f ofs Cur) (Mem.mem_access m).

  
Lemma setPermBlock_eq_implies_mem_access_range_Cur
  (m : Mem.mem) (l: Values.block * Z) (pmap0 : access_map) (n : nat) :
  setPermBlock (Some Nonempty) l.1 l.2 pmap0 n = mem_access_Cur m ->
  forall (i : Z),
    (0 <= i < Z.of_nat n)%Z ->
    (Mem.mem_access m) # (l.1) ((l.2 + i)%Z) Cur = Some Nonempty.
Proof.
  intros.
  have Hcur :
    (mem_access_Cur m) # (l.1) (l.2 + i)%Z = Some Nonempty.
  {
    rewrite <- H.
    apply setPermBlock_sets_range; try done. }
  unfold mem_access_Cur in Hcur.
  by rewrite Maps.PMap.gmap in Hcur.
Qed.

(*
Lemma can_store_at_getCurPerm_of_perm_order'1
  (m : Mem.mem) (b : Values.block) (ofs : Z) :
  Mem.perm_order' ((Mem.mem_access m) # b ofs Cur) Writable ->
  can_store_at (getCurPerm m) (b,ofs).
Proof.
  rewrite /Mem.perm_order' /can_store_at /getCurPerm /=.
  intros H.
  rewrite PMap.gmap.
  destruct ((Mem.mem_access m) # b ofs Cur); try done.
Qed.
*)

Lemma Mem_unchecked_restrPermMap :
  forall (m: Mem.mem) (p: access_map) (Hlt : permMapLt p (getMaxPerm m)) l,
    Mem_load_unchecked Mptr (restrPermMap Hlt) l.1 l.2 =
      Mem_load_unchecked Mptr m l.1 l.2.
Proof. intros m p Hlt [b ofs]; by unfold Mem_load_unchecked. Qed.

Lemma state_interp_to_frag m z :
  @state_interp Σ unit heapGS_gen_heapGS VST_extGS m z
  -∗ ∃ σ, frag_state_interp 1 m σ z.
Proof.
  rewrite /state_interp /frag_state_interp /frag_mem_auth /mem_auth .
  iIntros "(Hmem & Hext)".
  iDestruct "Hmem" as (σ Hcoh) "Hauth".
  iFrame "Hext".
  iExists σ.
  iSplit; first done.
  iExact "Hauth".
Qed.

Lemma corestep_invariant_sub (tp : dtp) (m m' : mem) (i : nat)
  (cnti : containsThread tp i)
  (p : access_map) (s c' : CC_core)
  (Hinv : invariant tp)
  (Hcompat : mem_compatible tp m)
  (Hlt : permMapLt p (getMaxPerm m))
  (Hsub : permMapLt p (getThreadR cnti).1)
  (Hstep : corestep (cl_core_sem ge) s (restrPermMap Hlt) c' m'):
  invariant
    (updThread cnti (Krun c')
       (getCurPerm m', (getThreadR cnti).2)).
Proof.
  Check (cl_core_sem ge) .
  assert (Hstep' :
           corestep semSem s (restrPermMap Hlt) c' m').
  { change (corestep (cl_core_sem ge) s (restrPermMap Hlt) c' m'); auto. }
  pose proof (msem_decay semSem s (restrPermMap Hlt) c' m' Hstep') as Hdecay.
  assert (Hmax : forall p0, permMapLt p0 (getMaxPerm m) ->
             permMapLt p0 (getMaxPerm (restrPermMap Hlt))).
  { intros p0 Hp b ofs.
    specialize (Hp b ofs).
    by rewrite restr_Max_eq. }
  assert (Hdisj_sub :
           forall p0, permMapsDisjoint (getThreadR cnti).1 p0 ->
             permMapsDisjoint (getCurPerm (restrPermMap Hlt)) p0).
  {
    intros p0 Hd b ofs.
    specialize (Hd b ofs).
    specialize (Hsub b ofs).
    rewrite getCurPerm_correct.
    rewrite restrPermMap_Cur.
    rewrite perm_union_comm in Hd |- *.
    pose proof (perm_union_lower (p0 # b ofs)  (((getThreadR cnti).1) # b ofs) (p # b ofs)).
    rewrite perm_union_comm.
    apply H; auto. 
  }
  assert (Hcoh_sub :
           forall p0, permMapCoherence (getThreadR cnti).1 p0 ->
                 permMapCoherence (getCurPerm (restrPermMap Hlt)) p0).
  { intros p0 Hcoh b ofs.
    rewrite getCurPerm_correct.
    rewrite restrPermMap_Cur.
    eapply perm_coh_lower; eauto.
    apply po_refl.
  }
  eapply ThreadPoolWF.updThread_inv; eauto.
  - intros j cntj Hneq.
    destruct (DryHybridMachine.no_race_thr _ Hinv _ _ cnti cntj Hneq) as (Hdata &  Hlocks).
    split; auto.
    eapply CoreLanguageDry.decay_disjoint; eauto.
    apply Hmax.
    pose proof (DryHybridMachine.compat_th _ _ Hcompat cntj).
    apply H.
  - intros j cntj _.
    simpl.
    destruct (thread_data_lock_coh tp Hinv i cnti) as (H & _).
    apply H.
  - simpl.
    intros j cntj _.
    eapply CoreLanguageDry.decay_coherence; eauto.
    + apply Hmax.
      pose proof (DryHybridMachine.compat_th _ _ Hcompat cntj).
      apply H.
    + apply Hcoh_sub.
      destruct (thread_data_lock_coh tp Hinv j cntj) as (H & _).
      apply H.
  - simpl; intros laddr pmap0 Hres.
    destruct (DryHybridMachine.no_race _ Hinv _ laddr cnti _ Hres) as (Hdata & Hlocks).
    destruct (DryHybridMachine.compat_lp _ _ Hcompat laddr _ Hres) as (Hlt_data & Hlt_lock).
    split.
    + apply permMapsDisjoint_comm.
      eapply CoreLanguageDry.decay_disjoint; eauto.
    + apply permMapsDisjoint_comm; auto.
  - simpl; intros laddr pmap0 Hres.
    destruct (DryHybridMachine.compat_lp _ _ Hcompat laddr _ Hres) as (Hlt_data & Hlt_lock).
    split.
    + eapply (DryHybridMachine.thread_data_lock_coh _ Hinv _ cnti); eauto.
    + eapply CoreLanguageDry.decay_coherence; eauto.
      apply Hcoh_sub.
      apply (DryHybridMachine.locks_data_lock_coh _ Hinv laddr _ Hres).
  - simpl.
    eapply CoreLanguageDry.decay_coherence; eauto.
    + apply Hmax.
      apply (DryHybridMachine.compat_th _ _ Hcompat cnti).
    + apply Hcoh_sub.
      apply (DryHybridMachine.thread_data_lock_coh _ Hinv _ cnti).
Qed.

Lemma corestep_compatible_sub (tp : dtp) (m m' : mem) (i : nat) (cnti : containsThread tp i)
  (p : access_map) (s c' : CC_core) (Hinv : invariant tp)
  (Hcompat : mem_compatible tp m) (Hlt : permMapLt p (getMaxPerm m))
  (Hsub : permMapLt p (getThreadR cnti).1)
  (Hstep : corestep (cl_core_sem ge) s (restrPermMap Hlt) c' m'):
    mem_compatible (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m'.
Proof.
  set (tp0 := updThread cnti (Krun s) (p, (getThreadR cnti).2)).
  assert (cnti0 : containsThread tp0 i).
  { subst tp0; eapply cntUpdate; eauto. }
  assert (Hinv0 : invariant tp0).
  { subst tp0; eapply ThreadPoolWF.invariant_decr; eauto.
    intros; apply po_refl. }
  assert (Hcompat0 : mem_compatible tp0 m).
  { subst tp0.
    constructor.
    - intros.
      assert (cnt_old : containsThread tp tid).
      { eapply cntUpdate'; eauto. }
      destruct (eq_nat_dec i tid); subst.
      + split.
        * replace cnt with cnti0 by apply proof_irrelevance.
          rewrite gssThreadRes //.
        * replace cnt with cnti0 by apply proof_irrelevance.
          rewrite gssThreadRes.
          apply (proj2 (DryHybridMachine.compat_th _ _ Hcompat cnti)).
      + erewrite @gsoThreadRes with (cntj := cnt_old); auto.
        apply (Hcompat tid cnt_old).
    - intros laddr pmaps Hres.
      rewrite gsoThreadLPool in Hres.
      eapply DryHybridMachine.compat_lp; eauto.
    - intros laddr rmap Hres.
      rewrite gsoThreadLPool in Hres.
      eapply DryHybridMachine.lockRes_blocks; eauto.
  }

  pose proof Hstep as Hev.
  apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hev as (ev & Hev).
  assert (Hrestr0: restrPermMap (proj1(DryHybridMachine.compat_th _ _ Hcompat0 cnti0)) =
        restrPermMap Hlt).
  { eapply restrPermMap_irr; eauto.
    subst tp0; rewrite gssThreadRes //. }  
  assert (Hev0 : ev_step semSem s
                   (restrPermMap(proj1 (DryHybridMachine.compat_th _ _ Hcompat0 cnti0))) ev c' m').
  { rewrite Hrestr0 //. }
  (* UP *)
  assert (Hcompat1 : mem_compatible
                       (updThread cnti0 (Krun c') (getCurPerm m', (getThreadR cnti0).2)) m').
  { eapply
      (CoreLanguageDry.corestep_compatible
         (Sem := Sem)); eauto.
    - subst tp0; rewrite gssThreadCode; auto.
    - simpl; done. }
  unfold tp0 in cnti0, Hcompat1.
  rewrite gssThreadRes /= in Hcompat1.
  rewrite OrdinalPool.updThread_twice // in Hcompat1.
Qed.
  End conc_heap.

  Existing Instance HybridMachine.DryHybridMachine.DryHybridMachineSig.

  Theorem dry_safety `{!VSTGpreS unit Σ} `{!inG Σ (gmap_view.gmap_viewR address unitR)}
    `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} sch n : exists b c_init,
    Genv.find_symbol (globalenv prog) (Ctypes.prog_main prog) = Some b /\
    cl_initial_core (globalenv prog) (Vptr b Ptrofs.zero) [] = Some c_init /\
    HybridMachineSig.HybridCoarseMachine.csafe
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
     (sch, [],
      DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
        c_init) (proj1_sig init_mem) n.
  Proof.
    eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
    simpl; intros; iIntros "_".
    pose proof (empty_coherent Mem.empty) as Hcoh_empty.
    Check  init_conc_VST_frag.
    iMod (init_conc_VST_frag () tt) as "H".
    iSpecialize ("H" $! Hinv).
    iDestruct "H" as (HG FS ES HL) "(Hstate & Hfunspec & Hext & locks & _)".
    set (HHfrag :=
           Build_VSTGS _ _
             ({| heapGS_invGS := Hinv;
                heapGS_gen_heapGS := HG;
                heapGS_funspecGS := FS |} : heapGS Σ)
             ES).
    destruct (spr HHfrag HL) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "[$Hstate $Hfunspec $Hext]") as (?) "(S & Hsafe)".
    iAssert (|={⊤}[∅]▷=>^n ⌜HybridMachineSig.HybridCoarseMachine.csafe
               (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
               (sch, [],
                 DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
                   q) (proj1_sig init_mem) n⌝) with "[S Hsafe locks]" as "Hdry".
    2: { iApply step_fupd_intro; first done.
         iNext; iApply (step_fupdN_mono with "Hdry").
         iPureIntro. intros.
         eexists. eexists. split; first done; split; first apply Hinit; done.
    }
    clear Hinit Hsafe.
    rewrite bi.and_elim_l.
    set (tp := initial_machine _ _).
    assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
    assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat
        by apply ThreadPoolWF.initial_mem_compatible.
    assert (threads_wellformed tp) as Htp_wf by done.
    iPoseProof (state_interp_to_frag with "S") as (σ) "S".
    set qs := (<[0 := 1%Qp]> (∅ : gmap nat Qp)).
    rewrite /frag_state_interp /frag_mem_auth.
    iDestruct "S" as "([%Hcoh Hmem] & Hext)".
    iAssert (@threads_safe HHfrag HL tp qs (`init_mem)) with "[Hsafe Hmem]" as "Hsafe".
    { subst tp.
      rewrite /frag_state_interp.
      unfold threads_safe, thread_safe; simpl.
      iSplit; auto.
      Print resource_map.resource_map_auth .
      assert (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm (`init_mem))).
      { apply (coherent_perm_of_rmap_max (`init_mem) σ Hcoh). }
      iExists 1%Qp, σ, _, Hlt.
      iSplit; auto.
      - rewrite /frag_mem_auth.
        iSplit; auto.
        iPureIntro.
        by apply coherent_perm_of_rmap.
      - rewrite /frag_mem_auth.
        iFrame.
        iSplit; auto.
        unshelve iExists _; first done.
        iApply (jsafe_jsafe_frag with "Hsafe").
        iPureIntro.
        split; auto.
        by apply coherent_restrPermMap.
    }
    assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    clearbody tp.
    set (ls := ∅) in Hlocks |- *.
    clearbody ls.
    clear dependent b x q.
    clearbody qs.
    clear Hcoh.
    clear σ.
    (* Is σ also generalized by the Löb induction *)
    iLöb as "IH" forall (sch tr tp m n ls qs Htp_wf Hinvariant Hcompat Hlocks).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2 : {
      Local Opaque lock_state.
      iApply step_fupd_intro; try done. iNext.
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros (U'').
        iApply ("IH" $! U'' tr tp m n ls qs with "[] [] [] [] locks Hext"); try done. }
      iApply (step_fupdN_mono with "H"); iPureIntro.
      intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
        with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
      eapply HybridMachineSig.schedfail; eauto.
      rewrite /containsThread /= /OrdinalPool.containsThread.
      intros ?.
      pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle;
        [lia | congruence].
    }
    rewrite {2}/threads_safe.
    iPoseProof (big_sepL_lookup_acc_impl i i with "[$Hsafe]") as "Hsafe".
    apply lookup_seq; eauto.
    iDestruct "Hsafe" as
      "((% & %σ1 & % & % & (% & %Hlt1) & ((% & Hsafei) &  Hfragi)) & Hsafe)".
    replace cnti0 with cnti by apply ProofIrrelevance.proof_irrelevance.
    clear cnti0.
    destruct (getThreadC cnti) eqn: Hi.
    - (* Krun *)
      destruct (cl_halted s) eqn: Hhalt; [|destruct (cl_at_external s) eqn: Hat_ext].
      + (* halted *)
        assert (HybridMachineSig.halted_thread cnti Int.zero) as Hhalt'.
        { econstructor; eauto. hnf; rewrite Hhalt //. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (threads_safe tp qs m) with "[Hsafei Hfragi Hsafe]" as "Hsafe".
        { iApply "Hsafe".
          * iIntros "!>" (????) "H"; iApply "H".
          * iExists q, σ1 , cnti, Hlt.
            iSplit; auto.
            iSplitL "Hsafei"; try iFrame.
            rewrite /thread_safe.
            iExists cnti.
            rewrite Hi; done. }
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros (x).
          iApply ("IH" $! _ _ _ _ _ _ with "[] [] [] [] locks Hext Hsafe"); try done.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro.
        intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl;
          rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.halted_step; eauto.
      + (* HybridMachineSig.suspend_step *)
        assert (HybridMachineSig.suspend_thread m cnti (updThreadC cnti (Kblocked s))) as Hsuspend.
        { eapply (HybridMachineSig.SuspendThread _ _ _ _ _ _ _ _ Hcompat); done. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, (updThreadC cnti (Kblocked s))) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros.
          iApply ("IH" $! x tr (updThreadC cnti (Kblocked s)) m n ls qs
                   with "[%] [%] [%] [%] locks Hext [Hsafe Hfragi Hsafei]"); try done.
          - intros j cntj.
            destruct (eq_dec j i) as [-> | Hneq].
            + rewrite (gssThreadCC cnti (Kblocked s) cntj).
              simpl.
              rewrite Hat_ext //.
            + pose proof (cntUpdateC' (Kblocked s) cnti cntj) as cntj0.
              rewrite -gsoThreadCC.
              by apply Htp_wf. done.
          - by apply ThreadPoolWF.updThreadC_invariant.
          - by apply StepLemmas.updThreadC_compatible.
          - iApply "Hsafe".
            + iIntros "!>" (k y (-> & ?)%lookup_seq Hneq) "Hy".
              iDestruct "Hy" as (q0 σ0 cnty Hltσ) "((%Hqy & %Hlt2) & Hsafe_y & Hfrag_y)".
              iExists q0, σ0, (cntUpdateC _ _ cnty), Hltσ.
              iSplit.
              * iPureIntro.
                split; auto.
                rewrite gThreadCR //.
              * iFrame.
                replace (0 + k) with k by lia.
                assert (Hneq' : i <> k) by lia.
                iDestruct "Hsafe_y" as (cntyk) "Hsafe_y".
                set (cntyk' := cntUpdateC (Kblocked s) cnti cntyk).
                iExists cntyk'.
                rewrite -(gsoThreadCC Hneq'). done.
            + iExists q, σ1, (cntUpdateC (Kblocked s) cnti cnti), Hlt.
              iSplit; auto.
              * destruct H. iSplit; auto.
                rewrite (gThreadCR cnti cnti (Kblocked s)
                            (cntUpdateC (Kblocked s) cnti cnti)).
                done.
              * iFrame.
                rewrite /thread_safe /frag_mem_auth.
                iExists (cntUpdateC (Kblocked s) cnti cnti).
                by rewrite gssThreadCC.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl;
          rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.suspend_step; eauto.
      + (* corestep: HybridMachineSig.thread_step *)
        rewrite jsafe_frag_unfold /jsafe_frag_pre.
        iAssert (⌜coherent (restrPermMap Hlt) σ1⌝) with "[Hfragi]" as "%Hcoh".
        { by iDestruct "Hfragi" as "(? & ?)". }
        
        (* UP *)
        
        Check compat_th _ _ Hcompat cnti.
        pose proof (proj1 (compat_th _ _ Hcompat cnti)) as Hthread.
        assert (Hab :
                 mem_coherent_le
                   (restrPermMap Hlt)
                   (@restrPermMap (getThreadR cnti).1 m Hthread)).
        { split.
          - rewrite !restrPermMap_nextblock.
            apply Ple_refl.
          - split; intro k.
            + rewrite !restrPermMap_contents //.
            + rewrite !access_at_restrPermMap_Cur //.
        }
        Check frag_mem_auth_mono q (restrPermMap Hlt).
        Check (getThreadR cnti).1 .
        iPoseProof (frag_mem_auth_mono q (restrPermMap Hlt)
          (@restrPermMap (getThreadR cnti).1 m Hthread) σ1 Hab
          with "Hfragi") as "Hfragi".
        iMod "Hsafei" as "Hsafei".
        iDestruct ("Hsafei" $! (restrPermMap Hthread) σ1
                    with "[$Hfragi $Hext]") as (Hlt0) "[Hhalt | [Hstep | Hext]]".
        iDestruct "Hhalt" as (? Hhalt') "?"; done.
        
        assert (Heq : restrPermMap Hlt0 = restrPermMap Hlt).
        { etransitivity; try apply restrPermMap_idem; apply restr_proof_irr. }
        (* HStep *)
        iMod "Hstep" as (???) "(%Hstep & S & Hsafei)".
        rewrite Heq in Hstep.
        (* Does we need getThreadR cnti = perm_of_rmap σ *)
        assert (Hmemstep : mem_step (restrPermMap Hlt) m').
        { eapply (CLC_corestep_mem _ _ (restrPermMap Hlt)); eauto. }
        iApply step_fupd_intro; try done.
        iNext.
        iDestruct "S" as "(Hfragi & Hext)".
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c')
                                    (getCurPerm m', (getThreadR cnti).2)) m' n ls qs
                      with "[%] [%] [%] [%] locks Hext [Hsafe Hsafei Hfragi]"); try done.
        * admit.
        * admit.
        * admit.
        * admit.
        * iApply "Hsafe".
          ** iIntros "!>" (k y (-> & ?)%lookup_seq Hneq) "Hy".
             iDestruct "Hy" as (q0 σ0 cnty Hltσ0) "((% & %Hqy) & Hsafe_y & Hfrag_y)".
             replace (0 + k) with k in * by lia.
             assert (Hneq' : i <> k) by lia.
             set (cnty' :=
                    @cntUpdate _ _ _ i (0 + k) tp
                      (Krun c')
                      (getCurPerm m', (getThreadR cnti).2)
                      cnti cnty).
             iExists q0, σ0, cnty'.
             assert (Hlt0' : permMapLt (perm_of_rmap σ0) (getThreadR cnty').1).
             { subst cnty'.
               erewrite gsoThreadRes; eauto. }
             pose proof ((no_race_thr _ Hinvariant) _ _ cnti cnty Hneq') as Hthread_disj2.
             assert (Hrmap_disj : permMapsDisjoint (perm_of_rmap σ1) (perm_of_rmap σ0)).
             { unfold permMapsDisjoint in *.
               intros b ofs.
               rewrite /permMapsDisjoint2 in Hthread_disj2.
               eapply perm_union_lower_2.
               - eapply ((proj1 Hthread_disj2) b ofs).
               - apply (Hlt1 b ofs).
               - apply (Hqy b ofs). }
             assert (Hdecay : decay (restrPermMap Hlt) m').
             { apply (@msem_decay CC_core (CLC_memsem ge) s (restrPermMap Hlt) c' m' Hstep). }
             assert (Hpres : permMapLt (perm_of_rmap σ0) (getMaxPerm m')).
             { eapply (permMapLt_decay_disjoint _ (restrPermMap Hlt)); eauto.
               + by rewrite restr_Max_eq.
               + unfold permMapsDisjoint in *.
                 intros b ofs.
                 rewrite getCurPerm_correct.
                 rewrite (restrPermMap_Cur Hlt b ofs).
                 apply (Hrmap_disj b ofs).
             }
             iExists Hpres.
             iSplit; auto.
             iSplitL "Hsafe_y".
             ++ iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
                iExists cnty'.
                rewrite gsoThreadCode; auto.
             ++ iApply (frag_mem_auth_corestep_other
                    q0 m m' (perm_of_rmap σ1)  σ0 Hlt Hltσ0 Hpres Hmemstep Hrmap_disj); auto.
          ** iDestruct "Hfragi" as "(% & Hauth)".
             assert (Hσcur : permMapLt (perm_of_rmap σ') (getCurPerm m')).
             { by apply coherent_perm_of_rmap. }
             (* assert (Hlt0 : permMapLt (perm_of_rmap σ') (getMaxPerm m')).
                   { etransitivity; eauto.
                     apply cur_lt_max. } *)
             iExists q, σ', _, _.
             repeat iSplit; auto.
             rewrite gssThreadRes; auto.
             iSplitR "Hauth".
             { iExists _; rewrite gssThreadCode; auto. }
             iFrame.
             iSplit; auto.
             iPureIntro.
             apply coherent_restrPermMap; auto.
        * iApply (step_fupdN_mono with "IH").
          iPureIntro; intros Hsafe.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe; last exact Hsafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          simpl in Hsafe.
          eapply step_dry; eauto.
          simpl.
            with (c := s)
                 (m1 := restrPermMap (proj1 (Hcompat i cnti)))
                 (c' := c')
                 (ev := _); eauto.
          
        
        
























        

        (* UP *)
        apply coherent_restrPermMap_of_coherent in Hcoh.
        destruct Hcoh as (Hlt2 & Hcoh).
        iMod "Hsafei" as "Hsafei".
        Print frag_mem_auth.
        Search coherent permMapLt.
        iDestruct ("Hsafei" $! (restrPermMap Hlt) σ1
                    with "[$Hfragi $Hext]") as (Hlt0) "[Hhalt | [Hstep | Hext]]".
        iDestruct "Hhalt" as (? Hhalt') "?"; done.
        2 : { iDestruct "Hext" as (???? Hext) "?". simpl in Hext. congruence. }
        assert (Hlt0 = Hlt2) by apply ProofIrrelevance.proof_irrelevance.
        subst Hlt0. 
        (* HStep *)
        iMod "Hstep" as (???) "(%Hstep & S & Hsafei)".
        (* Does we need getThreadR cnti = perm_of_rmap σ *)
        assert (Hrestr : restrPermMap Hlt2 = restrPermMap Hlt).
        { etransitivity; try apply restrPermMap_idem; apply restr_proof_irr. }
        assert (Hmemstep : mem_step (restrPermMap Hlt) m').
        { rewrite <- Hrestr.
          eapply (CLC_corestep_mem _ _ (restrPermMap Hlt2)); eauto. }
        iApply step_fupd_intro; try done.
        iNext.
        iDestruct "S" as "(Hfragi & Hext)".
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c')
                (getCurPerm m', (getThreadR cnti).2)) m' n ls qs
            with "[%] [%] [%] [%] locks Hext [Hsafe Hsafei Hfragi]"); try done.
        * intros j cntj.
          destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
          pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
        * eapply corestep_invariant_sub with (p := perm_of_rmap σ1) (m := m) (s := s); eauto.
          instantiate (1 := Hlt).
          by rewrite Hrestr in Hstep.
        * rewrite Hrestr in Hstep; eapply corestep_compatible_sub; eauto.
        * admit.
        * iApply "Hsafe".
          ** iIntros "!>" (k y (-> & ?)%lookup_seq Hneq) "Hy".
             iDestruct "Hy" as (q0 σ0 cnty Hltσ0) "((% & %Hqy) & Hsafe_y & Hfrag_y)".
             replace (0 + k) with k in * by lia.
             assert (Hneq' : i <> k) by lia.
             set (cnty' :=
                    @cntUpdate _ _ _ i (0 + k) tp
                      (Krun c')
                      (getCurPerm m', (getThreadR cnti).2)
                      cnti cnty).
             iExists q0, σ0, cnty'.
             assert (Hlt0' : permMapLt (perm_of_rmap σ0) (getThreadR cnty').1).
             { subst cnty'.
               erewrite gsoThreadRes; eauto. }
             pose proof ((no_race_thr _ Hinvariant) _ _ cnti cnty Hneq') as Hthread_disj2.
             assert (Hrmap_disj : permMapsDisjoint (perm_of_rmap σ1) (perm_of_rmap σ0)).
             { unfold permMapsDisjoint in *.
               intros b ofs.
               rewrite /permMapsDisjoint2 in Hthread_disj2.
               eapply perm_union_lower_2.
               - eapply ((proj1 Hthread_disj2) b ofs).
               - apply (Hlt1 b ofs).
               - apply (Hqy b ofs). }
             assert (Hdecay : decay (restrPermMap Hlt) m').
             { rewrite Hrestr in Hstep.
               apply (@msem_decay CC_core (CLC_memsem ge) s (restrPermMap Hlt) c' m' Hstep). }
             assert (Hpres : permMapLt (perm_of_rmap σ0) (getMaxPerm m')).
             { eapply (permMapLt_decay_disjoint _ (restrPermMap Hlt)); eauto.
               + by rewrite restr_Max_eq.
               + unfold permMapsDisjoint in *.
                 intros b ofs.
                 rewrite getCurPerm_correct.
                 rewrite (restrPermMap_Cur Hlt b ofs).
                 apply (Hrmap_disj b ofs).
             }
             iExists Hpres.
             iSplit; auto.
             iSplitL "Hsafe_y".
             ++ iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
                iExists cnty'.
                rewrite gsoThreadCode; auto.
             ++ iApply (frag_mem_auth_corestep_other
                    q0 m m' (perm_of_rmap σ1)  σ0 Hlt Hltσ0 Hpres Hmemstep Hrmap_disj); auto.
         ** iDestruct "Hfragi" as "(% & Hauth)".
            assert (Hσcur : permMapLt (perm_of_rmap σ') (getCurPerm m')).
            { by apply coherent_perm_of_rmap. }
            assert (Hlt0 : permMapLt (perm_of_rmap σ') (getMaxPerm m')).
            { etransitivity; eauto.
              apply cur_lt_max. }
            iExists q, σ', _, Hlt0.
            repeat iSplit; auto.
            rewrite gssThreadRes; auto.
            iSplitR "Hauth".
            { iExists _; rewrite gssThreadCode; auto. }
            iFrame.
            iSplit; auto.
            iPureIntro.
            apply coherent_restrPermMap; auto.
        * iApply (step_fupdN_mono with "IH").
          iPureIntro; intros Hsafe.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe; last exact Hsafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          eapply step_dry
            with (c := s)
                 (m1 := restrPermMap (proj1 (Hcompat i cnti)))
                 (c' := c')
                 (ev := _); eauto.
          (* Do we actually need p = (getThreadR cnti).1 ? *)
          Check (Hcompat i cnti).
          Print perm_of_rmap.
          Check frag_mem_auth.

       
            done.
            

            
            pose (cnti0 :=
                    cntUpdate
                      (Krun c')
                      (getCurPerm m', (getThreadR cnti).2)
                      cnti cnti).
            

            "(Hauth & %Hcoh')".

           (* UP *)
                iApply (frag_mem_auth_corestep_other
                          q0 m m' σ1 σ0 Hlt Hmemstep).

               Check frag_mem_auth_corestep_other.
                Check coherent_mem_step_other.

             
             iSplit.
             { iPureIntro.
               destruct Hqy as [Hq0 Hlt0].
               split; first exact Hq0. done. }
             iSplitL "Hsafe_y".
             ++ admit.
             ++ destruct Hqy as [_ Hσ_thread].
                assert (Hthread_max : permMapLt (getThreadR cnty).1 (getMaxPerm m)).
                { rewrite /HybridMachineSig.mem_compatible /= in Hcompat.
                  destruct Hcompat.
                  apply compat_th0. }
                assert ( Hlt2 : permMapLt (perm_of_rmap σ0) (getMaxPerm m)).
                { subst cnty'.
                  etransitivity; eauto.
                  erewrite gsoThreadRes; eauto. }
                iDestruct "Hfrag_y" as "(%Hcoh0 & Hauth0)".
                iApply (frag_mem_auth_corestep_other
                          q0 m m' σ1 σ0 Hlt Hmemstep).
                -- rewrite /other_lt_and_disjoint.
                   assert (permMapLt (perm_of_rmap σ0) (perm_of_rmap σ1)).
                   { admit. (* It's not true *) }
                   Search permMapsDisjoint.
                   pose proof ((no_race_thr _ Hinvariant) _ _ cnti cnty Hneq') as Hthread_disj2.
                   assert (Hrmap_disj : permMapsDisjoint (perm_of_rmap σ1) (perm_of_rmap σ0)).
                   { unfold permMapsDisjoint in *.
                     intros b ofs.
                     rewrite /permMapsDisjoint2 in Hthread_disj2.
                     eapply perm_union_lower_2.
                     - eapply ((proj1 Hthread_disj2) b ofs).
                     - apply (Hlt1 b ofs).
                     - apply (Hσ_thread b ofs).
                   }
                   repeat split; auto.
                   assert (Hdecay : decay (restrPermMap Hlt) m').
                   { apply (@msem_decay CC_core (CLC_memsem ge) s
                                   (restrPermMap Hlt) c' m' Hstep). }
                   assert (Hpres : permMapLt (perm_of_rmap σ0) (getMaxPerm m')).
                   { eapply permMapLt_decay_disjoint; eauto.
                     + rewrite restr_Max_eq. apply Hlt2.
                     + unfold permMapsDisjoint in *.
                       intros b ofs.
                       rewrite getCurPerm_correct.
                       rewrite (restrPermMap_Cur Hlt b ofs).
                       apply (Hrmap_disj b ofs).
                   }
                   assert (Hσ0_m' :
                            permMapLt (perm_of_rmap σ0) (getCurPerm m')).
                   { intros b ofs.
                     specialize (Hlt2 b ofs).
                     Search decay restrPermMap. 
                     specialize (Hthread_m' b ofs).

                     unfold Mem.perm_order'' in *.
                     unfold Mem.perm_order' in *.

                     destruct ((perm_of_rmap σ0) # b ofs) as [pσ |] eqn:Eσ;
                       destruct ((getThreadR cnty).1 # b ofs) as [pt |] eqn:Et;
                       destruct ((getCurPerm m') # b ofs) as [pm |] eqn:Em;
                       simpl in *; try contradiction; auto.

                     eapply Mem.perm_order_trans.
                     - exact Hthread_m'.
                     - exact Hσ0_thread.
                   }
                   Search "permMapLt" "trans".
                   eapply permMapLt_trans.
    - exact Hqy.2.
    - exact Hthread_m'.
    }

                   
                   done.
                -- rewrite /frag_mem_auth.
                  by iSplit; try iPureIntro.
            ** 
                iApply (frag_mem_auth_corestep_other q0 m m' σ1 σ0 Hlt with "[Hauth0]"); eauto.
                unfold other_lt_and_disjoint.
                repeat split; auto.
                rewrite /HybridMachineSig.mem_compatible /= in Hcompat.
                destruct Hcompat.
             

             
             iApply (frag_mem_auth_corestep_other
                          q0 m m' σ1 σ0
                          _
                         with "Hfrag_y").






        
        Check updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2).
        
        iApply step_fupd_intro; first done; iNext.
        set (tp' := updThread cnti (Krun c') (getThreadR cnti)).
        assert (Htp_wf' : threads_wellformed tp').
        { subst tp'.
          unfold threads_wellformed in *.
          intros j cntj'.
          destruct (Nat.eq_dec j 0) as [-> | Hneq]; try done.
          rewrite gsoThreadCode //; eapply Htp_wf.
        }

        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m' σ' _ with "[%] [%] [%] [%] locks S [Hsafe]"); try done.
        * admit.
        * admit.
        * admit.
        * iApply "Hsafe".
          ** iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & % & % & Hsafe)".
             iExists q.
             iSplit; auto.
             apply lookup_insert_Some in H1.
             destruct H1 as [? | ?]; try done.
             2 : {
               Search "∅" Some.

               admit. (* easy *) }
             destruct H1 as (? & ?).
             subst.
             rewrite lookup_insert.
             iSplit; auto.
             rewrite /thread_safe.
             iExists (cntUpdate _ _ cnti cnti0).
             
             rewrite gsoThreadCode // gsoThreadRes //.
             rewrite gsoThreadCode.
             iExists (cntUpdate _ _ cnti cnti0).
        
        
        Search jsafe_frag .
        
        
        iSpecialize ("IH" $! sch tr tp' m' n ls with
                      "[] [] [] [] locks S [Hsafe]"); try done.
        subst tp'.
        
        iSpecialize ("IH" $! sch tr tp' m' n ls with
                      "[] [] [] [] locks S [Hsafe Hsafei]").
        unfold thread_safe.
        iExists _.
        rewrite getThreadC_updThread_same.
        simpl.
        exact "Hsafei".

        
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m' (<[i := (g, getCurPerm m')]> perms) _ with "[%] [%] [%] [%] [%] locks S [Hsafe Hsafei]").
        iDestruct ("H" with "[$S]") as "S".








      
    
    Check big_sepL_lookup_acc _ (seq 0 (pos.n (OrdinalPool.num_threads tp))) i i .
    iDestruct (big_sepL_lookup_acc _ (seq 0 (pos.n (OrdinalPool.num_threads tp))) i i
                with "Hsafe") as "[Hsafe_i Hsafe_close]".
    { rewrite lookup_seq; try lia. }
    
    Check big_sepL2_lookup_acc.
    Check big_sepL2_lookup_acc _ (seq 0 (pos.n (OrdinalPool.num_threads tp))) [1%Qp] i i 1%Qp.
    iDestruct (big_sepL2_lookup_acc _ (seq 0 (pos.n (OrdinalPool.num_threads tp))) [1%Qp] i i 1%Qp
                with "Hsafe") as "[Hsafe_i Hsafe_close]".
    { rewrite lookup_seq; try lia. }
    { destruct i; simpl; try done.
      replicate (pos.n (OrdinalPool.num_threads tp)) 1%Qp.
    
    
    iDestruct (big_sepL2_lookup with "Hsafe") as "Hsafe"; auto.
    iPoseProof (big_sepL_lookup_acc_impl with "[$Hsafe]") as "Hsafe".
    apply lookup_seq; eauto.
    iDestruct "Hsafe" as "((% & %Hgi & % & Hsafei) & Hsafe)".
    destruct (getThreadC cnti) eqn: Hi.












    
    iAssert (threads_safe (*(getMaxPerm (`init_mem)) *) tp (fst <$> perms)) with "[Hsafe]" as "Hsafe".
    { rewrite /threads_safe /=.
      iSplit; last done.
      iExists γ0; iSplit; first done.
      unshelve iExists _; first done; simpl.
      iApply (jsafe_jsafe_perm with "Hsafe").
    }



    
    iPoseProof (thread_conc_state_interp O with "S") as "S".



    
    iDestruct "Hsafe" as "(Hjsafe & Hmatch)".

    
    Print state_interp.
    Print frag_state_interp.
    Print mem_auth.
    
    
    iMod (init_conc_VST_frag
            ()
            _ _ _
            Mem.empty
            (∅ : rmap)
            tt
            Hcoh_empty) as "H".
    iSpecialize ("H" $! Hinv).
    iDestruct "H" as (HG FS ES GM HL γm) "(Hstate & Hfunspec & Hext & Hγm)".
    set (HHfrag :=
           Build_VSTGS _ _
             ({| heapGS_invGS := Hinv;
                heapGS_gen_heapGS := HG;
                heapGS_funspecGS := FS |} : heapGS Σ)
             ES).
    destruct (spr HHfrag HL) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "[$Hstate $Hfunspec $Hext]") as "(S & Hsafe)".
    unfold state_interp in Hsafe.
    iMod (Hsafe with "H") as "(S & Hsafe)".





    

    
    iMod (@init_conc_VST _ _ VSTGpreS0 _ (`init_mem) tt) as "H".
    iDestruct ("H" $! Hinv) as (?? HE ????) "(H & ? & locks & ? & ?)".
    set (HC := ConcVSTGS _ _ (ConcHeapGS _ _ _ _) HE _).
    destruct (spr (thread_VSTGS γ0) _) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "H") as "(S & Hsafe)".
    iAssert (|={⊤}[∅]▷=>^n ⌜HybridMachineSig.HybridCoarseMachine.csafe
               (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
               (sch, [],
                 DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
                   q) (proj1_sig init_mem) n⌝) with "[S Hsafe locks]" as "Hdry".
    2: { iApply step_fupd_intro; first done.
         iNext; iApply (step_fupdN_mono with "Hdry").
         iPureIntro. intros.
         eexists. eexists. split; first done; split; first apply Hinit; done.
    }
    
    clear Hinit Hsafe.
    rewrite bi.and_elim_l.
    set (tp := initial_machine _ _).
    assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
    assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat
        by apply ThreadPoolWF.initial_mem_compatible.
    assert (threads_wellformed tp) as Htp_wf by done.
    iPoseProof (thread_conc_state_interp O with "S") as "S".
    set (perms := {[0 := (γ0, getCurPerm (`init_mem))]}).
    iAssert (threads_safe (*(getMaxPerm (`init_mem)) *) tp (fst <$> perms)) with "[Hsafe]" as "Hsafe".
    { rewrite /threads_safe /=.
      iSplit; last done.
      iExists γ0; iSplit; first done.
      unshelve iExists _; first done; simpl.
      iApply (jsafe_jsafe_perm with "Hsafe").
    }
    assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    assert (forall i r, snd <$> (perms !! i) = Some r <-> ∃ cnti : containsThread tp i, (getThreadR cnti).1 = r)
      as Hperms.
    { intros [|] ?; rewrite /perms /tp /= /OrdinalPool.containsThread /=.
      * rewrite lookup_insert /=.
        split; [by inversion 1; exists eq_refl | by intros (? & <-)].
      * rewrite lookup_insert_ne // lookup_empty.
        split; first done.
        intros (? & ?); done.
    }
    clearbody perms tp.
    set (ls := ∅) in Hlocks |- *.
    clearbody ls.
    clear dependent b x q.
    iLöb as "IH" forall (sch tr tp m perms n ls Htp_wf Hinvariant Hcompat Hlocks Hperms).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2: {
      Local Opaque lock_state.
      iApply step_fupd_intro; try done. iNext.
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros.
        iApply ("IH" with "[%] [%] [%] [%] [%]  locks S Hsafe"); done.
      }
      iApply (step_fupdN_mono with "H"); iPureIntro.
      intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
           with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
      eapply HybridMachineSig.schedfail; eauto.
      rewrite /containsThread /= /OrdinalPool.containsThread.
      intros ?.
      pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle;
           [lia | congruence].
    }
    rewrite {2}/threads_safe.
    iPoseProof (big_sepL_lookup_acc_impl with "[$Hsafe]") as "Hsafe".
    apply lookup_seq; eauto.
    iDestruct "Hsafe" as "((% & %Hgi & % & Hsafei) & Hsafe)".
    destruct (getThreadC cnti) eqn: Hi.
    - (* Krun *)
      destruct (cl_halted s) eqn: Hhalt; [|destruct (cl_at_external s) eqn: Hat_ext].
      + (* halted *)
        assert (HybridMachineSig.halted_thread cnti Int.zero) as Hhalt'.
        { econstructor; eauto. hnf; rewrite Hhalt //. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (threads_safe (*(getMaxPerm m)*) tp (fst <$> perms))
          with "[Hsafei Hsafe]" as "Hsafe".
        { iApply "Hsafe".
          * iIntros "!>" (????) "H"; iApply "H".
          * iFrame "%"; iExists cnti; rewrite Hi //. }
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros; iApply ("IH" with "[%] [%] [%] [%] [%] locks S Hsafe"); done.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro.
        intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.halted_step; eauto.
      + (* HybridMachineSig.suspend_step *)
        assert (HybridMachineSig.suspend_thread m cnti (updThreadC cnti (Kblocked s))) as Hsuspend.
        { eapply (HybridMachineSig.SuspendThread _ _ _ _ _ _ _ _ Hcompat); done. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, (updThreadC cnti (Kblocked s))) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros.
          iApply ("IH" with "[%] [%] [%] [%] [%] locks S [Hsafe Hsafei]"); try done.
          + intros j cntj.
            destruct (eq_dec j i).
            * subst; rewrite gssThreadCC Hat_ext //.
            * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
              rewrite -gsoThreadCC //; apply Htp_wf.
          + by apply ThreadPoolWF.updThreadC_invariant.
          + by apply StepLemmas.updThreadC_compatible.
          + iApply "Hsafe".
            * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & $ & % & Hsafe)".
              iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
            * iFrame "%"; iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
              by iApply "Hsafei".
        }
        iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.suspend_step; eauto.
      + (* corestep: HybridMachineSig.thread_step *)
        edestruct Hperms as [_ Hpermi].
        spec Hpermi; first by exists cnti.
        rewrite !lookup_fmap in Hgi Hpermi.
        destruct (perms !! (0 + i)) as [(?, p)|] eqn: Hpi; inv Hgi; inv Hpermi.
        iDestruct (conc_state_interp_lookup1 with "S") as "(% & S & H)"; first done.
        rewrite jsafe_perm_unfold /jsafe_perm_pre.
        iMod ("Hsafei" with "[%] S") as "[Hhalt | [Hstep | Hext]]".
        { apply mem_equiv.getCur_restr. (*
          split; [apply mem_equiv.getCur_restr | apply restr_Max_eq]. *) }
        { iDestruct "Hhalt" as (? Hhalt') "?"; done. }
        2: { iDestruct "Hext" as (??? Hext) "?". simpl in Hext; congruence. }
        (* HStep *)
        iMod "Hstep" as (?? Hstep) "(S & Hsafei)".
        assert (corestep (cl_core_sem ge) s (restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1) c' m') as Hstep'.
        { by erewrite restrPermMap_irr. }
        iApply step_fupd_intro; first done; iNext.
        apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (? & Hstep').
        assert (mem_compatible (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m') as Hcompat'
          by by eapply (CoreLanguageDry.corestep_compatible(Sem := Sem)).
        iDestruct ("H" with "[$S]") as "S".
        { iPureIntro; split; last done. split.
          * by eapply CLC_corestep_mem.
          * split.
            - intros ???? Hj.
              specialize (Hperms j); rewrite Hj /= in Hperms.
              edestruct Hperms as [(cntj & <-) _]; first done.
              inv Hcompat'.
              unshelve exploit compat_th0.
              2: by eapply cntUpdate.
              rewrite gsoThreadRes //.
              by intros (? & ?).
            - split.
              + intros j g0 p _ Hj.
                have Hj_snd : snd <$> perms !! j = Some p by rewrite Hj /=.
                have [cntj Hrj] := (proj1 (Hperms j p) Hj_snd).
                have Hj_lt : permMapLt (getThreadR cntj).1 (getMaxPerm m) :=
                  (ssrfun.pair_of_and (Hcompat j cntj)).1.
                by rewrite Hrj in Hj_lt.
              + inv Hinvariant.
                unfold permMapsDisjoint_at; intros.
                rewrite Hpi.
                destruct (perms !! j) as [(?,?)|] eqn: Hj; last done.
                specialize (Hperms j); rewrite Hj /= in Hperms.
                edestruct Hperms as [(cntj & <-) _]; first done.
                by apply no_race_thr0.
        }
        iAssert (lock_state γl m' ls) with "[locks]" as "locks". admit.
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m' (<[i := (g, getCurPerm m')]> perms) _ with "[%] [%] [%] [%] [%] locks S [Hsafe Hsafei]").
        * intros j cntj.
          destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
          pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
        * eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
          by eapply ev_step_ax1.
        * apply Hcompat'.
        * admit. (* intros ??; rewrite gsoThreadLPool.
          intros.
          rewrite /locks_coherent in Hlocks.
          pose proof Hlocks as Hlocks1.
          specialize (Hlocks l0).
          pose proof H1 as Hl0.
          assert (Hm: Mem_load_unchecked Mptr m l0.1 l0.2 =
                        Mem_load_unchecked Mptr (restrPermMap Hp) l0.1 l0.2) by done.
          rewrite Hm in Hlocks.
          apply Hlocks in Hl0.
          destruct Hl0 as (? & Hl1 & Hn).
          split; try apply Hl1; try done.
          split; intros.
          split; intros.
          ** eapply Hl1; try done.
             rewrite /Mem_unchecked in H2 |- *.
             rewrite <- H2.
             do 2 f_equal.
             eapply mem_step_preserves_lock_bytes; eauto.
             apply CLC_corestep_mem in Hstep; auto.
          ** apply Hl1 in H2.
             rewrite /Mem_unchecked in H2 |- *.
             rewrite <- H2.
             do 2 f_equal.
             symmetry.
             eapply mem_step_preserves_lock_bytes.
             apply CLC_corestep_mem in Hstep; auto.
             exact Hn.
          ** specialize (Hlocks1 l0).
             destruct (decide (i0 = i)); subst.
             ++ assert (HsameR : (getThreadR cnti0).1 = getCurPerm m').
                { by rewrite gssThreadRes. }
                assert (Hpcur : permMapLt (getCurPerm m') (getMaxPerm m')).
                { by rewrite <- HsameR. }
                replace (restrPermMap Hp0) with (restrPermMap Hpcur).
                2 : { eapply restrPermMap_irr'; auto. }
                rewrite restrPermMap_eq.
                rewrite /nonEmptyRangeCur in Hn |- *.
                eapply (mem_step_preserves_nonempty_range (restrPermMap Hp)).
                by apply CLC_corestep_mem in Hstep; auto. exact Hn.
             ++ assert (Hres0 : ∃ cntj : containsThread tp i0, getThreadR cnti0 = getThreadR cntj).
                { eexists. apply gsoThreadRes; done. }
                destruct Hres0 as [cntj Hres0].
                assert (Hpj : permMapLt (getThreadR cntj).1 (getMaxPerm m)) by apply Hcompat.
                specialize (Hlocks1 i0 cntj Hpj H0).
                destruct Hlocks1 as (_ & _ & Hne).
                assert (Hperm : (getThreadR cnti0).1 = (getThreadR cntj).1).
                { by rewrite Hres0. }
                pose proof Hp0 as Hp0'.
                rewrite Hperm in Hp0'.
                rewrite /nonEmptyRangeCur in Hne |- *.
                intros.
                specialize (Hne i1 H2).
                rewrite <- Hperm in Hp0'.
                assert (Heq_restr : restrPermMap Hp0 = restrPermMap Hp0').
                { apply restr_proof_irr. }
                rewrite restrPermMap_Cur_eq in Hne.
                rewrite restrPermMap_Cur_eq.
                by rewrite Hperm. *)
        * intros j r.
          destruct (decide (i = j)).
          { subst; rewrite lookup_insert; setoid_rewrite (gssThreadRes cnti); split.
            - inversion 1; by exists (OrdinalPool.cntUpdate _ _ cnti cnti).
            - by intros (? & <-). }
          { rewrite lookup_insert_ne // Hperms.
            setoid_rewrite (gsoThreadRes cnti); last done.
            split; intros (? & ?); eauto. }
        * iApply "Hsafe".
          ** iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & % & % & Hsafe)".
             rewrite lookup_fmap in H2.
             rewrite lookup_fmap lookup_insert_ne //; iExists _; iSplit; first done.
             iExists (cntUpdate _ _ cnti cnti0).
             rewrite gsoThreadCode // gsoThreadRes //.
          ** rewrite lookup_fmap lookup_insert /=; iExists _; iSplit; first done.
             iExists (cntUpdate _ _ cnti cnti).
             rewrite gssThreadCode gssThreadRes //.
        * iApply (step_fupdN_mono with "IH").
          iPureIntro; intros.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe; last done.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          by eapply step_dry.
    - (* Kblocked: HybridMachineSig.sync_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
      edestruct Hperms as [_ Hpermi].
      spec Hpermi; first by exists cnti.
      rewrite !lookup_fmap in Hgi Hpermi.
      destruct (perms !! (0 + i)) as [(?, p)|] eqn: Hpi; inv Hgi; inv Hpermi.
      iDestruct (conc_state_interp_lookup2 with "S") as "(% & S & H)"; first done.
      rewrite jsafe_perm_unfold /jsafe_perm_pre.
      iMod ("Hsafei" with "[%] S") as "[Hhalt | [Hstep | Hext]]".
      { apply mem_equiv.getCur_restr. }
      { iDestruct "Hhalt" as (? Hhalt') "?"; destruct s; done. }
      { iMod "Hstep" as (?? Hstep) "?".
        apply cl_corestep_not_at_external in Hstep; done.
      }
      (* cl_at_external s = Some (e, args) *)
      iDestruct "Hext" as (??? Hat_ext) "(S & Hpre & Hpost)".
      simpl in Hat_ext.
      iAssert (|={⊤}[∅]▷=> ∃ (tp' : t(ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev perms',
                ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
                 locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev /\
                  (∀ (i0 : nat) (r : access_map), snd <$> perms' !! i0 = Some r
                    ↔ ∃ cnti0 : OrdinalPool.containsThread tp' i0,
                      (OrdinalPool.getThreadR cnti0).1 = r)⌝ ∧
                  threads_safe (* (getMaxPerm m') *)
                    tp' (fst <$> (* <[i:=(g, getCurPerm m')]> *) perms') ∗
                    (conc_mem_auth m (delete i perms) -∗ conc_mem_auth m' (delete i perms')) ∗

                    (∃ (p : access_map) (Hlt : permMapLt p (getMaxPerm m')),
                     ⌜(perms' !! i = Some (g, p))⌝ ∧ 
                       thread_state_interp g (restrPermMap Hlt) (* z'  state_interp (restrPermMap Hlt) *) tt) ∗
                    lock_state γl m' ls  (* ∗ lock_set ls*) )
        with "[Hpost Hsafe locks Hpre S]" as "Hsafe".
      2 : {
        iMod "Hsafe".
        iIntros "!> !>".
        iMod "Hsafe" as (???? (? & ? & ? & ? & ? & ?)) "(Hsafe & SC & S1 & locks1)".
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros.
          iSpecialize ("SC" with "H"). 
          replace (0 + i) with i; auto.
          assert (snd <$> perms !! i = Some (OrdinalPool.getThreadR cnti).1).
          { by rewrite Hpi. }
          iDestruct "S1" as (??) "(% & S1)".
          assert (Hperms'i : snd <$> perms' !! i = Some p).
          { by rewrite H7. }
          destruct (proj1 (H5 i p) Hperms'i) as [cnti' Hcnti'].
          iDestruct (thread_state_interp_conc_state_interp_delete_insert_restr
                      with "[$S1 $SC]") as "SC".
          subst.
          (* iDestruct (lock_state_empty_mem_irrel m m' with "locks1") as "locks1". *)
          iApply ("IH" with "[%] [%] [%] [%] [%] locks1 SC"); try done.
          intros i0 r.
          replace (<[i := (g, (OrdinalPool.getThreadR cnti').1)]> perms') with perms'.
          - apply H5.
          - symmetry; by apply insert_id.
          - rewrite (insert_id perms' i (g, (OrdinalPool.getThreadR cnti').1)); auto.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro.
        intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe; simpl; last apply Hsafe.
        eapply HybridMachineSig.sync_step; eauto.
      }
      
      (* consider each of the concurrency functions *)
      clear Hwfi.
      destruct s as [|f ? k|]; try done; simpl in Hat_ext.
      destruct f as [|ext argsty retty cc]; try done.
      destruct (ef_inline ext); inv Hat_ext.
      destruct (CEspec_cases _ x) as [-> | [-> | [-> | [-> | ->]]]].
      + (* acquire *)
        iApply (acquire_safe with "Hsafe Hpost locks").
      + (* release *)
      + (* makelock *)
      + (* freelock *)
      + (* spawn *) *)
      admit.
    - (* Kresume: HybridMachineSig.resume_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi; destruct Hwfi as (? & ->).
      destruct s; try done.
      destruct f; try done.
      assert (HybridMachineSig.resume_thread m cnti (updThreadC cnti (Krun (Returnstate Vundef c)))) as Hresume.
      { unfold cl_at_external in *; destruct (ef_inline e) eqn: Hinline; try done.
        eapply (HybridMachineSig.ResumeThread _ _ _ _ _ _ _ _ _ Hcompat); try done; simpl; by rewrite ?Hinline. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ (updThreadC cnti (Krun (Returnstate Vundef c))) with "[%] [%] [%] [%] [%] [$] [S] [Hsafei Hsafe]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCC //.
        * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
          rewrite -gsoThreadCC //; apply Htp_wf.
      + by apply ThreadPoolWF.updThreadC_invariant.
      + by apply StepLemmas.updThreadC_compatible.
      + rewrite /locks_coherent in Hlocks |- *.
        intros. 
        rewrite gsoThreadCLPool.
        destruct (eq_nat_dec i i0) as [<- | Hneq].
        * assert (HsameR : (getThreadR cnti).1 = (getThreadR cnti0).1).
          { erewrite <- gThreadCR; eauto. }
          pose proof Hp as Hp'.
          rewrite <- HsameR in Hp'.
          specialize (Hlocks l1 i cnti Hp' H1).
          destruct Hlocks as (? & ? & ?).
          replace (restrPermMap Hp) with (restrPermMap Hp').
          2 : { eapply restr_proof_irr'; done. }
          split; try done.
        * (* Up *)
          by apply Hlocks.
      + intros.
        instantiate (1 := perms).
        split.
        ++ intros.
           destruct (eq_dec i0 i) as [-> | Hneq].
           * apply (proj1 (Hperms i r) H1).
           * apply (proj1 (Hperms i0 r) H1).
       ++ intros.
          set tp' := OrdinalPool.updThreadC cnti (Krun (Returnstate Vundef c)).
          destruct (eq_dec i0 i) as [-> | Hneq].
           * apply (proj2 (Hperms i r)).
             case: H1 => cntj Hcntj.
             exists cnti.
             by have ->: cnti = cntj by apply proof_irrelevance.
           * apply (proj2 (Hperms i0 r)).
             case: H1 => cntj Hcntj.
             have cnti0 : OrdinalPool.containsThread tp i0 by auto.
             exists cnti0.
             by have ->: cnti0 = cntj by apply proof_irrelevance.
      + done.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & % & Hsafe)".
          iExists g0.
          iSplit; auto.
          iDestruct "Hsafe" as (cntk) "Hthr".
          rewrite /thread_safe.
          erewrite gsoThreadCC; eauto.
        * iExists g.
          iSplit; auto.
          rewrite /thread_safe.
          assert (cnti' : containsThread (updThreadC cnti (Krun (Returnstate Vundef c))) i); try done.
          iExists cnti'.
          rewrite gssThreadCC.
          have -> : (getThreadR cnti').1 = (getThreadR cnti).1.
          { rewrite /getThreadR /=.
            have <- : fintype.Ordinal cnti = fintype.Ordinal cnti'.
            { f_equal; apply proof_irrelevance. }
            reflexivity.
          }
          by iApply ("Hsafei" $! (Returnstate Vundef c)).
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        eapply HybridMachineSig.resume_step; eauto. 
    - (* Kinit: HybridMachineSig.start_step *)
      iDestruct "Hsafei" as (? Hinit) "Hsafei".
      set (m' := restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1).
      set (tp' := updThread cnti (Krun q_new) (HybridMachineSig.add_block Hcompat cnti m')).
      assert (HybridMachineSig.start_thread m cnti tp' m').
      { econstructor; done. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ tp' m' with "[%] [%] [%] [%] [%] [$] [S] [Hsafei Hsafe]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCode //.
        * pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
      + by eapply (CoreLanguageDry.initial_core_invariant(Sem := Sem)).
      + eapply InternalSteps.start_compatible; try done.
      + (* Up: locks_coherent *)
        rewrite /locks_coherent in Hlocks |- *.
        intros.
        assert (Hlockeq : lockRes tp' l0 = lockRes tp l0).
        { by rewrite /tp' gsoThreadLPool. }
        assert (Hm : Mem_unchecked Mptr m' l0.1 l0.2 = Mem_unchecked Mptr m l0.1 l0.2) by done.
        destruct (eq_nat_dec i i0) as [<- | Hneq].
        * specialize (Hlocks l0 i cnti (ssrfun.pair_of_and (Hcompat i cnti)).1 H1).
          destruct Hlocks as (Hn & Hmem & Hnone).
          split; try by rewrite Hlockeq.
          split.
          ** split.
             intros.
             apply Hmem. by rewrite <- Hm.
             intros.
             apply Hmem. by rewrite Hlockeq in H2.
          ** rewrite /nonEmptyRangeCur in Hnone |- *.
             intros.
             specialize (Hnone i0 H2).
             rewrite restrPermMap_Cur_eq.
             rewrite restrPermMap_Cur_eq in Hnone.
             assert (Hget :
                      getThreadR cnti0 = HybridMachineSig.add_block Hcompat cnti m').
             { eapply gssThreadRes. }
             rewrite Hget.
             unfold HybridMachineSig.add_block.
             simpl.
             rewrite /m'.
             simpl.
             pose proof (mem_equiv.getCur_restr ((getThreadR cnti).1) m
                           (ssrfun.pair_of_and (Hcompat i cnti)).1) as Hcur.
             unfold mem_equiv.access_map_equiv in Hcur.
             by rewrite (Hcur (l0.1)).
        * assert (cnti0_old : containsThread tp i0).
          { subst tp'; eapply cntUpdate'; eauto. }
          assert (Hr_eq : (getThreadR cnti0).1 = (getThreadR cnti0_old).1).
          { subst tp'; rewrite gsoThreadRes; auto. }
          assert (Hp0 : permMapLt (getThreadR cnti0_old).1 (getMaxPerm m)).
          { replace ((getThreadR cnti0_old).1) with ((getThreadR cnti0).1). 
            subst m'.
            by rewrite restr_Max_eq in Hp.
          }
          specialize (Hlocks l0 i0 cnti0_old Hp0 H1).
          destruct Hlocks as (Hn & Hmem & Hnone).
          split; try by rewrite Hlockeq.
          split.
          ** split; rewrite Hlockeq.
             intros.
             apply Hmem. by rewrite <- Hm.
             intros.
             by apply Hmem.
          ** rewrite /nonEmptyRangeCur in Hnone |- *.
             intros.
             specialize (Hnone i1 H2).
             rewrite restrPermMap_Cur_eq in Hnone.
             rewrite restrPermMap_Cur_eq.
             by rewrite Hr_eq.
      + intros.
        instantiate (1 := <[i := (g, getCurPerm m')]> perms).
        split.
        ++ intros.
           destruct (eq_dec i0 i) as [-> | Hneq].
           * rewrite lookup_insert /= in H1.
             inv H1.
             exists (OrdinalPool.cntUpdate (Sem := Sem) (Krun q_new)
                      (HybridMachineSig.add_block Hcompat cnti m') cnti cnti).
             rewrite /tp' /m' OrdinalPool.gssThreadRes //.
           * rewrite lookup_insert_ne // in H1.
             have [cntj Hcntj] :
               exists cntj : OrdinalPool.containsThread tp i0, (OrdinalPool.getThreadR cntj).1 = r.
             { exact (proj1 (Hperms i0 r) H1). }
             exists (OrdinalPool.cntUpdate (Sem := Sem) (Krun q_new)
                      (HybridMachineSig.add_block Hcompat cnti m') cnti cntj).
             by rewrite OrdinalPool.gsoThreadRes.
        ++ intros.
           destruct (eq_dec i0 i) as [-> | Hneq].
           * rewrite lookup_insert /=.
             f_equal.
             rewrite /tp' in H1.
             destruct H1 as (cntj & <-).
             by rewrite OrdinalPool.gssThreadRes.
           * rewrite lookup_insert_ne //.
             destruct H1 as (cntj & Hcntj).
             set (cnt0 := OrdinalPool.cntUpdate' (Sem := Sem) (i := 0 + i) (j := i0) (tp := tp)
                            (c := Krun q_new)
                            (p := HybridMachineSig.add_block Hcompat cnti m') (cnti := cnti) cntj).
             apply (proj2 (Hperms i0 r)).
             exists cnt0.
             simpl.
             have Hres : OrdinalPool.getThreadR cntj = OrdinalPool.getThreadR cnt0.
             { eapply OrdinalPool.gsoThreadRes. lia. }
             have Hr0 : (OrdinalPool.getThreadR cnt0).1 = r; auto.
             { apply (f_equal fst) in Hres; by rewrite <- Hres. }
      + iDestruct "S" as "(S & ?)".
        iFrame.
        rewrite /m'.
        change (0 + i) with i in *.
        have Hsnd : snd <$> perms !! i = Some (getThreadR cnti).1.
        { apply (Hperms i (getThreadR cnti).1); by eexists. }
        have Hlookup : perms !! i = Some (g, (getThreadR cnti).1).
        { destruct (perms !! i) as [[g' r']|] eqn:Hp; simpl in *; try discriminate.
          f_equal.
          have Hg' : g' = g.
          { move: Hgi.
            rewrite lookup_fmap Hp /=.
            intros; by inv Hgi.
          }
          have Hr' : r' = (OrdinalPool.getThreadR cnti).1.
          { exact (Some_inj _ _ Hsnd). }
          by subst.
        }
        iDestruct (conc_mem_auth_lookup1 with "[$S]") as "H"; eauto.
        iDestruct "H" as (Hp) "[Hth Hk]".
        iApply ("Hk" $! (restrPermMap Hp)).
        iFrame.
        iPureIntro.
        repeat split.
        * apply semantics_lemmas.mem_step_refl.
        * intros ???? Hj.
          rewrite restr_Max_eq.
          specialize (Hperms j); rewrite Hj /= in Hperms.
          edestruct Hperms as [(cntj & <-) _]; first done.
          by destruct (Hcompat j cntj).
        * intros j g0 p _ Hj.
          have Hj_snd : snd <$> perms !! j = Some p by rewrite Hj /=.
          have [cntj Hcntj] := (proj1 (Hperms j p) Hj_snd).
          have Hj_lt : permMapLt (getThreadR cntj).1 (getMaxPerm m) :=
                  (ssrfun.pair_of_and (Hcompat j cntj)).1.
          by subst.
        * inv Hinvariant.
          unfold permMapsDisjoint_at; intros.
          rewrite Hlookup.
          destruct (perms !! j) as [(?,?)|] eqn: Hj; last done.
          specialize (Hperms j); rewrite Hj /= in Hperms.
          edestruct Hperms as [(cntj & <-) _]; first done; by apply no_race_thr0.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists g0.
          iDestruct "Hsafe" as "(% & Hthr)".
          change (0 + k) with k in *.
          iSplit; auto.
          iPureIntro.
          rewrite lookup_fmap lookup_insert_ne //.
          by rewrite lookup_fmap in H3.
          iDestruct "Hthr" as (cntk) "Hthr".
          iExists (OrdinalPool.cntUpdate (Sem:=Sem) (Krun q_new)
                   (HybridMachineSig.add_block Hcompat cnti m') cnti cntk).
          rewrite gsoThreadCode // gsoThreadRes //.
        * rewrite lookup_fmap lookup_insert /= /thread_safe.
          iExists g.
          iSplit; auto.
          iExists (OrdinalPool.cntUpdate (Sem:=Sem) (Krun q_new)
                     (HybridMachineSig.add_block Hcompat cnti m') cnti cnti).
          rewrite gssThreadCode // gssThreadRes // /m'.
          iApply (jsafe_perm_equiv with "Hsafei").
          set Hlt:=proj1 (Hcompat i cnti).
          eapply Equivalence_Symmetric; eauto.
          eapply mem_equiv.getCur_restr.
          (* Unshelve
             9 : { exact mem_equiv.access_map_equiv_Equivalence. *) 
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl;
          rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m').
        eapply HybridMachineSig.start_step; eauto.
  Admitted.

End Safety.
