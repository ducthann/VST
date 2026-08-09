(*
   A parallel initial-world construction that exposes the concrete resource map.
   This file is intended to live beside:
     VST/concurrency/juicy/semax_to_dry_machine.v

   It deliberately leaves [VST.veric.initial_world] and
   [VST.veric.Clight_initial_world] unchanged.  Consequently, the definitions
   whose ordinary [Nonempty] case changes from [Share.bot] to [Share.Lsh] are
   reproduced here under new names.

   After importing this file from [semax_to_dry_machine.v], remove the local
   duplicate definitions of [perm_row_of_rmap], [perm_of_rmap],
   [perm_of_rmap_lookup], and [frag_mem_auth] from that file.
*)

From iris.algebra Require Import agree.

Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".

From iris_ora.algebra Require Import agree.

Require Import VST.zlist.sublist.
Require Import VST.shared.shared.
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.shared.resource_map.
Require Import VST.veric.seplog.
Require Import VST.veric.shares.
Require Import VST.shared.dshare.
Require Import VST.veric.mpred.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.initial_world.
Require Import VST.veric.Clight_initial_world.
Require Import VST.veric.initialize.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.juicy.semax_conc_pred.

Set Bullet Behavior "Strict Subproofs".

Import Values.
Open Scope maps.


Section initial_world_with_rmap_lemmas.

  Context {Σ : gFunctors} `{!heapGS Σ}.

  (** ** Extracting the dry permission map *)

  Definition perm_row_of_rmap (σ : rmap) (b : positive) : Z -> option permission :=
    fun ofs => perm_of_res (σ @ (b, ofs)).

  Definition perm_of_rmap (σ : rmap) : access_map :=
    fold_right (fun '(loc, _) p =>
                  PMap.set loc.1 (perm_row_of_rmap σ loc.1) p) (PMap.init (fun _ => None))
    (map_to_list σ).

  Lemma perm_row_of_rmap_lookup :
    forall σ b ofs, perm_row_of_rmap σ b ofs = perm_of_res (σ @ (b, ofs)).
  Proof. reflexivity. Qed.

  Lemma perm_of_rmap_fold_lookup :
    forall σ (l : list (address * sharedR (leibnizO resource))) (b : block) (ofs : Z),
      (forall (ofs0 : Z) (r : sharedR (leibnizO resource)),
          (σ !! (b, ofs0) = Some r)%stdpp -> (((b, ofs0), r) ∈ l)%stdpp) ->
      PMap.get b (fold_right (fun '(loc, _) (p : PMap.t (Z -> option permission)) =>
                                PMap.set loc.1 (perm_row_of_rmap σ loc.1) p) (PMap.init (fun _ => None)) l) ofs = perm_of_res (σ @ (b, ofs)).
  Proof.
    intros σ l.
    induction l as [| [[b0 ofs0] r0] l IH]; intros b ofs Hin; simpl.
    - rewrite PMap.gi.
      assert ((σ !! (b, ofs))%stdpp  = None) as Hnone.
      { destruct (σ !! (b, ofs))%stdpp  as [r |] eqn:Hlook; auto.
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

  Lemma perm_of_rmap_lookup :
    forall σ b ofs, PMap.get b (perm_of_rmap σ) ofs = perm_of_res (σ @ (b, ofs)).
  Proof.
    intros σ b ofs.
    rewrite /perm_of_rmap.
    apply perm_of_rmap_fold_lookup.
    intros; rewrite elem_of_map_to_list //.
  Qed.

  Definition block_bounds_cover (m : Mem.mem') (block_bounds : block -> Z * nat) : Prop :=
    forall b ofs p, access_at m (b, ofs) Cur = Some p ->
               let '(lo, n) := block_bounds b in (lo <= ofs <= lo + Z.of_nat n)%Z.
  
  Lemma perm_of_rmap_of_mem_with_rmap_exact :
    forall (m : Mem.mem') (block_bounds : block -> Z * nat) {F : Type}
      (ge : Genv.t (fundef F) type) (G : funspecs),
      block_bounds_cover m block_bounds ->
      mem_equiv.access_map_equiv
        (perm_of_rmap (rmap_of_mem (Σ := Σ) m block_bounds ge G)) (getCurPerm m).
  Proof.
    intros m block_bounds F ge G Hcover.
    rewrite /access_map_equiv.
    intros b; apply functional_extensionality; intro ofs.
    rewrite perm_of_rmap_lookup.
    rewrite /getCurPerm PMap.gmap.
    change (perm_of_res (resource_at (rmap_of_mem m block_bounds ge G) (b, ofs))
            = access_at m (b, ofs) Cur).
    rewrite /resource_at.
    pose proof (rmap_of_mem_valid m block_bounds ge G) as Hvalid.
    specialize (Hvalid (b, ofs)).
    erewrite resR_to_resource_eq;
      [|exact Hvalid|apply lookup_of_mem].
    destruct (block_bounds b) as [lo n] eqn:Hbounds.
    simpl.
    rewrite Hbounds /=.
    destruct (access_at m (b, ofs) Cur) as [p |] eqn:Haccess.
    { pose proof (Hcover b ofs p Haccess) as Hrange.
      rewrite Hbounds /= in Hrange.
      destruct Hrange as (Hlo & Hhi).
      assert (Hperm : Mem.perm m b ofs Cur p).
      { unfold Mem.perm, access_at in *; rewrite Haccess; apply perm_refl. }
      apply Mem.perm_valid_block in Hperm.
      destruct (plt b (nextblock m)) as [Hb | Hb]; try contradiction.
      destruct (zle lo ofs) as [Hlo' | Hlo']; try lia.
      destruct (zle ofs (lo + Z.of_nat n)) as [Hhi' | Hhi']; try lia.
      rewrite /res_of_loc Haccess.
      destruct p.
      { rewrite /= elem_of_to_agree perm_of_freeable //. }
      { rewrite /= elem_of_to_agree perm_of_Ews //. }
      { rewrite /= elem_of_to_agree perm_of_Ers //. }
      { destruct (funspec_of_loc ge G (b, ofs)) as [f |] eqn:Hfun.
        { rewrite /= elem_of_to_agree //. }
        { rewrite /=; destruct (eq_dec Share.Lsh Share.bot) as [Heq | Hneq]; try done; subst.
          { exfalso; apply Lsh_bot_neq; done. }
          { rewrite if_false; auto. }
        }
      }
    }
    { destruct (plt b (nextblock m)); simpl; try reflexivity;
        destruct (zle lo ofs); simpl; try reflexivity;
        destruct (zle ofs (lo + Z.of_nat n)); simpl; try reflexivity;
        try rewrite /res_of_loc Haccess /=; rewrite eq_dec_refl //. }
  Qed.

  Lemma perm_of_rmap_of_mem_with_rmap_equiv :
    forall (m : Mem.mem') (block_bounds : block -> Z * nat) {F : Type}
      (ge : Genv.t (fundef F) type) (G : funspecs),
    block_bounds_cover m block_bounds ->
    mem_equiv.access_map_equiv
      (perm_of_rmap (rmap_of_mem (Σ := Σ) m block_bounds ge G)) (getCurPerm m).
  Proof. intros; apply perm_of_rmap_of_mem_with_rmap_exact; auto. Qed.

  (** ** Exposing the selected authoritative resource map *)
  
  Definition frag_mem_auth (q : Qp) (m : mem) (σ : rmap) : iProp Σ :=
    ⌜coherent m σ /\ mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m)⌝ ∧
      resource_map.resource_map_auth
        (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
        (gen_heap_name heapGS_gen_heapGS) q σ.
  
  Lemma frag_mem_auth_set (m : mem) (σ : rmap) (Hvalid : ✓ σ)
    (Hnext : forall loc, (loc.1 >= Mem.nextblock m)%positive -> (σ !! loc = None)%stdpp)
    (Hcoh : forall loc : address, coherent_loc m loc (resource_at σ loc))
    (Hperm : mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m)):
    mem_auth Mem.empty
      ⊢ |==>
      frag_mem_auth 1 m σ ∗
      ([∗ map] l ↦ x ∈ σ,
        match x with
        | shared.YES dq _ v =>
            l ↦{dq} (proj1_sig (elem_of_agree v))
        | shared.NO (Share sh) _ => mapsto_no l sh
        | _ => False
        end).
  Proof.
    iIntros "(%σ0 & %Hempty & Hauth)".
    apply coherent_empty in Hempty as ->.
    iMod (gen_heap_set with "Hauth") as "(Hauth & Hfrags)"; first done.
    iModIntro.
    iFrame "Hfrags".
    rewrite /frag_mem_auth.
    iSplit; auto.
    iPureIntro.
    split; auto.
    intros loc. split; auto.
  Qed.

  Lemma initialize_mem_with_rmap :
    forall (m : Mem.mem') (block_bounds : block -> Z * nat) {F : Type} (ge : Genv.t (fundef F) type)
      (G : funspecs) (Hcover : block_bounds_cover m block_bounds)
      (Hfun_bounds : forall b f, funspec_of_loc ge G (b, 0) = Some f -> block_bounds b = (0, 0%nat))
      (Hm : forall b, (b < nextblock m)%positive ->
                 match funspec_of_loc ge G (b, 0) with
                 | Some _ => access_at m (b, 0) Cur = Some Nonempty
                 | None => True
                 end),
      mem_auth Mem.empty ∗ funspec_auth ∅
        ⊢ |==>
        (∃ σ : rmap,
            frag_mem_auth 1 m σ ∗
              ⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m)⌝) ∗
        funspec_auth (init_funspecs m ge G) ∗ inflate_initial_mem m block_bounds ge G.
  Proof.
    intros.
    pose proof (rmap_of_mem_valid m block_bounds ge G) as Hvalid.
    pose proof (perm_of_rmap_of_mem_with_rmap_exact m block_bounds ge G Hcover) as Hperm.
    rewrite frag_mem_auth_set //.
    iIntros "(>(Hm & Hr) & Hf)".
    iCombine "Hf Hr" as "Hr"; iMod (rmap_inflate_equiv with "Hr") as "$"; try done.
    { iExists (rmap_of_mem m block_bounds ge G).
      iFrame. iPureIntro; auto. }
    { apply rmap_of_mem_nextblock. }
    { intros loc; apply rmap_of_mem_coherent.
      - intros b lo n ofs Hbb Hacc_ne.
        destruct (access_at m (b, ofs) Cur) eqn:Hacc.
        + specialize (Hcover b ofs p Hacc).
          rewrite Hbb in Hcover.
          exact Hcover.
        + exfalso.
          by apply Hacc_ne.
      - apply rmap_of_mem_valid.
    }
  Qed.

  (** ** Recovering [initial_core] from the parallel inflated memory *)

  (** ** Clight initial memories satisfy the coverage condition *)

  Notation initial_core_clight m := (initial_world.initial_core m (F := Clight.function)).

  Lemma initialize_mem_with_rmap' :
    forall (prog : Clight.program) G m (Hnorepet : list_norepet (prog_defs_names prog))
      (Hmatch : match_fdecs (prog_funct prog) G) (Hm : Genv.init_mem prog = Some m),
      mem_auth Mem.empty ∗ funspec_auth ∅
        ⊢ |==>
        (∃ σ : rmap,
            frag_mem_auth 1 m σ ∗ ⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m)⌝) ∗
        inflate_initial_mem m (block_bounds prog) (Genv.globalenv prog) G ∗
        initial_core_clight m (Genv.globalenv prog) G ∗
        matchfunspecs (Clight.globalenv prog) G.
  Proof.
    intros.
    assert (HnorepetG : list_norepet (map fst G)).
    { rewrite -match_fdecs_norepet //.
      apply prog_funct_norepet; auto.
    }
    assert (Hfun_access : forall b, (b < nextblock m)%positive ->
                               match funspec_of_loc (Genv.globalenv prog) G (b, 0) with
                               | Some _ =>
                                   access_at m (b, 0) Cur = Some Nonempty
                               | None => True
                               end).
    {
      intros ? Hb.
      eapply init_mem_all in Hb as (id & g & Hin & Hb); eauto.
      pose proof
        (prog_defmap_norepet _ _ _ Hnorepet Hin)
        as Hdef.
      apply Genv.find_def_symbol in Hdef
          as (b' & Hb' & Hdef).
      assert (b' = b) as ->.
      { rewrite Hb' in Hb; inv Hb; done. }
      apply Genv.init_mem_characterization_gen in Hm.
      specialize (Hm b _ Hdef).
      rewrite /funspec_of_loc /=.
      erewrite Genv.find_invert_symbol by done.
      destruct g.
      - apply In_prog_funct in Hin.
        assert (In id (map fst (prog_funct prog))) as Hin'.
        { rewrite in_map_iff; eexists (_, _); eauto. }
        rewrite match_ids // in_map_iff in Hin'.
        destruct Hin' as ((?, ?) & ? & ?); simpl in *; subst.
        erewrite find_id_i by done.
        destruct Hm as (Hperm & Hmax).
        apply perm_mem_access in Hperm
            as (? & Hperm & Haccess).
        destruct (Hmax _ _ _ (access_perm _ _ _ _ _ Haccess)); subst; done.
      - destruct (find_id id G) eqn:Hfind; last done.
        eapply match_fdecs_exists_Gfun in Hfind as (? & Hin' & ?); last done.
        eapply list_norepet_In_In in Hin; eauto; done.
    }
    assert
      (Hfun_bounds : forall b f,
          funspec_of_loc (Genv.globalenv prog) G (b, 0) = Some f -> block_bounds prog b = (0, 0%nat)).
    {
      rewrite /funspec_of_loc /=.
      intros ?? Hfind.
      destruct (Genv.invert_symbol _ _) eqn:Hb; try done.
      apply Genv.invert_find_symbol in Hb.
      apply find_symbol_globalenv in Hb
          as (? & g' & Hnth); last done.
      erewrite block_bounds_nth by done.
      apply nth_error_In in Hnth.
      eapply match_fdecs_exists_Gfun in Hfind
          as (? & Hin & ?); last done.
      eapply list_norepet_In_In in Hnth; eauto; subst; done.
    }
    assert
      (Hzero_bounds :
        forall b, (b < nextblock m)%positive ->
             (block_bounds prog b).1 <= 0 <= (block_bounds prog b).1 + Z.of_nat (block_bounds prog b).2).
    { intros ? Hb.
      eapply init_mem_all in Hb as (id & g & Hin & Hb); eauto.
      apply find_symbol_globalenv in Hb
          as (? & g' & Hnth); last done.
      erewrite block_bounds_nth by done.
      destruct g'; try done; simpl; lia.
    }
    pose proof (block_bounds_cover_init_mem prog m Hnorepet Hm) as Hcover.
    iIntros "(Hmem & Hf)".
    iMod (initialize_mem_with_rmap m (block_bounds prog) (Genv.globalenv prog)
            G Hcover Hfun_bounds Hfun_access with "[$Hmem $Hf]") as "(Hσ & Hf & Hinflate)".
    iPoseProof (initial_mem_initial_core m (block_bounds prog) (Genv.globalenv prog)
                  G Hfun_access Hzero_bounds with "Hinflate") as "(Hinflate & Hcore)".
    iPoseProof (init_funspecs_matchfunspecs with "Hf") as "Hmatchfunspecs".
    iModIntro.
    iFrame.
  Qed.

End initial_world_with_rmap_lemmas.

Section concurrent_opreations.
  
  Definition join_perm (p q : option permission) : option permission :=
    match p, q with
    | None, _ => q
    | _, None => p

    | Some Nonempty, Some Nonempty => Some Nonempty
    | Some Nonempty, Some Readable => Some Readable
    | Some Readable, Some Nonempty => Some Readable

    | Some Nonempty, Some Writable => Some Writable
    | Some Writable, Some Nonempty => Some Writable

    | Some Readable, Some Readable => Some Readable
    | Some Readable, Some Writable => Some Writable
    | Some Writable, Some Readable => Some Writable

    | _, _ => None
    end.

  Definition acquire_delta (p q maxp : access_map) : delta_map :=
    PTree.map
      (fun b f ofs =>
         match f ofs with
         | Some _ => Some (join_perm ((p !!! b) ofs) ((q !!! b) ofs))
         | None => None (* NOT create permissions outside the memory’s maximum permissions.*)
         end
      ) maxp.2.

  Lemma join_perm_correct :
    forall p q, (exists r, permjoin_def.permjoin p q r) -> permjoin_def.permjoin p q (join_perm p q).
  Proof.
    intros p q H.
    destruct p as [[]|], q as [[]|]; simpl in *;
      try constructor;
      try solve [destruct H as [r Hr]; inversion Hr].
  Qed.

  Lemma perm_union_permjoin :
    forall p q r, perm_union p q = Some r -> permjoin_def.permjoin p q r.
  Proof.
    intros p q r H.
    destruct p as [p |]; destruct q as [q |]; destruct r as [r |];
      simpl in H; try discriminate; inversion H; subst; try done; try constructor;
      destruct p, q; try done; inv H; constructor.
  Qed.

  Lemma acquire_delta_permMapJoin_new :
    forall p q maxp,
      (forall b ofs, (maxp.2 !! b)%maps = None -> (p !!! b) ofs = None) ->
      permMapLt p maxp ->
      permMapsDisjoint p q ->
      permMapJoin p q (computeMap q (acquire_delta p q maxp)).
  Proof.
    intros p q maxp Houtside Hlt Hdisj.
    unfold permMapJoin.
    intros b ofs.
    unfold acquire_delta, computeMap.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax |] eqn:Hmaxb.
    - destruct (fmax ofs) as [mx |] eqn:Hmaxofs.
      + (* maxp has permission here, so acquire_delta updates to join_perm *)
        rewrite Hmaxb /=.
        destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl.
        * rewrite Hmaxofs /=.
          (* Hqb : (q.2 !! b)%maps = Some fq
             q permission comes from block-specific function fq *)
          apply join_perm_correct.
          rewrite /permMapsDisjoint in Hdisj.
          specialize (Hdisj b ofs).
          destruct Hdisj as (pu & Hdisj).
          exists pu.
          rewrite /PMap.get in Hdisj.
          rewrite Hqb in Hdisj.
          by apply perm_union_permjoin.
        * rewrite Hmaxofs.
          (* None case: q permission comes from default function q.1. *)
          apply join_perm_correct.
          specialize (Hdisj b ofs).
          destruct Hdisj as (pu & Hdisj).
          exists pu.
          rewrite /PMap.get in Hdisj.
          rewrite Hqb in Hdisj.
          by apply perm_union_permjoin.
      + (* maxp has no permission at this offset, so no update *)
        rewrite Hmaxb /=.
        assert (Hpnone : (p !!! b) ofs = None).
        { specialize (Hlt b ofs).
          unfold PMap.get in Hlt.
          rewrite Hmaxb Hmaxofs in Hlt.
          destruct ((p !!! b) ofs) eqn: E; auto.
          rewrite /PMap.get in E.
          rewrite E in Hlt.
          easy.
        }
        destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl.
        * rewrite Hmaxofs.
          rewrite /PMap.get in Hpnone.
          rewrite Hpnone.
          constructor.
        * rewrite Hmaxofs.
          rewrite /PMap.get in Hpnone.
          rewrite Hpnone. constructor.
    - (* maxp has no block b, so no update *)
      rewrite Hmaxb /=.
      assert (Hpnone : (p !!! b) ofs = None).
      { by apply Houtside. }
      rewrite /PMap.get in Hpnone.
      rewrite Hpnone.
      constructor.
  Qed.

  Lemma computeMap_acquire_delta_permMapLt :
    forall p q maxp, permMapLt p maxp -> permMapLt q maxp ->
      (forall b ofs, Mem.perm_order'' ((maxp !!! b) ofs) (join_perm ((p !!! b) ofs) ((q !!! b) ofs))) ->
      permMapLt (computeMap q (acquire_delta p q maxp)) maxp.
  Proof.
    intros p q maxp Hp Hq Hjoin b ofs.
    rewrite /computeMap /acquire_delta /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax |] eqn:Hmaxb.
    - destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl;
        destruct (fmax ofs) as [mx |] eqn:Hmaxofs; simpl.
      + (* max has permission; delta uses join_perm *)
        specialize (Hjoin b ofs).
        by rewrite /PMap.get Hmaxb /= Hmaxofs Hqb /= in Hjoin.
      + specialize (Hq b ofs).
        unfold PMap.get in Hq.
        by rewrite Hmaxb /= Hmaxofs Hqb in Hq.
      + specialize (Hjoin b ofs).
        by rewrite /PMap.get Hmaxb /= Hmaxofs Hqb /Mem.perm_order'' /= in Hjoin.
      + specialize (Hq b ofs).
        by rewrite /PMap.get Hmaxb /= Hmaxofs Hqb in Hq.
    - specialize (Hq b ofs).
      by rewrite /PMap.get Hmaxb /= in Hq.
  Qed.

  Lemma join_perm_below_max :
    forall p q maxp b ofs, permMapLt p maxp -> permMapLt q maxp -> permMapsDisjoint p q ->
      Mem.perm_order'' ((maxp !!! b) ofs) (join_perm ((p !!! b) ofs) ((q !!! b) ofs)).
  Proof.
    intros p q maxp b ofs Hp Hq Hdisj.
    specialize (Hp b ofs).
    specialize (Hq b ofs).
    specialize (Hdisj b ofs).
    destruct Hdisj as (pu & Hdisj).
    destruct ((p !!! b) ofs) as [pp |] eqn:Hpbo;
      destruct ((q !!! b) ofs) as [qq |] eqn:Hqbo;
      simpl in *; try done.
    - destruct pp, qq; try done.
    - destruct pp; try done.
  Qed.

  Lemma computeMap_acquire_delta_empty_get :
    forall q maxp b ofs,
      ((computeMap q (acquire_delta empty_map q maxp)) !!! b) ofs = (q !!! b) ofs.
  Proof.
    intros q maxp b ofs.
    unfold computeMap, acquire_delta.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax |] eqn:Hmaxb;
      destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl; try done.
    - destruct (fmax ofs); simpl; reflexivity.
    - destruct (fmax ofs); simpl; reflexivity.
  Qed.

  Lemma permMapsDisjoint2_empty_l :
    forall rmap, permMapsDisjoint2 (empty_map, empty_map) rmap.
  Proof.
    intros rmap.
    rewrite /permMapsDisjoint2 /=.
    split; apply empty_disjoint'.
  Qed.

  Lemma permMapsDisjoint2_empty_r :
    forall rmap, permMapsDisjoint2 rmap (empty_map, empty_map).
  Proof.
    intros rmap.
    rewrite /permMapsDisjoint2 /=.
    split; apply permMapsDisjoint_comm; apply empty_disjoint'.
  Qed.

  Lemma join_perm_disjoint3 :
    forall a b c, (exists ab, perm_union a b = Some ab) ->
             (exists ac, perm_union a c = Some ac) ->
             (exists bc, perm_union b c = Some bc) ->
             exists u, perm_union (join_perm a b) c = Some u.
  Proof.
    intros a b c [ab Hab] [ac Hac] [bc Hbc].
    destruct a as [a|], b as [b|], c as [c|];
      simpl in *; try discriminate; eauto;
    try destruct a, b, c; simpl in *; try discriminate; eauto.
    destruct a, b; simpl in *; try discriminate; eexists; eauto.
    destruct a, c; simpl in *; try discriminate; eexists; eauto.
    destruct a; simpl in *; try discriminate; eexists; eauto.
  Qed.

  Lemma acquire_delta_preserves_disjoint3 :
    forall l p maxp x,
      permMapsDisjoint l p ->
      permMapsDisjoint l x ->
      permMapsDisjoint p x ->
      permMapsDisjoint (computeMap p (acquire_delta l p maxp)) x.
  Proof.
    intros l p maxp x Hlp Hlx Hpx b ofs.
    rewrite /acquire_delta /computeMap /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    specialize (Hlp b ofs) as [pu_lp Hlp].
    specialize (Hlx b ofs) as [pu_lx Hlx].
    specialize (Hpx b ofs) as [pu_px Hpx].
    rewrite /PMap.get in Hlp, Hlx, Hpx.
    destruct ((maxp.2 !! b)%maps) as [fmax|] eqn:Hmax.
    - destruct ((p.2 !! b)%maps) as [fp|] eqn:Hp; simpl.
      + destruct ((l.2 !! b)%maps) as [fl|] eqn:Hl; simpl.
        * (* updated case: new permission = join_perm l p *)
          destruct (fmax ofs) as [mx|] eqn:Hmax_ofs; simpl.
          ++ apply join_perm_disjoint3; eexists; done.
          ++ eexists; done.
        * (* lock permission l comes from its default function l.1 *)
          destruct (fmax ofs) as [mx |] eqn:Hmax_ofs; simpl.
          ++ apply join_perm_disjoint3; eexists; done.
          ++ eexists; done.
      + (* default permission function p.1 because Hp : (p.2 !! b)%maps = None *)
        destruct (fmax ofs) as [mx |] eqn:Hmax_ofs; simpl.
        * apply join_perm_disjoint3; eexists; eauto.
        * eexists; done.
    - (* no update because Hmax : (maxp.2 !! b)%maps = None *)
      simpl.
      eexists; done.
  Qed.

  Lemma join_perm_coh_right :
    forall a l p, perm_coh a l -> perm_coh a p -> perm_coh a (join_perm l p).
  Proof.
    intros a l p H1 H2.
    destruct a as [a|], l as [l|], p as [p|];
      simpl in *; try contradiction; auto;
      try destruct a, l, p; simpl in *; try contradiction; try done.
    - destruct a, l; try done.
    - destruct l, p; try done.
    - destruct l; try done.
  Qed.

  Lemma join_perm_coh_left :
    forall l p x, perm_coh l x -> perm_coh p x -> perm_coh (join_perm l p) x.
  Proof.
    intros l p x H1 H2.
    destruct l as [l|], p as [p|], x as [x|];
      simpl in *; try contradiction; auto;
      try destruct l, p, x; simpl in *; try contradiction; auto.
    - destruct l, p; try done.
    - destruct l, x; try done.
    - destruct l; try done.
  Qed.

  Lemma acquire_delta_preserves_coherence_right :
    forall a l p maxp, permMapCoherence a l -> permMapCoherence a p ->
      permMapCoherence a (computeMap p (acquire_delta l p maxp)).
  Proof.
    intros a l p maxp Hal Hap.
    unfold permMapCoherence in *.
    intros b ofs.
    specialize (Hal b ofs).
    specialize (Hap b ofs).
    unfold computeMap, acquire_delta.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax|] eqn:Hmax;
      destruct ((p.2 !! b)%maps) as [fp|] eqn:Hp;
      destruct ((l.2 !! b)%maps) as [fl|] eqn:Hl;
      simpl in *;
      unfold PMap.get in Hal, Hap;
      rewrite Hl in Hal;
      rewrite Hp in Hap;
      simpl in Hal, Hap;
      try (
          destruct (fmax ofs) as [mx|]; simpl;
          [ eapply join_perm_coh_right; eauto
          | exact Hap ]
        ); exact Hap.
  Qed.

  Lemma acquire_delta_preserves_coherence_left :
    forall l p x maxp, permMapCoherence l x -> permMapCoherence p x ->
      permMapCoherence (computeMap p (acquire_delta l p maxp)) x.
  Proof.
    intros l p x maxp Hlx Hpx.
    unfold permMapCoherence in *.
    intros b ofs.
    specialize (Hlx b ofs).
    specialize (Hpx b ofs).
    unfold computeMap, acquire_delta.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax|] eqn:Hmax;
      destruct ((p.2 !! b)%maps) as [fp|] eqn:Hp;
      destruct ((l.2 !! b)%maps) as [fl|] eqn:Hl;
      simpl in *;
      unfold PMap.get in Hlx, Hpx;
      rewrite Hl in Hlx;
      rewrite Hp in Hpx;
      simpl in Hlx, Hpx;
      try (
          destruct (fmax ofs) as [mx|]; simpl;
          [ eapply join_perm_coh_left; eauto
          | exact Hpx ]
        ); exact Hpx.
  Qed.

  Lemma permMapCoherence_writable_bound_r :
    forall p q, permMapCoherence p q ->
      forall b ofs, Mem.perm_order'' (Some Writable) ((q !!! b) ofs).
  Proof.
    intros p q Hcoh b ofs.
    specialize (Hcoh b ofs).
    unfold perm_coh in Hcoh.
    destruct ((p !!! b) ofs) as [pp|];
      destruct ((q !!! b) ofs) as [qq|];
      simpl in *; try contradiction; auto;
      try destruct pp, qq; simpl in *; try contradiction; auto.
    - constructor.
    - constructor.
    - constructor.
    - destruct qq; try done; try constructor.
  Qed.

  Lemma Mem_load_unchecked_store_unchecked_other:
   forall m b ofs b' ofs' v,
     b' <> b \/ (ofs' + size_chunk Mptr <= ofs \/ ofs + size_chunk Mptr <= ofs')%Z ->
     Mem_load_unchecked Mptr (Mem_store_unchecked Mptr m b ofs v) b' ofs' =
       Mem_load_unchecked Mptr m b' ofs'.
 Proof.
   intros.
   rewrite /Mem_load_unchecked /= /Mem_store_unchecked_contents.
   destruct (eq_dec b' b) as [Hb | Hb].
   - subst b'.
     rewrite PMap.gss.
     f_equal.
     rewrite Mem.getN_setN_outside; auto.
     rewrite encode_val_length -size_chunk_conv.
     destruct H; done.
   - by rewrite PMap.gso.
 Qed.

 Lemma Mem_load_unchecked_store_unchecked_lock_addresses_disjoint
   (m : mem) (ls : gset (Values.block * Z))
   (b b1 : Values.block) (o : ptrofs) (o1 : Z) :
   lock_addresses_disjoint ls ->
   (b1, o1) ∈ ls ->
   (b, Ptrofs.unsigned o) ∈ ls ->
   (b1, o1) <> (b, Ptrofs.unsigned o) ->
   Mem_load_unchecked Mptr (Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero)) b1 o1 = Mem_load_unchecked Mptr m b1 o1.
  Proof.
    intros Hdisj Hin1 Hin2 Hneq.
    pose proof (Hdisj (b, Ptrofs.unsigned o) (b1, o1) Hin2 Hin1) as Hsep.
    assert ((b, Ptrofs.unsigned o) <> (b1, o1)) by congruence.
    specialize (Hsep H).
    simpl in Hsep.
    unfold Mem_load_unchecked, Mem_store_unchecked.
    destruct (Mem.store Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero))
      as [m'|] eqn:Hstore; simpl; auto;
    eapply Mem_load_unchecked_store_unchecked_other; eauto.
  Qed.
(*
  Ltac get_lk n dq rsh Hvalid Hincl Hlk :=
  let Hseq := fresh "Hseq" in
  assert (Hseq : seq 0%nat (Z.to_nat LKSIZE) !! n = Some n) by
    (vm_compute; reflexivity);
  iDestruct (big_sepL_lookup_acc with "HLK") as "[HLKi Hclose]";
  first exact Hseq;
  iDestruct (mapsto_lookup with "Hm HLKi")
    as %(dq & rsh & Hvalid & Hincl & Hlk);
  iDestruct ("Hclose" with "HLKi") as "HLK".

Ltac norm_adr_add :=
  repeat match goal with
    | H : context[adr_add (?b, ?o) ?n] |- _ =>
        replace (adr_add (b, o) n) with (b, (o + Z.of_nat n)%Z) in H
          by (unfold adr_add; simpl; f_equal; lia)
    end.

Ltac solve_LK_VAL_contra :=
  norm_adr_add;
  match goal with
  | Hval : (resR_to_resource (?σ !! _)).2 = Some (VAL _) |- False =>
      erewrite resR_to_resource_eq in Hval; eauto;
      rewrite /= elem_of_to_agree in Hval;
      inversion Hval
  end.

Lemma frag_mem_auth_store_unchecked_lock_zero `{!heapGS Σ}
  (q : Qp) (m : mem) (σ : rmap) (sh : share) (b : Values.block) (o : Z) (v : val) :
  frag_mem_auth (Σ := Σ) q m σ -∗ LKspec (Σ := Σ) LKSIZE sh (b, o) ==∗
  frag_mem_auth (Σ := Σ) q (Mem_store_unchecked Mptr m b o v) σ ∗
  LKspec (Σ := Σ) LKSIZE sh (b, o).
Proof.
  iIntros "((%Hcoh & %Heq) & Hm) HLK".
  iDestruct (resource_map.resource_map_auth_valid with "Hm") as %(_ & Hvalid).
  rewrite /LKspec /=.
   (* Mptr store changes 8 bytes
      -> coherent must be re-proved for all 8 bytes
      -> need LK facts for all 8 addresses
    *)
  get_lk 0%nat dq0 rsh0 Hvalid0 Hincl0 Hlk0.
  get_lk 1%nat dq1 rsh1 Hvalid1 Hincl1 Hlk1.
   get_lk 2%nat dq2 rsh2 Hvalid2 Hincl2 Hlk2.
   get_lk 3%nat dq3 rsh3 Hvalid3 Hincl3 Hlk3.
   get_lk 4%nat dq4 rsh4 Hvalid4 Hincl4 Hlk4.
   get_lk 5%nat dq5 rsh5 Hvalid5 Hincl5 Hlk5.
   get_lk 6%nat dq6 rsh6 Hvalid6 Hincl6 Hlk6.
   get_lk 7%nat dq7 rsh7 Hvalid7 Hincl7 Hlk7.
   iSplitL "Hm"; auto.
   rewrite /mem_auth.
   iExists σ.
   iFrame "Hm".
   iPureIntro; split; last done.
     (* the store changes only these bytes: (b,o)+0 ... (b,o)+7
        and LKspec says exactly those bytes are LK, not VAL.
        coherent requires concrete memory contents to match σ only for VAL locations.
        -> contradiction

       - outside range: memory unchanged, use old coherence
       - inside range: locations are LK, so no VAL-content obligation
     *)
   unfold coherent, resource_at in *.
   intro loc.
   destruct (Hcoh loc) as (Hnext & Hcontents & Haccess).
   split3; try done.
   unfold contents_cohere, contents_at in *.
   intros mv Hval.
   destruct (adr_range_dec (b, o) (size_chunk Mptr) loc) as [Hin | Hout].
   - (* loc is inside the stored range *)
     destruct loc as [bb ofs].
     destruct Hin as (Hb & Hlo & Hhi); simpl in *.
     subst bb.
     change (size_chunk Mptr) with 8%Z in Hhi.
     assert (ofs = o \/ ofs = o + 1 \/ ofs = o + 2 \/ ofs = o + 3 \/
               ofs = o + 4 \/ ofs = o + 5 \/ ofs = o + 6 \/ ofs = o + 7)%Z as Hor by lia.
     exfalso.
     repeat destruct Hor as [-> | Hor]; repeat solve_LK_VAL_contra.
     (* solve_LK_VAL_contra doesn't work well with adr_add (b, o) 0 and adr_add (b, o) 7  *)
     + replace (adr_add (b, o) 0%nat) with (b, o) in Hlk0; last first.
       { rewrite /adr_add //=; f_equal. lia. }
       erewrite resR_to_resource_eq in Hval; eauto.
       rewrite /= elem_of_to_agree in Hval.
       inversion Hval.
     + subst ofs.
       erewrite resR_to_resource_eq in Hval; eauto.
       rewrite /= elem_of_to_agree in Hval.
       inv Hval.
   - (* outside range: memory unchanged, use old coherence *)
     rewrite <- (Hcontents mv Hval).
     rewrite /juicy_mem.contents_at /Mem_store_unchecked /=.
     rewrite /Mem_store_unchecked_contents.
     destruct loc as (b' & ofs); simpl in *.
     destruct (Pos.eq_dec b' b) as [Hb | Hb].
     + subst b'.
       rewrite Maps.PMap.gss Mem.setN_other; auto.
       intros.
       intro Heq; subst r.
       apply Hout.
       split; auto.
       rewrite encode_val_length in H.
       by rewrite size_chunk_conv.
     + rewrite Maps.PMap.gso; auto.
 Qed. *)

End concurrent_opreations.
  
