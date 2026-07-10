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
