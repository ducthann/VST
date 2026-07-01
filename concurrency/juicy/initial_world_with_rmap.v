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

Section inflate_with_rmap.

  Context {Σ : gFunctors} `{!heapGS Σ}.
  Variable (m : mem) (block_bounds : block -> Z * nat).
  Context {F : Type} (ge : Genv.t (Ctypes.fundef F) Ctypes.type) (G : funspecs (Σ := Σ)).

  Definition inflate_loc_with_rmap (loc : address) : iProp Σ :=
    match access_at m loc Cur with
    | Some Freeable => loc ↦ VAL (contents_at m loc)
    | Some Writable => loc ↦{#Ews} VAL (contents_at m loc)
    | Some Readable => loc ↦{#Ers} VAL (contents_at m loc)
    | Some Nonempty =>
        match funspec_of_loc ge G loc with
        | Some f => func_at f loc
        | None => mapsto_no loc Share.Lsh
        end
    | None =>
        mapsto_no loc Share.bot
    end.

  Definition res_of_loc_with_rmap (loc : address) : sharedR (leibnizO resource) :=
    match access_at m loc Cur with
    | Some Freeable =>
        (shared.YES(V := leibnizO resource)
           (DfracOwn (Share Tsh))
           readable_top (to_agree (VAL (contents_at m loc))))
    | Some Writable =>
        (shared.YES(V := leibnizO resource)
           (DfracOwn (Share Ews))
           readable_Ews (to_agree (VAL (contents_at m loc))))
    | Some Readable =>
        (shared.YES(V := leibnizO resource)
           (DfracOwn (Share Ers))
           readable_Ers (to_agree (VAL (contents_at m loc))))
    | Some Nonempty => match funspec_of_loc ge G loc with
                       | Some _ =>
                           (shared.YES(V := leibnizO resource)
                              (DfracBoth (Share Share.bot)) I (to_agree FUN))
                      | _ => (shared.NO (Share Share.Lsh) Lsh_nonreadable)
                       end
    | _ => (shared.NO (Share Share.bot) bot_unreadable)
    end.

(* As in [initial_world.rmap_of_mem], include one extra resource at the upper
   endpoint.  This preserves the existing treatment of zero-sized globals. *)

  Definition rmap_of_mem_with_rmap : gmapR address (sharedR (leibnizO resource)) :=
    [^op list] n ∈ seq 1 (Pos.to_nat (Mem.nextblock m) - 1),
      let b := Pos.of_nat n in
      let '(lo, z) := block_bounds b in
       [^op list] o ∈ seq 0 (z + 1),
        let loc := (b, lo + Z.of_nat o)%Z in {[loc := res_of_loc_with_rmap loc]}.
  
  Definition inflate_initial_mem_with_rmap: mpred :=
    [∗ list] n ∈ seq 1 (Pos.to_nat (Mem.nextblock m) - 1),
      let b := Pos.of_nat n in
      let '(lo, z) := block_bounds b in [∗ list] o ∈ seq 0 (z + 1),
        let loc := (b, lo + Z.of_nat o)%Z in inflate_loc_with_rmap loc.

End inflate_with_rmap.

Section initial_world_with_rmap_lemmas.

  Context {Σ : gFunctors} `{!heapGS Σ}.

  Lemma lookup_of_loc_with_rmap :
    forall (m : mem) {F : Type} (ge : Genv.t (fundef F) type) (G : funspecs (Σ := Σ)) b lo z loc,
      (([^op list] o ∈ seq 0 z,
         {[(b, (lo + Z.of_nat o)%Z) :=
             res_of_loc_with_rmap m ge G
               (b, (lo + Z.of_nat o)%Z)]}) !! loc
         ≡ if adr_range_dec (b, lo) z loc
         then Some (res_of_loc_with_rmap m ge G loc)
         else None)%stdpp.
  Proof.
    intros.
    evar (f : nat -> sharedR (leibnizO resource)).
    etrans; [|etrans;
            [apply (lookup_singleton_list (seq 0 z) f (b, lo) loc)|]].
    2: {
      rewrite seq_length; if_tac; last done.
      destruct loc, H; subst; simpl.
      rewrite lookup_seq_lt /=; last lia.
      subst f; instantiate (1 := fun i => res_of_loc_with_rmap m ge G (b, i + lo)); simpl.
      by replace (_ + _) with z0 by lia.
    }
    subst f.
    etrans; [|symmetry; apply (big_opL_seq_index (M := gmapR address _))].
    f_equiv; apply big_opL_ext; intros.
    rewrite (Z.add_comm _ lo) //.
  Qed.

  Lemma rmap_of_drop_last_block_with_rmap:
    forall (m : mem) {F : Type} (ge : Genv.t (fundef F) type) (G : funspecs (Σ := Σ)) loc,
      res_of_loc_with_rmap (drop_last_block m) ge G loc =
        if eq_dec loc.1 (nextblock m - 1)%positive
        then (shared.NO (Share Share.bot) bot_unreadable)
        else res_of_loc_with_rmap m ge G loc.
  Proof.
    intros; rewrite /res_of_loc_with_rmap /drop_last_block /access_at /contents_at /=.
    destruct (eq_dec loc.1 (nextblock m - 1)%positive).
    - rewrite e Maps.PMap.gss //.
    - rewrite Maps.PMap.gso //.
  Qed.

  Lemma rmap_of_drop_last :
    forall m block_bounds {F} (ge : Genv.t (fundef F) type) (G : funspecs (Σ := Σ)) n,
      (n < Pos.to_nat (nextblock m) - 1)%nat ->
      ([^op list] n0 ∈ seq 1 n,
        let '(lo, z) := block_bounds (Pos.of_nat n0) in
        [^op list] o ∈ seq 0 (z + 1), {[(Pos.of_nat n0, lo + Z.of_nat o) := res_of_loc_with_rmap m ge G (Pos.of_nat n0, lo + Z.of_nat o)]} ) =
  ([^op list] n0 ∈ seq 1 n, let '(lo, z) := block_bounds (Pos.of_nat n0) in
   [^op list] o ∈ seq 0 (z + 1), {[(Pos.of_nat n0, lo + Z.of_nat o) :=
                                     res_of_loc_with_rmap (drop_last_block m) ge G (Pos.of_nat n0, lo + Z.of_nat o)]} ).
  Proof.
    intros.
    apply big_opL_ext; intros ??[-> ?]%lookup_seq.
    destruct (block_bounds (Pos.of_nat _)).
    apply big_opL_ext; intros.
    rewrite rmap_of_drop_last_block_with_rmap.
    if_tac; try done.
    simpl in *; lia.
  Qed.

  Lemma lookup_of_mem_with_rmap :
    forall m {F : Type} (ge : Genv.t (fundef F) type) (G : funspecs (Σ := Σ)) block_bounds loc,
      (rmap_of_mem_with_rmap m block_bounds ge G !! loc ≡
         let '(lo, z) := block_bounds (fst loc) in
         if plt (fst loc) (nextblock m) && zle lo (snd loc) && zle (snd loc) (lo + Z.of_nat z)
         then Some (res_of_loc_with_rmap m ge G loc) else None)%stdpp.
  Proof.
    intros; rewrite /rmap_of_mem_with_rmap.
    remember (Pos.to_nat (nextblock m) - 1)%nat as n.
    generalize dependent m; induction n; intros.
    { rewrite /= lookup_empty.
      destruct (block_bounds loc.1).
      destruct (_ && _) eqn: Hin; last done.
      rewrite !andb_true_iff in Hin; destruct Hin as ((? & ?) & ?).
      destruct (plt _ _); try done.
      unfold Plt in *; lia. }
    rewrite seq_S lookup_proper; last apply big_opL_app.
    rewrite /= !lookup_op lookup_empty op_None_right_id.
    rewrite rmap_of_drop_last; last lia.
    rewrite IHn; last by simpl; lia.
    rewrite /= rmap_of_drop_last_block_with_rmap.
    rewrite Heqn Nat2Pos.inj_sub // Pos2Nat.id /= /Pos.of_nat.
    destruct (eq_dec loc.1 (nextblock m - 1)%positive).
    - rewrite -e.
      destruct (block_bounds loc.1) as (lo, z); simpl.
      destruct (plt _ _); first by unfold Plt in *; lia.
      rewrite /= left_id lookup_of_loc_with_rmap.
      destruct (plt _ _); try by unfold Plt in *; lia.
      if_tac.
      + destruct loc as (?, o), H; simpl in *.
        destruct (zle lo o); try lia; destruct (zle o (lo + z)); try lia; done.
      + destruct loc as (?, o); simpl.
        destruct (zle lo o); try done.
        destruct (zle o (lo + z)); try done.
        contradiction H; simpl; auto; lia.
    - destruct (block_bounds (nextblock m - 1)%positive).
      rewrite lookup_of_loc_with_rmap if_false; last by destruct loc; intros [??].
      rewrite right_id.
      destruct (plt _ _), (plt _ _); try done; unfold Plt in *; lia.
  Qed.

  Lemma rmap_of_loc_with_rmap_coherent :
    forall m F (ge : Genv.t (fundef F) type) (G : funspecs (Σ := Σ)) loc,
      coherent_loc m loc
        (resR_to_resource
           (Some (res_of_loc_with_rmap m ge G loc))).
  Proof.
    intros; rewrite /res_of_loc_with_rmap.
    destruct (access_at m loc Cur) eqn:Hloc; last apply coherent_bot.
    destruct p.
    - rewrite /= elem_of_to_agree.
      split.
      + unfold contents_cohere; simpl.
        by inversion 1.
      + rewrite /access_cohere Hloc /=.
        rewrite /perm_of_sh !if_true //; auto.
        constructor.
    - rewrite /= elem_of_to_agree.
      split.
      + unfold contents_cohere; simpl.
        by inversion 1.
      + rewrite /access_cohere Hloc /= perm_of_Ews.
        constructor.
    - rewrite /= elem_of_to_agree.
      split.
      + unfold contents_cohere; simpl.
        by inversion 1.
      + rewrite /access_cohere Hloc /= perm_of_Ers.
        constructor.
    - destruct (funspec_of_loc ge G loc) as [f |] eqn:Hfun.
      + rewrite /= elem_of_to_agree.
        split; first done.
        rewrite /access_cohere Hloc /=.
        constructor.
      + rewrite /=.
        split; first done.
        rewrite /access_cohere Hloc /=.
        destruct (eq_dec Share.Lsh Share.bot) as [Heq | Hneq].
        * exfalso.
          apply Lsh_bot_neq.
          exact Heq.
        * rewrite if_false; try done.
          constructor.
  Qed.

  Lemma rmap_of_loc_with_rmap_valid :
    forall m {F : Type}
           (ge : Genv.t (fundef F) type)
           (G : funspecs (Σ := Σ))
           loc,
      (✓ (res_of_loc_with_rmap (Σ := Σ) (F := F) m ge G loc))%stdpp.
  Proof.
    intros; rewrite /res_of_loc_with_rmap.
    destruct (access_at m loc Cur); try done.
    destruct p; try done;
      try destruct (funspec_of_loc _ _ _) as [[] |]; try done.
    split; try done.
    eexists; split; eauto.
    intros ?; apply bot_unreadable; auto.
  Qed.

  Check rmap_of_mem_with_rmap.
  Lemma rmap_of_mem_with_rmap_coherent :
    forall m block_bounds {F : Type} (ge : Genv.t (fundef F) type) (G : funspecs (Σ := Σ)) loc,
      (✓ rmap_of_mem_with_rmap (Σ := Σ) (F := F) m block_bounds ge G)%stdpp ->
      coherent_loc m loc
        (resource_at
           (rmap_of_mem_with_rmap (Σ := Σ) (F := F) m block_bounds ge G) loc).
  Proof.
    intros; rewrite /resource_at.
    specialize (H loc).
    erewrite resR_to_resource_eq;
      [|done|apply lookup_of_mem_with_rmap].
    rewrite lookup_of_mem_with_rmap in H.
    destruct loc as (b, o).
    destruct (block_bounds b) eqn:Hbounds; rewrite Hbounds /=.
    destruct (plt _ _); last apply coherent_bot.
    destruct (zle z o); simpl; last apply coherent_bot.
    destruct (zle o (z + n)); last apply coherent_bot; simpl.
    apply rmap_of_loc_with_rmap_coherent.
  Qed.

  Lemma rmap_of_mem_with_rmap_valid :
    forall m block_bounds {F} ge G,
      (✓rmap_of_mem_with_rmap (Σ := Σ) (F := F) m block_bounds ge G)%stdpp.
  Proof.
    intros.
    intros i; rewrite lookup_of_mem_with_rmap.
    destruct (block_bounds _).
    simple_if_tac; try done.
    apply rmap_of_loc_with_rmap_valid.
  Qed.

 Lemma rmap_of_mem_with_rmap_nextblock :
    forall m block_bounds {F}
           (ge : Genv.t (fundef F) type)
           (G : funspecs (Σ := Σ))
           (loc : address),
      (fst loc >= nextblock m)%positive ->
      (rmap_of_mem_with_rmap
        (Σ := Σ) (F := F) m block_bounds ge G !! loc = None)%stdpp.
  Proof.
    intros.
    pose proof
      (lookup_of_mem_with_rmap m ge G block_bounds loc) as Hlookup.
    destruct (plt _ _).
    { unfold Plt in *; clear -H p.
      apply Pos.lt_nle in p; contradiction p.
      apply Pos.ge_le; done.
    }
    simpl in Hlookup.
    destruct (block_bounds _); inv Hlookup; done.
  Qed.

(** ** Inflating the new resource map *)

  Lemma rmap_inflate_equiv_with_rmap : forall m block_bounds {F}
    (ge : Genv.t (fundef F) type) (G : funspecs (Σ := Σ))
    (Hfun_bounds : forall b f, funspec_of_loc ge G (b, 0) = Some f -> block_bounds b = (0, 0%nat))
    (Hm :forall b, (b < nextblock m)%positive ->
              match funspec_of_loc ge G (b, 0) with
              | Some _ =>
                  access_at m (b, 0) Cur = Some Nonempty
              | None => True
              end),
    funspec_auth ∅ ∗
      ([∗ map] l ↦ x ∈
         rmap_of_mem_with_rmap m block_bounds ge G,
       match x with
       | shared.YES dq _ v =>
           l ↦{dq} (proj1_sig (elem_of_agree v))
       | shared.NO (Share sh) _ => mapsto_no l sh
       | _ => False
       end)
    ⊢ |==>
      funspec_auth (init_funspecs m ge G) ∗
      inflate_initial_mem_with_rmap m block_bounds ge G.
Proof.
  intros.
  assert
    (forall (l : address)
            (y1 y2 : sharedR (leibnizO resource)),
       (✓ y1)%stdpp -> (y1 ≡ y2)%stdpp ->
       match y1 with
       | shared.YES dq _ v =>
           l ↦{dq} (proj1_sig (elem_of_agree v))
       | shared.NO (Share sh) _ => mapsto_no l sh
       | _ => False
       end
       ⊣⊢
       match y2 with
       | shared.YES dq _ v =>
           l ↦{dq} (proj1_sig (elem_of_agree v))
       | shared.NO (Share sh) _ => mapsto_no l sh
       | _ => False
       end).
  { intros ??? Hv Heq.
    destruct y1, y2; inv Heq; try done.
    destruct Hv.
    match goal with
    | H : (_ ≡ _)%stdpp |- _ =>
        apply (elem_of_agree_ne O) in H as ->%leibniz_equiv;
        done
    end.
  }
  rewrite /rmap_of_mem_with_rmap /init_funspecs
          /inflate_initial_mem_with_rmap big_opM_opL' //.
  assert
    (Pos.to_nat (nextblock m) - 1 < Pos.to_nat (nextblock m))%nat
    as Hlt by lia.
  induction (Pos.to_nat (nextblock m) - 1)%nat.
  { by iIntros. }
  rewrite seq_S /= !big_sepL_app foldl_snoc assoc IHn /=.
  iIntros "(>(Hf & $) & Hm & _)".
  destruct (block_bounds _) eqn:Hbounds.
  rewrite big_opM_opL' //.
  destruct (funspec_of_loc ge G (Pos.of_nat (S n), 0)) eqn:Hfun.
  - iMod (own_update with "Hf") as "($ & Hf)".
    { apply (gmap_view.gmap_view_alloc _ (Pos.of_nat (S n), 0) dfrac.DfracDiscarded);
        last done.
      apply init_funspecs_over; auto.
    }
    erewrite Hfun_bounds in Hbounds by done.
    inv Hbounds; simpl.
    rewrite !big_sepM_singleton
            /res_of_loc_with_rmap
            /inflate_loc_with_rmap.
    specialize (Hm (Pos.of_nat (S n)) ltac:(lia)).
    rewrite Hfun in Hm; rewrite Hm Hfun /func_at elem_of_to_agree.
    iDestruct "Hm" as "($ & _)"; iFrame; done.
  - iFrame.
    assert (forall z, funspec_of_loc ge G (Pos.of_nat (S n), z) = None) as Hfun'.
    { intros; unfold funspec_of_loc in *.
      simpl; if_tac; done.
    }
    rewrite bi.sep_emp -big_sepL_bupd.
    iApply (big_sepL_mono with "Hm").
    intros ?? [-> ?]%lookup_seq.
    rewrite big_opM_singleton.
    rewrite /res_of_loc_with_rmap /inflate_loc_with_rmap.
    destruct (access_at _ _ _) eqn:Haccess; last apply bupd_intro.
    destruct p; try apply bupd_intro; rewrite ?Hfun' ?elem_of_to_agree; apply bupd_intro.
  - apply NoDup_seq.
  - intros.
    intros i.
    rewrite /option_relation.
    assert(Hkeys :
            (Pos.of_nat (S n), (z + Z.of_nat a1)%Z) <> (Pos.of_nat (S n), (z + Z.of_nat a2)%Z)).
    { intros Heq; apply H2; inversion Heq; lia. }
    destruct (eq_dec i (Pos.of_nat (S n), z + a1)) as [Hi | Hi].
    + subst i.
      rewrite lookup_singleton.
      rewrite lookup_singleton_ne; done.
    + rewrite lookup_singleton_ne; last first.
      intro Heq; apply Hi; symmetry; done.
      destruct (({[(Pos.of_nat (S n), z + a2) :=
                   res_of_loc_with_rmap m ge G (Pos.of_nat (S n), z + a2)]} !! i)%stdpp);
        done.
  - intros i.
    rewrite lookup_of_loc_with_rmap.
    if_tac; try done.
    apply rmap_of_loc_with_rmap_valid.
  - lia.
  - apply NoDup_seq.
  - intros _ _ ?? Ha1%elem_of_seq Ha2%elem_of_seq ?.
    destruct (block_bounds _), (block_bounds _).
    intros i.
    rewrite disjoint_rel_proper;
      [|apply lookup_of_loc_with_rmap..].
    rewrite /option_relation.
    if_tac;
      last by destruct (if adr_range_dec _ _ _ then _ else _).
    if_tac; last done.
    destruct i, H1, H2; lia.
  - apply rmap_of_mem_with_rmap_valid.
Qed.

(** ** Extracting the dry permission map *)

Definition perm_row_of_rmap (σ : rmap) (b : positive) : Z -> option permission :=
  fun ofs => perm_of_res (σ @ (b, ofs)).

Definition perm_of_rmap (σ : rmap) : access_map :=
  fold_right
    (fun '(loc, _) p =>
       PMap.set loc.1 (perm_row_of_rmap σ loc.1) p)
    (PMap.init (fun _ => None))
    (map_to_list σ).

Lemma perm_row_of_rmap_lookup :
  forall σ b ofs, perm_row_of_rmap σ b ofs = perm_of_res (σ @ (b, ofs)).
Proof. reflexivity. Qed.

(* UP *)

Lemma perm_of_rmap_fold_lookup :
  forall σ (l : list (address * sharedR (leibnizO resource))) (b : block) (ofs : Z),
    (forall (ofs0 : Z) (r : sharedR (leibnizO resource)),
        (σ !! (b, ofs0) = Some r)%stdpp -> (((b, ofs0), r) ∈ l)%stdpp) ->
    PMap.get b (fold_right (fun '(loc, _) (p : PMap.t (Z -> option permission)) =>
          PMap.set loc.1 (perm_row_of_rmap σ loc.1) p) (PMap.init (fun _ => None)) l) ofs =
      perm_of_res (σ @ (b, ofs)).
Proof.
  intros σ l.
  induction l as [| [[b0 ofs0] r0] l IH];
    intros b ofs Hin; simpl.
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

(* Pointwise equality is the relevant notion for CompCert access maps. *)
Definition access_map_pointwise_eq (p q : access_map) : Prop :=
  forall b ofs, PMap.get b p ofs = PMap.get b q ofs.

Lemma access_map_pointwise_eq_equiv :
  forall p q, access_map_pointwise_eq p q -> mem_equiv.access_map_equiv p q.
Proof.
  intros p q Heq b.
  apply functional_extensionality; intro ofs.
  apply Heq.
Qed.

Definition block_bounds_cover (m : Mem.mem') (block_bounds : block -> Z * nat) : Prop :=
  forall b ofs p, access_at m (b, ofs) Cur = Some p ->
    let '(lo, n) := block_bounds b in (lo <= ofs <= lo + Z.of_nat n)%Z.

Lemma perm_of_rmap_of_mem_with_rmap_exact :
  forall (m : Mem.mem') (block_bounds : block -> Z * nat) {F : Type}
    (ge : Genv.t (fundef F) type) (G : funspecs),
    block_bounds_cover m block_bounds ->
    access_map_pointwise_eq
      (perm_of_rmap (rmap_of_mem_with_rmap (Σ := Σ) m block_bounds ge G)) (getCurPerm m).
Proof.
  intros m block_bounds F ge G Hcover b ofs.
  rewrite perm_of_rmap_lookup.
  rewrite /getCurPerm PMap.gmap.
  change (perm_of_res (resource_at (rmap_of_mem_with_rmap m block_bounds ge G) (b, ofs))
     = access_at m (b, ofs) Cur).
  rewrite /resource_at.
  pose proof (rmap_of_mem_with_rmap_valid m block_bounds ge G) as Hvalid.
  specialize (Hvalid (b, ofs)).
  erewrite resR_to_resource_eq;
    [|exact Hvalid|apply lookup_of_mem_with_rmap].
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
    rewrite /res_of_loc_with_rmap Haccess.
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
    try rewrite /res_of_loc_with_rmap Haccess /=; rewrite eq_dec_refl //. }
Qed.

Lemma perm_of_rmap_of_mem_with_rmap_equiv :
  forall (m : Mem.mem') (block_bounds : block -> Z * nat) {F : Type}
         (ge : Genv.t (fundef F) type) (G : funspecs),
    block_bounds_cover m block_bounds ->
    mem_equiv.access_map_equiv
      (perm_of_rmap (rmap_of_mem_with_rmap (Σ := Σ) m block_bounds ge G))
      (getCurPerm m).
Proof. intros; apply access_map_pointwise_eq_equiv, perm_of_rmap_of_mem_with_rmap_exact; auto. Qed.

(** ** Exposing the selected authoritative resource map *)

Definition frag_mem_auth (q : Qp) (m : mem) (σ : rmap) : iProp Σ :=
  ⌜coherent m σ⌝ ∧
    resource_map.resource_map_auth
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      (gen_heap_name heapGS_gen_heapGS) q σ.

Lemma frag_mem_auth_set (m : mem) (σ : rmap) (Hvalid : ✓ σ)
  (Hnext : forall loc, (loc.1 >= Mem.nextblock m)%positive -> (σ !! loc = None)%stdpp)
    (Hcoh : forall loc : address, coherent_loc m loc (resource_at σ loc)) :
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
  iSplit; iFrame.
  iPureIntro; intros loc; split; auto.
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
          ⌜access_map_pointwise_eq (perm_of_rmap σ) (getCurPerm m)⌝) ∗
           funspec_auth (init_funspecs m ge G) ∗ inflate_initial_mem_with_rmap m block_bounds ge G.
Proof.
  intros.
  pose proof (rmap_of_mem_with_rmap_valid m block_bounds ge G) as Hvalid.
  pose proof (perm_of_rmap_of_mem_with_rmap_exact m block_bounds ge G Hcover) as Hperm.
  rewrite frag_mem_auth_set //.
  iIntros "(>(Hm & Hr) & Hf)".
  iCombine "Hf Hr" as "Hr"; iMod (rmap_inflate_equiv_with_rmap with "Hr") as "$"; try done.
  { iExists (rmap_of_mem_with_rmap m block_bounds ge G); iFrame; done. }
  { apply rmap_of_mem_with_rmap_nextblock. }
  { intros loc; by apply rmap_of_mem_with_rmap_coherent. }
Qed.
   
(** ** Recovering [initial_core] from the parallel inflated memory *)

Lemma initial_mem_initial_core_with_rmap :
  forall m block_bounds {F} (ge : Genv.t (fundef F) type) G
    (Hm : forall b, (b < nextblock m)%positive ->
              match funspec_of_loc ge G (b, 0) with
              | Some _ =>
                  access_at m (b, 0) Cur = Some Nonempty
              | None => True
              end)
    (Hbounds : forall b, (b < nextblock m)%positive ->
              (block_bounds b).1 <= 0 <= (block_bounds b).1 + Z.of_nat (block_bounds b).2),
    inflate_initial_mem_with_rmap m block_bounds ge G
    ⊢ inflate_initial_mem_with_rmap m block_bounds ge G ∗
      initial_world.initial_core m ge G.
Proof.
  intros.
  rewrite /inflate_initial_mem_with_rmap /initial_world.initial_core.
  iIntros "H"; iSplit; first done.
  iApply big_sepL_absorb.
  iApply (big_sepL_mono with "H").
  intros ?? (-> & ?)%lookup_seq.
  iIntros "H".
  specialize (Hbounds (Pos.of_nat (1 + k)) ltac:(lia)).
  specialize (Hm (Pos.of_nat (1 + k)) ltac:(lia)).
  destruct (block_bounds _) as (lo, hi); simpl in *.
  iPoseProof
    (big_sepL_lookup_acc _ _ (Z.to_nat (-lo)) with "H")
    as "(H & _)".
  { apply lookup_seq; split; first done; lia. }
  replace (lo + _) with 0 by lia.
  rewrite /inflate_loc_with_rmap.
  destruct (funspec_of_loc _ _ _).
  - rewrite Hm //.
  - replace (DfracOwn (Share share_top)) with (ε ⋅ DfracOwn (Share share_top))
      by rewrite left_id //.
    replace (DfracOwn (Share Ews)) with (ε ⋅ DfracOwn (Share Ews)) by rewrite left_id //.
    replace (DfracOwn (Share Ers)) with (ε ⋅ DfracOwn (Share Ers)) by rewrite left_id //.
    destruct (access_at _ _ _); last done.
    destruct p;
      try iDestruct (mapsto_split_no with "H") as "($ & _)";
      simpl; auto;
      try (apply bot_unreadable ||
         apply readable_Ers ||
           apply Lsh_nonreadable).
    iDestruct (mapsto_no_split _ (Share.bot) (Share.Lsh) _ _ (Share.Lsh) with "H") as "($ & _)".
    rewrite share_op_bot //.
    Unshelve.
    + apply (@unreadable_bot _ share_instance).
    + apply Lsh_nonreadable.
Qed.

(** ** Clight initial memories satisfy the coverage condition *)

Notation initial_core_clight m := (initial_world.initial_core m (F := Clight.function)).

Lemma block_bounds_cover_init_mem :
  forall (prog : Clight.program) m (Hnorepet : list_norepet (prog_defs_names prog)) (Hm : Genv.init_mem prog = Some m),
    block_bounds_cover m (block_bounds prog).
Proof.
  intros prog m Hnorepet Hm b ofs p Haccess.
  assert (Hperm : Mem.perm m b ofs Cur p).
  { unfold Mem.perm; rewrite /access_at /= in Haccess.
    rewrite Haccess; apply perm_refl.
  }
  assert (Hb : (b < nextblock m)%positive).
  {
    pose proof Hperm as Hvalid_block.
    apply Mem.perm_valid_block in Hvalid_block.
    apply Hvalid_block.
  }
  eapply init_mem_all in Hb as (id & g & Hin & Hsym); eauto.
  pose proof (prog_defmap_norepet _ _ _ Hnorepet Hin) as Hdef.
  apply Genv.find_def_symbol in Hdef as (b' & Hsym' & Hdef).
  assert (b' = b) as ->.
  { rewrite Hsym' in Hsym; inv Hsym; done. }
  pose proof (Genv.init_mem_characterization_gen prog Hm b Hdef) as Hinit.
  apply find_symbol_globalenv in Hsym as (k & g' & Hnth_idx); last done.
  pose proof Hnth_idx as Hnth_in.
  apply nth_error_In in Hnth_in.
  assert (g' = g) as Hg.
  { eapply list_norepet_In_In; eauto. }
  subst g'.
  erewrite block_bounds_nth by exact Hnth_idx.
  destruct g as [fd | v].
  - destruct Hinit as (_ & Hall).
    specialize (Hall ofs Cur p Hperm) as [-> ->].
    simpl; lia.
  - destruct Hinit as (_ & Hall & _ & _).
    specialize (Hall ofs Cur p Hperm) as [Hlo Hhi].
    simpl.
    rewrite Z2Nat.id; try lia.
Qed.

Lemma initialize_mem_with_rmap' :
  forall (prog : Clight.program) G m (Hnorepet : list_norepet (prog_defs_names prog))
    (Hmatch : match_fdecs (prog_funct prog) G) (Hm : Genv.init_mem prog = Some m),
    mem_auth Mem.empty ∗ funspec_auth ∅
      ⊢ |==>
      (∃ σ : rmap,
          frag_mem_auth 1 m σ ∗ ⌜access_map_pointwise_eq (perm_of_rmap σ) (getCurPerm m)⌝) ∗
      inflate_initial_mem_with_rmap m (block_bounds prog) (Genv.globalenv prog) G ∗
      initial_core_clight m (Genv.globalenv prog) G ∗
      matchfunspecs (Clight.globalenv prog) G.
Proof.
  intros.
  assert (HnorepetG : list_norepet (map fst G)).
  { rewrite -match_fdecs_norepet //.
    apply prog_funct_norepet; auto.
  }
  assert
    (Hfun_access :
       forall b,
         (b < nextblock m)%positive ->
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
      {
        rewrite in_map_iff.
        eexists (_, _); eauto.
      }
      rewrite match_ids // in_map_iff in Hin'.
      destruct Hin' as ((?, ?) & ? & ?); simpl in *; subst.
      erewrite find_id_i by done.
      destruct Hm as (Hperm & Hmax).
      apply perm_mem_access in Hperm
        as (? & Hperm & Haccess).
      destruct (Hmax _ _ _
        (access_perm _ _ _ _ _ Haccess)); subst; done.
    - destruct (find_id id G) eqn:Hfind; last done.
      eapply match_fdecs_exists_Gfun in Hfind
        as (? & Hin' & ?); last done.
      eapply list_norepet_In_In in Hin; eauto; done.
  }
  assert
    (Hfun_bounds : forall b f,
         funspec_of_loc (Genv.globalenv prog) G (b, 0) = Some f ->
         block_bounds prog b = (0, 0%nat)).
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
       forall b,
         (b < nextblock m)%positive ->
         (block_bounds prog b).1 <= 0 <=
         (block_bounds prog b).1 +
           Z.of_nat (block_bounds prog b).2).
  { intros ? Hb.
    eapply init_mem_all in Hb as (id & g & Hin & Hb); eauto.
    apply find_symbol_globalenv in Hb
      as (? & g' & Hnth); last done.
    erewrite block_bounds_nth by done.
    destruct g'; try done; simpl; lia.
  }
  pose proof
    (block_bounds_cover_init_mem prog m Hnorepet Hm)
    as Hcover.
  iIntros "(Hmem & Hf)".
  iMod (initialize_mem_with_rmap m (block_bounds prog) (Genv.globalenv prog)
          G Hcover Hfun_bounds Hfun_access with "[$Hmem $Hf]") as "(Hσ & Hf & Hinflate)".
  iPoseProof (initial_mem_initial_core_with_rmap m (block_bounds prog) (Genv.globalenv prog)
                G Hfun_access Hzero_bounds with "Hinflate") as "(Hinflate & Hcore)".
  iPoseProof (init_funspecs_matchfunspecs with "Hf") as "Hmatchfunspecs".
  iModIntro.
  iFrame.
Qed.

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
  forall (ge : Clight.genv) m0 (v : globvar type) m1 b m2 m3 m4,
    Mem.alloc m0 0 (init_data_list_size (gvar_init v)) = (m1, b) ->
    store_zeros m1 b 0 (init_data_list_size (gvar_init v)) = Some m2 ->
    Genv.store_init_data_list (Clight.genv_genv ge) m2 b 0 (gvar_init v) = Some m3 ->
    Mem.drop_perm m3 b 0 (init_data_list_size (gvar_init v))
              (Genv.perm_globvar v) = Some m4 ->
    forall {F} (gl : list (ident * globdef F type)) i G
      (SANITY : (common.AST.init_data_list_size (gvar_init v) < Ptrofs.modulus)%Z)
      (AL : initializers_aligned 0 (gvar_init v) = true)
      (Hgl : Mem.nextblock m0 = Z.to_pos (Z.succ (Zlength gl))),
      inflate_initial_mem_with_rmap
        m4 (globals_bounds 1 (gl ++ [(i, Gvar v)])) (Clight.genv_genv ge) G
      ⊢
      inflate_initial_mem_with_rmap
      m0 (globals_bounds 1 gl) (Clight.genv_genv ge) G ∗
      if gvar_volatile v then True
      else init_data_list2pred
             (genviron2globals (tycontext.filter_genv ge))
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
      iAssert ([∗ list] o ∈ seq 0 (Z.to_nat (init_data_list_size (gvar_init v))),
                inflate_loc m4 (Clight.genv_genv ge) G (Mem.nextblock m0, (0 + Z.of_nat o)%Z)) with "[Hb]" as "Hb_old".
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

End initial_world_with_rmap_lemmas.
