open Prims
type 'l no_repeats = Obj.t
type ss_dom = Pulse_Syntax_Base.var Prims.list
type ss_map = (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t
let (remove_map :
  ss_map ->
    Pulse_Syntax_Base.var ->
      (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t)
  =
  fun m ->
    fun x ->
      FStar_Map.restrict (FStar_Set.complement (FStar_Set.singleton x))
        (FStar_Map.upd m x Pulse_Syntax_Base.tm_unknown)
type ('l, 'm) is_dom = Obj.t
type ss_t = {
  l: ss_dom ;
  m: ss_map }
let (__proj__Mkss_t__item__l : ss_t -> ss_dom) =
  fun projectee -> match projectee with | { l; m;_} -> l
let (__proj__Mkss_t__item__m : ss_t -> ss_map) =
  fun projectee -> match projectee with | { l; m;_} -> m
let (as_map :
  ss_t -> (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t) =
  fun ss -> ss.m
let (dom : ss_t -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun ss -> FStar_Map.domain (as_map ss)
let (contains : ss_t -> Pulse_Syntax_Base.var -> Prims.bool) =
  fun ss -> fun x -> FStar_Map.contains (as_map ss) x
let (sel : ss_t -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun ss -> fun x -> FStar_Map.sel (as_map ss) x
type ('ss, 'uvs) solves = unit
let (empty : ss_t) =
  {
    l = [];
    m =
      (FStar_Map.const_on (FStar_Set.empty ()) Pulse_Syntax_Base.tm_unknown)
  }
let (push :
  Pulse_Typing_Env.env ->
    ss_t -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term -> ss_t)
  =
  fun uvs ->
    fun ss ->
      fun x -> fun t -> { l = (x :: (ss.l)); m = (FStar_Map.upd ss.m x t) }
let (tail : ss_t -> ss_t) =
  fun ss ->
    {
      l = (FStar_List_Tot_Base.tl ss.l);
      m = (remove_map ss.m (FStar_List_Tot_Base.hd ss.l))
    }
let rec (push_ss : Pulse_Typing_Env.env -> ss_t -> ss_t -> ss_t) =
  fun uvs ->
    fun ss1 ->
      fun ss2 ->
        match ss2.l with
        | [] -> ss1
        | x::tl ->
            push_ss uvs (push uvs ss1 x (FStar_Map.sel ss2.m x)) (tail ss2)
let rec (remove_l : ss_dom -> Pulse_Syntax_Base.var -> ss_dom) =
  fun l ->
    fun x ->
      match l with
      | [] -> []
      | y::tl -> if y = x then tl else y :: (remove_l tl x)
let rec (ss_term : Pulse_Syntax_Base.term -> ss_t -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun ss ->
      match ss.l with
      | [] -> t
      | y::tl ->
          let t1 =
            Pulse_Syntax_Naming.subst_term t
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_term t1 (tail ss)
let rec (ss_st_term :
  Pulse_Syntax_Base.st_term -> ss_t -> Pulse_Syntax_Base.st_term) =
  fun t ->
    fun ss ->
      match ss.l with
      | [] -> t
      | y::tl ->
          let t1 =
            Pulse_Syntax_Naming.subst_st_term t
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_st_term t1 (tail ss)
let rec (ss_st_comp :
  Pulse_Syntax_Base.st_comp -> ss_t -> Pulse_Syntax_Base.st_comp) =
  fun s ->
    fun ss ->
      match ss.l with
      | [] -> s
      | y::tl ->
          let s1 =
            Pulse_Syntax_Naming.subst_st_comp s
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_st_comp s1 (tail ss)
let rec (ss_comp : Pulse_Syntax_Base.comp -> ss_t -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun ss ->
      match ss.l with
      | [] -> c
      | y::tl ->
          let c1 =
            Pulse_Syntax_Naming.subst_comp c
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_comp c1 (tail ss)
let rec (ss_binder :
  Pulse_Syntax_Base.binder -> ss_t -> Pulse_Syntax_Base.binder) =
  fun b ->
    fun ss ->
      match ss.l with
      | [] -> b
      | y::tl ->
          let b1 =
            Pulse_Syntax_Naming.subst_binder b
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_binder b1 (tail ss)
let rec (ss_env : Pulse_Typing_Env.env -> ss_t -> Pulse_Typing_Env.env) =
  fun g ->
    fun ss ->
      match ss.l with
      | [] -> g
      | y::tl ->
          ss_env
            (Pulse_Typing_Metatheory.subst_env g
               [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))])
            (tail ss)
type nt_substs = Pulse_Syntax_Naming.subst_elt Prims.list
let (nt_subst_term :
  Pulse_Syntax_Base.term -> nt_substs -> Pulse_Syntax_Base.term) =
  fun t ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun t1 -> fun elt -> Pulse_Syntax_Naming.subst_term t1 [elt]) t ss
let (nt_subst_binder :
  Pulse_Syntax_Base.binder -> nt_substs -> Pulse_Syntax_Base.binder) =
  fun b ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun b1 -> fun elt -> Pulse_Syntax_Naming.subst_binder b1 [elt]) b ss
let (nt_subst_st_term :
  Pulse_Syntax_Base.st_term -> nt_substs -> Pulse_Syntax_Base.st_term) =
  fun t ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun t1 -> fun elt -> Pulse_Syntax_Naming.subst_st_term t1 [elt]) t
        ss
let (nt_subst_st_comp :
  Pulse_Syntax_Base.st_comp -> nt_substs -> Pulse_Syntax_Base.st_comp) =
  fun s ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun s1 -> fun elt -> Pulse_Syntax_Naming.subst_st_comp s1 [elt]) s
        ss
let (nt_subst_comp :
  Pulse_Syntax_Base.comp -> nt_substs -> Pulse_Syntax_Base.comp) =
  fun c ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun c1 -> fun elt -> Pulse_Syntax_Naming.subst_comp c1 [elt]) c ss
type ('g, 'uvs, 'nts) well_typed_nt_substs = Obj.t
type ('uuuuu, 'nts, 'ss) is_permutation = Obj.t
let rec (ss_to_nt_substs :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      ss_t ->
        (nt_substs FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun uvs ->
             fun ss ->
               match Pulse_Typing_Env.bindings uvs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.Some [])))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Substs.fst"
                                    (Prims.of_int (206)) (Prims.of_int (26))
                                    (Prims.of_int (206)) (Prims.of_int (44)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Substs.fst"
                                    (Prims.of_int (205)) (Prims.of_int (8))
                                    (Prims.of_int (220)) (Prims.of_int (13)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Typing_Env.remove_binding uvs))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | (x, ty, rest_uvs) ->
                                     if FStar_Map.contains ss.m x
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Prover.Substs.fst"
                                                        (Prims.of_int (208))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (208))
                                                        (Prims.of_int (31)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Prover.Substs.fst"
                                                        (Prims.of_int (208))
                                                        (Prims.of_int (34))
                                                        (Prims.of_int (219))
                                                        (Prims.of_int (19)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Map.sel ss.m x))
                                               (fun uu___2 ->
                                                  (fun t ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Prover.Substs.fst"
                                                                   (Prims.of_int (209))
                                                                   (Prims.of_int (37))
                                                                   (Prims.of_int (209))
                                                                   (Prims.of_int (45)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Prover.Substs.fst"
                                                                   (Prims.of_int (210))
                                                                   (Prims.of_int (48))
                                                                   (Prims.of_int (219))
                                                                   (Prims.of_int (19)))))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                ()))
                                                          (fun uu___2 ->
                                                             (fun d ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Substs.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Substs.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (ss_to_nt_substs
                                                                    g
                                                                    (Pulse_Typing_Metatheory.subst_env
                                                                    rest_uvs
                                                                    [
                                                                    Pulse_Syntax_Naming.NT
                                                                    (x, t)])
                                                                    {
                                                                    l =
                                                                    (remove_l
                                                                    ss.l x);
                                                                    m =
                                                                    (remove_map
                                                                    ss.m x)
                                                                    }))
                                                                    (fun
                                                                    nts_opt
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match nts_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    nts ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((Pulse_Syntax_Naming.NT
                                                                    (x, t))
                                                                    :: nts)))))
                                                               uu___2)))
                                                    uu___2)))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  FStar_Pervasives_Native.None))))
                                uu___1)))) uu___2 uu___1 uu___