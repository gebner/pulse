open Prims
let (rt_recheck :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Tactics_NamedView.term ->
        FStar_Reflection_Types.typ ->
          unit ->
            ((unit, unit, unit) FStar_Reflection_Typing.tot_typing, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun gg ->
    fun g ->
      fun e ->
        fun ty ->
          fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (40)) (Prims.of_int (8))
                       (Prims.of_int (40)) (Prims.of_int (42)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (40)) (Prims.of_int (2))
                       (Prims.of_int (42)) (Prims.of_int (58)))))
              (Obj.magic
                 (FStar_Tactics_V2_Builtins.core_check_term g e ty
                    FStar_TypeChecker_Core.E_Total))
              (fun uu___1 ->
                 match uu___1 with
                 | (FStar_Pervasives_Native.Some tok, uu___2) ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 ->
                          FStar_Reflection_Typing.T_Token
                            (g, e, (FStar_TypeChecker_Core.E_Total, ty), ()))
                 | (FStar_Pervasives_Native.None, uu___2) ->
                     FStar_Tactics_V2_Derived.fail
                       "Checker.WithInv: rt_recheck failed")
let (recheck :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.typ ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun ty -> fun uu___ -> Pulse_Checker_Pure.core_check_tot_term g e ty
let (term_remove_inv :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun inv ->
         fun tm ->
           match tm.Pulse_Syntax_Base.t with
           | Pulse_Syntax_Base.Tm_Star (tm1, inv') ->
               if Pulse_Syntax_Base.eq_tm inv inv'
               then
                 Obj.magic
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> tm1))
               else
                 Obj.magic (FStar_Tactics_V2_Derived.fail "term_remove_inv")
           | uu___ ->
               Obj.magic
                 (FStar_Tactics_V2_Derived.fail
                    "term_remove_inv: not a star?")) uu___1 uu___
let (st_comp_remove_inv :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.st_comp ->
      (Pulse_Syntax_Base.st_comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun inv ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                 (Prims.of_int (57)) (Prims.of_int (17)) (Prims.of_int (57))
                 (Prims.of_int (42)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                 (Prims.of_int (57)) (Prims.of_int (4)) (Prims.of_int (58))
                 (Prims.of_int (44)))))
        (Obj.magic (term_remove_inv inv c.Pulse_Syntax_Base.pre))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                            (Prims.of_int (58)) (Prims.of_int (18))
                            (Prims.of_int (58)) (Prims.of_int (44)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                            (Prims.of_int (57)) (Prims.of_int (4))
                            (Prims.of_int (58)) (Prims.of_int (44)))))
                   (Obj.magic (term_remove_inv inv c.Pulse_Syntax_Base.post))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           {
                             Pulse_Syntax_Base.u = (c.Pulse_Syntax_Base.u);
                             Pulse_Syntax_Base.res =
                               (c.Pulse_Syntax_Base.res);
                             Pulse_Syntax_Base.pre = uu___;
                             Pulse_Syntax_Base.post = uu___1
                           })))) uu___)
let (check_iname_disjoint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.range ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r ->
      fun inv_p ->
        fun inames ->
          fun inv ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (63)) (Prims.of_int (13))
                       (Prims.of_int (63)) (Prims.of_int (46)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (63)) (Prims.of_int (49))
                       (Prims.of_int (79)) (Prims.of_int (3)))))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Pulse_Typing.inv_disjointness inv_p inames inv))
              (fun uu___ ->
                 (fun goal ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (65)) (Prims.of_int (4))
                                  (Prims.of_int (65)) (Prims.of_int (61)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (63)) (Prims.of_int (49))
                                  (Prims.of_int (79)) (Prims.of_int (3)))))
                         (Obj.magic
                            (Pulse_Checker_Pure.core_check_term_at_type g
                               goal Pulse_Typing.tm_prop))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | Prims.Mkdtuple2 (tag, goal_typing) ->
                                   if tag <> FStar_TypeChecker_Core.E_Total
                                   then
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_V2_Derived.fail
                                             "Impossible: prop typing is always total"))
                                   else
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.WithInv.fst"
                                                      (Prims.of_int (70))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (70))
                                                      (Prims.of_int (75)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.WithInv.fst"
                                                      (Prims.of_int (71))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (78))
                                                      (Prims.of_int (21)))))
                                             (Obj.magic
                                                (Pulse_Checker_Pure.try_check_prop_validity
                                                   g goal ()))
                                             (fun uu___2 ->
                                                (fun tok ->
                                                   match tok with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (95)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.uu___44
                                                                    inames))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "The set of invariant names: ")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (91)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.uu___44
                                                                    inv))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "may contain the invariant: ")
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___2 ::
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (Pulse_PP.text
                                                                    "Failed to prove that an invariant is not recursively opened:")
                                                                    :: uu___2))))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    r) uu___2))
                                                                    uu___2)))
                                                   | FStar_Pervasives_Native.Some
                                                       tok1 ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  ()))))
                                                  uu___2)))) uu___))) uu___)
let (remove_iname :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun inv_p ->
    fun inames ->
      fun inv ->
        Pulse_Syntax_Base.tm_fstar
          (Pulse_Reflection_Util.remove_inv_tm
             (Pulse_Elaborate_Pure.elab_term inv_p)
             (Pulse_Elaborate_Pure.elab_term inames)
             (Pulse_Elaborate_Pure.elab_term inv))
          inames.Pulse_Syntax_Base.range1
let (add_iname :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun inv_p ->
    fun inames ->
      fun inv ->
        Pulse_Syntax_Base.tm_fstar
          (Pulse_Reflection_Util.add_inv_tm
             (Pulse_Elaborate_Pure.elab_term inv_p)
             (Pulse_Elaborate_Pure.elab_term inames)
             (Pulse_Elaborate_Pure.elab_term inv))
          inames.Pulse_Syntax_Base.range1

let (disjointness_remove_i_i :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun inv_p ->
               fun inames ->
                 fun inv ->
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
            uu___3 uu___2 uu___1 uu___
let (add_remove_inverse :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun inv_p ->
               fun inames ->
                 fun inv ->
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
            uu___3 uu___2 uu___1 uu___
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Checker_Base.check_t ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (134)) (Prims.of_int (52))
                           (Prims.of_int (134)) (Prims.of_int (58)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (133)) (Prims.of_int (46))
                           (Prims.of_int (268)) (Prims.of_int (7)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> t.Pulse_Syntax_Base.term1))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax_Base.Tm_WithInv
                            { Pulse_Syntax_Base.name1 = inv_tm;
                              Pulse_Syntax_Base.body6 = body;
                              Pulse_Syntax_Base.returns_inv = returns_inv;_}
                            ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (138))
                                          (Prims.of_int (19))
                                          (Prims.of_int (138))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (138))
                                          (Prims.of_int (32))
                                          (Prims.of_int (268))
                                          (Prims.of_int (7)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       body.Pulse_Syntax_Base.range2))
                                 (fun uu___1 ->
                                    (fun body_range ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.WithInv.fst"
                                                     (Prims.of_int (139))
                                                     (Prims.of_int (21))
                                                     (Prims.of_int (139))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.WithInv.fst"
                                                     (Prims.of_int (139))
                                                     (Prims.of_int (36))
                                                     (Prims.of_int (268))
                                                     (Prims.of_int (7)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  inv_tm.Pulse_Syntax_Base.range1))
                                            (fun uu___1 ->
                                               (fun inv_tm_range ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (149))
                                                                (Prims.of_int (52))
                                                                (Prims.of_int (149))
                                                                (Prims.of_int (78)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (139))
                                                                (Prims.of_int (36))
                                                                (Prims.of_int (268))
                                                                (Prims.of_int (7)))))
                                                       (Obj.magic
                                                          (Pulse_Checker_Pure.compute_term_type
                                                             g inv_tm))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Pervasives.Mkdtuple4
                                                                 (inv_tm1,
                                                                  eff,
                                                                  inv_tm_ty,
                                                                  inv_tm_typing)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (if
                                                                    eff <>
                                                                    FStar_TypeChecker_Core.E_Total
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    "Ghost effect on inv?"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (match 
                                                                    inv_tm_ty.Pulse_Syntax_Base.t
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_Inv
                                                                    p ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p)))
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_FStar
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Pure.is_fvar_app
                                                                    inv_tm_ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun ropt
                                                                    ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (lid,
                                                                    uu___4,
                                                                    uu___5,
                                                                    FStar_Pervasives_Native.Some
                                                                    tm) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    lid =
                                                                    ["Pulse";
                                                                    "Lib";
                                                                    "Core";
                                                                    "inv"]
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    tm))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inv_tm_ty))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "Does not have invariant type ("
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    ")")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    uu___7))
                                                                    uu___7))))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inv_tm_ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Does not have invariant type ("
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ")")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    uu___5))
                                                                    uu___5))))
                                                                    uu___4)))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    inv_tm_ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Does not have invariant type ("
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ")")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (inv_tm1.Pulse_Syntax_Base.range1))
                                                                    uu___4))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    inv_p ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g inv_p
                                                                    Pulse_Syntax_Base.tm_vprop
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    inv_p_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.tm_star
                                                                    pre inv_p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun pre'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g pre'
                                                                    Pulse_Syntax_Base.tm_vprop
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pre'_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (match 
                                                                    (returns_inv,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    p) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    p)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b, p),
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Base.intro_post_hint
                                                                    g
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b.Pulse_Syntax_Base.binder_ty))
                                                                    p))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (uu___3,
                                                                    p),
                                                                    FStar_Pervasives_Native.Some
                                                                    q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.uu___44
                                                                    p))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "First postcondition:")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.uu___53
                                                                    q))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Second postcondition:")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5]))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___4 ::
                                                                    uu___5))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (FStar_Pprint.doc_of_string
                                                                    "Fatal: multiple annotated postconditions on with_invariant")
                                                                    :: uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___4))
                                                                    uu___4)))
                                                                    | 
                                                                    (uu___3,
                                                                    uu___4)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    "Fatal: no post hint on with_invariant")))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun post
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.tm_star
                                                                    post.Pulse_Typing.post
                                                                    inv_p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post_p'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Elaborate_Pure.elab_term
                                                                    post.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    elab_ret_ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    post.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.elab_env
                                                                    g'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun r_g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (rt_recheck
                                                                    g' r_g'
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post_p'
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x)))
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    Pulse_Syntax_Base.tm_vprop)
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post_p'_typing_src
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (119)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post_p'_typing
                                                                    ->
                                                                    match 
                                                                    post.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    [
                                                                    FStar_Pprint.doc_of_string
                                                                    "Cannot open invariants in a 'ghost' context"]))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Not yet handling inference of with_invariants in an stt context"))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens
                                                                    = opens;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    remove_iname
                                                                    inv_p
                                                                    opens
                                                                    inv_tm1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    opens_remove_i
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens
                                                                    =
                                                                    opens_remove_i
                                                                    }))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    effect_annot
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing.post_hint_typing
                                                                    g post
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)).Pulse_Typing.effect_annot_typing1)
                                                                    uu___3))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    opens_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    ())
                                                                    uu___3))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    effect_annot_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g
                                                                    post.Pulse_Typing.ret_ty
                                                                    (Pulse_Syntax_Pure.tm_type
                                                                    post.Pulse_Typing.u)
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = g;
                                                                    Pulse_Typing.effect_annot
                                                                    =
                                                                    effect_annot;
                                                                    Pulse_Typing.effect_annot_typing
                                                                    =
                                                                    effect_annot_typing;
                                                                    Pulse_Typing.ret_ty
                                                                    =
                                                                    (post.Pulse_Typing.ret_ty);
                                                                    Pulse_Typing.u
                                                                    =
                                                                    (post.Pulse_Typing.u);
                                                                    Pulse_Typing.ty_typing
                                                                    = ();
                                                                    Pulse_Typing.post
                                                                    = post_p';
                                                                    Pulse_Typing.x
                                                                    = x;
                                                                    Pulse_Typing.post_typing_src
                                                                    = ();
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "with_inv_body"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (check1 g
                                                                    pre' ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post')
                                                                    ppname
                                                                    body))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g pre'
                                                                    post' r
                                                                    ppname))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    c_body))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    obs, st)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    (st_comp_remove_inv
                                                                    inv_p st))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    obs,
                                                                    uu___5)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    c_out ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (disjointness_remove_i_i
                                                                    g inv_p
                                                                    opens
                                                                    inv_tm1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun tok
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = inv_tm1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (t.Pulse_Syntax_Base.range2);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_effect_annot
                                                                    post.Pulse_Typing.effect_annot)))
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_WithInv
                                                                    (g,
                                                                    inv_tm1,
                                                                    inv_p,
                                                                    (), (),
                                                                    body1,
                                                                    c_out,
                                                                    body_typing,
                                                                    ())))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.add_iname_at_least_unobservable
                                                                    c_out
                                                                    inv_p
                                                                    inv_tm1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    c_out1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    c_out1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs',
                                                                    st1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (add_remove_inverse
                                                                    g inv_p
                                                                    opens
                                                                    inv_tm1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun tok1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g,
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Atomic)
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = inv_tm1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (Pulse_Typing.add_iname_at_least_unobservable
                                                                    c_out
                                                                    inv_p
                                                                    inv_tm1),
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs',
                                                                    st1)), d,
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st1,
                                                                    add_inv,
                                                                    opens,
                                                                    obs',
                                                                    obs', ())))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs',
                                                                    st1)),
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                            uu___1))) uu___1)))
                                      uu___1))) uu___)