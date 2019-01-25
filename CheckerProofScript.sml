open preamble CheckerSpecTheory CheckerTheory
open ratTheory
                                       
val _ = new_theory "CheckerProof";

val list_MEM_dec_thm = Q.store_thm("list_MEM_dec_thm",
  `list_MEM_dec = list_MEM`,
  simp[FUN_EQ_THM]
  \\ Induct \\ rw[list_MEM_dec_def]);
 
 
val EWIN_thm = Q.store_thm("EWIN_thm",
  `EwinDec = EWIN`,
  simp[FUN_EQ_THM]
  \\ qx_gen_tac`params`
  \\ PairCases_on`params`
  \\ Cases \\ Cases
  \\ rw[EWIN_def,EwinDec_def]
  \\ PairCases_on`p`
  \\ rw[EWIN_def,EwinDec_def]
  \\ metis_tac[]);
  
val HWIN_thm = Q.store_thm("HWIN_thm",
  `HwinDec = HWIN`, 
  simp[FUN_EQ_THM]
  \\ qx_gen_tac`params`
  \\ PairCases_on`params`
  \\ Cases \\ Cases \\ rw[HWIN_def,HwinDec_def]
  \\ PairCases_on`p`
  \\ rw[HWIN_def,HwinDec_def]
  \\ metis_tac[HWIN_def,HwinDec_def])
  
val GET_CAND_TALLY_HEAD_REMOVAL_def = Q.store_thm ("GET_CAND_TALLY_HEAD_REM",
`!(h: cand #rat) t c. (~(c = FST h)) ==> (get_cand_tally c (h::t) = get_cand_tally c t)`,
          Induct_on `t `
               >- (rw[get_cand_tally_def] >>
                   Cases_on`h` >> fs[ALOOKUP_def])

               >- (REPEAT STRIP_TAC
                 >> first_assum (qspecl_then [`h`,`c`] strip_assume_tac)
                    >> rw[get_cand_tally_def] >>
                    Cases_on`h'` >> fs[ALOOKUP_def]))
 
val GET_CAND_TALLY_MEM2 = Q.store_thm ("GET_CAND_TALLY_MEM",
 `!(t: (cand #rat) list) c. (MEM c (MAP FST t))
                                    ==> (MEM (c, get_cand_tally c t) t) `,

    Induct_on `t`
        >- rw []

        >- ((REPEAT STRIP_TAC >> Cases_on `h` >> Cases_on `c =q`)
          >- fs[get_cand_tally_def,ALOOKUP_def]
	  >- fs[get_cand_tally_def,ALOOKUP_def]));
  
val PileTally_to_PileTally_DEC1 = Q.store_thm ("PileTally_to_PileTally_DEC1",
 `!l t. (!c. (MEM c (MAP FST t)) ==> (MEM c l)) ==> (Valid_PileTally_dec1 t l) `,

    Induct_on `t`
       >- rw [Valid_PileTally_dec1_def]
       >- (REPEAT STRIP_TAC
          >> first_assum (qspecl_then [`FST h`] strip_assume_tac)
            >> rfs[Valid_PileTally_dec1_def,MAP]));
  
val PileTally_DEC1_to_PileTally = Q.store_thm ("PileTally_DEC1_to_PileTally",
 `!l t. (Valid_PileTally_dec1 t l) ==> (!c. MEM c (MAP FST t) ==> (MEM c l))`,

    Induct_on `t`
        >- rw[]
        >- (REPEAT STRIP_TAC
            >> rfs [Valid_PileTally_dec1_def]));
  
val PileTally_to_PileTally_DEC2 = Q.store_thm ("PileTally_to_PileTally_DEC2",
   `!l t. (!c. (MEM c l) ==> (MEM c (MAP FST t))) ==> (Valid_PileTally_dec2 t l) `,

     Induct_on `l`
        >- rw [Valid_PileTally_dec2_def]
        >- rfs [Valid_PileTally_dec2_def]);
 

val PileTally_DEC2_IMP_PileTally = Q.store_thm ("PileTally_DEC2_IMP_PileTally",
  `!l t. (Valid_PileTally_dec2 t l) ==> (!c. (MEM c l) ==> (MEM c (MAP FST t)))`,

      Induct_on `l`
         >- rw []
         >- ((REPEAT STRIP_TAC
           >> FULL_SIMP_TAC list_ss [MEM])
              >- FULL_SIMP_TAC list_ss [Valid_PileTally_dec2_def]
              >- rfs [Valid_PileTally_dec2_def]));
    
val Valid_PileTally_Spec_iff_Valid_PileTally_DEC = Q.store_thm ("Valid_PileTally_Spec_iff_Valid_PileTally_DEC",
 `!l t. Valid_PileTally t l <=> (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)`,
   metis_tac[Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,PileTally_DEC2_IMP_PileTally]);
     
val REMOVE_ONE_CAND_APPEND = Q.store_thm ("REMOVE_ONE_CAND_APPEND",
 `! l1 l2 (c: cand). (~ MEM c l1) ==> (equal_except_dec c (l1 ++l2) = l1 ++ (equal_except_dec c l2))`,

   Induct_on `l1`
       >- RW_TAC list_ss [APPEND_NIL,equal_except_dec_def]
       >- (REPEAT STRIP_TAC
         >> first_assum (qspecl_then [`l2`,`c`] strip_assume_tac)
           >> FULL_SIMP_TAC list_ss [MEM,equal_except_dec_def]));
 
val REMOVE_ONE_CAND_NOTIN = Q.store_thm ("REMOVE_ONE_CAND_NOTIN",
 `!l (c: cand). (~ MEM c l) ==> (equal_except_dec c l = l) `,

    Induct_on `l`
        >- rw [equal_except_dec_def]
        >- (REPEAT STRIP_TAC
          >> FULL_SIMP_TAC list_ss [MEM, equal_except_dec_def])) ;
 
val EQE_REMOVE_ONE_CAND = Q.store_thm ("EQE_REMOVE_ONE_CAND",
  `!h (c: cand). (MEM c h) /\ (ALL_DISTINCT h) ==> (equal_except c (equal_except_dec c h) h) `,

 Induct_on `h`

   >-  rw[]
   >-  ((REPEAT STRIP_TAC
      >> Cases_on `c= h'`)
        >- (rw[equal_except_dec_def,equal_except_def]
          >> MAP_EVERY qexists_tac [`[]`,`h`]
	  >> FULL_SIMP_TAC list_ss [ALL_DISTINCT])
        >-  ((rw[equal_except_dec_def,equal_except_def]
           >> `ALL_DISTINCT h` by fs[ALL_DISTINCT]
            >> `equal_except c (equal_except_dec c h) h` by metis_tac [ALL_DISTINCT,MEM]
             >> rfs[equal_except_def])
              >-  rw[]
              >- (MAP_EVERY qexists_tac [`h'::l1`,`l2`]
                >> FULL_SIMP_TAC list_ss []))));
 
val EQE_IMP_REMOVE_ONE_CAND = Q.store_thm ("EQE_IMP_REMOVE_ONE_CAND",
 `!h1 h2 (c: cand). (MEM c h2) /\ (equal_except c h1 h2) ==> (h1 = equal_except_dec c h2) `,

   FULL_SIMP_TAC list_ss [equal_except_def]
    >> REPEAT STRIP_TAC
     >>  ASSUME_TAC REMOVE_ONE_CAND_APPEND
         >> first_assum (qspecl_then [`l1`,`[c]++l2`,`c`] strip_assume_tac)
             >> rfs [equal_except_dec_def]);
 
val APPEND_NIL_LEFT = Q.store_thm ("APPEND_NIL_LEFT",
                                                `!l. [] ++ l = l `,
                                                       STRIP_TAC >> EVAL_TAC) ;

val APPEND_NIL_LEFT_COR = Q.store_thm("APPEND_NIL_lEFT_COR",
                                             `!h t. [] ++ (h::t) = h::t `,
                                                   rw[APPEND_NIL_LEFT]) ;
 

val MAP_APPEND_TRIO = Q.store_thm ("MAP_APPEND_TRIO",
  `!t l1 l0 l2. (t = l1 ++ [l0] ++ l2) ==> (MAP FST t = (MAP FST l1) ++ [FST l0] ++ (MAP FST l2))`,

     REPEAT STRIP_TAC
          >> `l1 ++ [l0] ++ l2 = l1 ++([l0] ++ l2)` by FULL_SIMP_TAC list_ss [APPEND_ASSOC]
            >> RW_TAC bool_ss []
              >> rfs [MAP_APPEND]);

val NoDupCand_BOTH_SIDES= Q.store_thm ("NoDupCand_BOTH_SIDES",
 `!l1 l2 (c:cand) (h1: cand list) h2. (l1 ++ [c] ++ l2 = h1 ++ [c] ++ h2)
                                      /\ (~ MEM c h1) /\ (~ MEM c h2) ==> (~ MEM c l1) `,

    Induct_on `l1`
         >- rw []
         >- ((REPEAT STRIP_TAC >>
               Cases_on `h1`)

               >-   (rfs[APPEND,CONS_11]
                    >> RW_TAC bool_ss []
                      >> rfs[])

               >-   (rfs[CONS_11]
                    >> first_assum (qspecl_then [`l2`,`c`,`t`,`h2`] strip_assume_tac)
                      >> rfs[])));
  
val get_cand_tally_APPEND = Q.store_thm ("get_cand_tally_APPEND",
  `!(l1: (cand #rat) list) l2 c. (~ MEM c (MAP FST l1))
                                  ==> (get_cand_tally c (l1++l2) = get_cand_tally c l2) `,

      Induct_on `l1`
           >- rw[APPEND_NIL,get_cand_tally_def] >>
	      Cases_on `h`
           >- (REPEAT STRIP_TAC >>
               `c <> q` by fs[MEM,MAP] >>
               fs[get_cand_tally_def,ALOOKUP_def]))


val EVERY_CAND_HAS_ONE_TALLY = Q.store_thm ("EVERY_CAND_HAS_ONE_TALLY",
  `!t c (x: rat). (ALL_DISTINCT (MAP FST t)) /\ (MEM (c,x) t) ==> (get_cand_tally c t = x) `,

      REPEAT STRIP_TAC
           >>  FULL_SIMP_TAC list_ss [MEM_SPLIT]
               >>
               ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] ALL_DISTINCT_APPEND)
               >> first_assum (qspecl_then [`MAP FST l1`,`MAP FST ([(c,x)] ++ l2)`] strip_assume_tac)
               >> `ALL_DISTINCT ((MAP FST l1) ++ (MAP FST ([(c,x)] ++ l2)))`
	        by FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, MAP_APPEND]
               >> `!e. MEM e (MAP FST l1) ==> (~ MEM e (MAP FST ([(c,x)] ++ l2)))` by metis_tac[]
               >> `MEM c (MAP FST ([(c,x)] ++ l2))` by FULL_SIMP_TAC list_ss [MAP_APPEND]
               >> `~ MEM c (MAP FST l1)` by metis_tac[]
	       >> fs[get_cand_tally_APPEND,get_cand_tally_def,ALOOKUP_def])
  
val LESS_THAN_QUOTA_OK = Q.store_thm ("LESS_THAN_QUOTA_OK",
`!qu t0 t1 h. (less_than_quota qu (t0::t1) h) ==> (!c.(MEM c h) ==> (get_cand_tally c (t0::t1) < qu))`,

    Induct_on `h`
       >- rw []
       >- (REPEAT STRIP_TAC
         >> FULL_SIMP_TAC list_ss [MEM,less_than_quota_def,get_cand_tally_def]));
 
val less_than_qu_IMP_LogicalLessThanQuota = Q.store_thm ("less_than_qu_IMP_LogicalLessThanQuota",
 `!h t0 t1 (qu:rat). (less_than_quota qu (t0::t1) h) /\ (Valid_PileTally_dec2 (t0::t1) h) ==>
           (!c. (MEM c h) ==> ?x. (MEM (c,x) (t0::t1)) /\ (x < qu))`,

       Induct_on `h`
          >- rw []
          >- ((REPEAT STRIP_TAC
            >> FULL_SIMP_TAC bool_ss [MEM])
             >- ((ASSUME_TAC (INST_TYPE [alpha |-> ``:rat``] PileTally_DEC2_IMP_PileTally)
                >> first_x_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac)
                  >> `!c. MEM c (h'::h) ==> (MEM c (MAP FST (t0::t1))) ` by metis_tac []
                     >> `!(h: (cand#rat)) t c. (MEM c (MAP FST (h::t)))
                                 ==> (MEM (c,get_cand_tally c (h::t)) (h::t))`
                        by (ASSUME_TAC GET_CAND_TALLY_MEM2
                         >> REPEAT STRIP_TAC
                         >> first_x_assum (qspecl_then [`h''::t`,`c'`] strip_assume_tac)
                         >> rw [])
                          >> first_assum (qspecl_then [`h'`] strip_assume_tac)
                            >> first_assum (qspecl_then [`t0`,`t1`,`h'`] strip_assume_tac) >> rfs[])
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`
                               >> rfs [less_than_quota_def])
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`
                              >> rw [] >> ASSUME_TAC LESS_THAN_QUOTA_OK
                               >> first_x_assum (qspecl_then [`qu`,`t0`,`t1`,`c::h`] strip_assume_tac)
                                >> rfs []))
             >- (first_assum (qspecl_then [`t0`,`t1`,`qu`] strip_assume_tac)
               >> rfs [less_than_quota_def,Valid_PileTally_dec2_def])));
 
val LogicalLessThanQu_IMP_less_than_quota =Q.store_thm ("LogicalLessThanQu_IMP_less_than_quota",
  `!(qu:rat) t h. (!c. (MEM c h) ==> ?x. (MEM (c,x) t)
                                       /\ (x < qu)) /\ (ALL_DISTINCT (MAP FST t))
                                       /\ (!c''. (MEM c'' h) ==> (MEM c'' (MAP FST t)))
                                   ==> (less_than_quota qu t h)`,

   Induct_on `h`
     >- rw [less_than_quota_def]
     >- ((REPEAT STRIP_TAC >>
        rw[less_than_quota_def])
          >- (`?x. (MEM (h',x) t) /\ (x < qu)` by metis_tac[MEM]
           >> `MEM h' (MAP FST t)` by metis_tac[MEM]
             >> `MEM (h', get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                 >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY
                 >> `get_cand_tally h' t = x` by rfs [EVERY_CAND_HAS_ONE_TALLY]
                   >> metis_tac [])
        >- (`less_than_quota qu t h` by  metis_tac[MEM]
           >> fs[less_than_quota_def])))
  
val bigger_than_cand_OK = Q.store_thm ("bigger_than_cand_OK",
 `!c t h. (bigger_than_cand c t h) ==> (!d. (MEM d h) ==> (get_cand_tally c t <= get_cand_tally d t))`,

      Induct_on `h`
          >- rw []
          >- (REPEAT STRIP_TAC
            >> FULL_SIMP_TAC list_ss [MEM,bigger_than_cand_def]));

val bigger_than_cand_LogicallyOK = Q.store_thm ("bigger_than_cand_LogicallyOK",
 `!h (t0: cand #rat) t1 c. (bigger_than_cand c (t0::t1) h)
                        /\ (Valid_PileTally_dec2 (t0::t1) h) /\ (MEM c h) ==>
   (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) (t0::t1)) /\ (MEM (d,y) (t0::t1)) /\ (x <= y)))`,

     Induct_on `h`
        >- rw []
        >- (REPEAT STRIP_TAC
          >> ASSUME_TAC (INST_TYPE [alpha |-> ``:rat``] PileTally_DEC2_IMP_PileTally)
            >> first_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac)
              >> `!c'. (MEM c' (h'::h)) ==> (MEM c' (MAP FST (t0::t1)))` by metis_tac []
                >> first_assum (qspecl_then [`c`] strip_assume_tac)
                  >> first_assum (qspecl_then [`d`] strip_assume_tac)
                    >> `MEM (c,get_cand_tally c (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]
                      >> `MEM (d,get_cand_tally d (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]
                       >> MAP_EVERY qexists_tac [`get_cand_tally c (t0::t1)`,`get_cand_tally d (t0::t1)`]
                         >> RW_TAC list_ss []
                           >> ASSUME_TAC bigger_than_cand_OK
                             >> first_assum (qspecl_then [`c`,`t0::t1`,`h'::h`] strip_assume_tac)
                               >> metis_tac []));
  
val Logical_bigger_than_cand_IMP_TheFunctional = Q.store_thm ("Logical_bigger_than_cand_IMP_TheFunctional",
 `!h t c. (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) t)
                                                  /\ (MEM (d,y) t) /\ (x <= y)))
                                                  /\ (ALL_DISTINCT (MAP FST t))
                                                  /\ (MEM c (MAP FST t))
                                                  /\ (!d''. (MEM d'' h) ==> (MEM d'' (MAP FST t)))
                                                 ==> (bigger_than_cand c t h)`,

    Induct_on `h`
        >- rw [bigger_than_cand_def]
        >- ((REPEAT STRIP_TAC
             >> rw[bigger_than_cand_def])
               >-( `?x y. (MEM (c,x) t) /\ (MEM (h',y) t) /\ (x <= y) ` by metis_tac [MEM]
                >> `MEM c (MAP FST t)` by metis_tac [MEM]
                 >> `MEM (c,get_cand_tally c t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                   >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY
                   >> `x = get_cand_tally c t` by rfs []
                    >> `MEM h' (MAP FST t)` by metis_tac [MEM]
                     >> `MEM (h',get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                      >> `y = get_cand_tally h' t ` by rfs []
                       >> RW_TAC bool_ss [])
             >-( first_assum(qspecl_then [`t`,`c`] strip_assume_tac)
               >> rfs[bigger_than_cand_def,MEM])));

val SUBPILE_ONE_HEAD_REMOVAL = Q.store_thm ("SUBPILE_ONE_HEAD_REMOVAL",
 `! p1 p2 c h. (subpile1 c (h::p1) p2) ==> (subpile1 c p1 p2)`,
  rw[subpile1_def]);
 
 
val Functional_subpile1_IMP_TheLogical = Q.store_thm ("Functional_subpile1_IMP_TheLogical",
 `!p1 p2 c. (subpile1 c p1 p2) ==>  (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p1 ==> MEM (d',l) p2))))`,

     Induct_on `p1`
        >- rw[]
        >- ((REPEAT STRIP_TAC
          >> FULL_SIMP_TAC list_ss [MEM])
            >- (`d' = FST h` by RW_TAC bool_ss [PAIR_EQ,FST]
              >> `c <> FST h` by RW_TAC bool_ss []
                >> FULL_SIMP_TAC list_ss [subpile1_def])
            >- (first_assum (qspecl_then [`p2`,`c`] strip_assume_tac)
              >> metis_tac[SUBPILE_ONE_HEAD_REMOVAL])));
 
  
val GET_CAND_PILE_MEM = Q.store_thm ("GET_CAND_PILE_MEM",
 `!(p:piles) c. (MEM c (MAP FST p))
                          ==> (MEM (c,get_cand_pile c p) p)`,

        Induct_on `p`
             >-  rw []
               >- ((REPEAT STRIP_TAC
                 >>Cases_on `c = FST h`)

                 >- (Cases_on `h`
                   >> fs[get_cand_pile_def,ALOOKUP_def,MEM])

                 >- (Cases_on `h`
                   >> rfs [get_cand_pile_def,ALOOKUP_def,MEM,MAP]
                     >> rw[])));
  
val get_cand_pile_APPEND = Q.store_thm ("get_cand_pile_APPEND",
 `! (l1: piles) l2 c. (~ MEM c (MAP FST l1))
                           ==> (get_cand_pile c (l1++l2) = get_cand_pile c l2)`,

     Induct_on `l1`
        >-  rw []
        >- (REPEAT STRIP_TAC >>
	      Cases_on `h` >> FULL_SIMP_TAC list_ss [ALOOKUP_def,MEM,MAP,get_cand_pile_def]));
 
val EVERY_CAND_HAS_ONE_PILE = Q.store_thm ("EVERY_CAND_HAS_ONE_PILE",
 `! p c (y: (((cand list) # rat) list) list). (ALL_DISTINCT (MAP FST p)) /\ (MEM (c,y) p)
                          ==> (get_cand_pile c p = y)`,

      (REPEAT STRIP_TAC
      >> FULL_SIMP_TAC list_ss [MEM_SPLIT]

               >> ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] ALL_DISTINCT_APPEND)
               >> first_assum (qspecl_then [`MAP FST l1`,`MAP FST ([(c,x)] ++ l2)`] strip_assume_tac)
               >> `ALL_DISTINCT ((MAP FST l1) ++ (MAP FST ([(c,x)] ++ l2)))`
	        by FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, MAP_APPEND]
               >> `!e. MEM e (MAP FST l1) ==> (~ MEM e (MAP FST ([(c,x)] ++ l2)))` by metis_tac[]
               >> `MEM c (MAP FST ([(c,x)] ++ l2))` by FULL_SIMP_TAC list_ss [MAP_APPEND]
               >> `~ MEM c (MAP FST l1)` by metis_tac[]
               >> ASSUME_TAC get_cand_pile_APPEND
               >> first_assum (qspecl_then [`l1`,`(c,y)::l2`] strip_assume_tac)
               >>  fs [get_cand_pile_def,get_cand_pile_APPEND,ALOOKUP_def]));
  
 
val Logical_subpile1_IMP_TheFunctional = Q.store_thm ("Logical_subpile1_IMP_TheFunctional",
 `! p1 p2 c. (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p1 ==> MEM (d',l) p2)))
                /\ ((d' = c) ==> (MEM (c,[]) p2))) ==> (subpile1 c p1 p2)`,

         Induct_on `p1`
           >- rw[subpile1_def] 
           >- ((REPEAT STRIP_TAC 
             >>  rw[subpile1_def]) 
               >-( Cases_on `c = FST h`
                   >- RW_TAC bool_ss []
                   >- (first_assum (qspecl_then [`FST h`] strip_assume_tac)
		       >> fs[]))
          >- rfs[subpile1_def]

          >- (first_assum (qspecl_then [`FST h`] strip_assume_tac)
            >> rfs[]
            >> ` (FST h,SND h) = h` by rfs[PAIR]
             >> `MEM (FST h, SND h) p2` by metis_tac[PAIR,PAIR_EQ]
               >> fs[])
       >- rfs[subpile1_def]));
  
val SUBPILE_TWO_HEAD_REMOVAL = Q.store_thm ("SUBPILE_TWO_HEAD_REMOVAL",
 `!p1 p2 c h. (subpile2 c (h::p2) p1) ==> (subpile2 c p2 p1) `,
 rw[subpile2_def]);

 
val Functional_subpile2_IMP_TheLogical = Q.store_thm ("Functional_subpile2_IMP_TheLogical",
 `!p1 p2 c. (subpile2 c p2 p1) ==>  (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p2 ==> MEM (d',l) p1))))`,

    Induct_on `p2`
        >- rw []
        >- ((REPEAT STRIP_TAC
          >> FULL_SIMP_TAC bool_ss [MEM])
             >- (`d' = FST h` by RW_TAC bool_ss [PAIR_EQ,FST]
               >> `c <> FST h` by RW_TAC bool_ss []
                 >>  RW_TAC bool_ss [subpile2_def]
                   >> FULL_SIMP_TAC list_ss [subpile2_def])
             >- (first_assum (qspecl_then [`p1`,`c`] strip_assume_tac)
               >> metis_tac [SUBPILE_TWO_HEAD_REMOVAL])));
 
 
val subpile1_CandPile_Empty = Q.store_thm ("subpile1_CandPile_Empty",
 `!(l: cand list) p1 p2 c. (subpile1 c p1 p2) /\ (MEM c (MAP FST p2))
                                              /\ (MEM c (MAP FST p1))  ==> (MEM (c,[]) p2)`,

Induct_on `p1`
     >- rw[]
   >- ((REPEAT STRIP_TAC
          >> Cases_on `c = FST h`)
          >- (FULL_SIMP_TAC list_ss [subpile1_def]
              >> metis_tac [subpile1_def,MAP,MEM])
         >- fs[subpile1_def,MEM]));
 
val Logical_subpile2_IMP_TheFunctional = Q.store_thm ("Logical_subpile2_IMP_TheFunctional",
 `!p1 p2 c. (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p2 ==> MEM (d',l) p1)))
              /\ ((d' = c) ==> (?l. MEM (c,l) p1))) ==> (subpile2 c p2 p1)`,

      Induct_on `p2`
           >-   rw[subpile2_def]
           >- ((REPEAT STRIP_TAC
	       >> Cases_on `c = FST h`)
                 >-  fs [subpile2_def]
                 >- (fs [subpile2_def]
                     >> first_assum(qspecl_then [`FST h`] strip_assume_tac)
                       >> rfs[]
                        >> `MEM (FST h,SND h) p1` by rfs[PAIR,PAIR_EQ]
                          >> metis_tac[PAIR,PAIR_EQ])));
   
val logical_GetCandPile_IMP_TheFunctional = Q.store_thm ("logical_GetCandPile_IMP_TheFunctional",
 `!(p: piles) nba c. (!d. (d <> c) ==>
   (!l. MEM (d,l) p ==> ~ ((d,l) = (d,nba)))) /\ (!d. (d = c) ==> (!l. MEM (c,l) p /\ ((c,l) = (c,nba))))
/\ MEM c (MAP FST p) ==> (nba = get_cand_pile c p)`,

    Induct_on `p`
        >- rw[]
        >- ((REPEAT STRIP_TAC >>
	     Cases_on `c = FSt h`)
               >- (ASSUME_TAC GET_CAND_PILE_MEM
                 >> first_assum (qspecl_then [`h::p`,`c`] strip_assume_tac)
                   >> `MEM (c,get_cand_pile c (h::p)) (h::p)` by metis_tac[]
                     >> `(c,get_cand_pile c (h::p)) =  (c,nba)` by metis_tac[]
                       >> RW_TAC bool_ss [PAIR_EQ,EQ_SYM_EQ])
            >- metis_tac[MEM,MAP,PAIR_EQ,EQ_SYM_EQ]));
   
val list_not_MEM_verified_fully= Q.store_thm ("list_not_MEM_verified_fully",
 `!l1 (l2: cand list). (!c. MEM c l1 ==> (~ MEM c l2)) <=> (list_not_MEM l1 l2)`,

        Induct_on `l1`
             >- rw[]
             >- (REPEAT STRIP_TAC
	          >> fs[]
                    >> metis_tac[MEM]));


val Logical_list_MEM_VICE_VERCA_TheFunctional = Q.store_thm("Logical_list_MEM_VICE_VERCA_TheFunctional",
 `!(l1: cand list) l2. (!c. MEM c l1 ==> MEM c l2) <=> list_MEM_dec l1 l2`,

    Induct_on `l1`
      >-  fs[list_MEM_dec_def]
      >- (REPEAT STRIP_TAC >> fs[]
        >> metis_tac[MEM,list_MEM_dec_def]));

  
val Logical_AllNonEpty_to_Functional = Q.store_thm("Logical_AllNonEpty_to_Functional",
 `! l p. (ALL_DISTINCT (MAP FST p)) /\ (!c. MEM c l ==> MEM c (MAP FST p)) ==>
         (!c. MEM c l ==> (!l'. MEM (c,l') p ==> l' <> [])) ==> ALL_NON_EMPTY p l`,

Induct_on`l`
   >- rw[ALL_NON_EMPTY_def] 
   >- (rw[ALL_NON_EMPTY_def]
       >- metis_tac[GET_CAND_PILE_MEM,MEM,ALL_NON_EMPTY_def]
       >- metis_tac[ALL_NON_EMPTY_def,MEM]));
  

val Functional_AllNonEmpty_to_Logical = Q.store_thm("Functional_AllNonEmpty_to_Logical",
 `!l p. (ALL_DISTINCT (MAP FST p)) /\ (!c. MEM c l ==> MEM c (MAP FST p)) ==>
         (ALL_NON_EMPTY p l) ==> (!c. MEM c l ==> (!l'. MEM (c,l') p ==> l' <> []))`,

Induct_on `l`
    >- rw[]
    >- (rw[]
     >- (rfs[ALL_NON_EMPTY_def]
         >> metis_tac[ALL_NON_EMPTY_def,EVERY_CAND_HAS_ONE_PILE,MEM])
     >- rfs[ALL_NON_EMPTY_def]));

  
val Logical_elim_to_Functional_Elim = Q.store_thm ("Logical_elim_to_Functional_Elim",
 `!st qu l c j1 j2. ELIM_CAND c (qu,st,l) j1 j2 ==> (ElimCandDec c (qu,st,l) j1 j2)`,

   (REPEAT STRIP_TAC >> Cases_on `j1`)
 
     >-  (Cases_on `j2` 

        >- ((PairCases_on`p` >>
	  PairCases_on`p'` >>
	  rfs[ELIM_CAND_def,ElimCandDec_def] >>
          REPEAT STRIP_TAC) 

         >-  (`l <> []` by metis_tac[Valid_Init_CandList_def]
               >> `?l1 x. l = x::l1` by metis_tac [list_nchotomy]
               >> fs[NULL]) 
         >- fs[Valid_Init_CandList_def]  
         >- (`!(l1:cand list) l2 (c':cand). MEM c' l1 \/ MEM c' l2 ==> MEM c' (l1++l2)`
               by FULL_SIMP_TAC list_ss [MEM,MEM_APPEND] 
               >> `!c'. MEM c' (p6++p5) ==> MEM c' l` by metis_tac [MEM,MEM_APPEND] 
               >> metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])   
         >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def] 
         >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]   
         >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]  
         >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]  
         >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def] 
         >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def] 
         >- metis_tac[LogicalLessThanQu_IMP_less_than_quota,Valid_PileTally_def,ALOOKUP_def] 
         >-  metis_tac [EQE_IMP_REMOVE_ONE_CAND] 
         >-  (`MEM c (MAP FST p1)` by metis_tac [Valid_PileTally_def,FST,MAP]
               >> `!d. MEM d p6 ==> MEM d (MAP FST p1)` by metis_tac [Valid_PileTally_def]
               >> metis_tac [Logical_bigger_than_cand_IMP_TheFunctional])  
         >-  metis_tac [Logical_subpile1_IMP_TheFunctional] 
         >-  (`!d. (d = c) ==> ?l. MEM (c,l) p2` by metis_tac[GET_CAND_PILE_MEM,Valid_PileTally_def]
          >> metis_tac [Logical_subpile2_IMP_TheFunctional])) 
      >- rfs[ELIM_CAND_def])
    >- rfs[ELIM_CAND_def]); 
   
val Functional_Elim_to_Logical_elim = Q.store_thm ("Functional_Elim_to_Logical_elim",
 `!st qu l c j1 j2. ElimCandDec c (qu,st,l) j1 j2 ==> ELIM_CAND c (qu,st,l) j1 j2`,



  (REPEAT STRIP_TAC >> Cases_on `j1`) 
         >- (Cases_on `j2`
 
           >- ((PairCases_on`p` >> PairCases_on`p'`
	    >> rfs[ELIM_CAND_def,ElimCandDec_def]
              >> REPEAT STRIP_TAC) 
                >- metis_tac[NULL_EQ] 
                >- metis_tac [NULL_EQ]
                >- metis_tac[NULL_EQ] 
                >- metis_tac[NULL_EQ,Valid_Init_CandList_def,ALL_DISTINCT]
                >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND] 
                >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND] 
                >- rw[] 
                >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
                >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
                >- fs[]  
                >- fs[] 
                >- rw[] 
                >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
                >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]   
                      >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM] 
                      >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy] 
                      >> `!d. MEM d p6 ==> MEM d l`
                           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]  
                      >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally] 
                    >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota])   
                >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d p6 ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                     >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac [PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK]) 
                 >- metis_tac [EQE_REMOVE_ONE_CAND,ALL_DISTINCT_APPEND] 
                 >-  metis_tac [Functional_subpile1_IMP_TheLogical]
                 >- metis_tac [Functional_subpile2_IMP_TheLogical]  
                 >- metis_tac [NULL_EQ]
		 >- metis_tac [NULL_EQ])  
           >- rfs[ElimCandDec_def])  
         >- rfs[ElimCandDec_def]); 


val eqe_list_dec_MEM1 = Q.store_thm ("list_eqe_dec_MEM1",
 `!l0 l1 l2. eqe_list_dec l0 l1 l2 ==> (!c. MEM c l0 \/ MEM c l1 ==> MEM c l2)`,

Induct_on `l0`
  >- fs [eqe_list_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,list_MEM_dec_thm]
  >- (REPEAT STRIP_TAC
     >- metis_tac [eqe_list_dec_def,MEM]
     >- metis_tac [MEM,eqe_list_dec_def]));


val logical_to_functional_eqe_list_dec = Q.store_thm ("logical_to_functional_eqe_list_dec",
`!l0 l1 l2. (ALL_DISTINCT (l0 ++ l1)) /\ (!c. MEM c l0 \/ MEM c l1 ==> MEM c l2) ==> eqe_list_dec l0 l1 l2`,

   Induct_on `l0`
     >- metis_tac [eqe_list_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,list_MEM_dec_thm]
     >-  ((REPEAT STRIP_TAC
       >> rw[eqe_list_dec_def])
          >- fs [ALL_DISTINCT]
          >- (`!c. MEM c l0 \/ MEM c l1 ==> MEM c l2` by metis_tac[MEM]
	    >> `ALL_DISTINCT (l0 ++ l1)` by fs[ALL_DISTINCT]
              >> metis_tac[ALL_DISTINCT,MEM])));


val eqe_list_dec2_verified = Q.store_thm ("eqe_list_dec2_verified",
 `! l0 l1 l2. eqe_list_dec2 l0 l1 l2 <=> (!c. MEM c l2 ==> MEM c l0 \/ MEM c l1)`,
  Induct_on `l2`
    >-  (EVAL_TAC >> rw[])
    >- (REPEAT STRIP_TAC >> rfs[]
        >> fs[eqe_list_dec2_def]
        >> metis_tac[eqe_list_dec2_def]));

(*
val Logical_TransferAux_to_Functional = Q.store_thm ("Logical_TransferAux_to_Functional",
 `! st qu l ba t t' p np bl bl2 bl2' e e' h h'. TRANSFER_AUX_SPEC (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'
             ==> TRANSFER_AUX_IMP (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'`,
   
  REPEAT STRIP_TAC
   >> fs[TRANSFER_AUX_SPEC_def,TRANSFER_AUX_IMP_def]
     >> (STRIP_TAC              
        >- (`(!d. MEM d h \/ MEM d e ==> MEM d l) ==> (!d. MEM d (h++e) ==> MEM d l)`
               by  FULL_SIMP_TAC list_ss [MEM_APPEND] >>  
               metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])     
        >- (fs[Logical_list_MEM_VICE_VERCA_TheFunctional]  
	    >> fs[PileTally_to_PileTally_DEC1,Valid_PileTally_def,
	       PileTally_to_PileTally_DEC2,NULL_EQ,NULL,
	       Valid_Init_CandList_def,LogicalLessThanQu_IMP_less_than_quota,MEM])));
 

val Functional_TransferAux_to_Logical = Q.store_thm("Functional_TransferAux_to_Logical",
 `! st qu l ba t t' p np bl bl2 bl2' e e' h h'. TRANSFER_AUX_IMP (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'
                   ==> TRANSFER_AUX_SPEC (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'`,
    
 (REPEAT STRIP_TAC >> 
  fs[TRANSFER_AUX_IMP_def,TRANSFER_AUX_SPEC_def]
   >> fs[NULL,NULL_EQ,Valid_Init_CandList_def,NULL_EQ,MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional,
        Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
	less_than_qu_IMP_LogicalLessThanQuota]   
   >> REPEAT CONJ_TAC)                   
    >- metis_tac[MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional] 
    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
    >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. t = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d h ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
		     >> `!d. MEM d h ==> MEM d (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota]));
*)
(*
val _ = mesonLib.max_depth := 10;
   
    
val Functional_Transfer_to_Logical_transfer_act = Q.store_thm("Functional_Transfer_to_Logical_transfer_act",
 `! st qu l j1 j2. TRANSFER_ACT_IMP (qu,st,l) j1 j2 ==> TRANSFER_ACT_SPEC (qu,st,l) j1 j2`,
   
 Cases_on `j1`    
   >- (Cases_on `j2`          
    >- ((REPEAT STRIP_TAC >> PairCases_on `p` >> PairCases_on `p'` 
      >> fs[TRANSFER_ACT_IMP_def,TRANSFER_ACT_SPEC_def]   
      >> Cases_on `p3`)        
        >- fs[]             
        >- (rfs[NULL,NULL_EQ,Logical_TransferAux_to_Functional,Logical_list_MEM_VICE_VERCA_TheFunctional] 
         >> fs[Functional_TransferAux_to_Logical]
         >> (mesonLib.ASM_MESON_TAC[Functional_TransferAux_to_Logical,TRANSFER_AUX_IMP_def,
	     MEM_MAP,GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE,MEM,Logical_list_MEM_VICE_VERCA_TheFunctional,
	     Functional_subpile1_IMP_TheLogical,MEM,Functional_subpile2_IMP_TheLogical,
             TRANSFER_AUX_IMP_def]
         ORELSE  
	  metis_tac[NULL,NULL_EQ,Logical_TransferAux_to_Functional,
	       Functional_subpile1_IMP_TheLogical,TRANSFER_AUX_IMP_def,
               Functional_subpile2_IMP_TheLogical,Functional_TransferAux_to_Logical,
	       TRANSFER_AUX_IMP_def,MEM])))     
    >- rfs[TRANSFER_ACT_IMP_def])
    >- rfs[TRANSFER_ACT_IMP_def]); 


val _ = mesonLib.max_depth := 22; 
    
                 
val Logical_transfer_to_Functional_Transfer_act = Q.store_thm("Logical_transfer_to_Functional_Transfer_act",
 `! st qu l j1 j2. TRANSFER_ACT_SPEC (qu,st,l) j1 j2 ==> TRANSFER_ACT_IMP (qu,st,l) j1 j2`,

  REPEAT STRIP_TAC
   >> fs[TRANSFER_ACT_SPEC_def,TRANSFER_ACT_IMP_def]    
   >> fs[Logical_TransferAux_to_Functional,NULL,NULL_EQ]   
    >> ((`MEM c (MAP FST np)` by metis_tac[MEM_MAP,FST,TRANSFER_AUX_SPEC_def]
      >> `!d. (d = c) ==> ?l. MEM (c,l) np` by metis_tac[GET_CAND_PILE_MEM,Valid_PileTally_def]
       >> mesonLib.ASM_MESON_TAC[Logical_TransferAux_to_Functional,    
             Logical_subpile1_IMP_TheFunctional,Logical_subpile2_IMP_TheFunctional,TRANSFER_AUX_SPEC_def,
	     GET_CAND_PILE_MEM,Valid_PileTally_def,MEM_MAP])
        ORELSE   
	 (metis_tac[TRANSFER_AUX_SPEC_def])));
*)
      
val Logical_transfer_to_Functional_Transfer = Q.store_thm ("Logical_transfer_to_Functional_Transfer",
 `! st qu l j1 j2. TRANSFER (qu,st,l) j1 j2 ==> TransferDec (qu,st,l) j1 j2`,
  
    (REPEAT STRIP_TAC    
      >> Cases_on `j1`)         
         >- (Cases_on `j2`           
          >- ((PairCases_on `p`      
              >> PairCases_on `p'`      
              >> rfs[TransferDec_def,TRANSFER_def]
              >> REPEAT STRIP_TAC)        
            >- (`(!d. MEM d p6 \/ MEM d p5 ==> MEM d l) ==> (!d. MEM d (p6++p5) ==> MEM d l)`
               by  FULL_SIMP_TAC list_ss [MEM_APPEND] >>
               metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])         
            >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]     
            >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]     
            >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]      
            >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]      
            >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]      
            >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]     
            >- metis_tac [Valid_Init_CandList_def,NULL_EQ]     
            >- fs[Valid_Init_CandList_def]    
            >- metis_tac[ Logical_list_MEM_VICE_VERCA_TheFunctional]
            >- (`!c. MEM c p6 ==> MEM c (MAP FST p1)` by            
                 metis_tac[PileTally_to_PileTally_DEC1,Valid_PileTally_def,PileTally_to_PileTally_DEC2
		 ,Valid_Init_CandList_def,MEM]
               >> metis_tac[EVERY_CAND_HAS_ONE_PILE,GET_CAND_TALLY_MEM2,LogicalLessThanQu_IMP_less_than_quota])
            >- (`!c. MEM c p3 ==> MEM c (MAP FST p2)` by metis_tac[Valid_Init_CandList_def, 
                   Logical_list_MEM_VICE_VERCA_TheFunctional,logical_to_functional_eqe_list_dec,
		   Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
		   Logical_list_MEM_VICE_VERCA_TheFunctional,MEM]  
               >>  metis_tac[ Logical_list_MEM_VICE_VERCA_TheFunctional,PileTally_to_PileTally_DEC2,
	           Valid_PileTally_def,Valid_Init_CandList_def,Logical_AllNonEpty_to_Functional,
	           ALL_NON_EMPTY_def,MEM])       
            >- metis_tac [Logical_subpile1_IMP_TheFunctional]       
            >- ((`MEM c (MAP FST np)` by (FULL_SIMP_TAC list_ss [MEM_MAP,FST] >>    
                 MAP_EVERY qexists_tac [`(c,[])`] >> metis_tac [FST]))  
             >> `!d. (d = c) ==> ?l. MEM (c,l) np` by
		    metis_tac[GET_CAND_PILE_MEM,Valid_PileTally_def]  
             >> metis_tac[Logical_subpile2_IMP_TheFunctional,GET_CAND_PILE_MEM,Valid_PileTally_def]))    
         >- fs[TRANSFER_def]) 
       >- fs[TRANSFER_def]);  
                  
val Functional_Transfer_to_Logical_transfer = Q.store_thm ("Functional_Transfer_to_Logical_transfer",
 `! st qu l j1 j2. TransferDec (qu,st,l) j1 j2 ==> TRANSFER (qu,st,l) j1 j2`,

 (REPEAT STRIP_TAC
  
    >> Cases_on `j1`)    
      >- (Cases_on `j2`  
  
          >-  ((PairCases_on`p` >> PairCases_on`p'`   
              >> rfs [TransferDec_def,TRANSFER_def] >> REPEAT STRIP_TAC  
              >> Cases_on `p3`)  
  
                 >- rfs[] 
    
                 >- (MAP_EVERY qexists_tac [`LAST (get_cand_pile h p2)`,`t`,`p'2`] >> REPEAT STRIP_TAC
                     >- fs[NULL_EQ]  
		     >- fs[NULL_EQ]  
                     >- rw[]    
                     >-  metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]  
                     >-  metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional] 
		     >-  metis_tac []    
         >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]  
         >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]  
         >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
         >-  metis_tac[Valid_Init_CandList_def,NULL_EQ]    
         >-  rw []
	 >- metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,MEM] 
         >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                 >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                 >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                 >> `!d. MEM d p6 ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
		 >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                 >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota]) 
          >-(`!d. MEM d (h::t) ==> MEM d (MAP FST p2)` by metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
	       Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
             >> metis_tac[Functional_AllNonEmpty_to_Logical,MEM]) 
          >- ((MAP_EVERY qexists_tac [`h`] 
             >> `(p'3 = t) /\ (p'0 = LAST (get_cand_pile h p2)) /\ (MEM (h,[]) p'2) /\ (subpile1 h p2 p'2)
	                   /\ (subpile2 h p'2 p2)` by rfs[] >> REPEAT STRIP_TAC)  
           >- rw[]  
           >- rw[]  
           >- rfs[]  
           >- metis_tac [Functional_subpile1_IMP_TheLogical]  
           >- metis_tac [Functional_subpile2_IMP_TheLogical] 
           >- rw[] 
           >- rw[] 
           >- rw[]
	   >- fs[NULL_EQ])))
     >- rfs[TransferDec_def])  
     >- rfs[TransferDec_def]); 
 
 

val fcc_to_first_continuing_cand = Q.store_thm ("fcc_to_first_continuing_cand",
 `! c b h. first_continuing_cand_dec c b h ==> first_continuing_cand c b h`,

  Induct_on `b`
    >- rw[first_continuing_cand_dec_def]
    >- ((REPEAT STRIP_TAC
      >>  rw[first_continuing_cand_def]
       >> Cases_on `c = h`)
         >- (MAP_EVERY qexists_tac [`[]`,`b`]
          >> FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT])
         >- (rfs [first_continuing_cand_dec_def]
           >- RW_TAC bool_ss []
           >- (rfs [first_continuing_cand_def]
            >> `?L1 L2. (b = L1 ++ [c]++L2) /\ (!d. MEM d L1 ==> ~ MEM d h')` by metis_tac[]
             >> MAP_EVERY qexists_tac [`h::L1`,`L2`]
              >> FULL_SIMP_TAC list_ss [MEM] >> metis_tac [MEM]))));
 
 
 val first_continuing_cand_IMP_fcc = Q.store_thm ("first_continuing_cand_IMP_fcc",
 `! c b h. first_continuing_cand c b h ==> first_continuing_cand_dec c b h`,

Induct_on `b`

>- rw[first_continuing_cand_def]
>- ((REPEAT STRIP_TAC
  >> rw[first_continuing_cand_dec_def]
    >> Cases_on `c = h`)
      >- RW_TAC bool_ss []
      >- ((rfs [first_continuing_cand_def]
      >> `(l1 = []) \/ (?L1 x. l1 = x::L1)` by metis_tac [list_nchotomy])
        >- FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT,CONS_11]
        >- (FULL_SIMP_TAC list_ss [CONS_11]
          >> first_assum (qspecl_then [`c`,`h'`] strip_assume_tac)
            >> metis_tac [MEM]))));
   
val intermediate_count = Define `
        (intermediate_count ((qu,st,l):params) j1 j2 = ? ba t nt p np bl e h.
          (j1 = NonFinal (ba, t, p, bl, [], e, h))
       /\ (!d. MEM d (h++e) ==> MEM d l)
       /\ (ALL_DISTINCT (h++e))
       /\ (Valid_PileTally t l)
       /\ (Valid_PileTally nt l)
       /\ (Valid_PileTally p l)
       /\ (Valid_PileTally np l)
       /\ (Valid_Init_CandList l)
       /\ (ALL_DISTINCT (MAP FST p))
       /\ (ALL_DISTINCT (MAP FST t))
       /\ (ALL_DISTINCT (MAP FST np))
       /\ (ALL_DISTINCT (MAP FST nt))
       /\ (ba <> [])
       /\ (h <> [])
       /\ (!c. MEM c l ==>
                            ((MEM c h ==>
                             ?(l': ((cand list) # rat) list).
                               (l' = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                            /\ (get_cand_pile c np = (get_cand_pile c p) ++ [l'])
                            /\ (get_cand_tally c nt = (get_cand_tally c t) + (SUM_RAT (l'))))
                            /\ (~ MEM c h ==>
                                           (get_cand_pile c np = get_cand_pile c p)
                                        /\ (get_cand_tally c nt = get_cand_tally c t))))
       /\ (j2 = NonFinal ([], nt, np, bl, [], e, h)))`;
   
  
val Logical_to_Functional_Count_Dec_Aux = Q.store_thm ("Logical_to_Functional_Count_Dec_Aux",
 `!t nt p np ba h l.
       (!c. MEM c l ==>
               ((MEM c h ==>
                   (get_cand_pile c np = (get_cand_pile c p)
	             ++ [(FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)])
                /\ (get_cand_tally c nt = (get_cand_tally c t) + (SUM_RAT (
		   (FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba))))))
                            /\ (~ MEM c h ==>
                                           (get_cand_pile c np = get_cand_pile c p)
                                        /\ (get_cand_tally c nt = get_cand_tally c t)))
                                           ==> COUNTAux_dec p np t nt ba h l`,


Induct_on `l`
  >- rw[COUNTAux_dec_def]
  >- ((REPEAT STRIP_TAC
      >> rw[COUNTAux_dec_def])

    >- (first_assum (qspecl_then [`h`] strip_assume_tac)
     >> FULL_SIMP_TAC list_ss [MEM]
      >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
         >> metis_tac [])

    >- (first_assum (qspecl_then [`h`] strip_assume_tac)
     >> FULL_SIMP_TAC list_ss []
       >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
         >> metis_tac [])));
   
  
val Functional_to_Logical_Count_Dec_Aux = Q.store_thm ("Functional_to_Logical_Count_Dec_Aux",
`!t t' p np ba h l. COUNTAux_dec p np t t' ba h l ==>
          (!c. MEM c l ==>
                 ((MEM c h ==>
                    ?(l': ((cand list) # rat) list).
                      (l' = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                         /\ (get_cand_pile c np = (get_cand_pile c p) ++ [l'])
                         /\ (get_cand_tally c t' = (get_cand_tally c t) + (SUM_RAT (l'))))
                         /\ (~ MEM c h ==>
                                      (get_cand_pile c np = get_cand_pile c p)
                                      /\ (get_cand_tally c t' = get_cand_tally c t))))`,

Induct_on `l`
    >- rw[]
    >- (REPEAT STRIP_TAC
      >- ((MAP_EVERY qexists_tac
      [`FILTER (\ (b: (cand list) # rat). (first_continuing_cand_dec c (FST b) h')) ba`]
        >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
        >> `(c = h) \/ MEM c l` by FULL_SIMP_TAC list_ss [])
            >- (REPEAT STRIP_TAC
               >- metis_tac[]
               >-  metis_tac[COUNTAux_dec_def]
               >-  metis_tac[COUNTAux_dec_def])
            >- (REPEAT STRIP_TAC
              >- metis_tac []
              >- (first_assum (qspecl_then [`t`,`t'`,`p`,`np`,`ba`,`h'`] strip_assume_tac)
                >> `COUNTAux_dec p np t t' ba h' l` by metis_tac[COUNTAux_dec_def]
                >>  FULL_SIMP_TAC list_ss [])
              >- (first_assum (qspecl_then [`t`,`t'`,`p`,`np`,`ba`,`h'`] strip_assume_tac)
                >> `COUNTAux_dec p np t t' ba h' l` by metis_tac[COUNTAux_dec_def]
                >> FULL_SIMP_TAC list_ss [])))
       >- (`(c = h) \/ MEM c l` by FULL_SIMP_TAC list_ss []
         >- metis_tac[COUNTAux_dec_def]
         >- metis_tac[COUNTAux_dec_def])
       >- (`(c = h) \/ MEM c l` by FULL_SIMP_TAC list_ss [MEM]
         >- metis_tac[COUNTAux_dec_def]
         >- metis_tac[COUNTAux_dec_def])));
    
val intermediate_count_IMP_Count_Aux = Q.store_thm ("intermediate_count_IMP_Count_Aux",
 `! (st: num) (qu: rat) l j1 j2. intermediate_count (qu,st,l) j1 j2 ==> COUNT (qu,st,l) j1 j2`,


(REPEAT STRIP_TAC >> rw[COUNT_def] >> rfs[intermediate_count]
     >> STRIP_TAC)
     >- metis_tac[]
     >- (REPEAT STRIP_TAC

       >- metis_tac[Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE]
       >- (`!L. MEM (c,L) nt' ==> (get_cand_tally c nt' = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
         >> `!L. MEM (c,L) t ==> (get_cand_tally c t = L)` by
           metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
	    >> metis_tac[])
       >- (`!L. MEM (c,L) np ==> (get_cand_pile c np = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE]
         >> `!L. MEM (c,L) p ==> (get_cand_pile c p = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE]
         >> `!L. MEM (c,L) p ==> MEM (c,L) np` by (REPEAT STRIP_TAC >>
              metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM])
            >> `!L. MEM (c,L) np ==> MEM (c,L) p` by (REPEAT STRIP_TAC >>
                 metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM])
              >> metis_tac [])
        >- (`!L. MEM (c,L) nt' ==> (get_cand_tally c nt' = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
         >> `!L. MEM (c,L) t ==> (get_cand_tally c t = L)` by
           metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
         >> `!L. MEM (c,L) t ==> MEM (c,L) nt'` by (REPEAT STRIP_TAC >>
              metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_TALLY_MEM2])
            >> `!L. MEM (c,L) nt' ==> MEM (c,L) t` by (REPEAT STRIP_TAC >>
                 metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_TALLY_MEM2])
              >> metis_tac [])));
  
  
 val Count_Aux_IMP_intermediate_count = Q.store_thm ("Count_Aux_IMP_intermediate_count",
`! (st: num) (qu: rat) l j1 j2. COUNT (qu,st,l) j1 j2 ==> intermediate_count (qu,st,l) j1 j2`,

(REPEAT STRIP_TAC
 >> rw[intermediate_count]
  >> rfs[COUNT_def]
   >> STRIP_TAC)
   >- metis_tac[]
   >- (REPEAT STRIP_TAC
     >- (`(!l'. MEM (c,l') np ==>
       (l' = (get_cand_pile c p) ++ [(FILTER (\ (b: (cand list) # rat).(first_continuing_cand c (FST b) h)) ba)]))`
        by  metis_tac[]
      >> first_assum (qspecl_then [`get_cand_pile c np`] strip_assume_tac)
        >> metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM])
     >- metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_TALLY_MEM2]
     >- (`(!l'. MEM c l /\ MEM (c,l') np <=> MEM c l /\ MEM (c,l') p)` by metis_tac []
       >> `MEM (c,get_cand_pile c np) p` by
           metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
         >> metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE])
     >- (`(!r. MEM c l /\ MEM (c,r) t <=> MEM c l /\ MEM (c,r) nt') ` by metis_tac []
      >> metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY,GET_CAND_TALLY_MEM2])));
  
val Count_Aux_IMP_Count_Aux_dec = Q.store_thm ("Count_Aux_IMP_Count_Aux_dec",
 `! (st: num) (qu: rat) l j1 j2. COUNT (qu,st,l) j1 j2 ==> CountDec (qu,st,l) j1 j2`,

  (ASSUME_TAC Count_Aux_IMP_intermediate_count
   >> REPEAT STRIP_TAC
   >> `intermediate_count (qu,st,l) j1 j2` by metis_tac[COUNT_def,Count_Aux_IMP_intermediate_count]
     >> rfs[CountDec_def,COUNT_def]
      >> REPEAT STRIP_TAC)
        >-  (rfs [intermediate_count]
            >> metis_tac [Logical_to_Functional_Count_Dec_Aux])
        >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac [Valid_Init_CandList_def,NULL_EQ]
        >- metis_tac [Valid_Init_CandList_def]
        >- rfs[NULL_EQ]
        >- metis_tac [NULL_EQ]);
   
 
val Count_Aux_dec_IMP_Count_Aux = Q.store_thm ("Count_Aux_dec_IMP_Count_Aux",
 `! (st : num) (qu:rat) l j1 j2. CountDec (qu,st,l) j1 j2 ==> COUNT (qu,st,l) j1 j2 `,

 (ASSUME_TAC intermediate_count_IMP_Count_Aux
  >> REPEAT STRIP_TAC 
    >> `intermediate_count (qu,st,l) j1 j2` by
      (Cases_on `j1` 
       >- (Cases_on `j2` 
         >- ((PairCases_on `p` >> PairCases_on `p'` >> rfs[intermediate_count,CountDec_def] 
              >> REPEAT STRIP_TAC)
            >- fs[NULL_EQ]
            >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND] 
            >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND] 
            >- metis_tac []
            >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
            >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
            >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
            >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
            >- metis_tac[Valid_Init_CandList_def,NULL_EQ] 
            >- metis_tac [NULL_EQ] 
            >- metis_tac [NULL_EQ] 
            >- metis_tac [Functional_to_Logical_Count_Dec_Aux] 
            >-  metis_tac [Functional_to_Logical_Count_Dec_Aux] 
            >- metis_tac [Functional_to_Logical_Count_Dec_Aux] 
            >- metis_tac [Functional_to_Logical_Count_Dec_Aux]
	    >- fs[NULL_EQ])  
         >- rfs [CountDec_def]) 
        >-  rfs[CountDec_def]) 
           >> metis_tac[intermediate_count_IMP_Count_Aux]));
     
 
val APPEND_EQ_NIL2 = Q.store_thm ("APPEND_EQ_NIL2",
    `!l1 l2. ([] = l1 ++ l2) ==> ((l1 = []) /\ (l2 = [])) `,
      Cases_on `l2`
        >- ASM_SIMP_TAC bool_ss [APPEND_NIL]
        >- (Cases_on `l1`
          >> rw[APPEND_NIL_LEFT_COR]
            >> (ASM_SIMP_TAC bool_ss [NOT_NIL_CONS]
              >> STRIP_TAC
                >> rw[NOT_NIL_CONS]))) ;

val take_append_returns_appended = Q.store_thm ("take_append_returns_appended",
 `! l1 l2 l3. (l1 = l2 ++ l3) ==> (l3 = take_append l1 l2)`,

 Induct_on `l1`
  >- FULL_SIMP_TAC list_ss [APPEND_EQ_NIL2,take_append_def]
  >- (Induct_on `l2`
    >- FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT,take_append_def]
    >- (REPEAT STRIP_TAC
     >> rw[take_append_def]
       >> FULL_SIMP_TAC list_ss [CONS_11])));


val functional_to_logical_BiggerThanQuota = Q.store_thm ("logical_to_functional_BiggerThanQuota",
 `! (qu:rat) l t. bigger_than_quota l t qu /\ ALL_DISTINCT (MAP FST t) ==>
                                     (!c. MEM c l ==> (!r. MEM (c,r) t ==> qu <= r))`,

  Induct_on `l`
    >- rw[]
    >- ((REPEAT STRIP_TAC
      >> FULL_SIMP_TAC list_ss [])
         >- (`get_cand_tally c t = r` by metis_tac [ALL_DISTINCT,EVERY_CAND_HAS_ONE_TALLY]
           >> RW_TAC bool_ss [] >> rfs[bigger_than_quota_def])
         >- (`bigger_than_quota l t qu` by fs[bigger_than_quota_def]
	    >> metis_tac [])));


val logical_to_functional_BiggerThanQuota = Q.store_thm ("logical_to_functional_BiggerThanQuota",
`! (qu: rat) l t. (ALL_DISTINCT (MAP FST t)) /\ (!d. MEM d l ==> MEM d (MAP FST t)) /\
                  (!c. MEM c l ==> (!r. MEM (c,r) t ==> qu <= r)) ==> bigger_than_quota l t qu`,

  Induct_on `l`
     >- rw[bigger_than_quota_def]
     >- ((REPEAT STRIP_TAC
       >> rw[bigger_than_quota_def])
          >- (`MEM (h,get_cand_tally h t) t` by metis_tac [MEM,GET_CAND_TALLY_MEM2]
            >> metis_tac[MEM])
          >- metis_tac [bigger_than_quota_def,MEM]));

 
val functional_to_logicl_piles_eq = Q.store_thm ("functional_to_logical_piles_eq",
 `! l1 l2 p1 p2. ALL_DISTINCT (MAP FST p1) /\ ALL_DISTINCT (MAP FST p2) /\ (list_MEM_dec l1 (MAP FST p1)) /\
                (list_MEM_dec l1 (MAP FST p2)) /\ (piles_eq_list l1 l2 p1 p2) ==>
   (!c. MEM c l1 ==> (~ MEM c l2 ==> (!l'. MEM (c,l') p1 <=> MEM (c,l') p2)))`,


Induct_on `l1`
 >- rw[]

 >- ((REPEAT STRIP_TAC
    >> Cases_on `c= h`)

  >- (`get_cand_pile h p1 = get_cand_pile h p2` by metis_tac [piles_eq_list_def] >>
     (`MEM (h,l') p1 ==> MEM (h, l') p2` by (STRIP_TAC >>
     `get_cand_pile c p1 = l'` by
     metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
     GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
       `MEM (h,get_cand_pile h p2) p2` by
       metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
       GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
         `l' = get_cand_pile h p2` by
         metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
         GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
           metis_tac [MEM])) >>
     (`MEM (h,l') p2 ==> MEM (h,l') p1` by (STRIP_TAC >>
     `get_cand_pile c p2 = l'`
     by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
     GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
       `MEM (h,get_cand_pile h p1) p1` by
       metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
       GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
         `l' = get_cand_pile h p1` by
         metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
         GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
            metis_tac [MEM])) >>
     metis_tac [MEM])
  >- (`list_MEM_dec l1 (MAP FST p1)` by metis_tac [MEM,Logical_list_MEM_VICE_VERCA_TheFunctional] >>
      `list_MEM_dec l1 (MAP FST p2)` by metis_tac [MEM,Logical_list_MEM_VICE_VERCA_TheFunctional] >>
      `piles_eq_list l1 l2 p1 p2` by metis_tac [piles_eq_list_def] >>
      metis_tac [MEM])));
 

val logical_to_functional_piles_eq = Q.store_thm ("logical_to_functional_piles_eq",
`! l1 l2 p1 p2.  (!c. MEM c l1 ==> (~ MEM c l2 ==> (!l'. MEM (c,l') p1 <=> MEM (c,l') p2)))
              /\ (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2) )
              /\ (!d. MEM d l1 ==> MEM d (MAP FST p1) /\ MEM d (MAP FST p2)) ==> piles_eq_list l1 l2 p1 p2`,

  Induct_on `l1`
    >- rw[piles_eq_list_def]
    >- (REPEAT STRIP_TAC
     >> rw[piles_eq_list_def]
      >> `!l'. MEM (h,l') p1 <=> MEM (h,l') p2` by FULL_SIMP_TAC list_ss [MEM]
       >> metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE,MEM]));
 

val functional_to_logical_update_pile = Q.store_thm ("functional_to_logical_update_pile",
 `! (qu: rat) (t: (cand # rat) list) l p1 p2. (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2))
        /\   (update_cand_pile qu t l p1 p2) ==>
              (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                         (MAP FST (FLAT l') = MAP FST (FLAT(get_cand_pile c p1)))
                                      /\ (MAP SND (FLAT l') = update_cand_trans_val qu c t (FLAT (get_cand_pile c p1)))))`,

   Induct_on `l`
     >- rw[]
     >- (REPEAT STRIP_TAC
       >- (FULL_SIMP_TAC list_ss []
          >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
           >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
            >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
             >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
              >> metis_tac [update_cand_pile_def])
          >- metis_tac [update_cand_pile_def])
       >- (FULL_SIMP_TAC list_ss []
         >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
          >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
           >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
            >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
             >> metis_tac[update_cand_pile_def])
       >- metis_tac [update_cand_pile_def])));
  
 
val logical_to_functional_update_pile = Q.store_thm ("logical_to_functional_update_pile",
 `! (qu: rat) (t: (cand #rat) list) l p1 p2. (!c. MEM c l ==> MEM c (MAP FST p2)) /\
                                            (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                              (MAP FST (FLAT l') = MAP FST (FLAT (get_cand_pile c p1)))
                                                /\ (MAP SND (FLAT l') = update_cand_trans_val qu c t (FLAT (get_cand_pile c p1))))) ==>
                                                    (update_cand_pile qu t l p1 p2)`,

    Induct_on `l`
      >- rw [update_cand_pile_def]
      >- ((REPEAT STRIP_TAC
       >> rw[update_cand_pile_def])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])));
  

val tally_comparison_total = Q.store_thm ("tally_comparison_total",
 `!t c1 c2. ((tally_comparison t) c1 c2) \/ ((tally_comparison t) c2 c1)`,
  ((REPEAT STRIP_TAC
    >> rw[tally_comparison_def]
     >> ASSUME_TAC RAT_LES_TOTAL
      >> first_assum (qspecl_then [`get_cand_tally c2 t`,`get_cand_tally c1 t`] strip_assume_tac))
         >- (DISJ1_TAC
          >> metis_tac [RAT_LES_IMP_LEQ])
         >- (DISJ1_TAC
          >> metis_tac [RAT_LEQ_REF])
         >- (DISJ2_TAC
          >> metis_tac [RAT_LES_IMP_LEQ])));

 
val tally_comparison_total_COR = Q.store_thm ("tally_comparison_total_COR",
 `!t. total (tally_comparison t)`,

   (ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] total_def)
     >> STRIP_TAC
       >> first_assum (qspecl_then [`tally_comparison t`] strip_assume_tac)
         >> metis_tac [tally_comparison_total]));

 

val tally_comparison_trans = Q.store_thm ("tally_comparison_trans",
 `!t. transitive (tally_comparison t)`,

   (STRIP_TAC
     >> `! c1 c2 c3. (tally_comparison t) c1 c2 /\ (tally_comparison t) c2 c3 ==> (tally_comparison t) c1 c3`
       by (REPEAT STRIP_TAC
        >> metis_tac [tally_comparison_def,RAT_LEQ_TRANS])
          >> metis_tac[transitive_def]));

  
val functional_to_logical_update_pile_ACT = Q.store_thm ("functional_to_logical_update_pile_ACT",
 `! (qu: rat) (t: (cand # rat) list) l p1 p2. (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2))
        /\   (update_cand_pile_ACT qu t l p1 p2) ==>
              (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                         (MAP FST (LAST l') = MAP FST (LAST (get_cand_pile c p1)))
                                      /\ (MAP SND (LAST l') = update_cand_transVal_ACT qu c t p1)))`,

   Induct_on `l`
     >- rw[]
     >- (REPEAT STRIP_TAC
       >- (FULL_SIMP_TAC list_ss []
          >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
           >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
            >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
             >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
              >> metis_tac [update_cand_pile_ACT_def])
          >- metis_tac [update_cand_pile_ACT_def])
       >- (FULL_SIMP_TAC list_ss []
         >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
          >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
           >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
            >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
             >> metis_tac[update_cand_pile_ACT_def])
       >- metis_tac [update_cand_pile_ACT_def])));

 
val logical_to_functional_update_pile_ACT = Q.store_thm ("logical_to_functional_update_pile_ACT",
 `! (qu: rat) (t: (cand #rat) list) l p1 p2. (!c. MEM c l ==> MEM c (MAP FST p2)) /\
                                            (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                              (MAP FST (LAST l') = MAP FST (LAST (get_cand_pile c p1)))
                                                /\ (MAP SND (LAST l') = update_cand_transVal_ACT qu c t p1))) ==>
                                                    (update_cand_pile_ACT qu t l p1 p2)`,

    Induct_on `l`
      >- rw [update_cand_pile_ACT_def]
      >- ((REPEAT STRIP_TAC
       >> rw[update_cand_pile_ACT_def])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])));

val TAKE_DROP_LENGTH_BACKLOG = Q.store_thm ("TAKE_DROP_LENGTH_BACKLOG",
 `! bl nbl (l1: cand list). nbl = bl ++ l1 ==> (bl = TAKE (LENGTH bl) nbl) /\ (l1 = DROP (LENGTH bl) nbl)`,

  REPEAT STRIP_TAC
   >- FULL_SIMP_TAC list_ss [TAKE_APPEND1,APPEND_11]
   >- (`TAKE (LENGTH bl) nbl = bl` by FULL_SIMP_TAC list_ss [TAKE_APPEND1,TAKE_LENGTH_ID]
        >> `nbl = (TAKE (LENGTH bl) nbl) ++ (DROP (LENGTH bl) nbl)` by  FULL_SIMP_TAC list_ss [TAKE_DROP]
          >> metis_tac[APPEND_11]));


val DROP_LENGTH = Q.store_thm ("DROP_LENGTH",
 `! bl (l1: cand list). DROP (LENGTH bl) (bl ++ l1) = l1`,
 Induct_on `bl`
   >- rw[]
   >- (REPEAT STRIP_TAC
     >> FULL_SIMP_TAC list_ss [DROP,MEM]));

(*
val Functional_AllNonZero_to_Logical = Q.store_thm("Functional_AllNonZero_to_Logical",
 `! l p. ALL_NON_ZERO p l ==> (!c. MEM c l ==> SUM_RAT (LAST (get_cand_pile c p)) <> 0)`,
 
Induct
  >- rw[]
  >- (rw[]
      >- rfs[ALL_NON_ZERO_def,MEM]
      >- rfs[ALL_NON_ZERO_def,MEM]));


val Logical_AllNonZero_to_Functional = Q.store_thm("Logical_AllNonZero_to_Functional",
 `!l p . (!c. MEM c l ==> SUM_RAT (LAST (get_cand_pile c p)) <> 0) ==> ALL_NON_ZERO p l`,

Induct
   >- rw[ALL_NON_ZERO_def]
   >- rfs[ALL_NON_ZERO_def,MEM]) 


val New_NonEmptyPiles_def = Define `
    New_NonEmptyPiles (l: cand list) (p: piles) <=>
      EVERY (\x. ~ MEM (x, []) p) l`;

`! l p. (ALL_DISTINCT (MAP FST p) /\ (!d. MEM d l ==> MEM d (MAP FST p))) ==>
    (!c. MEM c l ==> (get_cand_pile c p <> [])) ==> New_NonEmptyPiles l p`
 
Induct
  rw[]
  rw[New_NonEmptyPiles_def]
   Cases_on`c = h`
       >- metis_tac[GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE,MEM] 
       >- strip_tac >> `get_cand_pile h p = []` by metis_tac[GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE,MEM]
     `!d. MEM d l ==>
*)
      
val Logical_to_Functional_elect = Q.store_thm ("Logical_to_Functional_elect",
 `! st (qu: rat) l j1 j2. ELECT (qu,st,l) j1 j2 ==> ElectDec (qu,st,l) j1 j2`,

  (REPEAT STRIP_TAC
   >> Cases_on`j1`)  
     >- (Cases_on `j2`  
             
      >- ((PairCases_on`p` >> PairCases_on`p'`  
	   >> fs[ELECT_def,ElectDec_def]   
	   >> `DROP (LENGTH p3) (p3 ++ l1) = l1` by metis_tac[TAKE_DROP_LENGTH_BACKLOG] 
           >> fs[NULL,NULL_EQ]    
            >> `(!c. MEM c l ==> MEM c (MAP FST p2))` by metis_tac [MEM,Valid_PileTally_def]  
            >> `(!c. MEM c p6 ==> MEM c (MAP FST p'2))` by metis_tac [MEM,Valid_PileTally_def]    
            >> `!c. MEM c l1 ==> MEM c (MAP FST p1)` by metis_tac [MEM, Valid_PileTally_def] 
            >> fs [logical_to_functional_eqe_list_dec,logical_to_functional_piles_eq,
                   eqe_list_dec2_verified,TAKE_DROP_LENGTH_BACKLOG,Valid_Init_CandList_def,
                   Logical_list_MEM_VICE_VERCA_TheFunctional]
             >>  REPEAT CONJ_TAC)
         
            >- (`!c. MEM c l1 ==> MEM c (MAP FST p1)`
                 by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM, Valid_PileTally_def]
             >> metis_tac [logical_to_functional_BiggerThanQuota,bigger_than_quota_def,MEM])   
            >- metis_tac [logical_to_functional_eqe_list_dec]  
            >- metis_tac [logical_to_functional_piles_eq,logical_to_functional_eqe_list_dec,
                           eqe_list_dec2_verified] 
            >- metis_tac [logical_to_functional_eqe_list_dec]  
            >- metis_tac[]      
            >- (`(!c. MEM c p6 ==> MEM c (MAP FST p2) /\ MEM c (MAP FST p'2))`
                 by metis_tac [MEM,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional]
             >> metis_tac [logical_to_functional_piles_eq]) 
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]  
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2] 
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2] 
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2] 
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2] 
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2] 
            >- (`!c. MEM c l1 ==> MEM c (MAP FST p2)` by metis_tac[Valid_Init_CandList_def, 
                   Logical_list_MEM_VICE_VERCA_TheFunctional,
		   Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
		   Logical_list_MEM_VICE_VERCA_TheFunctional,
 		   logical_to_functional_eqe_list_dec,MEM]
               >> metis_tac[Logical_AllNonEpty_to_Functional])
    (*        >- metis_tac[Logical_AllNonZero_to_Functional]  *)
            >- (`!c. MEM c l1 ==> MEM c (MAP FST p'2)` by metis_tac[Valid_Init_CandList_def, 
                   Logical_list_MEM_VICE_VERCA_TheFunctional,
		   Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
		   Logical_list_MEM_VICE_VERCA_TheFunctional,
 		   logical_to_functional_eqe_list_dec,MEM]
               >> metis_tac[Logical_AllNonEpty_to_Functional]) 
       (*     >- metis_tac[Logical_AllNonZero_to_Functional] *) 
            >- (`(!c. MEM c p6 ==> MEM c (MAP FST p'2))` by
	        metis_tac [MEM,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional] 
             >> `(!c. MEM c l ==> MEM c (MAP FST p2))` by
	           metis_tac [MEM,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional]  
	       >> metis_tac[logical_to_functional_update_pile_ACT]))      
         >- fs[ELECT_def])
    >- fs[ELECT_def]);  
     
	       
        
val Functional_to_Logical_elect = Q.store_thm ("Functional_to_Logical_elect",
 `! st qu l j1 j2. ElectDec (qu,st,l) j1 j2 ==> ELECT (qu,st,l) j1 j2`,

 (REPEAT STRIP_TAC 
    >> Cases_on `j1`) 
  >- (Cases_on `j2`     
    >- ((PairCases_on`p` >> PairCases_on`p'`   
       >> rfs[ElectDec_def,ELECT_def] 
        >> MAP_EVERY qexists_tac [`DROP (LENGTH p3) p'3`]
         >> `p'3 = p3 ++ (DROP (LENGTH p3) p'3)` by
              metis_tac[TAKE_DROP,DROP_LENGTH,TAKE_DROP_LENGTH_BACKLOG,APPEND_11]
          >> fs[functional_to_logical_update_pile_ACT,NULL,NULL_EQ]
            >> REPEAT CONJ_TAC)  
          >- rw[]     
	  >- metis_tac [functional_to_logical_BiggerThanQuota]  
          >- metis_tac [eqe_list_dec_MEM1,MEM]   
	  >- metis_tac [eqe_list_dec2_verified]   
	  >- metis_tac [eqe_list_dec2_verified,eqe_list_dec_MEM1,MEM]   
	  >- metis_tac [eqe_list_dec2_verified,eqe_list_dec_MEM1,MEM]  
	  >- (`!c. MEM c p6 ==> MEM c l` by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]
            >> `!c. MEM c p6 ==> MEM c (MAP FST p'2)`
                by metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,MEM]
              >> `!c. MEM c p6 ==> MEM c (MAP FST p2)`
                   by metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
                    MEM,Logical_list_MEM_VICE_VERCA_TheFunctional]
                  >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,functional_to_logicl_piles_eq])  
          >- metis_tac [Valid_Init_CandList_def,NULL_EQ]    
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
          >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional] 
	  >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional] 
          >- (`!c. MEM c (DROP (LENGTH p3) p'3) ==> MEM c (MAP FST p2)`
	      by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,Valid_Init_CandList_def,
	         Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
		 MEM,eqe_list_dec2_verified,eqe_list_dec_MEM1,Functional_AllNonEmpty_to_Logical]
                 >> metis_tac[Functional_AllNonEmpty_to_Logical])    
       (*   >- metis_tac[Functional_AllNonZero_to_Logical] *)
	  >- (`!c. MEM c (DROP (LENGTH p3) p'3) ==> MEM c (MAP FST p'2)`
	      by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,Valid_Init_CandList_def,
	         Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
		 MEM,eqe_list_dec2_verified,eqe_list_dec_MEM1,Functional_AllNonEmpty_to_Logical]
                 >> metis_tac[Functional_AllNonEmpty_to_Logical])
	(*  >- metis_tac[Functional_AllNonZero_to_Logical] *)	  
	  >- metis_tac [functional_to_logical_update_pile_ACT]) 
        >- fs[ElectDec_def])
      >- fs[ElectDec_def]); 
     
 
val subpile1_BlMem_trans2_IsCorrect = Q.store_thm ("subpile1_BlMem_trans2_IsCorrect",
 `!p bl. (!d. MEM d bl ==> MEM (d,[]) p) <=> subpile1_BlMem_trans2 p bl`,

  Induct_on `bl`
    >- rw[subpile1_BlMem_trans2_def]   
    >- (REPEAT STRIP_TAC >> fs[MEM,subpile1_BlMem_trans2_def] >> metis_tac[]));
     
   
val Logical_to_Functional_subpileBacklogTrans2 = Q.store_thm("Logical_to_Functional_subpileBacklogTrans2",
  `!bl p np. (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)))
                /\ (MEM d' bl ==> MEM (d',[]) np)) ==> (subpile1_backlog_trans2 bl p np)`,
 
   Induct_on `p` 
       >- rw[subpile1_backlog_trans2_def] 
       >-((REPEAT STRIP_TAC   
        >> rw[subpile1_backlog_trans2_def] 
        >> (` !d'. (¬MEM d' bl ⇒ ∀l'. MEM (d',l') p ⇒ MEM (d',l') np)` by fs[]) 
        >>  (`!d'. MEM d' bl ⇒ MEM (d',[]) np` by fs[]) 
        >> rw[subpile1_backlog_trans2_def])    
         >- (first_assum(qspecl_then [`bl`,`np`] strip_assume_tac) 
          >> (`subpile1_backlog_trans2 bl p np` by fs[]) 
           >> rfs[subpile1_backlog_trans2_def]) 
         >- ((`∀l'. MEM (FST h,l') (h::p) ⇒ MEM (FST h,l') np` by metis_tac[])  
          >> first_assum(qspecl_then [`SND h`] strip_assume_tac) 
           >> (`(FST h, SND h) = h` by rfs[PAIR])       
            >> (`MEM (FST h, SND h) (h::np)` by fs[])
          >> fs[])    
         >- (first_assum(qspecl_then [`bl`,`np`] strip_assume_tac) 
          >> (`subpile1_backlog_trans2 bl p np` by fs[]) 
           >> rfs[subpile1_backlog_trans2_def])));
            
val Functional_to_Logical_subpile1BacklogTrans2 = Q.store_thm("Functional_to_Logical_subpile1BacklogTrans2",
 `!bl p np. subpile1_backlog_trans2 bl p np ==> (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np))))`,

 Induct_on`p`
   >- rw[]
   >- ((REPEAT STRIP_TAC
     >> Cases_on`d' = FST h`)
    >- (fs[subpile1_backlog_trans2_def]
      >> first_assum(qspecl_then [`bl`,`np`] strip_assume_tac)
       >> fs[])
     >- (fs[subpile1_backlog_trans2_def]
      >- (rw[] >> fs[FST]) 
      >- (first_assum(qspecl_then[`bl`,`np`] strip_assume_tac)
           >> fs[])))); 
   
val Functional_to_Logical_subpile2_backlog_trans2 = Q.store_thm("Functional_to_Logical_subpile2_backlog_trans2",
 `!bl p np. subpile2_backlog_trans2 bl np p ==>  (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') np ==> MEM (d',l') p))))`,

  Induct_on`np`
    >- rw[]
    >- ((REPEAT STRIP_TAC 
     >>  first_assum(qspecl_then [`bl`,`p`] strip_assume_tac)
      >> `subpile2_backlog_trans2 bl np p` by fs[subpile2_backlog_trans2_def]
       >> Cases_on`d' = FST h`)
        >- fs[subpile2_backlog_trans2_def]
        >- (`MEM (d',l') np` by (FULL_SIMP_TAC list_ss [MEM] >> rw[] >> rfs[FST]) 
         >> fs[])));       
    
     
val Logical_to_Functional_subpile2Backlog_trans = Q.store_thm("Logical_to_Functional_subpile2Backlog_trans",
  `!bl p np. (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') np ==> MEM (d',l') p)))
           ) ==>
           subpile2_backlog_trans2 bl np p`,
   
Induct_on`np`
   >- rw[subpile2_backlog_trans2_def]  
   >- ((REPEAT STRIP_TAC 
     >> rw[subpile2_backlog_trans2_def])   
      >- (Cases_on`MEM (FST h) bl`  
          >- fs[]  
          >- (first_assum(qspecl_then [`FST h`] strip_assume_tac)  
            >> ` ∀l'. MEM (FST h,l') (h::np) ⇒ MEM (FST h,l') p` by (rfs[] >> fs[]) 
	     >> first_assum(qspecl_then[`SND h`] strip_assume_tac) 
              >> fs[]))
      >- (first_assum(qspecl_then [`bl`,`p`] strip_assume_tac)
        >> rfs[subpile2_backlog_trans2_def])));
 
   
val TRANSFER_EXCLUDED_thm = Q.store_thm("TRANSFER_EXCLUDED_thm",
`TransferExcludedDec = TRANSFER_EXCLUDED`,
  (simp[FUN_EQ_THM]
  >> qx_gen_tac`params`
  >> PairCases_on `params` 
  >> Cases)
   >- (Cases
    >- (PairCases_on`p` 	
     >> PairCases_on`p'`
       >> simp[TransferExcludedDec_def,TRANSFER_EXCLUDED_def])
     >- simp[TransferExcludedDec_def,TRANSFER_EXCLUDED_def])
   >- simp[TransferExcludedDec_def,TRANSFER_EXCLUDED_def]);  
     
(*---------------------------------------------------------------------------------*)
                (* Proofs related to transfer_varSTV *)
(*---------------------------------------------------------------------------------*)

 

(*
val Functional_Transfer_to_Logical_transfer = Q.store_thm("Functional_Transfer_to_Logical_transfer",
 `! st qu l j1 j2. TransferDec (qu,st,l) j1 j2 ==> TRANSFER (qu,st,l) j1 j2` ,
     
   (REPEAT STRIP_TAC     
     >> Cases_on`j1`)
        
           >- (Cases_on`j2`
             
            >- ((PairCases_on`p` >> PairCases_on`p'`   
              >> rfs[TransferDec_def,TRANSFER_def]
               >> REPEAT STRIP_TAC
	        >> Cases_on`p3`)
            
               >- rfs[]
     	          
              (*beginning of the second subgoal of the nearest Cases_on*) 
             >-((MAP_EVERY qexists_tac [`FLAT (get_cand_pile_list (h::t) p2)`,`[]`,`p'2`] 
                >> REPEAT STRIP_TAC)
	      (*13 subgoals to prove*)
  	         
              >-  fs[NULL_EQ]
       
              >-  fs[NULL_EQ]
     
              >-  rw[]
    
              >-  metis_tac[MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
      
              >-  metis_tac[MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
     
              >-  metis_tac[]               
     
              >- metis_tac[Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]   
 
              >- metis_tac[Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]   
                  
             >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]      
   
             >-  metis_tac[Valid_Init_CandList_def,NULL_EQ]
 
             >-  rw[]
 
             >-  (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                 >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                 >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                 >> `!d. MEM d p6 ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
		 >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally] 
                 >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota]) 
  
              (*last subgoal among the 13 to discharge*)
	    >- ((MAP_EVERY qexists_tac [`t`,`h`]
              >> fs[]  
               >> REPEAT STRIP_TAC)
               (*five subgoals to deal with*)
	        >- metis_tac[subpile1_BlMem_trans2_IsCorrect,subpile1_BlMem_trans2_def]
 
                >- metis_tac[subpile1_BlMem_trans2_IsCorrect,subpile1_BlMem_trans2_def]
      
                >- metis_tac[MEM,Functional_to_Logical_subpile1BacklogTrans2,
                            Functional_to_Logical_subpile2_backlog_trans2,
                            subpile1_backlog_trans2_def,subpile2_backlog_trans2_def]

                >- metis_tac[MEM,Functional_to_Logical_subpile1BacklogTrans2,
                             Functional_to_Logical_subpile2_backlog_trans2,
                             subpile1_backlog_trans2_def,subpile2_backlog_trans2_def]
 
               >- fs[NULL_EQ])))
           (*end of the 13 intial subgoals*)
 
        >- rfs[TransferDec_def])
 
      >- rfs[TransferDec_def]);
 
val Logical_transfer_to_Functional_Transfer = Q.store_thm("Logical_transfer_to_Functional_Transfer",
 `!st qu l j1 j2. TRANSFER (qu,st,l) j1 j2 ==> TransferDec (qu,st,l) j1 j2`,

 (REPEAT STRIP_TAC
  >> Cases_on`j1`) 
 
     >- (Cases_on`j2`
 
         >- ((PairCases_on`p` >> PairCases_on`p'` >>
	      rfs[TRANSFER_def,TransferDec_def] >> REPEAT STRIP_TAC) 
             (* 14 subgoals to prove*)
	   >- (`(!d. MEM d p6 \/ MEM d p5 ==> MEM d l) ==> (!d. MEM d (p6++p5) ==> MEM d l)`
               by  FULL_SIMP_TAC list_ss [MEM_APPEND] >>
               metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])  
           >- metis_tac[PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_PileTally_def]   
           >- metis_tac[PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_PileTally_def] 
	   >- metis_tac[PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_PileTally_def] 
	   >- metis_tac[PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_PileTally_def] 
	   >- metis_tac[PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_PileTally_def] 
	   >- metis_tac[PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_PileTally_def]  
	   >- metis_tac[Valid_Init_CandList_def,NULL_EQ] 
           >- fs[Valid_Init_CandList_def]  
           >- metis_tac[LogicalLessThanQu_IMP_less_than_quota,Valid_PileTally_def] 
           >- fs[NULL_EQ] 
           >- metis_tac[subpile1_BlMem_trans2_IsCorrect] 
           >- metis_tac[Logical_to_Functional_subpileBacklogTrans2,MEM] 
           >- metis_tac[Logical_to_Functional_subpile2Backlog_trans,MEM]) 
            (*end of 14 subgoals*)
	 >- rfs[TRANSFER_def])
        >- rfs[TRANSFER_def]);	 
*)

(*--------------------end of proofs for transfer_varSTV ---------------------------*)


val Initial_Judgement_IMP_TheLogical = Q.store_thm ("Initial_Judgement_IMP_TheLogical",
 `! l j. Initial_Judgement_dec l j ==> initial_judgement l j`,

  (REPEAT STRIP_TAC >> rw[initial_judgement_def]
    >> Cases_on `j`)

     >- (PairCases_on `p`
        >> MAP_EVERY qexists_tac [`p0`,`p1`,`p2`]
           >>  rfs[Initial_Judgement_dec_def,EVERY_MEM]
             >>  metis_tac[NULL_EQ])
     >- metis_tac[Initial_Judgement_dec_def]);
  
 
val Logical_to_Functional_Initial_Judgement = Q.store_thm ("Logical_to_Functional_Initial_Judgement",
 `! l j. initial_judgement l j ==> Initial_Judgement_dec l j`,

  (REPEAT STRIP_TAC
    >> rfs [initial_judgement_def] 
       >> FULL_SIMP_TAC list_ss [Initial_Judgement_dec_def,EVERY_MEM])); 
         
  
val No_Valid_Step_After_Final = Q.store_thm("No_Valid_Step_After_Final",
 `! qu st h l w. ~ (Valid_Step (qu,st,l) (Final w) h)`,

 REPEAT STRIP_TAC
  >> rfs[Valid_Step_def]
        >- rfs[HwinDec_def]
	>- rfs[EwinDec_def]
	>- rfs[CountDec_def]
	>- rfs[TransferDec_def]
	>- rfs[ElectDec_def]
        >- rfs[TransferExcludedDec_def] 
	>- rfs[ElimCandDec_def]);
 
val COUNT_thm = Q.store_thm("COUNT_thm",
  `CountDec = COUNT`,
  simp[FUN_EQ_THM,Count_Aux_IMP_Count_Aux_dec,Count_Aux_dec_IMP_Count_Aux,FORALL_PROD,EQ_IMP_THM]);

val TRANSFER_thm = Q.store_thm("TRANSFER_thm",
  `TransferDec = TRANSFER`,
  simp[FUN_EQ_THM,Functional_Transfer_to_Logical_transfer,Logical_transfer_to_Functional_Transfer,FORALL_PROD,EQ_IMP_THM]);

val ELECT_thm = Q.store_thm("ELECT_thm",
  `ElectDec = ELECT`,
  simp[FUN_EQ_THM,Functional_to_Logical_elect,Logical_to_Functional_elect,FORALL_PROD,EQ_IMP_THM]);

val ELIM_CAND_thm = Q.store_thm("ELIM_CAND_thm",
  `ElimCandDec = ELIM_CAND`,
  simp[FUN_EQ_THM,Logical_elim_to_Functional_Elim,Functional_Elim_to_Logical_elim,FORALL_PROD,EQ_IMP_THM]);

val initial_judgement_thm = Q.store_thm("initial_judgement_thm",
  `Initial_Judgement_dec = initial_judgement`,
  rw[FUN_EQ_THM,Initial_Judgement_IMP_TheLogical,Logical_to_Functional_Initial_Judgement,EQ_IMP_THM]);
     
 
val valid_judgements_thm = Q.store_thm("valid_judgements_thm",
  `valid_judgements_dec = valid_judgements`,    
  rw[FUN_EQ_THM,valid_judgements_dec_LRC,valid_judgements_def,EQ_IMP_THM] \\ rw[]       
  >- (  
   fs[APPEND_EQ_APPEND] \\ rw[] \\ fs[LRC_APPEND,LRC_def] 
   \\ TRY(last_x_assum(assume_tac o Q.AP_TERM`LENGTH`) \\ fs[] \\ NO_TAC)
   \\ TRY (
     qpat_x_assum`Valid_Step _ j0 j1`mp_tac
     \\ simp[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_thm,ELECT_thm,TRANSFER_EXCLUDED_thm,ELIM_CAND_thm,EXISTS_MEM]
     \\ NO_TAC)
   \\ first_assum(mp_tac o SYM o Q.AP_TERM`LENGTH`)
   \\ simp_tac std_ss [LENGTH,LENGTH_EQ_NUM_compute]
   \\ rw[APPEND_EQ_SING] \\ fs[] \\ rw[] \\ fs[LRC_def] \\ rw[]
   \\ qpat_x_assum`Valid_Step _ j0 _` mp_tac
   \\ simp[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_thm,ELECT_thm,TRANSFER_EXCLUDED_thm,ELIM_CAND_thm,EXISTS_MEM]) 
  >- (    
    qmatch_assum_rename_tac`ls ≠ []`  
    \\ Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES \\ fs[] \\ rw[]
    \\ qexists_tac`HD(l++[Final w])`
    \\ Induct_on`l` \\ rw[LRC_def]
    \\ last_x_assum mp_tac
    \\ impl_tac 
    >- (
      rw[] \\ fs[]
      \\ first_x_assum(qspec_then`h::J0`mp_tac)
      \\ rw[] )
    \\ rw[]
    \\ qexists_tac`HD(l++[Final w])`
    \\ rw[]
    \\ first_x_assum(qspec_then`[]`mp_tac)
    \\ rw[]
    \\ Cases_on`l ++ [Final w]` \\ fs[]
    \\ rw[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_thm,ELECT_thm,TRANSFER_EXCLUDED_thm,ELIM_CAND_thm,EXISTS_MEM]
    \\ metis_tac[] )
);
   
val Valid_intermediate_judgements_thm = Q.store_thm ("Valid_intermediate_judegments_thm",
 `Valid_intermediate_judgements = valid_judgements`,  
   rw[FUN_EQ_THM,valid_judgements_def,Valid_intermediate_judgements_def,Valid_Step_Spec_def]);
         
val Check_Parsed_Certificate_iff_Valid_Certificate = Q.store_thm ("Check_Parsed_Certificate_iff_Valid_Certificate",
 `! params J. Check_Parsed_Certificate params J = Valid_Certificate params J`,

  Cases_on `J`
    >- rw[Check_Parsed_Certificate_def,Valid_Certificate_def]    
    >- metis_tac [Check_Parsed_Certificate_def,Valid_Certificate_def,Valid_intermediate_judgements_thm,valid_judgements_thm,initial_judgement_thm]); 



(*---------------------------------------------------------------------*)
             (*Checker adapted for TRANSFER_VarSTV*)

(*---------------------------------------------------------------------*)

(*
val Initial_Judgement_IMP_TheLogical = Q.store_thm ("Initial_Judgement_IMP_TheLogical",
 `! l j. Initial_Judgement_dec l j ==> initial_judgement l j`,

  (REPEAT STRIP_TAC >> rw[initial_judgement_def]
    >> Cases_on `j`)

     >- (PairCases_on `p`
        >> MAP_EVERY qexists_tac [`p0`,`p1`,`p2`]
           >>  rfs[Initial_Judgement_dec_def,EVERY_MEM]
             >>  metis_tac[NULL_EQ])
     >- metis_tac[Initial_Judgement_dec_def]);
    
 
val Logical_to_Functional_Initial_Judgement = Q.store_thm ("Logical_to_Functional_Initial_Judgement",
 `! l j. initial_judgement l j ==> Initial_Judgement_dec l j`,

  (REPEAT STRIP_TAC
    >> rfs [initial_judgement_def]
      >> rw[Initial_Judgement_dec_def])
         >- FULL_SIMP_TAC list_ss [EVERY_MEM]
         >- FULL_SIMP_TAC list_ss [EVERY_MEM]);
    
    
val No_Valid_Step_After_Final = Q.store_thm("No_Valid_Step_After_Final",
 `! qu st h l w. ~ (Valid_Step (qu,st,l) (Final w) h)`,
 
 REPEAT STRIP_TAC
  >> rfs[Valid_Step_def] 
        >- rfs[HwinDec_def]
	>- rfs[EwinDec_def]
	>- rfs[CountDec_def]
	>- rfs[TRANSFER_VarSTV_dec_def]
	>- rfs[ElectDec_def]
        >- rfs[TransferExcludedDec_def]
	>- rfs[ElimCandDec_def]);
  
val COUNT_thm = Q.store_thm("COUNT_thm",
  `CountDec = COUNT`,
  simp[FUN_EQ_THM,Count_Aux_IMP_Count_Aux_dec,Count_Aux_dec_IMP_Count_Aux,FORALL_PROD,EQ_IMP_THM]);
 
val TRANSFER_VarSTV_thm = Q.store_thm("TRANSFER_thm",
  `TRANSFER_VarSTV_dec = TRANSFER_VarSTV`,
  simp[FUN_EQ_THM, Logical_to_Functional_TRANSFER_VarSTV, Functional_to_Logical_TRANSFER_VarSTV,FORALL_PROD,EQ_IMP_THM]);
 
val ELECT_thm = Q.store_thm("ELECT_thm",
  `ElectDec = ELECT`,
  simp[FUN_EQ_THM,Functional_to_Logical_elect,Logical_to_Functional_elect,FORALL_PROD,EQ_IMP_THM]);

val ELIM_CAND_thm = Q.store_thm("ELIM_CAND_thm",
  `ElimCandDec = ELIM_CAND`,
  simp[FUN_EQ_THM,Logical_elim_to_Functional_Elim,Functional_Elim_to_Logical_elim,FORALL_PROD,EQ_IMP_THM]);
 
val initial_judgement_thm = Q.store_thm("initial_judgement_thm",
  `Initial_Judgement_dec = initial_judgement`,
  rw[FUN_EQ_THM,Initial_Judgement_IMP_TheLogical,Logical_to_Functional_Initial_Judgement,EQ_IMP_THM]);
      
   
val valid_judgements_thm = Q.store_thm("valid_judgements_thm",
  `valid_judgements_dec = valid_judgements`,    
  rw[FUN_EQ_THM,valid_judgements_dec_LRC,valid_judgements_def,EQ_IMP_THM] \\ rw[]       
  >- (  
   fs[APPEND_EQ_APPEND] \\ rw[] \\ fs[LRC_APPEND,LRC_def] 
   \\ TRY(last_x_assum(assume_tac o Q.AP_TERM`LENGTH`) \\ fs[] \\ NO_TAC)
   \\ TRY (
     qpat_x_assum`Valid_Step _ j0 j1`mp_tac
     \\ simp[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_VarSTV_thm,ELECT_thm,ELIM_CAND_thm,EXISTS_MEM]
     \\ NO_TAC)
   \\ first_assum(mp_tac o SYM o Q.AP_TERM`LENGTH`)
   \\ simp_tac std_ss [LENGTH,LENGTH_EQ_NUM_compute]
   \\ rw[APPEND_EQ_SING] \\ fs[] \\ rw[] \\ fs[LRC_def] \\ rw[]
   \\ qpat_x_assum`Valid_Step _ j0 _` mp_tac
   \\ simp[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_VarSTV_thm,ELECT_thm,ELIM_CAND_thm,EXISTS_MEM]) 
  >- (    
    qmatch_assum_rename_tac`ls ≠ []`  
    \\ Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES \\ fs[] \\ rw[]
    \\ qexists_tac`HD(l++[Final w])`
    \\ Induct_on`l` \\ rw[LRC_def]
    \\ last_x_assum mp_tac
    \\ impl_tac 
    >- (
      rw[] \\ fs[]
      \\ first_x_assum(qspec_then`h::J0`mp_tac)
      \\ rw[] )
    \\ rw[]
    \\ qexists_tac`HD(l++[Final w])`
    \\ rw[]
    \\ first_x_assum(qspec_then`[]`mp_tac)
    \\ rw[]
    \\ Cases_on`l ++ [Final w]` \\ fs[]
    \\ rw[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_VarSTV_thm,ELECT_thm,ELIM_CAND_thm,EXISTS_MEM]
    \\ metis_tac[] )
);
   
val Valid_intermediate_judgements_thm = Q.store_thm ("Valid_intermediate_judegments_thm",
 `Valid_intermediate_judgements = valid_judgements`,  
   rw[FUN_EQ_THM,valid_judgements_def,Valid_intermediate_judgements_def,Valid_Step_Spec_def]);
          
val Check_Parsed_Certificate_iff_Valid_Certificate = Q.store_thm ("Check_Parsed_Certificate_iff_Valid_Certificate",
 `! params J. Check_Parsed_Certificate params J = Valid_Certificate params J`,

  Cases_on `J`
    >- rw[Check_Parsed_Certificate_def,Valid_Certificate_def]    
    >- metis_tac [Check_Parsed_Certificate_def,Valid_Certificate_def,Valid_intermediate_judgements_thm,valid_judgements_thm,initial_judgement_thm]); 

*)

(*---------------------------------------------------------------------------------*)
   (* end of adapting the checker for TRANSFER_VarSTV*)

(*---------------------------------------------------------------------------------*)


val _ = export_theory();
