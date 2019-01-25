open preamble
           
val _ = new_theory "CheckerSpec";
  
 
(* The main datatypes *)

(* A candidate is represented by a CakeML string *)
val _ = Datatype`cand = Cand mlstring`;
 
(* N.B. A more idiomatic approach might be to use records rather than tuples *)
 
val _ = type_abbrev("ballots",``:(((cand list) # rat) list)``);
val _ = type_abbrev("tallies",``:(cand,rat) alist``); 
val _ = type_abbrev("piles",``:(cand # ((((cand list) # rat) list) list)) list``);
      
(* Helper functions that have nothing to do with vote counting *)
(* Sum a list of rational numbers *)
val SUM_RAT_def = Define`
  SUM_RAT ([]: ballots) = (0:rat) /\
  SUM_RAT (h::t) = (SND h) + SUM_RAT t`;
(* -- *)



(* A judgement is a state in the application of the vote counting rules.
   It is either a NonFinal state or a Final state.
*)
val _ = Datatype `
  judgement =
    NonFinal (
     (* ballots    *)               ballots #
     (* tallies    *)               tallies #
     (* piles      *)               piles #
     (* backlog of elected   *)     (cand list) #
     (* backlog of removed *)       (cand list) #
     (* elected    *)               (cand list) #
     (* continuing *)               (cand list) )
  | Final
    (* winners *) (cand list)`;

 
(* The rules *)

(* Each of rule corresponds to a step of vote counting
   A rule is of the following form:
   RULE (qu,st,l) j1 j2
   where
     (parameters of the election)
       qu is the quota (least amount of vote necessary to be elected)
       st is the number of seats
       l  is the list of initial candidates
     (transition step)
       j1 is the judgement before the rule application
       j2 is the judgement after the rule application
*)

val _ = type_abbrev("params",``:rat # num # (cand list)``);
  

val Count_Occurrences_def = Define `
    Count_Occurrences (x: rat) (l: (((cand list) # rat) list)) <=>
                         case l of
                              [] => (0: num)
                            | l0 ::ls => if (x = SND l0) then (1 + (Count_Occurrences x ls))
                                         else Count_Occurrences x ls`;

 
val Count_Occurrences_IsCorrect = Q.store_thm("Count_Occurrences_IsCorrect",
 `! r l. Count_Occurrences r l = LENGTH (FILTER (\x.  (x = r)) (MAP SND l))`, 

 Induct_on `l`
    >- rw[Count_Occurrences_def]
  
    >- ((REPEAT STRIP_TAC 
         >> Cases_on `r = SND h`)
       >- (FULL_SIMP_TAC list_ss []
         >> rw[Count_Occurrences_def])
       >- (first_assum(qspecl_then [`r`] strip_assume_tac)
         >> rw[Count_Occurrences_def])));


val ReGroup_Piles_def = tDefine "ReGroup_Piles" `
    ReGroup_Piles (l: ballots) <=> case l of
                           [] => []
                          |l0 ::ls => let k = Count_Occurrences (SND l0) ls in
                                          (l0 :: (TAKE k ls)) :: (ReGroup_Piles (DROP k ls))` 
(WF_REL_TAC `measure LENGTH ` >> simp[LENGTH]) 



(* EWIN rule *)

val EWIN_def = Define `
  EWIN ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h bl2.
      (j1 = NonFinal (u, t, p, bl, bl2, e, h))
      /\ (j2 = Final e)
      /\ ((LENGTH e) = st)`;
    
(* HWIN rule *)

val HWIN_def = Define `
  HWIN ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h bl2.
       (j1 = NonFinal (u, t, p, bl, bl2, e, h))
       /\ (j2 = Final (e++h))
       /\ ((LENGTH (e ++ h)) <= st)`;
    
(* ELIM_CAND rule *)

val get_cand_tally_def = Define `
  get_cand_tally (c:cand) (ls:tallies) =
    case ALOOKUP ls c of NONE => -1 | SOME r => r`;
 
val get_cand_pile_def = Define `
  get_cand_pile (c:cand) (ls:piles) =
    case ALOOKUP ls c of NONE => [] | SOME r => r`;

val empty_cand_pile_def = Define `
   (empty_cand_pile (c:cand) ([]:piles) = []) /\
   (empty_cand_pile c (h::t) =
      if (c = FST h) then ((c, []) :: t)
      else h :: (empty_cand_pile c t))`;

 
val Valid_Init_CandList = Define `
  Valid_Init_CandList (l: cand list) = ((l <> []) /\ ALL_DISTINCT l) `;
 
val Valid_PileTally = Define `
  Valid_PileTally t (l: cand list) = (!c. (MEM c l) <=> (MEM c (MAP FST t))) `;

(* this function checks if the piles p1 and p2 are equal except for candidate c where
   (c,[]) belongs to p2 but not necessarily to p1.
*)
(*
val subpile1_def = Define `
  subpile1 c (p1:piles) p2 ⇔
    EVERY (λp. MEM (if c = FST p then (c,[]) else p) p2) p1`;
*)
 

val subpile1_def = Define `
  subpile1 c (p1:piles) p2 ⇔
    EVERY (λp. MEM (if c = FST p then (c,[]) else p) p2) p1`;
  
(* this function checks if candidate c appears as a first component in both ps and p1 and
   also checks if all of the other members of ps belong to p1
*)

val subpile2_def = Define`
  subpile2 c (ps:piles) p1 ⇔
    EVERY (λp. if c = FST p then T else MEM p p1) ps`; 
 
(*   
val _ = overload_on("list_MEM",``λl1 l2. set l1 ⊆ set l2``);
val _ = overload_on("list_not_MEM",``λl1 l2. DISJOINT (set l1) (set l2)``);

*)
 
val equal_except_def = Define `
 ((equal_except (c: cand) l nl ) =
   ?l1 l2.
     (l = l1 ++ l2)
     /\ (nl = l1 ++ [c] ++ l2)
     /\ (~ (MEM c l1))
     /\ (~ (MEM c l2))) `;
     
val ELIM_CAND_def = Define `
  ELIM_CAND (c:cand) ((qu,st,l):params) j1 j2 =
    ?t p e h nh nba np.
     (j1 = NonFinal ([], t, p, [], [], e, h))
     /\ Valid_Init_CandList l
     /\ (!c'. MEM c' (h++e) ==> (MEM c' l))
     /\ ALL_DISTINCT (h++e)
     /\ Valid_PileTally p l
     /\ Valid_PileTally np l
     /\ LENGTH (e ++ h) > st
     /\ LENGTH e < st
     /\ ALL_DISTINCT (MAP FST t)
     /\ Valid_PileTally t l
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ MEM c h
     /\ (!d. (MEM d h ==> (?x y. (MEM (c,x) t) /\ (MEM (d,y) t) /\ ( x <= y))))
     /\ equal_except c nh h
     /\ (nba = FLAT (get_cand_pile c p))
     /\ MEM (c,[]) np
     /\ (!d'. ((d' <> c) ==>
         (!l. (MEM (d',l) p ==> MEM (d',l) np) /\ (MEM (d',l) np ==> MEM (d',l) p))))
     /\ (j2 = NonFinal (nba, t, np, [], [], e, nh))`;
  
    
(* TRANSFER rule *)


val TransferAuxSpec_def = Define `
  TransferAuxSpec ((qu,st,l):params) (ba: ballots) (t: tallies) t'
                           (p: piles) (p': piles) (bl: cand list) (bl2: cand list) 
                           (bl2': cand list) e e' h h' <=>
        (bl2 = []) 
     /\ (bl <> [])
     /\ (ba = [])
     /\ (bl2' = [])
     /\ (t' = t)
     /\ (e' = e)
     /\ (h' = h)
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ (!d. MEM d bl ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ (Valid_PileTally p' l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ ALL_DISTINCT (MAP FST p)`;
    (* /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))`;*)

val TRANSFER_def = Define `
  TRANSFER ((qu,st,l):params) j1 j2 =
    ? nba t p bl e h nbl np.
     (j1 = NonFinal ([], t, p, bl, [], e, h))
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ (Valid_PileTally np l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ (!d. MEM d bl ==> MEM d l)
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ (!d. MEM d bl ==> (!l'. MEM (d,l') p ==> l' <> []))
     /\ (ALL_DISTINCT (MAP FST p))
     /\ ? l c.
              ((bl = c::l)
           /\ (nbl = l)
           /\ (nba = LAST (get_cand_pile c p))
           /\ (MEM (c,[]) np)
           /\ (!d'. ((d' <> c) ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)
                            /\ (MEM (d',l') np ==> MEM (d',l') p)))))
           /\ (j2 = NonFinal (nba, t, np, nbl, [], e, h))`;


(* ------------------TRANSFER2-------------------------*)
(* transferring all of the bl in one step *)
 
(*
val get_cand_pile_list_def = Define `
  (get_cand_pile_list ([]: cand list) (ls: piles) = []) /\
    (get_cand_pile_list (l0::l1) ls = (case ALOOKUP ls l0 of NONE =>
              (get_cand_pile_list l1 ls) | SOME r => (r ++ (get_cand_pile_list l1 ls)))) `;



val TRANSFER_def = Define `
   TRANSFER ((qu,st,l):params) j1 j2 =
    ? nba t p bl e h nbl np.
     (j1 = NonFinal ([], t, p, bl, [], e, h))
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ (Valid_PileTally np l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ ? l c. 
         ((bl = c::l)
      /\ (NULL nbl)
      /\ nba = FLAT (get_cand_pile_list bl p)
      /\ (!d. MEM d bl ==> MEM (d,[]) np) 
      /\ (!d'. (~ MEM d' bl) ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)
                            /\ (MEM (d',l') np ==> MEM (d',l') p))))
           /\ (j2 = NonFinal (nba, t, np, nbl, [], e, h))`;
*)

(*-----------------end of definitions for transfer2---------------*)

(* COUNT rule *)
 
val first_continuing_cand_def = Define `
   first_continuing_cand (c: cand) (b: cand list)  (h: cand list) =
      (?l1 l2. (b = l1 ++ c::l2) /\ (!d. MEM d l1 ==> ~ MEM d h))`;
     
val COUNT_def = Define `
         (COUNT (qu,st,l) j1 j2 = ? ba t nt p np bl e h.
          (j1 = NonFinal (ba, t, p, bl, [], e, h))
       /\ (!d. MEM d (h++e) ==> MEM d l)
       /\ ALL_DISTINCT (h++e)
       /\ (Valid_PileTally t l)
       /\ (Valid_PileTally nt l)
       /\ (Valid_PileTally p l)
       /\ (Valid_PileTally np l)
       /\ (Valid_Init_CandList l)
       /\ ALL_DISTINCT (MAP FST p)
       /\ ALL_DISTINCT (MAP FST t)
       /\ ALL_DISTINCT (MAP FST np)
       /\ ALL_DISTINCT (MAP FST nt)
       /\ (ba <> [])
       /\ (h <> [])
       /\ (!c. MEM c l ==>
                            ((MEM c h ==>
                             ?(l: ((cand list) # rat) list).
                               (l = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                            /\ (!l'. MEM (c,l') np ==> (l' = (get_cand_pile c p) ++ [l]))
                            /\ (!r. MEM (c,r) nt ==> (r = (get_cand_tally c t) + SUM_RAT (l))))
                            /\ (~ MEM c h ==>
                                           (!l'. MEM c l /\ MEM (c,l') np <=> MEM c l /\ MEM (c,l') p)
                                        /\ (!r. MEM c l /\ MEM (c,r) t <=> MEM c l /\ MEM (c,r) nt))))
       /\ (j2 = NonFinal ([], nt, np, bl, [], e, h)))`;
  
   
(* ELECT rule *)
 
val tally_comparison_def = Define `
  tally_comparison (t:tallies) c1 c2 ⇔ (get_cand_tally c2 t <= get_cand_tally c1 t)`;
 
(*the Gregorian method for updating transfer value*)
val update_cand_trans_val_def = Define `
    (update_cand_trans_val (qu:rat) (c:cand) (t:tallies) (p: ((cand list) # rat) list) =
        MAP (λr. r * (((get_cand_tally c t) - qu) / (get_cand_tally c t)))
          (MAP SND (p)))`;
    
(*
val ACT_TransValue_def = Define `
    ACT_TransValue (p: piles) (t: tallies) (qu: rat) (c: cand) <=>
       let Sum_Parcel = SUM_RAT  (LAST (get_cand_pile c p))
         in
           let transValue = (((get_cand_tally c t) - qu) / Sum_Parcel)
             in
               case ((\r. r <= 0) Sum_Parcel) of
                  T => 1
                | _ => (case ((\r. 1 < r) transValue) of
                         T => 1
                        |_ => transValue) `;
*)


val ACT_TransValue_def = Define `
    ACT_TransValue (p: piles) (t: tallies) (qu: rat) (c: cand) <=>
       let Sum_Parcel = SUM_RAT  (LAST (get_cand_pile c p))
         in
            case ((\r. r <> 0) Sum_Parcel) of
               T =>  let transValue = (((get_cand_tally c t) - qu) / Sum_Parcel)
                       in
                       (case ((\r. 0 < r) Sum_Parcel) of
                        T => (case ((\r. r < 1) transValue) of
                               T => transValue
                               |_ => 1)
                      |_ => 1)
             |_ => 1 `; 



 
val update_cand_transVal_ACT_def = Define `
    update_cand_transVal_ACT (qu:rat) (c:cand) (t:tallies) (p: piles) <=>
        MAP (λr. r * (ACT_TransValue p t qu c))
          (MAP SND (LAST (get_cand_pile c p)))`;


val update_cand_pile_ACT = Define `
          (update_cand_pile_ACT (qu: rat) t ([]: cand list) p1 p2 ⇔ T)
       /\ (update_cand_pile_ACT qu t (l0::ls) p1 p2 ⇔
            let Flat_pile2 = LAST (get_cand_pile l0 p2)
              in
               let Flat_pile1 = LAST (get_cand_pile l0 p1)
                in
                 (MAP FST Flat_pile2 = MAP FST (Flat_pile1))
              /\ (MAP SND Flat_pile2 = update_cand_transVal_ACT qu l0 t p1) /\
                 update_cand_pile_ACT qu t ls p1 p2)`;
   
 
val ELECT1_def = Define `
  ELECT1 ((qu,st,l):params) j1 j2 =
  (? t p bl e h nh ne np nbl l1 .
    (j1 = NonFinal ([], t, p, bl, [], e, h))
    /\ (l1 <> [])
    /\ (SORTED (tally_comparison t) l1)
    /\ (!c. MEM c l1 ==> (!(r :rat). MEM (c,r) t ==> (qu <= r)))
    /\ (LENGTH (l1 ++ e) <= st)
    /\ (!c. MEM c l1 \/ MEM c nh ==> MEM c h)
    /\ (!c. MEM c h ==> MEM c nh \/ MEM c l1)
    /\ ALL_DISTINCT h
    /\ ALL_DISTINCT (l1 ++ nh)
    /\ ALL_DISTINCT (l1 ++ e)
    /\ ALL_DISTINCT ne
    /\ (!c. MEM c l1 \/ MEM c e ==> MEM c ne)
    /\ (!c. MEM c ne ==> MEM c e \/ MEM c l1)
    /\ (!c. MEM c h /\ (~ MEM c l1) ==> (!l'. MEM (c,l') np <=> MEM (c,l') p))
    /\ ALL_DISTINCT (MAP FST p)
    /\ ALL_DISTINCT (MAP FST t)
    /\ ALL_DISTINCT (MAP FST np)
    /\ (0 < qu)
    /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') np ==>
                           let (PileCand_c = FLAT (get_cand_pile c p))
                            in
                             let (Flat_l' = FLAT l')
	                      in
                               (MAP FST Flat_l' = MAP FST PileCand_c)
                            /\ (MAP SND (Flat_l') = update_cand_trans_val qu c t PileCand_c)))
    /\ (nbl = bl ++ l1)
    /\ (Valid_Init_CandList l)
    /\ (Valid_PileTally t l)
    /\ (Valid_PileTally p l)
    /\ (Valid_PileTally np l)
    /\ (!c. MEM c ne ==> MEM c l)
    /\ (!c. MEM c h ==> MEM c l)
    /\ (j2 = NonFinal ([], t, np, nbl, [], ne, nh)))`;



val TRANSFER_EXCLUDED_def = Define `
    TRANSFER_EXCLUDED (qu,st,l) j1 j2 <=>
      (? ba ba' t t' p p' bl bl' bl2 bl2' e e' h h'. 
          (j1 = NonFinal (ba,t,p,bl,bl2,e,h))
     /\ ? bs c.
        (bl2 = c :: bs)
     /\ ((MEM (c, []) p' ==> (bl2' = []))
        /\ (~ MEM (c, []) p' ==> (bl2' = bl2)))
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ ALL_DISTINCT (MAP FST p')
     /\ (Valid_PileTally p' l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ (!d'. ~ MEM d' [c] ==>
        (!l'. (MEM (d',l') p ==> MEM (d',l') p')) /\ (!l'. (MEM (d',l') p' ==> MEM (d',l') p)))
     /\ ? xs. xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
     /\ (ba' = LAST xs)
     /\ MEM (c, TAKE ((LENGTH xs) - 1) xs) p'
     /\ (ba = []) /\ (t = t') /\ (e = e') /\ (h = h') /\ (bl = bl')
     /\ (j2 = NonFinal (ba',t',p',bl',bl2',e',h'))) /\ F`;
 

val ELECT_def = Define `
  ELECT ((qu,st,l):params) j1 j2 =
  (? t p bl e h nh ne np nbl l1 .
    (j1 = NonFinal ([], t, p, bl, [], e, h))
    /\ (l1 <> [])
    /\ (SORTED (tally_comparison t) l1)
    /\ (!c. MEM c l1 ==> (!(r :rat). MEM (c,r) t ==> (qu <= r)))
    /\ (LENGTH (l1 ++ e) <= st)
    /\ (!c. MEM c l1 \/ MEM c nh ==> MEM c h)
    /\ (!c. MEM c h ==> MEM c nh \/ MEM c l1)
    /\ ALL_DISTINCT h
    /\ ALL_DISTINCT (l1 ++ nh)
    /\ ALL_DISTINCT (l1 ++ e)
    /\ ALL_DISTINCT ne
    /\ (!c. MEM c l1 \/ MEM c e ==> MEM c ne)
    /\ (!c. MEM c ne ==> MEM c e \/ MEM c l1)
    /\ (!c. MEM c h /\ (~ MEM c l1) ==> (!l'. MEM (c,l') np <=> MEM (c,l') p))
    /\ ALL_DISTINCT (MAP FST p)
    /\ ALL_DISTINCT (MAP FST t)
    /\ ALL_DISTINCT (MAP FST np)
    /\ (0 < qu)
    /\ (nbl = bl ++ l1)
    /\ (Valid_Init_CandList l)
    /\ (Valid_PileTally t l)
    /\ (Valid_PileTally p l)
    /\ (Valid_PileTally np l)
    /\ (!c. MEM c ne ==> MEM c l)
    /\ (!c. MEM c h ==> MEM c l)
    /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') p ==> l' <> []))
(*   /\ (!c. MEM c l1 ==> SUM_RAT (LAST (get_cand_pile c p)) <> 0) *)
    /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') np ==> l' <> []))
(*    /\ (!c. MEM c l1 ==> SUM_RAT (LAST (get_cand_pile c np)) <> 0) *)
    /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') np ==>
                           let (PileCand_c = LAST (get_cand_pile c p))
                            in
                             let (Flat_l' = LAST l')
                              in
                               (MAP FST Flat_l' = MAP FST PileCand_c)
                            /\ (MAP SND (Flat_l') = update_cand_transVal_ACT qu c t p)))
    /\ (j2 = NonFinal ([], t, np, nbl, [], ne, nh)))`;
 

(* Initial judgement *)
   
val initial_judgement_def = Define `
   initial_judgement (l: cand list) j =
     ? ba t p bl bl2 e h.
     (j = NonFinal (ba, t, p, bl, bl2, e, h))
     /\ (!c. MEM c (MAP SND t) ==> (c = 0))
     /\ (!c. MEM c (MAP SND p) ==> (c = []))
     /\ (bl = [])
     /\ (bl2 = [])
     /\ (e = [])
     /\ (h = l)`;
  

(*-------------------------------------------------------------------------------*)
    (* adapting the checker for transfer_varSTV *)
 
(*-------------------------------------------------------------------------------*)

(*

val valid_judgements_def =  Define `
 valid_judgements params J ⇔
   (J <> []) /\ (∃w. LAST J = Final w)
   /\ (! J0 J1 j0 j1.
         (J = J0 ++ [j0;j1]++ J1) ==>
           ((HWIN params j0 j1)
           \/ (EWIN params j0 j1)
           \/ (COUNT params j0 j1)
           \/ (TRANSFER_VarSTV params j0 j1)
           \/ (ELECT params j0 j1)
           \/ (?c. MEM c (SND(SND params)) /\ ELIM_CAND c params j0 j1)))`;
  
 
val Valid_Step_Spec_def = Define `
 Valid_Step_Spec params j0 j1 = 
          ((HWIN params j0 j1)
           \/ (EWIN params j0 j1)
           \/ (COUNT params j0 j1)
           \/ (TRANSFER_VarSTV params j0 j1)
           \/ (ELECT params j0 j1)
           \/ (?c. MEM c (SND(SND params)) /\ ELIM_CAND c params j0 j1))`;
    
val Valid_intermediate_judgements_def = Define `
 Valid_intermediate_judgements params J = 
  ((J <> []) /\ (?w. LAST J = Final w)
  /\ (! J0 J1 j0 j1.
       (J = J0 ++ [j0;j1] ++ J1) ==> Valid_Step_Spec params j0 j1))`;
   
val Valid_Certificate_def = Define `
  (Valid_Certificate params [] ⇔ F) /\
  (Valid_Certificate params (first_judgement::rest_judgements) ⇔
     initial_judgement (SND(SND params)) first_judgement /\
     Valid_intermediate_judgements params (first_judgement::rest_judgements))`;
*)     
(*--------------------------------------------------------------------------------*)
   (* end of adapting the checker for transfer_varSTV *)

(*--------------------------------------------------------------------------------*)



(* -------------------------------------------------------------------------------*)
      (* the ANU_Union checker *)

(*--------------------------------------------------------------------------------*)


(* Valid list of judgements *)

val valid_judgements_def =  Define `
 valid_judgements params J ⇔
   (J <> []) /\ (∃w. LAST J = Final w)
   /\ (! J0 J1 j0 j1.
         (J = J0 ++ [j0;j1]++ J1) ==>
           ((HWIN params j0 j1)
           \/ (EWIN params j0 j1)
           \/ (COUNT params j0 j1)
           \/ (TRANSFER params j0 j1)
           \/ (ELECT params j0 j1)
           \/ (TRANSFER_EXCLUDED params j0 j1) 
           \/ (?c. MEM c (SND(SND params)) /\ ELIM_CAND c params j0 j1)))`;
	   
val Valid_Step_Spec_def = Define `
 Valid_Step_Spec params j0 j1 =
          ((HWIN params j0 j1)
           \/ (EWIN params j0 j1)
           \/ (COUNT params j0 j1)
           \/ (TRANSFER params j0 j1)
           \/ (ELECT params j0 j1)
           \/ (TRANSFER_EXCLUDED params j0 j1) 
           \/ (?c. MEM c (SND(SND params)) /\ ELIM_CAND c params j0 j1))`;
 
val Valid_intermediate_judgements_def = Define `
 Valid_intermediate_judgements params J =
  ((J <> []) /\ (?w. LAST J = Final w)
  /\ (! J0 J1 j0 j1.
       (J = J0 ++ [j0;j1] ++ J1) ==> Valid_Step_Spec params j0 j1))`;

val Valid_Certificate_def = Define `
  (Valid_Certificate params [] ⇔ F) /\
  (Valid_Certificate params (first_judgement::rest_judgements) ⇔
     initial_judgement (SND(SND params)) first_judgement /\
     Valid_intermediate_judgements params (first_judgement::rest_judgements))`;


(*--------------------------------------------------------------------------------*)
             (* end of the ANU_Union checker *)

(*--------------------------------------------------------------------------------*)
val _ = export_theory();
 
