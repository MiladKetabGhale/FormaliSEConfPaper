open preamble CheckerSpecTheory
         
val _ = new_theory "Checker";
 
(* TODO: move to HOL *)
val LRC_APPEND = Q.store_thm("LRC_APPEND",
  `∀l1 l2 x y.
   LRC R (l1 ++ l2) x y ⇔
   ∃z. LRC R l1 x z ∧ LRC R l2 z y`,
  Induct \\ rw[LRC_def] \\ metis_tac[])
(* -- *)
 
val EwinDec_def = Define `
  (EwinDec ((qu,st,l):params) (NonFinal (_,_,_,_,_,e,_)) (Final e')
     ⇔ (e = e') /\ LENGTH e = st) ∧
  (EwinDec _ _ _ ⇔ F)`;
 
val HwinDec_def = Define `
  (HwinDec ((qu,st,l):params) (NonFinal (_,_,_,_,_,e,h)) (Final e')
    ⇔ (e' = e ++ h) ∧ (LENGTH (e++h) ≤ st)) ∧
  (HwinDec _ _ _ = F)`;
  
val equal_except_dec_def = Define `
     (equal_except_dec (c :cand) [] = [])
  /\ (equal_except_dec c (h::t) = (if c = h then t
                                  else h:: equal_except_dec c t)) `;

val Valid_PileTally_dec1_def = Define `
        (Valid_PileTally_dec1 [] (l: cand list) ⇔ T)
     /\ (Valid_PileTally_dec1 (h::t) l ⇔ (MEM (FST h) l) /\ (Valid_PileTally_dec1 t l)) `;


val Valid_PileTally_dec2_def = Define `
        (Valid_PileTally_dec2 t ([]: cand list) ⇔ T)
     /\ (Valid_PileTally_dec2 t (l0::ls) ⇔ if (MEM l0 (MAP FST t))
                                                then (Valid_PileTally_dec2 t ls)
                                           else F) `;


val _ = overload_on("list_MEM",``λl1 l2. set l1 ⊆ set l2``);
val _ = overload_on("list_not_MEM",``λl1 l2. DISJOINT (set l1) (set l2)``);

 
val list_MEM_dec_def = Define `
      (list_MEM_dec [] l ⇔ T)
   /\ (list_MEM_dec (h::t) l ⇔ (MEM h l) /\ (list_MEM_dec t l))`;
 

val less_than_quota_def = Define `
  less_than_quota qu l ls <=>
    EVERY (λh. get_cand_tally h l < qu) ls`;

val bigger_than_cand_def = Define `
  bigger_than_cand c t ls <=>
    EVERY (λh0. get_cand_tally c t <= get_cand_tally h0 t) ls`;
 
val All_NON_EMPTY_def = Define `
    ALL_NON_EMPTY p ls <=>
     EVERY (λl0. get_cand_pile l0 p <> []) ls `;
  
val get_cand_pile_list_def = Define `
  (get_cand_pile_list ([]: cand list) (ls: piles) = []) /\
    (get_cand_pile_list (l0::l1) ls = (case ALOOKUP ls l0 of NONE =>
              (get_cand_pile_list l1 ls) | SOME r => (r ++ (get_cand_pile_list l1 ls)))) `;


val subpile1_BlMem_trans2_def = Define `
  (subpile1_BlMem_trans2 (p: piles) [] <=> T) /\
  (subpile1_BlMem_trans2 p (l0::ls) <=> MEM (l0, []) p /\ (subpile1_BlMem_trans2 p ls))`;   
 
val subpile1_backlog_trans2_def = Define `
    (subpile1_backlog_trans2 bl (p1: piles) (p2: piles)) <=>
      EVERY (λp. MEM (if MEM (FST p) bl then (FST p,[]) else p) p2) p1`;
 
val subpile2_backlog_trans2_def = Define`
    subpile2_backlog_trans2 bl (ps:piles) p1 ⇔
      EVERY (λp. if MEM (FST p) bl then T else MEM p p1) ps`; 

(*
val ALL_NON_ZERO_def = Define `
    ALL_NON_ZERO p ls <=>
     EVERY(λl0. SUM_RAT (LAST (get_cand_pile l0 p)) <> 0) ls`;
*) 

val AppendAllAux_def = Define `
     AppendAllAux (bs: ballots) x <=> bs ++ (FLAT (SND x))`;
  
val APPEND_ALL_ACC_def = Define `
    APPEND_ALL_ACC acc (p: piles) <=> FOLDL AppendAllAux acc p` ; 
   
val APPEND_ALL_def = Define `
    APPEND_ALL p <=> APPEND_ALL_ACC [] p`; 
 
val ALL_EMPTY_def = Define `
    ALL_EMPTY l p <=> EVERY (\c. if MEM c l then MEM (c,[]) p else F) l` ;

val ElimCandDec_def = Define `
  (ElimCandDec c ((qu,st,l):params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
     (NULL bl') /\ (NULL bl2) /\ (NULL ba) /\ (NULL bl) /\ (NULL bl2') /\ (t = t') /\ (e = e')
   /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (list_MEM_dec (h++e) l)
   /\ (ALL_DISTINCT (h++e))
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ ALL_DISTINCT (MAP FST t)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (MEM c h)
   /\ (less_than_quota qu t h)
   /\ (h' = equal_except_dec c h)
   /\ (bigger_than_cand c t h)
   /\ (ba' = FLAT (get_cand_pile c p))
   /\ (MEM (c,[]) p')
   /\ (subpile1 c p p') /\ (subpile2 c p' p))
   /\ (ElimCandDec c _ (Final _ ) _ = F)
   /\ (ElimCandDec c _ _ (Final _ ) = F)`;
   

val TransferAuxDec_def = Define `
  (TransferAuxDec ((qu,st,l):params) (ba: ballots) (t: tallies) t'
                           (p: piles) (p': piles) (bl: cand list) (bl2: cand list)  
                           (bl2': cand list) e e' h h')  ⇔
      (NULL bl2)
   /\ (e' = e)
   /\ (h' = h)
   /\ (t' = t)
   /\ (LENGTH e < st)
   /\ (list_MEM_dec (h++e) l)
   /\ (list_MEM_dec bl l)
   /\ ALL_DISTINCT (h++e)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (ALL_DISTINCT (MAP FST t))
   /\ ALL_DISTINCT (MAP FST p)
   /\ (~ NULL bl)
   /\ (NULL ba)
   /\ (NULL bl2')`;

val TransferCadeDec_def = Define `
  (TransferCadeDec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
         (TransferAuxDec (qu,st,l) ba t t' p p' bl bl2 bl2' e e' h h')
      /\ (case bl of [] => F | hbl::tbl =>
              (tbl = []) /\ (bl' = []) /\ (ba' = APPEND_ALL p)
           /\ (~ NULL (get_cand_pile hbl p)) /\ (ALL_EMPTY l p') /\ (h' = l))) ∧
  (TransferCadeDec _ (Final _) _ = F) /\
  (TransferCadeDec _ _ (Final _) = F)`;



val TransferActDec_def = Define `
  (TransferActDec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
      (TransferAuxDec (qu,st,l) ba t t' p p' bl bl2 bl2' e e' h h')
   /\ (less_than_quota qu t h)
   /\ (case bl of [] => F | hbl::tbl =>
         let gcp = get_cand_pile hbl p in
              (~ NULL gcp) /\ (MEM hbl l)
           /\ (bl' = tbl) /\ (ba' = LAST gcp) /\ (MEM (hbl,[]) p')
           /\ (subpile1 hbl p p') /\ (subpile2 hbl p' p))) ∧
  (TransferActDec _ (Final _) _ = F) /\
  (TransferActDec _ _ (Final _) = F)`;
  

val TransferActSpec_def = Define `
  TransferActSpec ((qu,st,l):params) j1 j2 =
    ? ba nba t nt p np bl nbl bl2 nbl2 e ne h nh.
     (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
     /\ (TransferAuxSpec (qu,st,l) ba t nt p np bl bl2 nbl2 e ne h nh)
     /\ (!c'. MEM c' h ==> ? x. MEM (c',x) t /\ (x < qu)) 
     /\ ? l' c.
              ((bl = c::l')
           /\ (MEM c l)
           /\ (!l''. MEM (c,l'') p ==> l'' <> [])
           /\ (nbl = l')
           /\ (nba = LAST (get_cand_pile c p))
           /\ (MEM (c,[]) np)
           /\ (!d'. ((d' <> c) ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)
                            /\ (MEM (d',l') np ==> MEM (d',l') p)))))
           /\ (j2 = NonFinal (nba, nt, np, nbl, nbl2, ne, nh))`;

val TransferVicDec_def = Define `
  (TransferVicDec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
         (TransferAuxDec (qu,st,l) ba t t' p p' bl bl2 bl2' e e' h h')
      /\ (less_than_quota qu t h)
      /\ (case bl of [] => F | hbl::tbl =>
           let gcp = get_cand_pile hbl p in
              (bl' = tbl) /\ (~ NULL gcp) /\ (ba' = FLAT gcp)
           /\ (MEM (hbl,[]) p')
           /\ (subpile1 hbl p p') /\ (subpile2 hbl p' p))) ∧
  (TransferVicDec _ (Final _) _ = F) /\
  (TransferVicDec _ _ (Final _) = F)`;


val TransferActVarDec_def = Define `
  (TransferActVarDec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
         (TransferAuxDec (qu,st,l) ba t t' p p' bl bl2 bl2' e e' h h')
      /\ (less_than_quota qu t h)
      /\ (case bl of [] => F | hbl::tbl =>
         (bl' = [])
         /\ (ba' = FLAT (get_cand_pile_list (hbl::tbl) p))
         /\ (subpile1_BlMem_trans2 p' (hbl::tbl))
         /\ (subpile1_backlog_trans2 (hbl::tbl)  p p') /\ (subpile2_backlog_trans2 (hbl::tbl) p' p))) ∧
  (TransferActVarDec _ (Final _) _ = F) /\
  (TransferActVarDec _ _ (Final _) = F)`;


val TransferDec_def = Define `
  (TransferDec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
       (NULL bl2) /\ (NULL bl2') /\ (NULL ba) /\ (e = e') /\ (h = h') /\ (t = t')
   /\ (LENGTH e < st)
   /\ (list_MEM_dec (h++e) l)
   /\ ALL_DISTINCT (h++e)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (ALL_DISTINCT (MAP FST t))
   /\ (list_MEM_dec bl l)
   /\ (less_than_quota qu t h)
   /\ (ALL_NON_EMPTY p bl)
   /\ (ALL_DISTINCT (MAP FST p))
   /\ (case bl of [] => F | hbl::tbl =>
         (bl' = tbl)
         /\ (ba' = LAST (get_cand_pile hbl p))
         /\ (MEM (hbl,[]) p')
         /\ (subpile1 hbl p p') /\ (subpile2 hbl p' p))) ∧
  (TransferDec _ (Final _) _ = F) /\
  (TransferDec _ _ (Final _) = F)`;


(*------------------------------*)
(* decidable TRANSFER2*)

 
val subpile1_BlMem_trans2_def = Define `
  (subpile1_BlMem_trans2 (p: piles) [] <=> T) /\
  (subpile1_BlMem_trans2 p (l0::ls) <=> MEM (l0, []) p /\ (subpile1_BlMem_trans2 p ls))`;   
 
(* 
val subpile1_backlog_trans2_def = Define `
    (subpile1_backlog_trans2 bl (p1: piles) (p2: piles)) <=>
      EVERY (λp. MEM (if MEM (FST p) bl then (FST p,[]) else p) p2) p1`;
 
val subpile2_backlog_trans2_def = Define`
    subpile2_backlog_trans2 bl (ps:piles) p1 ⇔
      EVERY (λp. if MEM (FST p) bl then T else MEM p p1) ps`; 


val TransferDec_def = Define `
   (TransferDec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
       (NULL bl2) /\ (NULL bl2') /\ (NULL ba) /\ (e = e') /\ (h = h') /\ (t = t')
   /\ (LENGTH e < st)
   /\ (list_MEM_dec (h++e) l)
   /\ ALL_DISTINCT (h++e)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (ALL_DISTINCT (MAP FST t))
   /\ (less_than_quota qu t h)
   /\ (case bl of [] => F | hbl::tbl =>
         (bl' = [])
         /\ (ba' = FLAT (get_cand_pile_list (hbl::tbl) p))
         /\ (subpile1_BlMem_trans2 p' (hbl::tbl))
         /\ (subpile1_backlog_trans2 (hbl::tbl)  p p') /\ (subpile2_backlog_trans2 (hbl::tbl) p' p))) ∧
  (TransferDec _ (Final _) _ = F) /\
  (TransferDec _ _ (Final _) = F)`;
*)

(*----------- end of definitions for transfer2 -------------------*)


val first_continuing_cand_dec_def = Define `
  (first_continuing_cand_dec (c:cand) ([]: cand list)  (h: cand list) ⇔ F) /\
  (first_continuing_cand_dec c (b0::bs) h =
    if (c = b0) then T
    else if (~ MEM b0 h) /\ (first_continuing_cand_dec c bs h) then T
    else F)`;
  
val COUNTAux_dec_def = Define `
     (COUNTAux_dec p np t t' ba h [] <=> T)
  /\ (COUNTAux_dec p np t t' ba  h (l0::ls) <=>
      (let (l' = FILTER (λb. (first_continuing_cand_dec l0 (FST b) h)) ba)
       in
          if (MEM l0 h) then
                (get_cand_pile l0 np = (get_cand_pile l0 p) ++[l']) /\
                (get_cand_tally l0 t' = (get_cand_tally l0 t) + SUM_RAT (l'))
           else
                (get_cand_pile l0 np = get_cand_pile l0 p) /\
                (get_cand_tally l0 t' = get_cand_tally l0 t)) /\
	(COUNTAux_dec p np t t' ba h ls))`;
  

val CountDec_def = Define `
   (CountDec ((st, qu, l): params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e', h')) ⇔
    (COUNTAux_dec p p' t t' ba h l)
    /\ (bl2 = bl2') /\ (NULL bl2) /\ (bl = bl') /\ (e = e') /\ (h = h')
    /\ ALL_DISTINCT (h++e)
    /\ ALL_DISTINCT (MAP FST p)
    /\ (list_MEM_dec (h++e) l)
    /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
    /\ (Valid_PileTally_dec1 t' l) /\ (Valid_PileTally_dec2 t' l)
    /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
    /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
    /\ ALL_DISTINCT (MAP FST p')
    /\ ALL_DISTINCT (MAP FST t')
    /\ (~ (NULL l)) /\ (ALL_DISTINCT l)
    /\ ALL_DISTINCT (MAP FST t)
    /\ ~ (NULL ba)
    /\ ~ (NULL h)
    /\ (ba' = [])) /\
   (CountDec _ (Final _) _ = F) /\
   (CountDec _ _ (Final _) = F)`;
 
  
val take_append_def = Define `
   (take_append (l0::ls) (h::t) = (take_append ls t)) ∧
   (take_append l1 _ = l1)`;

val eqe_list_dec_def = Define `
     (eqe_list_dec ([]: cand list) l1 l2 ⇔ list_MEM_dec l1 l2)
  /\ (eqe_list_dec (l0::ls) l1 l2 ⇔ (~ MEM l0 l1) /\ (MEM l0 l2) /\ eqe_list_dec ls l1 l2)`;


val eqe_list_dec2_def = Define `
    eqe_list_dec2 l0 l1 l = EVERY (\l'. MEM l' l0 \/ MEM l' l1) l`


val bigger_than_quota = Define `
  bigger_than_quota ls (t:tallies) (qu:rat) =
    EVERY (λl0. qu ≤ get_cand_tally l0 t) ls`;

(* this function takes two lists l1 and l and checks if the given piles p1 and p2 are equal for
   all of the members of l1 which do not belong to l *)
val piles_eq_list_def = Define `
     (piles_eq_list ([]: cand list) l p1 p2 = T)
  /\ (piles_eq_list (l0::ls) l p1 p2 =
          if ~ (MEM l0 l)
              then (get_cand_pile l0 p1 = get_cand_pile l0 p2) /\ (piles_eq_list ls l p1 p2)
          else (piles_eq_list ls l p1 p2))`; 
      
val update_cand_pile = Define `
          (update_cand_pile (qu: rat) t ([]: cand list) p1 p2 ⇔ T)
       /\ (update_cand_pile qu t (l0::ls) p1 p2 ⇔
            let Flat_pile2 = FLAT (get_cand_pile l0 p2)
	      in
	       let Flat_pile1 = FLAT (get_cand_pile l0 p1)
	        in
                 (MAP FST Flat_pile2 = MAP FST (Flat_pile1))
              /\ (MAP SND Flat_pile2 = update_cand_trans_val qu l0 t Flat_pile1) /\
                 update_cand_pile qu t ls p1 p2)`;
     
(*
val ACT_TransValue_def = Define `
    ACT_TransValue (p: ((cand list) # rat) list) (t: tallies) (qu: rat) (c: cand) <=>
       let Sum_Parcel = SUM_RAT (MAP SND p)
         in
           let transValue = (((get_cand_tally c t) - qu) / Sum_Parcel)
             in
               case ((\r. r <= 0) Sum_Parcel) of
                  T => 1
                | _ => (case ((\r. 1 < r) Sum_Parcel) of
                         T => 1
                        |_ => Sum_Parcel) `;


val update_cand_transVal_ACT_def = Define `
    update_cand_transVal_ACT (qu:rat) (c:cand) (t:tallies) (p: ((cand list) # rat) list) <=>
        MAP (λr. r * (ACT_TransValue p t qu c))
          (MAP SND p)`;


val update_cand_pile_ACT = Define `
          (update_cand_pile_ACT (qu: rat) t ([]: cand list) p1 p2 ⇔ T)
       /\ (update_cand_pile_ACT qu t (l0::ls) p1 p2 ⇔
            let Flat_pile2 = LAST (get_cand_pile l0 p2)
              in
               let Flat_pile1 = LAST (get_cand_pile l0 p1)
                in
                 (MAP FST Flat_pile2 = MAP FST (Flat_pile1))
              /\ (MAP SND Flat_pile2 = update_cand_transVal_ACT qu l0 t Flat_pile1) /\
                 update_cand_pile_ACT qu t ls p1 p2)`;
*)

val ElectDec = Define `
     (ElectDec ((qu,st,l): params)
           (NonFinal (ba, t, p, bl, bl2, e, h))
           (NonFinal (ba', t', p', bl', bl2', e',h')) <=>
              let (l1 = DROP (LENGTH bl) bl')
                 in
                   (SORTED (tally_comparison t) l1)
                /\ (ALL_DISTINCT (l1 ++ e))
		/\ (bl2 = bl2') /\ (bl2 = [])
                /\ (ba = []) /\ (ba' = [])
                /\ (t = t')
                /\ (~ (NULL l1))
                /\ (bigger_than_quota l1 t qu)
                /\ (0 < qu)
                /\ (LENGTH (l1 ++ e) <= st)
                /\ (eqe_list_dec l1 h' h)
                /\ (eqe_list_dec2 l1 h' h)
                /\ ALL_DISTINCT h
                /\ ALL_DISTINCT (l1 ++ h')
                /\ ALL_DISTINCT e'
                /\ (eqe_list_dec l1 e e')
                /\ (eqe_list_dec2 l1 e e')
                /\ (piles_eq_list h l1 p p')
                /\ ALL_DISTINCT (MAP FST p)
                /\ ALL_DISTINCT (MAP FST t)
                /\ ALL_DISTINCT (MAP FST p')
                /\ (~ (NULL l))
                /\ ALL_DISTINCT l
                /\ (bl' = bl ++ l1)
                /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
                /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
                /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
                /\ (list_MEM_dec e' l)
                /\ (list_MEM_dec h l)
                /\ (ALL_NON_EMPTY p l1)
 (*               /\ (ALL_NON_ZERO p l1) *)
                /\ (ALL_NON_EMPTY p' l1)
 (*               /\ (ALL_NON_ZERO p' l1) *)
                /\ (update_cand_pile_ACT qu t l1 p p')) /\
     (ElectDec _ (Final _) _ <=> F) /\
     (ElectDec _ _ (Final _) <=> F)`;
  
 
val subpile1_backlog_trans2_def = Define `
    (subpile1_backlog_trans2 bl (p1: piles) (p2: piles)) <=>
      EVERY (λp. MEM (if MEM (FST p) bl then (FST p,[]) else p) p2) p1`;

val subpile2_backlog_trans2_def = Define`
    subpile2_backlog_trans2 bl (ps:piles) p1 ⇔
      EVERY (λp. if MEM (FST p) bl then T else MEM p p1) ps`;



val TransferExcludedDec_def = Define `
    (TransferExcludedDec (qu,st,l)
          (NonFinal (ba,t,p,bl,bl2,e,h))
          (NonFinal (ba',t',p',bl',bl2',e',h')) <=>
           F /\ (NULL ba) /\ (t = t') /\ (e = e') /\ (h = h') /\ (bl = bl')
	  /\
            (case bl2 of
                c :: ls =>
             (case NULL (get_cand_pile c p') of
                T => (NULL bl2')
               |_ => (bl2' = bl2))
          /\ (LENGTH e) < st
          /\ (list_MEM_dec (h ++ e) l)
          /\ (ALL_DISTINCT (h ++ e)) /\ (ALL_DISTINCT (MAP FST p'))
          /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
          /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
          /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
          /\ (~ NULL l) /\ (ALL_DISTINCT l)
          /\ ALL_DISTINCT (MAP FST t)
          /\ (less_than_quota qu t h)
          /\ (let xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
               in
                 (ba' = LAST xs) /\ (MEM (c, (TAKE ((LENGTH xs) - 1) xs)) p'))
          /\ (subpile2_backlog_trans2 [c] p p') /\ (subpile2_backlog_trans2 [c] p' p)
         | _ => F)) /\
    (TransferExcludedDec _ (Final _) _ = F) /\
    (TransferExcludedDec _ _ (Final _) = F) `;
 
(*
TRANSFER_EXCLUDED_Auxiliary_dec_def = Define `
       TRANSFER_EXCLUDED_Auxiliary_dec ((qu,st,l):params) ba' (t: tallies)
                           (p: piles) (p': piles) (bl2: cand list) bl2'
                           (e: cand list) (h: cand list) <=>
       case bl2 of
         c :: ls =>
             (case NULL (get_cand_pile c p') of
                T => (NULL bl2')
               |_ => (bl2' = bl2))
          /\ (LENGTH e) < st
          /\ (list_MEM_dec (h ++ e) l)
          /\ (ALL_DISTINCT (h ++ e)) /\ (ALL_DISTINCT (MAP FST p'))
          /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
          /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
          /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
          /\ (~ NULL l) /\ (ALL_DISTINCT l)
          /\ ALL_DISTINCT (MAP FST t)
          /\ (less_than_quota qu t h)
          /\ (let xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
               in
                 (ba' = LAST xs) /\ (MEM (c, (TAKE ((LENGTH xs) - 1) xs)) p'))
          /\ (subpile2_backlog_trans2 [c] p p') /\ (subpile2_backlog_trans2 [c] p' p)
         | _ => F `;

*)
 
val Initial_Judgement_dec_def = Define `
        (Initial_Judgement_dec _ (Final _) ⇔ F)
     /\ (Initial_Judgement_dec l (NonFinal (ba, t, p, bl, bl2, e, h)) ⇔
                                (EVERY ((=) 0) (MAP SND t))
			     /\	(EVERY ((=) []) (MAP SND p))
                             /\ (bl = [])
			     /\ (bl2 = [])
                             /\ (e = [])
                             /\ (h = l))`;
                               
(* /\ (EVERY NULL (MAP SND p)))`; *)
  


val Valid_Step_def = Define`
  Valid_Step params j0 j1 ⇔
       HwinDec params j0 j1
    \/ EwinDec params j0 j1
    \/ CountDec params j0 j1
    \/ TransferDec params j0 j1
    \/ ElectDec params j0 j1
    \/ TransferExcludedDec params j0 j1 
    \/ EXISTS (λc. ElimCandDec c params j0 j1) (SND(SND params))`;
 
val valid_judgements_dec_def = Define `
       (valid_judgements_dec _ [] ⇔ F)
    /\ (valid_judgements_dec _ [Final _] ⇔ T)
    /\ (valid_judgements_dec _ [_] ⇔ F)
    /\ (valid_judgements_dec params (j0::j1::js) ⇔
        Valid_Step params j0 j1
        /\ (valid_judgements_dec params (j1::js)))`;
 
val valid_judgements_dec_ind = theorem"valid_judgements_dec_ind";
 
val valid_judgements_dec_LRC = Q.store_thm("valid_judgements_dec_LRC",
  `∀params ls.
    valid_judgements_dec params ls ⇔
    ∃s ls0 w. (ls = ls0 ++ [Final w]) ∧
      LRC (Valid_Step params) ls0 s (Final w)`,
  recInduct valid_judgements_dec_ind
  \\ rw[valid_judgements_dec_def,LRC_def]
  \\ Q.ISPEC_THEN`js`STRUCT_CASES_TAC SNOC_CASES
  \\ fs[SNOC_APPEND,LRC_def]
  \\ metis_tac[]);
  
val Check_Parsed_Certificate_def = Define`
  (Check_Parsed_Certificate params [] ⇔ F) /\
  (Check_Parsed_Certificate params(first_judgement::rest_judgements) ⇔
     Initial_Judgement_dec (SND(SND params)) first_judgement /\
     valid_judgements_dec params (first_judgement::rest_judgements))`;
 
val Check_Parsed_Certificate_LRC = Q.store_thm("Check_Parsed_Certificate_LRC",
  `Check_Parsed_Certificate params js ⇔
   ∃j0 ints w.
     (js = [j0] ++ ints ++ [Final w]) ∧
     LRC (Valid_Step params) (j0::ints) j0 (Final w) ∧
     Initial_Judgement_dec (SND(SND params)) j0`,
  Cases_on`js`
  \\ rw[Check_Parsed_Certificate_def,LRC_def,Initial_Judgement_dec_def,PULL_EXISTS,valid_judgements_dec_LRC]
  \\ rw[EQ_IMP_THM] \\ rw[LRC_def]
  >- (
    Cases_on`ls0` \\ fs[LRC_def,Initial_Judgement_dec_def]
    \\ metis_tac[] )
  \\ metis_tac[]);


 

(*------------------------------------------------------------------------*)
      (* adapting the checker for transfer_varSTV*)

(*------------------------------------------------------------------------*)
(*
 
val Valid_Step_def = Define`
  Valid_Step params j0 j1 ⇔
       HwinDec params j0 j1
    \/ EwinDec params j0 j1
    \/ CountDec params j0 j1
    \/ TRANSFER_VarSTV_dec params j0 j1
    \/ ElectDec params j0 j1
    \/ EXISTS (λc. ElimCandDec c params j0 j1) (SND(SND params))`;
   
val valid_judgements_dec_def = Define `
       (valid_judgements_dec _ [] ⇔ F)
    /\ (valid_judgements_dec _ [Final _] ⇔ T)
    /\ (valid_judgements_dec _ [_] ⇔ F)
    /\ (valid_judgements_dec params (j0::j1::js) ⇔
        Valid_Step params j0 j1
        /\ (valid_judgements_dec params (j1::js)))`;
  
val valid_judgements_dec_ind = theorem"valid_judgements_dec_ind";
  
val valid_judgements_dec_LRC = Q.store_thm("valid_judgements_dec_LRC",
  `∀params ls.
    valid_judgements_dec params ls ⇔
    ∃s ls0 w. (ls = ls0 ++ [Final w]) ∧
      LRC (Valid_Step params) ls0 s (Final w)`,
  recInduct valid_judgements_dec_ind
  \\ rw[valid_judgements_dec_def,LRC_def]
  \\ Q.ISPEC_THEN`js`STRUCT_CASES_TAC SNOC_CASES
  \\ fs[SNOC_APPEND,LRC_def]
  \\ metis_tac[]);
  
val Check_Parsed_Certificate_def = Define`
  (Check_Parsed_Certificate params [] ⇔ F) /\
  (Check_Parsed_Certificate params(first_judgement::rest_judgements) ⇔
     Initial_Judgement_dec (SND(SND params)) first_judgement /\
     valid_judgements_dec params (first_judgement::rest_judgements))`;
    
val Check_Parsed_Certificate_LRC = Q.store_thm("Check_Parsed_Certificate_LRC",
  `Check_Parsed_Certificate params js ⇔
   ∃j0 ints w.
     (js = [j0] ++ ints ++ [Final w]) ∧
     LRC (Valid_Step params) (j0::ints) j0 (Final w) ∧
     Initial_Judgement_dec (SND(SND params)) j0`,
  Cases_on`js`
  \\ rw[Check_Parsed_Certificate_def,LRC_def,Initial_Judgement_dec_def,PULL_EXISTS,valid_judgements_dec_LRC]
  \\ rw[EQ_IMP_THM] \\ rw[LRC_def]
  >- (
    Cases_on`ls0` \\ fs[LRC_def,Initial_Judgement_dec_def]
    \\ metis_tac[] )
  \\ metis_tac[]);
 *)
(*--------------------------------------------------------------------*)
        (* end of adapting the checker for transfer_varSTV *)

(*--------------------------------------------------------------------*)
 

(*
TRANSFER_EXCLUDED_Auxiliary_dec_def = Define `
       TRANSFER_EXCLUDED_Auxiliary_dec ((qu,st,l):params) ba' (t: tallies)
                           (p: piles) (p': piles) (bl2: cand list) bl2'
                           (e: cand list) (h: cand list) =
       (case bl2 of
         c :: ls =>
             (case NULL (get_cand_pile c p') of
                T => (NULL bl2')
               |_ => (bl2' = bl2))
          /\ (LENGTH e) < st
          /\ (list_MEM_dec (h ++ e) l)
          /\ (ALL_DISTINCT (h ++ e)) /\ (ALL_DISTINCT (MAP FST p'))
          /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
          /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
          /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
          /\ (~ NULL l) /\ (ALL_DISTINCT l)
          /\ ALL_DISTINCT (MAP FST t)
          /\ (less_than_quota qu t h)
          /\ (let xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
               in
                 (ba' = LAST xs) /\ (MEM (c, (TAKE ((LENGTH xs) - 1) xs)) p'))
          /\ (subpile2_backlog_trans2 [c] p p') /\ (subpile2_backlog_trans2 [c] p' p)
         | _ => F) `;
*)

val _ = export_theory();

