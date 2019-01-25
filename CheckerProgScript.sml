(*
  This theory creates a CakeML program implementing the Checker_Aux2_dec HOL
  function via proof-producing translation.
*) 
open preamble basis CheckerTheory CheckerSpecTheory CheckerProofTheory 
                    
val _ = new_theory "CheckerProg";
 
val _ = translation_extends"basisProg";
  
val r = translate SUM_RAT_def;
 
val r = translate get_cand_tally_def;
 
val r = translate less_than_quota_def;
val r = translate equal_except_dec_def;
val r = translate bigger_than_cand_def;
val r = translate get_cand_pile_def;
(* val r = translate get_cand_pile_list_def; *)
 
val () = use_mem_intro := true;

val r = translate list_MEM_dec_def;
    
val r = translate Valid_PileTally_dec1_def;
val r = translate Valid_PileTally_dec2_def;
val r = translate subpile1_def;
val r = translate subpile2_def; 
val r = translate ElimCandDec_def;
 
val r = translate subpile1_BlMem_trans2_def;
val r = translate subpile1_backlog_trans2_def;
val r = translate subpile2_backlog_trans2_def;
    
val r = translate first_continuing_cand_dec_def;
val r = translate COUNTAux_dec_def;
val r = translate CountDec_def;

val r = translate ALL_NON_EMPTY_def;
   
val r = translate TransferDec_def;
 
val transferdec_side_def = fetch"-""transferdec_side_def";
   
val transferdec_side = Q.prove(
  `transferdec_side a b c = T`,
  rw[definition"transferdec_side_def"]    
  >> fs[ALL_NON_EMPTY_def,MEM]) |> update_precondition; 

val r = translate eqe_list_dec_def;
val r = translate eqe_list_dec2_def;
val r = translate piles_eq_list_def;

val r = translate DROP_def; 
val r = translate TAKE_def;

 
val r = translate Count_Occurrences_def; 
val r = translate ReGroup_Piles_def;
 
val r = translate pairTheory.PAIR_MAP;
val r = translate PART3_DEF; 
val r = translate QSORT3_DEF; 
val r = translate TransferExcludedDec_def;
  

val () = use_mem_intro := false;
 
val r = translate HwinDec_def;
val r = translate EwinDec_def;
      
(* val r = translate take_append_def; 
val r = translate DROP_def; 
val r = translate TAKE_def;
*)
  
val r = translate SORTED_DEF;
val r = translate tally_comparison_def;
val r = translate bigger_than_quota_def;
            
(* val r = translate ALL_NON_EMPTY_def; *)

(* val r = translate ALL_NON_ZERO_def;
val all_non_zero_side_def = fetch"-""all_non_zero_side_def";
*)
         
val r = translate ACT_TransValue_def;
val r = translate update_cand_transVal_ACT_def;  
val r = translate update_cand_pile_ACT_def;    
         
val r = translate update_cand_trans_val_def;  
val r = translate update_cand_pile_def; 
      
val r = translate ElectDec_def; 
               
           
val act_transvalue_side_def = fetch"-""act_transvalue_side_def";  
val update_cand_transval_act_side_def = fetch"-""update_cand_transval_act_side_def";
val update_cand_pile_act_side_def = fetch"-""update_cand_pile_act_side_def";   
            
           
val update_cand_trans_val_side_def = fetch"-""update_cand_trans_val_side_def";
val update_cand_pile_side_def = fetch"-""update_cand_pile_side_def"; 
val electdec_side_def = fetch"-""electdec_side_def";   
      

(*
val all_non_zero_side = Q.prove(
 `! v3 v2. EVERY(\x. (get_cand_pile x v3) <> []) v2 ==> all_non_zero_side v3 v2`,
  Induct_on `v2` 
    >- rw[all_non_zero_side_def]   
    >- (rw[MEM] >> fs[all_non_zero_side_def] >> metis_tac[MEM]))|> update_precondition; 
*)    
 
val act_transvalue_side = Q.prove(
 `! v4 v6 v5 v3. (get_cand_pile v3 v4 <> [])
          ==> act_transvalue_side v4 v6 v5 v3`,
   rw[act_transvalue_side_def])|> update_precondition;
    
    
val update_cand_transval_act_side = Q.prove(
 `! v4 v2 v5 v3. (get_cand_pile v2 v3 <> [])
                  ==> update_cand_transval_act_side v4 v2 v5 v3`,
   rw[update_cand_transval_act_side_def]
    >> rw[act_transvalue_side])|> update_precondition; 
        
val update_cand_pile_act_side = Q.prove(
 `! a0 a1 a2 a3 a4.
  EVERY(\x. (get_cand_pile x a3 <> [])) a2 /\ EVERY(\x. (get_cand_pile x a4 <> [])) a2
       ==> update_cand_pile_act_side a0 a1 a2 a3 a4`,  
       
         Induct_on `a2`   
  \\ rw[Once update_cand_pile_act_side_def,update_cand_transval_act_side_def] 
    \\ rw[act_transvalue_side_def]) |> update_precondition;
            
 
(*Globals.max_print_depth:= ~1*)
 
      
val electdec_side = Q.prove(
  `electdec_side a b c = T`,
  rw[definition"electdec_side_def"]    
    >> match_mp_tac update_cand_pile_act_side  
      >> metis_tac[ALL_NON_EMPTY_def,Functional_AllNonEmpty_to_Logical,
         GET_CAND_PILE_MEM,Functional_AllNonEmpty_to_Logical,GET_CAND_PILE_MEM,
         EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
         Valid_PileTally_def,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional,
         eqe_list_dec2_verified,EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,
	 PileTally_to_PileTally_DEC2,Valid_PileTally_def,Valid_PileTally_def,
	 Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified])|> update_precondition;
    
         

val r = translate Initial_Judgement_dec_def;

val r = translate Valid_Step_def;

(* To see the code:
val () = astPP.enable_astPP()

val Prog_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def];

val () = astPP.disable_astPP()
*)

val _ = export_theory();
