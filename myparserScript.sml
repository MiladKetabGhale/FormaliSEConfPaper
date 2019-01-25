open preamble CheckerSpecTheory
      
val _ = new_theory "myparser"

(* start of first part *)
val t_cand_list_def = Define`
t_cand_list tlst =
       case tlst of
           [] => []
         | (#"," :: t) => t_cand_list t
         | (#"[" :: t) => t_cand_list t
         | (#"]" :: t) => t_cand_list t
         | (#" " :: t) => t_cand_list t
         | (x :: t) => (Cand (str x)) :: t_cand_list t`
 
 
val cand_list_def = Define`
cand_list st =
  let lst = explode st in
  t_cand_list lst`
   
  
val process_chunk_def = tDefine "process_chunk" `
process_chunk tlst acc lst=
  case  tlst of
      [] => lst
    | (#")" :: #"," :: t) =>
      process_chunk t (strlit"")
                    (lst ++ [strcat acc (strlit")")])
    | (#")" :: t) =>
      process_chunk t (strlit"")
                    (lst ++ [strcat acc (strlit")")])
    | (x :: t)  => process_chunk t (strcat acc (str x)) lst`
((WF_REL_TAC `measure (LENGTH o FST )` >>
REPEAT STRIP_TAC )
  >- FULL_SIMP_TAC list_ss []
  >- FULL_SIMP_TAC list_ss []
  >- FULL_SIMP_TAC list_ss []
  >- FULL_SIMP_TAC list_ss [])
 
(* the following function takes in a string of list of pairs and parses it into a list of
   separated mlstring pairs*)
   
val split_it_into_pair_def = Define`
split_it_into_pair st =
    case explode st of
    | [] => NONE
    | _::lst => SOME (process_chunk lst (strlit"") [])`
 
 
val parse_pair_end_def = Define`
  parse_pair_end [] = strlit "" ∧
  parse_pair_end [#")"] = strlit "" ∧
  parse_pair_end (x::xs) = strcat (str x) (parse_pair_end xs)`;
 
val parse_pair_t_def = tDefine "parse_pair_t" `
parse_pair_t ts ac =
    case ts of
        [] => (ac, strlit"")
      | (#"(" :: t) => parse_pair_t t ac
      | (#"]" :: #"," :: t) =>
        (strcat ac (strlit"]"), parse_pair_end t)
      | (x :: t) =>
        parse_pair_t t (strcat ac (str x))`
((WF_REL_TAC `measure (LENGTH o FST)` >>
             REPEAT STRIP_TAC)
     \\ FULL_SIMP_TAC list_ss [])
 

val parse_pair_def = Define`
parse_pair str =
        let tm = explode str in
        parse_pair_t tm (strlit"")`


val parse_number_def = Define`
parse_number str = mlint$fromChars (strlen str) str`


val parse_rational_def = Define`
parse_rational str =
    case tokens (\x. x = #"%") str of
    | [n1;n2] =>
      OPTION_BIND (parse_number n1) (λn1.
      OPTION_BIND (parse_number n2) (λn2.
      if n2 = 0 then NONE
      else SOME ((&n1:rat) / (&n2:rat))))
    | _ => NONE`;


(* lets plug the values togather for first part*)
(*the following takes lists of ballots and parses them*)

val parse_first_part_def = Define`
parse_first_part str =
 case split_it_into_pair str of SOME l1 =>
   let l2 = MAP parse_pair l1 in
   OPT_MMAP
     (\(x, y). case parse_rational y of SOME y => SOME (cand_list x,y) | _ => NONE)
     l2
 | _ => NONE`


(* End of first part. *)

(* start of second part *)

val parse_second_t_def = Define`
parse_second_t tstr =
  case tokens (\x. x = #"{") tstr of
  | [first;lrest] =>
    (case parse_rational (extract lrest 0 (SOME (strlen lrest - 1))) of
     | SOME r => SOME (Cand first, r)
     | _ => NONE)
  | _ => NONE`;

(*the following takes a pair of cands and their votes and parses them*)

val parse_second_part_def = Define`
parse_second_part str =
 let strs = tokens (\x. x = #" ") str in
 OPT_MMAP parse_second_t strs`

    
(* parse_third_part *)



(* -------------------------------------------------------------------------------------------- *)

(*
val parse_third_aux1_def = Define `
 parse_third_aux1 lst acc =
   case lst of
              [] => [acc]
	    | (#"]" :: #"]":: rest) => [strcat acc (strlit "]")]
	    | (#"[" :: #"]" :: rest) => [strlit ""]
	    | (#"]" ::  #"," :: #"[" :: rest) => (strcat acc (str #"]")) :: (parse_third_aux1 (#"[":: rest) (strlit ""))
	    | (#"[" :: #"]" :: #"," :: rest) => parse_third_aux1 rest acc
	    | (#"[" :: #"[":: rest)  => parse_third_aux1 (#"[" :: rest) acc  
            | (x :: rest) => parse_third_aux1 rest  (strcat acc (str x))` 


EVAL ``parse_third_aux1 "[]" (strlit "")`` 

EVAL ``parse_third_aux11 "[]" (strlit "")``
 


val parse_m2_def = Define `
 parse_m2 st =
   case explode st of
    | [] => NONE
    | _::lst => SOME (parse_m lst (strlit ""))` 
 

val parse_m3_def = Define `
 parse_m3 st =
   case parse_m2 st of
     NONE => NONE
    |SOME x => OPT_MMAP parse_first_part x`
 
(* in the following, I changed parse_first_part and placed parse_third_aux3 there instead*)
  
val parse_third_tm_def = Define`
parse_third_tm tstr =
 case tokens (\x. x = #"{") tstr of
 | [first;second] =>
   (case parse_m3 second of
    | SOME x => SOME (Cand first, x)
    | _ => NONE)
 | _ => NONE`;
  
 
(*the following takes a lists of pairs of cands with their piles*)
 
val parse_third_partm_def = Define`
parse_third_partm str =
  let strs = tokens (\x. x = #" ") str in
  OPT_MMAP parse_third_tm strs`

*)
    
(* ----------------------------------------------------------------------------------------------- *)
     
val parse_third_aux1_def = Define `
 parse_third_aux1 lst acc =
   case lst of
              [] => [acc]
	    | [#"["; #"]"; #"}"] => []
	    | (#"]" :: #"]":: rest) => [strcat acc (strlit "]")]
	    | (#"]" ::  #"," :: #"[" :: rest) => (strcat acc (strlit "]")) :: (parse_third_aux1 (#"[":: rest) (strlit "")) 
            | (#"[" :: #"[" :: rest) => parse_third_aux1 (#"[" :: rest) acc
            | (x :: rest) => parse_third_aux1 rest  (strcat acc (str x))` 
           
(* EVAL ``parse_third_aux1 "[]" (strlit "")`` 
EVAL ``parse_third_aux1 "[[([A,B],1%2)],[foo]]" (strlit "")``
EVAL ``parse_third_aux1 "{[]}" (strlit "")`` 
*)
     

val parse_third_aux2_def = Define `
 parse_third_aux2 st =
   case explode st of
    | [] => NONE
    | l0::lst => SOME (parse_third_aux1 (l0::lst) (strlit ""))` 
     
(* EVAL ``parse_third_aux2 (strlit "[]")`` *)
     
val parse_third_aux3_def = Define `
 parse_third_aux3 st =
   case parse_third_aux2 st of
     NONE => NONE
    |SOME x => OPT_MMAP parse_first_part x`
    
(* 
type_of ``parse_third_aux1``
type_of ``parse_third_aux2``
type_of ``parse_third_aux3``

EVAL ``parse_third_aux3 (strlit "[]}")``
--> EVAL ``parse_third_aux2 (strlit "[]}")`` = SOME [strlit "]}"]

*)     


(* in the following, I changed parse_first_part and placed parse_third_aux3 there instead*)
 
val parse_third_t_def = Define`
parse_third_t tstr =
 case tokens (\x. x = #"{") tstr of
 | [first;second] =>
   (case parse_third_aux3 second of
    | SOME x => SOME (Cand first, x)
    | _ => NONE)
 | _ => NONE`;
    
    
(* 
EVAL ``parse_third_part (strlit "A{[]} B{[]} C{[[([A,B],1%1)]]}")``
 
EVAL ``parse_third_part (strlit "A{[[([A,B],1%1)]]} B{[]}")``  
   EVAL ``tokens (\x. x = #" " ) (strlit "A{[]} B{[]}")``  
--> EVAL ``parse_third_t (strlit "A{[]}")``   
    EVAL ``tokens (\x. x = #"{") (strlit "A{[]}")``   
    --> EVAL ``parse_third_aux3 (strlit "[]}")`` 
type_of``OPT_MMAP``
 
EVAL ``OPT_MMAP parse_first_part [strlit "[]" ; strlit "[([A,B],1%3), ([B,C],3%4)]" ]`` 
*)

(*the following takes a lists of pairs of cands with their piles*)

val parse_third_part_def = Define`
parse_third_part str =
  let strs = tokens (\x. x = #" ") str in
  OPT_MMAP parse_third_t strs`
     
   
(* EVAL ``parse_third_part (strlit"A{[]} B{[[([A,B],3%4)]]}")`` *) 
   

(* end of third part *)

(* parse rest part, third, fourth and final *)
val parse_rest_def = Define`
parse_rest str = cand_list str`
  

(* combine all to parse one line *)
 
val parse_whole_line_def = Define`
parse_whole_line str =
  case tokens (\x. x = #";") str of
  | [f;s;t;fr;fs;fi;sx] =>
  (case (parse_first_part f, parse_second_part s, parse_third_part t) of
   (SOME x, SOME y, SOME z) => SOME (NonFinal (x, y, z, parse_rest fr, parse_rest fs, parse_rest fi, parse_rest sx))
   | _ => NONE)
  | _ => NONE`
 
(* end of parsing one line *)
 

val parse_quota_def = Define`
  parse_quota line = parse_rational (extract line 0 (SOME (strlen line - 1)))`;
 
val parse_seats_def = Define`
  parse_seats line = parse_number (extract line 0 (SOME (strlen line - 1)))`;

val parse_candidates_def = Define`
  parse_candidates line = SOME (parse_rest (extract line 0 (SOME (strlen line - 1))))`;
 
val parse_judgement_def = Define`
  parse_judgement line = parse_whole_line (extract line 0 (SOME (strlen line - 1)))`;
     
val _ = export_theory ();


 
(*---------------------------------EVAL for making sure parts are correct ----------------------*)
(*
EVAL ``t_cand_list ( [#"["; #"A"; #","; #"B"; #","; #"C"; #"]"] )``
 
EVAL ``explode (strlit ( [#"["; #"A"; #","; #"B"; #","; #"C"; #"]"]))`` 


EVAL ``split_it_into_pair (strlit"[([A,B,C],1.0)],[([C,B,A],1.0),([B,A,C],1.0),([C,A,B],1.0),([A,B,C],1.0),([A,B,C],1.0),([C,B,A],1.0),([A,C,B],1.0),([B,C,A],1.0),([A,B,C],3.0)]")``

EVAL ``(split_it_into_pair(parse_pair_end ("[([A,B,C],1.0)],[([C,B,A],1.0),([B,A,C],1.0),([C,A,B],1.0),([A,B,C],1.0),([A,B,C],1.0),([C,B,A],1.0),([A,C,B],1.0),([B,C,A],1.0),([A,B,C],3.0)]")))``


EVAL ``parse_pair (strlit"([B,A,C],1%2)")``

EVAL ``parse_rational (strlit"1%2")``

EVAL `` parse_first_part (strlit"[([A,B,C],1%2),([C,B,A],1%2),([B,A,C],1%2),([C,A,B],1%2),([A,B,C],1%2),([A,B,C],1%2),([C,B,A],1%2),([A,C,B],1%2),([B,C,A],1%2),([A,B,C],3%4)]")``


EVAL ``parse_second_part (strlit" A{5%6} B{2%3} C{3%4}")``

EVAL ``(parse_third_part (strlit ("A{[[([A,B,C],1%2),([A,B,C],1%2),([A,B,C],1%2),([A,C,B],1%2),([A,B,C],1%3)],[],[([A,B,C],1%3)]]} B{[([B,A,C],1%40),([B,C,A],1%2)]} C{[([C,B,A],1%2),([C,A,B],1%5),([C,B,A],15%16)]}")))``
 
EVAL ``parse_whole_line (strlit"[([A,B,C],1%1),([C,B,A],1%1),([B,A,C],1%1),([C,A,B],1%1),([A,B,C],1%1),([A,B,C],1%1),([C,B,A],1%1),([A,C,B],1%1),([B,C,A],1%1),([A,B,C],1%1)]; A{0%1} B{0%1} C{0%1}; A{[]} B{[]} C{[]}; []; [A];[]; [A,B,C]")``
  
EVAL ``parse_whole_line (strlit"[([A,B],1%1),([A,B],1%1)]; A{0%1} B{0%1}; A{[]} B{[]}; []; []; []; [A,B]")`` 

EVAL ``parse_quota (strlit"3%5\n")``;

EVAL ``parse_quota (strlit"32%50\n")``;

EVAL ``parse_seats (strlit"30\n")``;

EVAL ``parse_candidates (strlit"[A,B,C]\n")``;

EVAL ``parse_judgement (strlit"[]; A{5%1} B{2%1} C{3%1}; A{[([A,B,C],0%1),([A,B,C],0%1),([A,B,C],0%1),([A,C,B],0%1),([A,B,C],0%1)]} B{[([B,A,C],0%1),([B,C,A],0%1)]} C{[([C,B,A],1%1),([C,A,B],1%1),([C,B,A],1%1)]}; [A]; [A]; [B,C]\n")``;

*)
(*-------------------------end of EVALs --------------------------------------------------------*)
