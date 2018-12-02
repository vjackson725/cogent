theory TypeProofTactic
  imports TypeTrackingSemantics CogentHelper Lib.TermPatternAntiquote Lib.Trace_Schematic_Insts
begin

definition
  abbreviatedType1 :: " Cogent.type"
where
  "abbreviatedType1 \<equiv> TSum [(''A'', (TUnit, Unchecked)), (''B'', (TUnit, Unchecked))]"

lemmas abbreviated_type_defs =
  abbreviatedType1_def

definition
  foo_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "foo_type \<equiv> ([], (abbreviatedType1, abbreviatedType1))"

definition
  foo :: "string Cogent.expr"
where
  "foo \<equiv> Let (Var 0) (Case (Var 0) ''A'' (Let (Var 0) (Let Unit (Let (Con [(''A'', (TUnit, Unchecked)), (''B'', (TUnit, Checked))] ''A'' (Var 0)) (Var 0)))) (Let (Esac (Var 0)) (Let (Var 0) (Let Unit (Let (Con [(''A'', (TUnit, Checked)), (''B'', (TUnit, Unchecked))] ''B'' (Var 0)) (Var 0))))))"

ML {*
val Cogent_functions = ["foo"]
val Cogent_abstract_functions = []
*}

definition
  \<Xi> :: " string \<Rightarrow>  Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "\<Xi> \<equiv> (\<lambda>_.([], TUnit, TUnit))(''foo'' := foo_type)"

definition
  "\<xi> \<equiv> \<lambda>_. (\<lambda>_ _. False)"

definition
  "foo_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some abbreviatedType1] (TyTrSplit (Cons (Some TSK_L) (Cons None [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 2 None) []) [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) [])) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 3 None) [])) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [Some (TSum [(''A'', (TUnit, Unchecked)), (''B'', (TUnit, Checked))])] TyTrLeaf))) [Some (TSum [(''A'', (TUnit, Checked)), (''B'', (TUnit, Unchecked))])] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) [])) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 3 None) [])) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 5 None) [])) [] TyTrLeaf [Some (TSum [(''A'', (TUnit, Checked)), (''B'', (TUnit, Unchecked))])] TyTrLeaf))))))"


ML {* open TTyping_Tactics *}

ML_quiet {*
val typing_helper_1_script : tac list = [
(SimpTac ([@{thm kinding_def},@{thm kinding_all_def},@{thm kinding_variant_def},@{thm kinding_record_def}],[]))
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType1 {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_2_script : tac list = [
(SimpTac ([@{thm kinding_def},@{thm kinding_all_def},@{thm kinding_variant_def},@{thm kinding_record_def}],[]))
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "kinding [] TUnit {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_3_script : tac list = [
(SimpTac ([@{thm kinding_def},@{thm kinding_all_def},@{thm kinding_variant_def},@{thm kinding_record_def}],[]))
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''A'', (TUnit, Checked)), (''B'', (TUnit, Unchecked))]) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_4_script : tac list = [
(SimpTac ([@{thm kinding_def},@{thm kinding_all_def},@{thm kinding_variant_def},@{thm kinding_record_def}],[]))
] *}


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''A'', (TUnit, Unchecked)), (''B'', (TUnit, Checked))]) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY *})
  done

ML_quiet {*
val foo_typecorrect_script : hints treestep list = [
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepUp,
Val (TypingTacs []),
StepDown,
Val (TypingTacs []),
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
Val (KindingTacs [(RTac @{thm typing_helper_3})]),
StepUp,
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
StepUp,
Val (TypingTacs []),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_unit}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_2}])]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_4})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_2}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(SimpTac ([@{thm kinding_def},@{thm kinding_all_def},@{thm kinding_variant_def},@{thm kinding_record_def}],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[]))]),
Val (TypingTacs []),
StepUp,
StepUp,
StepUp,
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_esac}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(SimpTac ([],[]))]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
StepUp,
Val (TypingTacs []),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_2})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_unit}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_2}])]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_3})]),
StepUp,
Val (TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_2}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(SimpTac ([@{thm kinding_def},@{thm kinding_all_def},@{thm kinding_variant_def},@{thm kinding_record_def}],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[]))]),
Val (TypingTacs []),
StepUp,
StepUp,
StepUp,
StepUp,
StepUp,
StepUp,
StepUp
] *}


ML {*

fun cterm_simplify ctxt (t : cterm) : cterm = t
  |> Simplifier.rewrite ctxt
  |> Thm.concl_of
  |> Logic.dest_equals
  |> snd
  |> Thm.cterm_of ctxt;

datatype goal_type = TTyping | Typing | Simp of thm list | TTSplit | TTSplitInner

fun goal_type_of_term @{term_pat "TypeTrackingSemantics.ttyping _ _ _ _ _"} = SOME TTyping
  | goal_type_of_term @{term_pat "Cogent.typing _ _ _ _ _"}               = SOME Typing
  | goal_type_of_term @{term_pat "Cogent.kinding _ _ _"}                  = SOME (Simp @{thms kinding_defs})
  | goal_type_of_term @{term_pat "\<not> composite_anormal_expr _"}            = SOME (Simp @{thms composite_anormal_expr_def})
  | goal_type_of_term @{term_pat "ttsplit _ _ _ _ _ _ _"}                 = SOME TTSplit
  | goal_type_of_term @{term_pat "ttsplit_inner _ _ _ _ _"}               = SOME TTSplitInner
  | goal_type_of_term @{term_pat "weakening _ _ _"}                       = SOME (Simp @{thms weakening_def weakening_comp.simps Cogent.empty_def})
  | goal_type_of_term @{term_pat "tsk_split_comp _ _ _ _ _"}              = SOME (Simp @{thms tsk_split_comp.simps})
  | goal_type_of_term @{term_pat "ttsplit_triv _ _ _ _ _"}                = SOME (Simp @{thms ttsplit_triv_def})
  | goal_type_of_term _                                                   = NONE

fun tactic_of_goal_type ctxt TTyping =
  ((resolve_tac ctxt @{thms ttyping.intros(2-)} 1) ORELSE
  (resolve_tac ctxt @{thms ttyping.intros(1)} 1)) (* try the default case second, as it resolves with every ttyping (but won't complete most of the time) *)
| tactic_of_goal_type ctxt Typing = (resolve_tac ctxt @{thms typing_typing_all.intros} 1)
| tactic_of_goal_type ctxt (Simp thms) =
  CHANGED (Simplifier.asm_full_simp_tac (fold Simplifier.add_simp thms ctxt) 1)
| tactic_of_goal_type ctxt TTSplit = (resolve_tac ctxt @{thms ttsplitI} 1)
| tactic_of_goal_type ctxt TTSplitInner = (resolve_tac ctxt @{thms ttsplit_innerI} 1)

*}

ML_val {*

*}

declare [[ ML_debugger = true ]]

ML {*

datatype proof_status =
  ProofDone of thm
(*
need this eventually for branching
(* a subgoal is a goal which we apply to the main goal after it gets solved, to eliminate schemantic
  variables in the goal for future subgoals *)
| ProofSubgoal of thm
*)
| ProofTodo of thm * proof_status tree list

(* solve_typeproof takes a proposition term and solves it by recursively solving the term tree *)
fun solve_typeproof ctxt (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t_rest) : proof_status tree =
  let
    val t_start = (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t_rest);
    val goal = Thm.cterm_of ctxt t_start |> cterm_simplify ctxt |> Goal.init;
  in
    case goal_type_of_term t_rest of
      SOME goal_type =>
        let
          val results = goal |> tactic_of_goal_type ctxt goal_type
          (* TODO more principled handling of tactic results *)
          val goal' = (case Seq.pull results of
              SOME (goal, _) => goal
            | NONE => raise ERROR ("solve_typing_goal: failed on " ^ (@{make_string} (Thm.cterm_of ctxt t_start))))
          val solved_prems = solve_typeproof_subgoals ctxt goal' []
          in
            case fst solved_prems of
              SOME thm => Tree { value = ProofDone thm, branches = snd solved_prems }
            | NONE => Tree { value = ProofTodo (goal', snd solved_prems), branches = [] }
          end
      | NONE => Tree { value = ProofTodo (goal, []), branches = [] }
  end
| solve_typeproof _ _ = raise ERROR "solve_typeproof was not passed a Trueprop!"
(* iteratively solve the subgoals, unifying as we go *)
and solve_typeproof_subgoals ctxt goal (solved_subgoals_rev : proof_status tree list) : thm option * proof_status tree list = 
  case Thm.prems_of goal of
    (t_subgoal :: _) =>
      (* TODO branching *)
      (case tree_value (solve_typeproof ctxt t_subgoal) of
        (ProofDone thm_subgoal) =>
          let
            (* resolve solution to subgoal with goal to make the goal smaller *)
            val goal' =
              case Seq.pull (resolve_tac ctxt [thm_subgoal] 1 goal) of
                SOME (thm_soln, _) => thm_soln
              | NONE =>  (* this shouldn't happen! *)
                raise ERROR ("failed to unify subgoal (" ^ @{make_string} goal ^ ") with solved subgoal: " ^ (@{make_string} thm_subgoal))
          in
            solve_typeproof_subgoals ctxt goal' solved_subgoals_rev
          end
      | (ProofTodo (thm, subgoals)) =>
        (NONE, rev (Tree { value = ProofTodo (thm, subgoals), branches = [] } :: solved_subgoals_rev))
      )
  (* no more subgoals, we've solved the goal *)
  | [] => (SOME (Goal.finish ctxt goal), rev solved_subgoals_rev)
*}

ML {*
(*
val script_tree = (case parse_treesteps foo_typecorrect_script of
    SOME tree => tree
  | NONE => raise ERROR ("failed to parse script tree"))
*)
val simpctxt = fold Simplifier.add_simp
  [@{thm foo_def}, @{thm foo_type_def}, @{thm foo_typetree_def}, @{thm abbreviatedType1_def}]
  @{context};

val f = "foo";

val t = Syntax.read_prop @{context}
         ("\<Xi>, fst " ^ f ^ "_type, (" ^ f ^ "_typetree, [Some (fst (snd " ^ f ^ "_type))])" ^
          "            T\<turnstile> " ^ f ^ " : snd (snd " ^ f ^ "_type)")

val proof_solver_tree = solve_typeproof simpctxt t;
*}

ML_val {*
  Thm.prems_of @{thm ttyping_let}
*}

ML_val {*
(*
tree_foldr (fn acc => fn x =>
  case x of
    ProofTrue => acc
  | ProofTodo th => th :: acc
  | ProofDone _ => acc)
  proof_solver_tree []
*)
*}

end