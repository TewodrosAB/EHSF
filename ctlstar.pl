:- use_module('../clplib3/clp_utils.pl').
:- use_module('../utils/utils-include.pl').

:- ['qarmc.pl'].
:- [casesplit].

:- dynamic skolem_guard/3.    % skolem_guard(Sym, Vars, Body)
:- dynamic skolem_solution/4. % skolem_solution(Sym, Vars, Guard, Body)
:- dynamic skolem_def/2.      % skolem_def(Sym, TId)
:- dynamic skolem_guard_def/2.	% skolem_guard_defs(Sym, TId)

% skolem_constraint_store(SymCoeffsMap, Store)
:- dynamic skolem_constraint_store/2. 

ctlstar_specs([skolem_guard/3, skolem_solution/4, skolem_def/2,
	       skolem_guard_def/2, skolem_constraint_store/2]).

upd_skolem_constraint_store(SymParamsMap, S1, KeyValuePairs) :-
	(   foreach(Key-Value, KeyValuePairs),
	    fromto(S1, In, Out, S2)
	do  avl_store(Key, In, Value, Out)
	),
	assert(skolem_constraint_store(SymParamsMap, S2)).


ctlstar_init(File) :-
	bb_put(input_file, File),
	clean_input,
	ctlstar_specs(Specs),
	maplist(retractall_predspec, Specs),
	load_input(File),
	if_flag(case_split, do_case_split),
	findall(Sym, skolem_relation(Sym, _, _, _), Syms),
	empty_avl(Emp),
	(   foreach(Sym, Syms),
	    fromto(Emp, InM, OutM, SymParamsMap),
	    fromto(true, InE, (Extra, InE), Extras)
	do  once(skolem_relation(Sym, Vars, InVars, OutVars)),
	    ensure(skolem_template(Sym, Vars, Params, Init, _, _, Extra),
		   'provide Skolem template for'(Sym)),
	    avl_store(Sym, InM, Params, OutM),
	    ensure(project(InVars, Init, false, InitGuard),
		   'provide satisfiable init guard for'(Sym)),
	    assert(skolem_solution(Sym, Vars, InitGuard, Init))
	),
	(   bb_get(use_gurobi, 1) ->
	    avl_range(SymParamsMap, SkolemParamsRange),
	    term_variables_set(SkolemParamsRange, SkolemParams),
	    bb_get(gurobi_max_param, MaxParam),
	    MinParam is -MaxParam,
	    (   foreach(SkolemParam, SkolemParams),
		foreach(SkolemParam-(MinParam-MaxParam), Case),
		param(MinParam, MaxParam)
	    do  true
	    )
	;   Case = true
	),
	norm_constraint(Extras, NormExtras),
	upd_skolem_constraint_store(SymParamsMap, Emp,
				    [exists_forall-[], exists-NormExtras,
				     kinds-[], case-Case]),
	flush_watch,
	bb_put(smt_model_walltime, 0),
	bb_put(smt_solver_walltime, 0),
	init_statcounter([(num_iterations, 'number of refinement iterations')]),
	install_watches([(total_mcc, 'total with MCC'),
			 (total, 'total without MCC'),
			 (mcc, 'Model Checker Checker'),
			 (resolve_tree_like_horn_clauses, % horn_solver_inc.pl
			     'resolve tree-like horn clauses'),
			 (input, 'input'),
			 (ranking, 'ranking function generation'),
			 (abstract, 'abstract_head'),
			 (concretize_cube, 'concretize_cube'),
			 (assert_abstract, 'assert_abstract_query'),
			 (refine, 'refinement'),
			 (preprocess, 'preprocess'),
			 (horn_solver, 'horn_solver'),
			 (horn_simplifier, 'horn_simplifier'),
			 (insert_scoped_pred, 'insert_scoped_pred')
			]),
	install_horn_utils_watches,
	bb_put(horn_core_simplify, 1),
	process_tcs,
	store_qarmc_input.

ctlstar_check :-
	bb_inc(skolem_refinement_iteration, I),
	format('skolem refinement iteration: ~p\n', [I]),
	all(skolem_solution_to_clause),
	catch((
	       check(Result),
	       (   Result == ok ->
		   true
	       ;   Result == nok ->
		   bb_delete(error_id, Error),
		   Error = reach(Id),
		   refine(exists(Id)),
		   restore_qarmc_input,
		   ctlstar_check
	       )
	      ),
	      E, 
	      (   E == skolem_changed ->
		  restore_qarmc_input,
		  ctlstar_check
	      ;   throw(E)
	      )
	     ).

user:runtime_entry(start) :-
	bb_put(mainFn, main),
	prolog_flag(argv, Argv),
	CmdShape =
	[
	 ('--whoami', [], (print('ctlstar revision:1\n'), halt),
	     'print whoami'),
	 ('-nopreprocess', [], set_flag(nopreprocess),
	     'do not run the preprocessor'),
	 ('-max-lambda', [integer(N)], bb_put(max_lambda, N),
	     'maximal absolute value for lambda coefficients'),
	 ('-use-next-skolem', [], set_flag(use_next_skolems),
	     'use next to strengthen skolem'),
	 ('-nomcc', [], set_flag(nomcc), 'do not run the MCC'),
	 ( '-no-extra-insert-pred', [],
	     set_flag(no_insert_pred_wrt_query_naming),
	     'do not insert extra predicates wrt. query naming'),
	 ( '-barcelogic', [], bb_put(smt_interface, smt12_barcelogic),
	     'use barcelogic as SMT solver (instead of z3)'),
	 ( '-gurobi', [], (
			    set_flag(use_gurobi),
			    bb_put(gurobi_max_param, 20),
			    bb_put(gurobi_li_max_lambda, 20),
			    bb_put(gurobi_bi_max_lambda, 20)
			  ),
	     'use gurobi for non linear constraint solving'),
	 ( '-case-split', [], set_flag(case_split),
	     'do case split on the input clauses'),
	 ( '-exp-eval', [], set_flag(exp_eval), 'explicit evaluation'),
	 ( '-query-finite-sorts', [], set_flag(query_finite_sorts),
	     'use query_finite_sorts for -exp-eval'), 
	 ( '-use-finite-sorts', [], set_flag(use_finite_sorts),
	     'use query_finite_sorts for -exp-eval'),
	 ( '-no-accel', [], set_flag(no_accel),
	     'do not use acceleration'),
	 ( '-mcc-smt', [], set_flag(mcc_smt), 'use SMT solver for MCC'),
	 ( '-debug',         [], start_debug ),
	 ( '--help',         [], print_help_halt, 'prints this help'),
	 ( '-help',          [], print_help_halt, 'prints this help'),
	 ( '-h',             [], print_help_halt, 'prints this help')
	],
	cmd_line_parse(Argv, CmdShape, Files),
	(   Files = [File] ->
	    ctlstar_init(File),
	    (   ctlstar_check ->
		if_debug(pp_preds),
		if_debug(pp_solution),
		print_watch,
		pp_skolem_solution,
		Result = ok,
		print('CTL*: program is correct\n')
	    ;	if_debug(pp_tc), 
		Result = nok,
		print('CTL*: program is not correct\n')
	    ),
	    read_watch_sec(total, TotalTime),
	    read_watch_sec(refine, RefineTime),
	    read_watch_sec(abstract, AbstractTime),
	    bb_get(smt_model_walltime, ModelTime),
	    bb_get(smt_solver_walltime, SolverTime),

	    get_statcount(num_iterations, Cnt1),
	    bb_get(skolem_refinement_iteration, Cnt2),
	    
	    list_to_avl([total_time-TotalTime,
			 time_in_refinement-RefineTime,
			 time_in_fixpoint-AbstractTime,
			 smt_model_walltime-ModelTime,
			 smt_solver_walltime-SolverTime,
			 num_iterations-Cnt1,
			 result-Result,
			 skolem_refinement_iteration-Cnt2], J1),
	    list_to_avl([measures-J1], J2),
	    to_json(J2, JSON),
	    format('~p\n', [JSON])
	;   print('ERROR: input file is missing\n'),
	    print_help_halt
	).

print_help_halt :-
	print_cmd_format('ctlstar'),
	halt.

skolem_solution_to_clause :-	% all
	skolem_solution(Sym, Vars, Grd, Upd),
	format('skolem_solution_to_clause ~p\n', [Sym]),
	all((
	     retract(skolem_def(Sym, TId)),
	     del_tc(TId)
	    )),
	norm_to_dnf(Upd, UpdDNF),
	term_leaves(UpdDNF, ';', UpdDisjs),
	(   foreach(D, UpdDisjs),
	    count(I, 1, _),
	    param(Sym, Vars)
	do  (   project(Vars, D, ProjD) ->
		format_atom('~p-~p', [Sym, I], TId),
		assert(skolem_def(Sym, TId)),
		add_tc(TId, ProjD, [], Sym-Vars)
	    ;   true
	    )
	),
	/* -case-split might have Sym not yet occuring in bodies */
	(   solution(Sym, _, _) ->
	    true
	;   assert(solution(Sym, _, unknown))
	),
	
	all((
	     retract(skolem_guard_defs(Sym, TId)),
	     del_tc(TId)
	    )),
	once(skolem_guard(Sym, Vars, Body)),
	norm_to_dnf((Body, \+Grd), BodyGrdDNF),	
	BodyGrdDNF \== false,
	term_leaves(BodyGrdDNF, ';', BodyGrdDisjs),
	(   foreach(D, BodyGrdDisjs),
	    count(I, 1, _),
	    param(Sym, Vars)
	do  (   D \== true,
		term_leaves(D, ',', Cs),
		list_partition(Cs, user:clpq_pred, As, Qs),
		project(Qs, As, ProjAs) ->
		(   foreach(Q, Qs),
		    foreach(QSym-QVars, QSymsVars)
		do  Q =.. [QSym|QVars]
		),
		format_atom('~p-grd-~p', [Sym, I], TId),
		assert(skolem_guard_defs(Sym, TId)),
		add_tc(TId, ProjAs, QSymsVars, false-[])
	    ;   true
	    )
	),
	format('done skolem_solution_to_clause ~p\n', [Sym]).

