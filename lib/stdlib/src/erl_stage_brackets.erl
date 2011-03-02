%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2011 All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%
%% File    : erl_stage_brackets.erl
%% Author  : Anthony Ramine <nox@dev-extend.eu>
%% Purpose : Expand brackets into abstract trees.

-module(erl_stage_brackets).

-export([module/1, expr/1, pattern/1]).

%% Is is assumed that Fs is a valid list of forms. It should pass erl_lint
%% without errors.
module(Fs) ->
    forms(Fs, []).

forms([{attribute, _, _, _} = Attr | Fs], Acc) ->
    forms(Fs, [Attr | Acc]);
forms([{function, Line, Name, A, Cs} | Fs], Acc) ->
    NewCs = clauses(Cs, Line),
    forms(Fs, [{function, Line, Name, A, NewCs} | Acc]);
forms([{eof, _}] = End, Acc) ->
    lists:reverse(Acc, End).

clauses(Cs, Line) ->
    TCs = walk_clauses(Cs, Line, {expr, return}),
    walk_clauses(TCs, Line, {expr, line}).

expr(E) ->
    walk_expr(walk_expr(E, {expr, return}), {expr, line}).

pattern(P) ->
    walk_pattern(walk_pattern(P, {pattern, return}), {pattern, line}).

walk_clauses(Cs, Line, St) ->
    element(1, walk_some_wrap(Cs, Line, St, fun walk_clause/2)).

walk_clause({clause, Line, H, G, B}, St) ->
    TH = element(1, walk_some_wrap(H, Line, St, fun walk_pattern/2)),
    TG = walk_guard(G, Line, St),
    TB = walk_exprs(B, Line, St),
    node(clause, Line, [TH, TG, TB], St).

walk_guard([GTs | Gs], Line, St) ->
    {TGTs, Lg} = walk_some_wrap(GTs, Line, St, fun walk_expr/2),
    term([TGTs | walk_guard(Gs, Lg, St)], Lg, St);
walk_guard([], Line, St) ->
    term([], Line, St).

walk_exprs(Es, Line, St) ->
    element(1, walk_some_wrap(Es, Line, St, fun walk_expr/2)).

walk_pattern({match, Line, P, E}, St) ->
    node(match, Line, [walk_pattern(P, St), walk(E, St)], St);
walk_pattern(P, St) ->
    walk_common(P, St).

walk_expr({lc, _, _, _} = ListComp, St) ->
    walk_comp(ListComp, St);
walk_expr({bc, _, _, _} = BinComp, St) ->
    walk_comp(BinComp, St);
walk_expr({block, Line, Es}, St) ->
    node(block, Line, [walk_exprs(Es, Line, St)], St);
walk_expr({'if', Line, Cs}, St) ->
    node('if', Line, [walk_clauses(Cs, Line, St)], St);
walk_expr({'case', Line, E, Cs}, St) ->
    node('case', Line, [walk_expr(E, St), walk_clauses(Cs, Line, St)], St);
walk_expr({'receive', Line, Cs}, St) ->
    node('receive', Line, [walk_clauses(Cs, Line, St)], St);
walk_expr({'receive', Line, Cs, To, ToEs}, St) ->
    TCs = walk_clauses(Cs, Line, St),
    TTo = walk_expr(To, St),
    TToEs = element(1, walk_exprs(ToEs, Line, St)),
    node('receive', Line, [TCs, TTo, TToEs], St);
walk_expr({'fun', Line, {function, F, A}}, St) ->
    TF = term(F, Line, St),
    TA = term(A, Line, St),
    TFA = term({term(function, Line, St), TF, TA}, Line, St),
    node('fun', Line, [TFA], St);
walk_expr({'fun', Line, {function, M, F, A}}, St) ->
    TM = term(M, Line, St),
    TF = term(F, Line, St),
    TA = term(A, Line, St),
    TMFA = term({term(function, Line, St), TM, TF, TA}, Line, St),
    node('fun', Line, [TMFA], St);
walk_expr({'fun', Line, {clauses, Cs}}, St) ->
    TCs = walk_clauses(Cs, Line, St),
    TClauses = term({term(clauses, Line, St), TCs}, Line, St),
    node('fun', Line, [TClauses], St);
walk_expr({call, Line, {remote, Lr, Mod, Fun}, As}, St) ->
    TMod = walk_expr(Mod, St),
    TFun = walk_expr(Fun, St),
    TAs = walk_exprs(As, Line, St),
    node(call, Line, [node(remote, Lr, [TMod, TFun], St), TAs], St);
walk_expr({call, Line, Fun, As}, St) ->
    TFun = walk_expr(Fun, St),
    TAs = walk_exprs(As, Line, St),
    node(call, Line, [TFun, TAs], St);
walk_expr({'try', Line, Es, SCs, CCs, As}, St) ->
    TEs = walk_exprs(Es, Line, St),
    TCs = walk_clauses(SCs, Line, St),
    TCs = walk_clauses(CCs, Line, St),
    TAs = walk_exprs(As, Line, St),
    node('try', Line, [TEs, TCs, TCs, TAs], St);
walk_expr({'catch', Line, E}, St) ->
    node('catch', Line, [walk_expr(E, St)], St);
walk_expr({match, Line, P, E}, St) ->
    node(match, Line, [walk(pattern(P), St), walk(E, St)], St);
walk_expr(E, St) ->
    walk_common(E, St).

walk_common({var, _, _} = Var, St) ->
    walk_term(Var, St);
walk_common({char, _, _} = Char, St) ->
    walk_term(Char, St);
walk_common({integer, _, _} = Int, St) ->
    walk_term(Int, St);
walk_common({float, _, _} = Float, St) ->
    walk_term(Float, St);
walk_common({atom, _, _} = Atom, St) ->
    walk_term(Atom, St);
walk_common({string, _, _} = String, St) ->
    string(String, St);
walk_common({nil, Line}, St) ->
    node(nil, Line, [], St);
walk_common({cons, Line, H, T}, St) ->
    node(cons, Line, [walk(H, St), walk(T, St)], St);
walk_common({tuple, Line, Es}, St) ->
    TEs = element(1, walk_some_wrap(Es, Line, St, fun walk/2)),
    node(tuple, Line, [TEs], St);
walk_common({bin, Line, Es}, St) ->
    TEs = element(1, walk_some(Es, Line, St, fun walk_bin_element/2)),
    node(bin, Line, [TEs], St);
walk_common({op, Line, Op, A}, St) ->
    node(op, Line, [term(Op, Line, St), walk(A, St)], St);
walk_common({op, Line, Op, L, R}, St) ->
    TL = walk(L, St),
    TR = walk(R, St),
    node(op, Line, [term(Op, Line, St), TL, TR], St);
walk_common({line, _, _} = Line, St) ->
    line(Line, St);
walk_common({escape, _Line, _A} = E, St) ->
    escape(E, St);
walk_common({code, _Line, _A} = E, St) ->
    stage(E, St).

walk_comp({Type, Line, E, Qs}, St) ->
    TE = walk_expr(E, St),
    TQs = element(1, walk_some_wrap(Qs, Line, St, fun walk_qual/2)),
    node(Type, Line, [TE, TQs], St).

walk_qual({generate, _, _, _} = ListGen, St) ->
    walk_gen(ListGen, St);
walk_qual({b_generate, _, _, _} = BinGen, St) ->
    walk_gen(BinGen, St);
walk_qual(Q, St) ->
    walk_expr(Q, St).

walk_gen({Type, Line, P, G}, St) ->
    TP = walk_expr(pattern(P), St),
    TG = walk_expr(G, St),
    node(Type, Line, [TP, TG], St).

walk_bin_element({bin_element, Line, Expr, Size, Type}, St) ->
    TExpr = walk(Expr, St),
    TSize = case Size of
                default -> term(default, Line, St);
                _ -> walk(Size, St)
            end,
    TType = term(Type, Line, St),
    {node(bin_element, Line, [TExpr, TSize, TType], St), Line}.

walk_some([E | Es], _Line, St, F) ->
    {TE, Le} = F(E, St),
    {TEs, Line} = walk_some(Es, Le, St, F),
    {term([TE | TEs], Line, St), Line};
walk_some([], Line, St, _F) ->
    {term([], Line, St), Line}.

walk_some_wrap(Es, Line, St, F) ->
    F1 = fun (E, St1) ->
             TE = F(E, St1),
             {TE, element(2, TE)}
         end,
    walk_some(Es, Line, St, F1).

walk_term({Type, Line, Term}, St) ->
    node(Type, Line, [term(Term, Line, St)], St).

string({string, Line, _} = Node, {_, lift} = St) ->
    node(string, Line, [Node], St);
string(Node, _St) ->
    Node.

node(Type, Line, Rest, St) ->
    TType = term(Type, Line, St),
    TLine = line(Line, St),
    term(list_to_tuple([TType, TLine | Rest]), Line, St).

walk(E, {expr, _} = St) ->
    walk_expr(E, St);
walk(P, {pattern, _} = St) ->
    walk_pattern(P, St).

escape({escape, _Line, A}, {_, lift}) ->
    A;
escape({escape, _Line, _A} = E, _St) ->
    E.

stage({code, _Line, A}, St) ->
    walk(walk_expr(walk_expr(A, {expr, return}), {expr, lift}), St).

term(Term, Line, {_, lift}) ->
    lift(Term, Line);
term(Term, _Line, _St) ->
    Term.

lift([H | T], Line) ->
    {cons, Line, H, T};
lift([], Line) ->
    {nil, Line};
lift(Tuple, Line) when is_tuple(Tuple) ->
    {tuple, Line, tuple_to_list(Tuple)};
lift(Term, Line) ->
    erl_parse:abstract(Term, Line).

line(Line, {_, return}) ->
    Line;
line({line, Line, Level}, {_, lift}) ->
    {line, Line, Level + 1};
line(Line, {_, lift}) ->
    {line, Line, 1};
line({line, Line, Level}, {expr, line}) ->
    abstract_line(Line, Level);
line({line, Line, _Level}, {pattern, line}) ->
    {var, Line, '_'};
line(Line, _St) ->
    Line.

abstract_line(Line, 0) ->
    Line;
abstract_line(Line, Level) ->
    erl_parse:abstract(abstract_line(Line, Level - 1), Line).
