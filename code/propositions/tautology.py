# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
# from propositions.operators import *
from propositions.axiomatic_systems import *

def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a

    model_return = list()

    for val in sorted(model):
        if model[val]:
            model_return.append(Formula(val))
        else:
            model_return.append(Formula("~", Formula(val)))

    return model_return

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

    model_use = formulae_capturing_model(model) #updating model


    #base case
    if is_variable(formula.root):
        if formula in model_use: # assumption
            return Proof(InferenceRule(model_use, formula), AXIOMATIC_SYSTEM, [Proof.Line(formula)])
        else:
            return Proof(InferenceRule(model_use, Formula("~", formula)),
                         AXIOMATIC_SYSTEM, [Proof.Line(Formula("~", formula))])

    if is_unary(formula.root) and is_variable(formula.first.__repr__()):
        if model[formula.first.__repr__()]:
            lines = list()
            lines.append(Proof.Line(formula.first))
            lines.append(Proof.Line(Formula("->", formula.first, Formula("~", formula)), NN, []))
            lines.append(Proof.Line(Formula("~", formula), MP, [0,1]))
            return Proof(InferenceRule(model_use, Formula("~", formula)), AXIOMATIC_SYSTEM, lines)
        return Proof(InferenceRule(model_use, formula), AXIOMATIC_SYSTEM, [Proof.Line(formula)])

    #second case
    if is_unary(formula.root):
        my_proof = prove_in_model(formula.first, model)
        if not evaluate(formula, model):
            return prove_corollary(my_proof, Formula("~", formula), NN)
        return my_proof

    else: # third case -> without ~
        if evaluate(formula, model): #No negation
            if not evaluate(formula.first, model): # True if the first is false or the scd is true
                my_proof = prove_in_model(Formula("~", formula.first), model)
                return prove_corollary(my_proof, formula, I2)
            if evaluate(formula.second, model):
                return prove_corollary(prove_in_model(formula.second, model), formula, I1)
        my_proof_left = prove_in_model(formula.first, model)
        my_proof_right = prove_in_model(formula.second, model)
        return combine_proofs(my_proof_left, my_proof_right, Formula("~", formula), NI)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2

    remove_affirmation = remove_assumption(proof_from_affirmation)
    remove_negation = remove_assumption(proof_from_negation)
    return combine_proofs(remove_affirmation, remove_negation, proof_from_negation.statement.conclusion, R)

def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a

    variables = tautology.variables()
    model_variables = model.keys()

    if len(variables - model_variables) == 0:
        return prove_in_model(tautology, model)

    for var in sorted(variables):
        if var not in sorted(model_variables):
            aff_model, neg_model = dict(model), dict(model) #getting all the values
            aff_model[var] = True #updating the dicts to the booleans we need for the values
            neg_model[var] = False
            affimation = prove_tautology(tautology, aff_model)
            negation = prove_tautology(tautology, neg_model)
            return reduce_assumption(affimation, negation)

def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b

    variables = sorted(formula.variables())
    models = all_models(variables)

    for model in models:
        if not evaluate(formula, model):
            return model

    return prove_tautology(formula)



def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a

    if len(rule.assumptions) == 0:
        return rule.conclusion

    if len(rule.assumptions) > 1 :
        new_formula = encode_as_formula(InferenceRule(rule.assumptions[1:], rule.conclusion))
        return Formula("->", rule.assumptions[0], new_formula)

    return Formula("->", rule.assumptions[0], rule.conclusion) # len == 1

def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b



    proof_t = prove_tautology(encode_as_formula(rule))
    my_formula = encode_as_formula(rule)
    lines = list(proof_t.lines)

    for index, ass in enumerate(rule.assumptions):
        my_formula = my_formula.second
        lines.append(Proof.Line(ass))
        index_start = len(proof_t.lines) - 1 + 2 * index + 1
        index_end = len(proof_t.lines) - 1 + 2 * index
        lines.append(Proof.Line(my_formula, MP, [index_start, index_end]))

    return  Proof(rule, AXIOMATIC_SYSTEM, lines)

def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5

    rule = InferenceRule(list(formulae), Formula.parse("~(p->p)"))
    if is_sound_inference(rule):
        return prove_sound_inference(rule)
    return proof_or_counterexample(encode_as_formula(rule))

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
